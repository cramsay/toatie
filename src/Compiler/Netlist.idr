module Compiler.Netlist

import Compiler.CompileExpr

import Core.CompileExpr
import Core.TT
import Core.Env
import Core.Context
import Core.UnifyState

import Compiler.Inline
import TTImp.ProcessData

import Data.Nat
import Data.Maybe
import Data.List
import Data.Vect
import Data.String

%default covering

data SType = SLV Nat Nat
           | SUnit

data STag = Tag Nat   Nat
         -- ^   width value

data SAtom = Const STag
           | Signal Name

data STree = Tree SAtom (List STree)

data SExpr = SSplit Name  --^ Output signal
                    Nat   --^ Upper bound
                    Nat   --^ Lower bound
                    SAtom --^ Input signal

           | SJoin  Name         --^ Output signal
                    STag         --^ Tag for this constructor
                    (List STree) --^ Ordered inputs

           | SMux   Name                --^ Output signal
                    Nat                 --^ Tag upper bound
                    Nat                 --^ Tag lower bound
                    Name                --^ Scrutinee name
                    (List (STag,STree)) --^ Clause tag and returns
                    STree               --^ "Others" clause

           | SId    Name --^ Output name
                    Name --^ Input name

record Netlist where
  constructor MkNetlist
  -- Entity info
  name : Name
  inputs : List (Name, SType)
  output : SType

  -- Architecture
  signals : List (Name, SType)
  assignments : List SExpr

isConst : SAtom -> Bool
isConst (Const  _) = True
isConst (Signal _) = False

addSignal : Netlist -> Name -> SType -> Netlist
addSignal nl n ty = record { signals $= ((n,ty)::) } nl

addAssignment : Netlist -> SExpr -> Netlist
addAssignment nl a = record { assignments $= (a::) } nl

outputName : Name
outputName = UN "res"

pruneSTree : STree -> Maybe STree
pruneSTree (Tree (Const (Tag 0 0)) []) = Nothing
pruneSTree (Tree (Const (Tag 0 0)) xs)
  = do let xs' = map pruneSTree xs
       let [] = mapMaybe id xs'
            | ((Tree x ys) :: xs'') => pure $ Tree x (ys ++ xs'')
       Nothing
pruneSTree (Tree x xs) = do let xs' = map pruneSTree xs
                            let xs'' = mapMaybe id xs'
                            pure $ (Tree x xs'')

pruneSJoin : SExpr -> Maybe SExpr
pruneSJoin (SJoin x (Tag 0 0) xs) = do let xs' = map pruneSTree xs
                                       let [] = mapMaybe id xs'
                                            | xs'' => pure $ SJoin x (Tag 0 0) xs''
                                       Nothing
pruneSJoin (SJoin x tag xs) = do let xs' = map pruneSTree xs
                                 let xs'' = mapMaybe id xs'
                                 pure $ SJoin x tag xs''
pruneSJoin tm = Just tm

typeToSType : {auto c : Ref Ctxt Defs} ->
              {auto u : Ref UST UState} ->
              Term [] -> Core SType
typeToSType ty = do wTag <- tyTagWidth [] ty
                    wField <- tyFieldWidth [] ty
                    let (S w) = plus wTag wField
                           | Z => pure SUnit-- throw $ InternalError $ "Trying to synthesise an empty type: " ++ show ty
                    pure $ SLV w Z

tagForCons : {auto c : Ref Ctxt Defs} ->
             {auto u : Ref UST UState} ->
             Term [] -> Name -> Core STag
tagForCons ty n
  = do opts <- dataConsForType [] ty
       ntag <- findTag n Z opts
       wtag <- tyTagWidth [] ty
       pure $ Tag wtag ntag
  where
  findTag : Name -> Nat -> List (Name, Term[]) -> Core Nat
  findTag n tag ((conn,conty)::ms)
    = if n==conn then pure tag
                 else findTag n (S tag) ms
  findTag n tag [] = throw $ InternalError $ "Constructor " ++ show n ++
                       " isn't a valid option for the type " ++ show ty

tmToName : {vars : _} ->
            {auto c : Ref Ctxt Defs} ->
            {auto u : Ref UST UState} ->
            Term [] ->
            CExp vars -> Core SAtom
tmToName ty (CLocal {idx} p) = pure $ Signal (nameAt idx p)
tmToName ty (CCon n []) = do tag <- tagForCons ty n
                             pure $ Const tag
tmToName ty tm = throw $ InternalError $ "Can't convert term to SAtom: " ++ show tm

tmToSTree : {vars : _} ->
            {auto c : Ref Ctxt Defs} ->
            {auto u : Ref UST UState} ->
            List (Term []) -> Term [] ->
            CExp vars -> Core STree
tmToSTree tys ty (CLocal {idx} p) = pure $ Tree (Signal $ nameAt idx p) []
tmToSTree tys ty (CCon n args)
  = do tag <- tagForCons ty n
       let iargs = zip [0 .. length args] args
       args' <- traverse argToSTree iargs
       pure $ Tree (Const tag) args'
  where
  argToSTree : (Nat, CExp vars) -> Core STree
  argToSTree (field, arg) = do argty <- getFieldType [] ty n field
                               tmToSTree tys argty arg
tmToSTree tys ty tm = throw $ InternalError $ "Can't convert term to STree: " ++ show tm

netlistTm : {vars : _} -> {auto c : Ref Ctxt Defs} ->
            {auto u : Ref UST UState} ->
            Netlist -> List (Term []) -> CExp vars -> Core Netlist
-- Bind locals to SId
netlistTm nl tys (CLet x (CLocal {idx} p) ty sc)
  = do nl' <- netlistTm nl (ty::tys) sc
       let nl' = addSignal nl' x !(typeToSType ty)
       let nl' = addAssignment nl' (SId x $ nameAt idx p)
       pure nl'
-- Bind constructor application to SJoin
netlistTm nl tys (CLet x (CCon n args) ty sc)
  = do nl' <- netlistTm nl (ty::tys) sc
       let nl' = addSignal nl' x !(typeToSType ty)
       tag <- tagForCons ty n
       args' <- traverse argToSTree (zip [0 .. length args] args)
       Z <- getConsPadding [] ty n
         | pad => do let j = (SJoin x tag (args'++[Tree (Const $ Tag pad 0) []]))
                     let Just j' = pruneSJoin j
                          | Nothing => pure nl'
                     pure $ addAssignment nl' j'
       let j = (SJoin x tag args')
       let Just j' = pruneSJoin j
         | Nothing => pure nl'
       pure $ addAssignment nl' j'
  where
  argToSTree : (Nat, CExp vars) -> Core STree
  argToSTree (field, arg) = do argty <- getFieldType [] ty n field
                               tmToSTree tys argty arg
netlistTm nl tys (CLet x (CConCase (CLocal {idx} p) alts def) ty sc)
  = do nl' <- netlistTm nl (ty::tys) sc
       scTy <- typeOfLocal tys idx
       let nl' = addSignal nl' x !(typeToSType ty)
       (tagu, tagl) <- getTagPos [] scTy
       alts' <- traverse (netlistAlt scTy ty) alts
       def'  <- netlistDef ty def
       let cs = SMux x tagu tagl (nameAt idx p) alts' def'
       pure $ addAssignment nl' cs
  where

  netlistAlt : Term [] -> Term [] -> CConAlt vars -> Core (STag,STree)
  netlistAlt scTy ty (MkConAlt n args tm)
    = do let tys' = map (const Erased) args ++ tys
         tag <- tagForCons scTy n
         tree <- tmToSTree tys' ty tm
         let Just tree' = pruneSTree tree
               | Nothing => throw $ GenericMsg $ "Alternative scrutinee is empty!"
         pure (tag,tree')

  netlistDef : Term [] -> Maybe (CExp vars) -> Core STree
  netlistDef ty Nothing = do wTag <- tyTagWidth [] ty
                             wFields <- tyFieldWidth [] ty
                             pure $ Tree (Const $ Tag (plus wTag wFields) 0) []
  netlistDef ty (Just tm) =  tmToSTree tys ty tm
netlistTm nl tys (CLet x (CPrj con field (CLocal {idx} p)) ty sc)
  = do nl' <- netlistTm nl (ty::tys) sc
       let nl' = addSignal nl' x !(typeToSType ty)
       let inner = Signal (nameAt idx p)
       Just (u,l) <- getFieldPos [] !(typeOfLocal tys idx) con field
         | Nothing => pure $ nl' --addAssignment nl' (SJoin x (Tag 0 0) [])
       pure $ addAssignment nl' (SSplit x u l inner)
-- Output refers to name
netlistTm nl tys (CLocal {idx} p) = pure $ addAssignment nl (SId outputName (nameAt idx p))
-- Catch-all
netlistTm nl tys tm
  = throw $ InternalError $ "Term is not in normal form for netlist generation: " ++ show tm

export
genNetlist : {auto c : Ref Ctxt Defs} ->
             Name ->
             Core Netlist
genNetlist n
  = do u <- newRef UST initUState
       defs <- get Ctxt
       Just gdef <- lookupDef n defs
         | Nothing => throw $ InternalError $ "Couldn't find function in context: " ++ show n
       let Just (MkFun args prog) = compexpr gdef
             | _ => throw $ InternalError $ "Couldn't find compiled function in context: " ++ show n

       (argTys, retTy) <- closedQuoteType $ type gdef

       -- Make initial netlist record with in/out types
       let nl = MkNetlist
                  n
                  (zip args !(traverse typeToSType argTys)) -- Inputs
                  !(typeToSType retTy)                      -- Outputs
                  [] -- Signals
                  [] -- Assignments

       netlistTm nl argTys prog

showName : Name -> String
showName (UN x) = x
showName (MN x y) = x ++ "_" ++ show y

export
Show SType where
  show (SLV u l) = "std_logic_vector (" ++ show u ++ " downto " ++ show l ++ ")"
  show SUnit = "std_logic_vector (99 downto 100)"

Show STag where
  show tag = "\"" ++ show' tag ++ "\""
    where
    show' : STag -> String
    show' (Tag 0 val) = ""
    show' (Tag (S k) val) = let val' = divNatNZ val 2 SIsNonZero
                            in case modNatNZ val 2 SIsNonZero of
                                 Z => show' (Tag k val') ++ "0"
                                 _ => show' (Tag k val') ++ "1"

Show SAtom where
  show (Const x) = show x
  show (Signal x) = showName x

Show STree where
  show (Tree atom []) = show atom
  show (Tree atom rest) = show atom ++ foldl (\acc=> \elem=> acc ++ " & " ++ show elem) "" rest

Show SExpr where
  show (SSplit x u l y) = showName x ++ " <= " ++ show y ++ "(" ++ show u ++ " downto " ++ show l ++ ");"
  show (SJoin x y []) = showName x ++ " <= " ++ show y ++ ";"
  show (SJoin x y xs) = showName x ++ " <= " ++ show y ++ foldl (\acc => \elem => acc ++ " & " ++ show elem) "" xs ++ ";"
  show (SMux x u l scr xs def)
    = unlines $ ("with " ++ showName scr ++ "(" ++ show u ++ " downto " ++ show l ++ ") select " ++ showName x ++ " <=")
        :: map (\(tag,tm) => "    " ++ show tm ++ " when " ++ show tag ++ ",") xs
        ++ ["    " ++ show def ++ " when others;"
      ]
  show (SId x y) = showName x ++ " <= " ++ showName y ++ ";"

export
Show Netlist where
  show (MkNetlist name inputs output signals assignments)
    = unlines [
         "library ieee;"
        ,"use ieee.std_logic_1164.all;"
        ,"use ieee.numeric_std.all;"
        ,"entity " ++ showName name ++ " is"
        ,"  port (\n" ++ concat (map (\(n,ty)=>"    " ++ showName n ++ " : in " ++ show ty ++ ";\n") inputs)
                      ++ "    " ++ showName outputName ++ " : out " ++ show output ++ "\n  );"
        ,"end " ++ showName name ++ ";"
        ,""
        ,"architecture behaviour of " ++ showName name ++ " is"
        ,unlines (map (\(n, ty) => "  signal " ++ showName n ++ " : " ++ show ty ++ ";") signals)
        ,"begin"
        ,unlines (map (\e => "  " ++ show e) assignments)
        ,"end behaviour;"
        ]
