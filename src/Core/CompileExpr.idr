-- Representation of expressions ready for compiling
-- Explicit case trees, types retained
module Core.CompileExpr

import Core.TT

import Data.List
import Data.Vect
import Data.String

%default covering

mutual
  ||| CExp - an expression ready for compiling.
  public export
  data CExp : List Name -> Type where
       CLocal : {idx : Nat} ->  (0 p : IsVar x idx vars) -> CExp vars
       CRef : Name -> CExp vars
       -- Lambda expression
       CLam :  (x : Name) -> (ty : CExp vars) -> (sc : CExp (x :: vars)) -> CExp vars
       -- Pi expression
       CPi  :  (x : Name) -> (ty : CExp vars) -> (sc : CExp (x :: vars)) -> CExp vars
       -- Let bindings
       CLet :  (x : Name) -> (val : CExp vars) -> (ty : CExp vars) ->
               (sc : CExp (x :: vars)) -> CExp vars
       -- Application of a defined function. The length of the argument list is
       -- exactly the same length as expected by its definition (so saturate with
       -- lambdas if necessary, or overapply with additional CApps)
       CApp :  (f : CExp vars) -> (args : List (CExp vars)) -> CExp vars
       -- A saturated constructor application
       CCon :  (x : Name) ->
              (args : List (CExp vars)) -> CExp vars
       -- A case match statement
       CConCase :  (scr : CExp vars) -> (alts : List (CConAlt vars)) -> (def : Maybe (CExp vars)) -> CExp vars
       -- An erased value
       CErased :  CExp vars

  public export
  data CConAlt : List Name -> Type where
    -- If no tag, then match by constructor name. Back ends might want to
    -- convert names to a unique integer for performance.
    MkConAlt : Name -> (args : List Name) ->
               CExp (args ++ vars) -> CConAlt vars

public export
data CDef : Type where
  -- Normal function defnition
  MkFun : (args : List Name) -> (ty : CExp []) -> CExp args -> CDef
  -- Constructor
  MkCon : (tag : Maybe Int) -> (arity : Nat) -> CDef

mutual
  export
  insertNames : {outer : _} -> (ns : List Name) -> CExp (outer ++ inner) ->
                CExp (outer ++ (ns ++ inner))
  insertNames ns (CLocal {idx} p)
    = let MkNVar var' = insertNVarNames idx p
      in CLocal var'
  insertNames ns (CRef n) = CRef n
  insertNames ns (CLam x ty sc)
    = let sc' = insertNames {outer=x :: outer} ns sc
          ty' = insertNames ns ty
      in CLam x ty' sc'
  insertNames ns (CPi  x ty sc)
    = let sc' = insertNames {outer=x :: outer} ns sc
          ty' = insertNames ns ty
      in CPi  x ty' sc'
  insertNames ns (CLet x val ty sc)
    = let sc' = insertNames {outer=x :: outer} ns sc
          ty' = insertNames ns ty
          val' = insertNames ns val
      in CLet x val' ty' sc'
  insertNames ns (CApp f args) = CApp (insertNames ns f) (map (insertNames ns) args)
  insertNames ns (CCon x args) = CCon x $ map (insertNames ns) args
  insertNames ns (CConCase scr alts def)
    = let scr'  = insertNames ns scr
          alts' = map (insertNamesConAlt ns) alts
          def'  = map (insertNames ns) def
      in CConCase scr' alts' def'
  insertNames ns CErased = CErased

  insertNamesConAlt : {outer : _} -> (ns : List Name) -> CConAlt (outer ++ inner) ->
                      CConAlt (outer ++ (ns ++ inner))
  insertNamesConAlt ns (MkConAlt x args sc)
    = let sc' : CExp ((args ++ outer) ++ inner)
              = rewrite sym (appendAssociative args outer inner) in sc
      in MkConAlt x args (rewrite appendAssociative args outer (ns ++ inner) in
                          insertNames {outer=args++outer} ns sc')

export
Weaken CExp where
  weakenNs ns tm = insertNames {outer=[]} ns tm

export
Weaken CConAlt where
  weakenNs ns tm = insertNamesConAlt {outer=[]} ns tm

mutual
  -- Shrink the scope of a compiled expression, replacing any variables not
  -- in the remaining set with Erased
  export
  shrinkCExp : SubVars newvars vars -> CExp vars -> CExp newvars
  shrinkCExp sub (CLocal p)
    = case subElem p sub of
        Nothing => CErased
        Just (MkVar p') => CLocal p'
  shrinkCExp sub (CRef x) = CRef x
  shrinkCExp sub (CLam x ty sc)
    = let sc' = shrinkCExp (KeepCons sub) sc
          ty' = shrinkCExp sub ty
      in CLam x ty' sc'
  shrinkCExp sub (CPi x ty sc)
    = let sc' = shrinkCExp (KeepCons sub) sc
          ty' = shrinkCExp sub ty
      in CPi x ty' sc'
  shrinkCExp sub (CLet x val ty sc)
    = let sc' = shrinkCExp (KeepCons sub) sc
          ty' = shrinkCExp sub ty
          val' = shrinkCExp sub val
      in CLet x val' ty' sc'
  shrinkCExp sub (CApp f args)
    = CApp (shrinkCExp sub f) (map (shrinkCExp sub) args)
  shrinkCExp sub (CCon x args)
    = CCon x $ map (shrinkCExp sub) args
  shrinkCExp sub (CConCase scr alts def)
    = CConCase (shrinkCExp sub scr)
               (map (shrinkConAlt sub) alts)
               (map (shrinkCExp   sub) def)
  shrinkCExp sub CErased = CErased

  shrinkConAlt : SubVars newvars vars -> CConAlt vars -> CConAlt newvars
  shrinkConAlt sub (MkConAlt x args sc)
    = MkConAlt x args (shrinkCExp (subExtend args sub) sc)

-- Substitute some explicit terms for names in a term, and remove those
-- names from the scope
namespace SubstCEnv
  public export
  data SubstCEnv : List Name -> List Name -> Type where
       Nil : SubstCEnv [] vars
       (::) : CExp vars ->
              SubstCEnv ds vars -> SubstCEnv (d :: ds) vars

findDrop : Var (dropped ++ vars) ->
           SubstCEnv dropped vars -> CExp vars
findDrop (MkVar p) [] = CLocal p
findDrop (MkVar First) (tm :: env) = tm
findDrop (MkVar (Later p)) (tm :: env) = findDrop (MkVar p) env

find : {outer, vars : _} ->
       Var (outer ++ (dropped ++ vars)) ->
       SubstCEnv dropped vars ->
       CExp (outer ++ vars)
find {outer=[]} var env = findDrop var env
find {outer=(o::os)} (MkVar First) env = CLocal First
find {outer=(o::os)} (MkVar (Later p)) env = weaken (find (MkVar p) env)

mutual
  substEnv : {outer, vars, dropped : _} ->
             SubstCEnv dropped vars ->
             CExp (outer ++ (dropped ++ vars)) ->
             CExp (outer ++ vars)
  substEnv env (CLocal p) = find (MkVar p) env
  substEnv env (CRef x) = CRef x
  substEnv env (CLam x ty sc)
    = let sc' = substEnv {outer=x::outer} env sc
          ty' = substEnv env ty
      in CLam x ty' sc'
  substEnv env (CPi x ty sc)
    = let sc' = substEnv {outer=x::outer} env sc
          ty' = substEnv env ty
      in CPi x ty' sc'
  substEnv env (CLet x val ty sc)
    = let sc' = substEnv {outer=x::outer} env sc
          ty' = substEnv env ty
          val' = substEnv env val
      in CLet x val' ty' sc'
  substEnv env (CApp f args) = CApp (substEnv env f) (map (substEnv env) args)
  substEnv env (CCon x args) = CCon x (map (substEnv env) args)
  substEnv env (CConCase scr alts def)
    = CConCase (substEnv env scr)
               (map (substEnvConAlt env) alts)
               (map (substEnv env) def)
  substEnv env CErased = CErased

  substEnvConAlt : {outer, vars, dropped: _} ->
                   SubstCEnv dropped vars ->
                   CConAlt (outer ++ (dropped ++ vars)) ->
                   CConAlt (outer ++ vars)
  substEnvConAlt {outer} {vars} {dropped} env (MkConAlt x args sc)
    = MkConAlt x args
       (rewrite appendAssociative args outer vars in
                substEnv {outer=args++outer} env
                  (rewrite sym (appendAssociative args outer (dropped ++vars)) in sc))

export
substs : {dropped, vars : _} ->
         SubstCEnv dropped vars -> CExp (dropped ++ vars) -> CExp vars
substs env tm = substEnv {outer=[]} env tm

spacerFor : String -> String
spacerFor s = replicate (length s) ' '

mutual
  showCExp : {vars : _} -> String -> CExp vars -> String
  showCExp indent (CLocal {idx} p) = indent ++ "(local " ++ show (nameAt idx p) ++ ")"
  showCExp indent (CRef x) = indent ++ "(ref " ++ show x ++ ")"
  showCExp indent CErased = indent ++ "erased"
  showCExp indent (CLam x ty sc)
    = unlines [ indent ++ "(\\" ++ show x ++ " =>"
              , showCExp (indent ++ "  ") sc ++ indent ++ ")"
              ]
  showCExp indent (CPi x ty sc) = indent ++ "Pi ..."
  showCExp indent (CLet x val ty sc)
    = indent ++ "(let " ++ show x ++ " = " ++ show val ++ " in " ++ show sc ++ ")"
  showCExp indent (CApp f args)
    = unlines [ indent ++ "(" ++ show f ++ "["
              , unlines (map (showCExp (indent++"  ")) args) ++ indent ++ "])"
              ]
  showCExp indent (CCon x []) = indent ++ "(" ++ show x ++ " [])"
  showCExp indent (CCon x args)
    = unlines [ indent ++ "(" ++ show x ++ "["
              , unlines (map (showCExp (indent++"  ")) args) ++ indent ++ "])"
              ]
  showCExp indent (CConCase scr alts def)
    = indent ++ "(case " ++ show scr ++ " of {\n" ++
      unlines (map (showCExpConAlt (indent ++ "  ")) alts)
      ++ indent ++ "  " ++ (fromMaybe "" (map (\x=> "_ => " ++ show x) def)) ++ "\n" ++ indent ++ "})"

  showCExpConAlt : {vars : _} -> String -> CConAlt vars -> String
  showCExpConAlt indent (MkConAlt x args sc)
    = indent ++ show x ++ " " ++ show args ++ " =>\n" ++ showCExp ("  " ++ indent) sc
{-
  showCExp : {vars : _} -> String -> CExp vars -> String
  showCExp indent (CLocal {idx} p) = indent ++ "(local " ++ show (nameAt idx p) ++ ")"
  showCExp indent (CRef x) = indent ++ "(ref " ++ show x ++ ")"
  showCExp indent CErased = indent ++ "erased"
  showCExp indent (CLam x ty sc)
    = let intro = "\\" ++ show x ++ " : "
      in unlines [ indent ++ intro
                 , showCExp (spacerFor intro ++ indent) ty
                 , indent ++  " => "
                 , showCExp (spacerFor " => " ++ indent) sc
                 ]
  showCExp indent (CPi x ty sc)
    = let intro = "\\pi " ++ show x ++ " : "
      in unlines [ indent ++ intro
                 , showCExp (spacerFor intro ++ indent) ty
                 , indent ++  " => "
                 , showCExp (spacerFor " => " ++ indent) sc
                 ]
  showCExp indent (CLet x val ty sc)
    = let intro = "let " ++ show x ++ " : "
      in unlines [ indent ++ intro
                 , showCExp (spacerFor intro ++ indent) ty
                 , indent ++ (spacerFor "let " ++ show x) ++ " = "
                 , showCExp (spacerFor intro ++ indent) val ++ " in"
                 , showCExp indent sc
                 ]
  showCExp indent (CApp f args) = indent ++ "(" ++ show f ++ " @ " ++ show args ++ ")"
  showCExp indent (CCon x args) = indent ++ "(con " ++ show x ++ " @ " ++ show args ++ ")"
  showCExp indent (CConCase scr alts def)
    = unlines $ [ indent ++ "case "
              , showCExp (indent ++ spacerFor "case ") scr ++ " of"
              ] ++ map (showCExpConAlt (indent ++ spacerFor "case ")) alts
                ++ [show $ map (showCExp       (indent ++ spacerFor "case ")) def]

  showCExpConAlt : {vars : _} -> String -> CConAlt vars -> String
  showCExpConAlt indent (MkConAlt x args sc)
    = unlines [ indent ++ show x
              , indent ++ "  with args " ++ show args
              , indent ++ "  => "
              , showCExp (spacerFor "  => " ++ indent) sc
              ]
-}

  export
  {vars : _} -> Show (CExp vars) where
    show tm = showCExp "" tm

  export
  {vars : _} -> Show (CConAlt vars) where
    show tm = showCExpConAlt "" tm

  export
  Show CDef where
    show (MkFun args ty x) = "func with (" ++ show args ++ ") : " ++ show ty ++ " =\n" ++ show x
    show (MkCon tag arity) = "con " ++ show tag ++ " [" ++ show arity ++ " args]"