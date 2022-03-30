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
       CLam :  (x : Name) -> (sc : CExp (x :: vars)) -> CExp vars
       -- Let bindings
       CLet :  (x : Name) -> (val : CExp vars) -> (ty : Term []) ->
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
       -- Project the an argument of a given constructor
       CPrj : (con : Name) -> (field : Nat) -> CExp vars -> CExp vars
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
  MkFun : (args : List Name) -> CExp args -> CDef
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
  insertNames ns (CLam x sc)
    = let sc' = insertNames {outer=x :: outer} ns sc
      in CLam x sc'
  insertNames ns (CLet x val ty sc)
    = let sc' = insertNames {outer=x :: outer} ns sc
          val' = insertNames ns val
      in CLet x val' ty sc'
  insertNames ns (CApp f args) = CApp (insertNames ns f) (map (insertNames ns) args)
  insertNames ns (CCon x args) = CCon x $ map (insertNames ns) args
  insertNames ns (CConCase scr alts def)
    = let scr'  = insertNames ns scr
          alts' = map (insertNamesConAlt ns) alts
          def'  = map (insertNames ns) def
      in CConCase scr' alts' def'
  insertNames ns (CPrj c f tm) = CPrj c f (insertNames ns tm)
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
  export
  embed : CExp args -> CExp (args ++ vars)
  embed cexp = believe_me cexp

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
  shrinkCExp sub (CLam x sc)
    = let sc' = shrinkCExp (KeepCons sub) sc
      in CLam x sc'
  shrinkCExp sub (CLet x val ty sc)
    = let sc' = shrinkCExp (KeepCons sub) sc
          val' = shrinkCExp sub val
      in CLet x val' ty sc'
  shrinkCExp sub (CApp f args)
    = CApp (shrinkCExp sub f) (map (shrinkCExp sub) args)
  shrinkCExp sub (CCon x args)
    = CCon x $ map (shrinkCExp sub) args
  shrinkCExp sub (CConCase scr alts def)
    = CConCase (shrinkCExp sub scr)
               (map (shrinkConAlt sub) alts)
               (map (shrinkCExp   sub) def)
  shrinkCExp sub (CPrj c f tm) = CPrj c f (shrinkCExp sub tm)
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
  substEnv env (CLam x sc)
    = let sc' = substEnv {outer=x::outer} env sc
      in CLam x sc'
  substEnv env (CLet x val ty sc)
    = let sc' = substEnv {outer=x::outer} env sc
          val' = substEnv env val
      in CLet x val' ty sc'
  substEnv env (CApp f args) = CApp (substEnv env f) (map (substEnv env) args)
  substEnv env (CCon x args) = CCon x (map (substEnv env) args)
  substEnv env (CConCase scr alts def)
    = CConCase (substEnv env scr)
               (map (substEnvConAlt env) alts)
               (map (substEnv env) def)
  substEnv env (CPrj c f tm) = CPrj c f (substEnv env tm)
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

resolveRef : {outer, done : _} ->
             Bounds bound -> Name ->
             Maybe (CExp (outer ++ (done ++ bound ++ vars)))
resolveRef None _ = Nothing
resolveRef {outer} {vars} {done} (Add {xs} new old bs) n
  = if n == old
       then rewrite appendAssociative outer done (new :: xs ++ vars) in
            let MkNVar p = weakenNVar (outer ++ done) First in
              Just (CLocal p)
       else rewrite appendAssociative done [new] (xs ++ vars)
            in resolveRef {outer=outer} {done=done++[new]} bs n

mutual
  export
  mkLocals : {outer, bound : _} -> Bounds bound ->
             CExp (outer ++ vars) ->
             CExp (outer ++ (bound ++ vars))
  mkLocals bs (CLocal p) = let MkNVar p' = addVars bs p in CLocal p'
  mkLocals bs (CRef x) = maybe (CRef x) id (resolveRef {outer=outer} {done=[]} bs x)
  mkLocals bs (CLam x sc)
    = let sc' = mkLocals {outer=x::outer} bs sc
      in CLam x sc'
  mkLocals bs (CLet x val ty sc)
    = let sc' = mkLocals {outer=x::outer} bs sc
          val' = mkLocals bs val
      in CLet x val' ty sc'
  mkLocals bs (CApp f args)
    = CApp (mkLocals bs f) (map (mkLocals bs) args)
  mkLocals bs (CCon x args) = CCon x (map (mkLocals bs) args)
  mkLocals bs (CConCase scr alts def) = CConCase (mkLocals bs scr)
                                                 (map (mkLocalsConAlt bs) alts)
                                                 (map (mkLocals bs) def)
  mkLocals bs (CPrj con field x) = CPrj con field (mkLocals bs x)
  mkLocals bs CErased = CErased

  mkLocalsConAlt : {outer, bound : _} -> Bounds bound ->
                   CConAlt (outer ++ vars) ->
                   CConAlt (outer ++ (bound ++ vars))
  mkLocalsConAlt bs (MkConAlt x args tm)
    = let sc' : CExp ((args ++ outer) ++ vars)
              = rewrite sym (appendAssociative args outer vars) in tm
      in MkConAlt x args (rewrite appendAssociative args outer (bound ++ vars) in
                          mkLocals {outer=(args ++ outer)} bs sc')

export
refsToLocals : {bound : _} -> Bounds bound -> CExp vars -> CExp (bound ++ vars)
refsToLocals None tm = tm
refsToLocals bs y = mkLocals {outer=[]} bs y

export
renameVars : CompatibleVars xs ys -> CExp xs -> CExp ys
renameVars compat tm = believe_me tm -- no names in term, so it's identity

mutual

  export
  {vars : _} -> Eq (CExp vars) where
     (CLocal {idx} p)   == (CLocal {idx=idx'} p') = idx == idx'
     (CRef x)           == (CRef x') = x == x'
     (CLam x sc)     == (CLam x' sc')
       = case nameEq x x' of
           Nothing => False
           Just Refl => sc == sc'
     (CLet x val ty sc) == (CLet x' val' ty' sc')
       = case nameEq x x' of
           Nothing => False
           Just Refl => ty == ty' && sc == sc' && val == val'
     (CApp f args) == (CApp f' args')
       = f == f' && args == args'
     (CCon x args) == (CCon x' args')
       = x == x' && args == args'
     (CPrj con field x) == (CPrj con' field' x')
       = con == con' && field == field' && x == x'
     CErased == CErased = True
     (CConCase scr alts def) == (CConCase scr' alts' def')
       = scr == scr' && alts == alts' && def == def'
     _ == _ = False

  export
  {vars : _} -> Eq (CConAlt vars) where
     (MkConAlt x args sc) == (MkConAlt x' args' sc')
        = case namesEq args args' of
            Nothing   => False
            Just Refl => x == x' && sc == sc'

  export
  Eq CDef where
    (MkFun args x) == (MkFun args' x')
      = case namesEq args args' of
          Nothing => False
          Just Refl => x == x'
    (MkCon tag arity) == (MkCon tag' arity') = tag  == tag'  && arity == arity'
    _ == _ = False

mutual
  showCExp : {vars : _} -> String -> CExp vars -> String
  showCExp indent (CLocal {idx} p) = indent ++ "(local " ++ show (nameAt idx p) ++ ")"
  showCExp indent (CRef x) = indent ++ "(ref " ++ show x ++ ")"
  showCExp indent CErased = indent ++ "erased"
  showCExp indent (CPrj c f tm) = indent ++ "prj^" ++ show c ++ "_" ++ show f ++ " " ++ show tm
  showCExp indent (CLam x sc)
    = unlines [ indent ++ "(\\" ++ show x ++ " =>"
              , showCExp (indent ++ "  ") sc ++ indent ++ ")"
              ]
  showCExp indent (CLet x val ty sc)
    = indent ++ "(let " ++ show x ++ " : " ++ show ty ++ " =\n" ++ showCExp ("     " ++ indent) val ++ " in\n" ++ showCExp indent sc ++ ")"
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
    show (MkFun args x) = "func with (" ++ show args ++ ") : =\n" ++ show x
    show (MkCon tag arity) = "con " ++ show tag ++ " [" ++ show arity ++ " args]"
