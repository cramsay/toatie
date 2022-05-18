module Core.Coverage

import Core.CaseTree
import Core.Context
import Core.Env
import Core.Normalise
import Core.TT
import Core.Value

import Data.List
import Data.Maybe
import Data.String

-- Return whether any of the name matches conflict
conflictMatch : {vars : _} -> List (Name, Term vars) -> Bool
conflictMatch [] = False
conflictMatch ((x, tm) :: ms) = conflictArgs x tm ms || conflictMatch ms
  where
    clash : Term vars -> Term vars -> Bool
    clash (Ref (DataCon t _) _) (Ref (DataCon t' _) _)
        = t /= t'
    clash (Ref (TyCon _ t _) _) (Ref (TyCon _ t' _) _)
        = t /= t'
    clash (Ref t _) TType = isJust (isCon t)
    clash TType (Ref t _) = isJust (isCon t)
    clash _ _ = False

    findN : Nat -> Term vars -> Bool
    findN i (Local i' _) = i == i'
    findN i tm
        = let (Ref (DataCon _ _) _, args) = getFnArgs tm
                   | _ => False in
              any (findN i) args

    -- Assuming in normal form. Look for: mismatched constructors, or
    -- a name appearing strong rigid in the other term
    conflictTm : Term vars -> Term vars -> Bool
    conflictTm (Local i _) tm
        = let (Ref (DataCon _ _) _, args) = getFnArgs tm
                   | _ => False in
              any (findN i) args
    conflictTm tm (Local i _)
        = let (Ref (DataCon _ _) _, args) = getFnArgs tm
                   | _ => False in
              any (findN i) args
    conflictTm tm tm'
        = let (f, args) = getFnArgs tm
              (f', args') = getFnArgs tm' in
          clash f f' || any (uncurry conflictTm) (zip args args')

    conflictArgs : Name -> Term vars -> List (Name, Term vars) -> Bool
    conflictArgs n tm [] = False
    conflictArgs n tm ((x, tm') :: ms)
        = (n == x && conflictTm tm tm') || conflictArgs n tm ms

-- Return whether any part of the type conflicts in such a way that they
-- can't possibly be equal (i.e. mismatched constructor)
conflict : {vars : _} ->
           {auto c : Ref Ctxt Defs} ->
           Defs -> Env Term vars -> NF vars -> Name -> Core Bool
conflict defs env nfty n
    = do Just gdef <- lookupDef n defs
              | Nothing => pure False
         case (definition gdef, type gdef) of
              (DCon t arity, dty)
                  => do Nothing <- conflictNF 0 nfty !(nf defs NoLets [] dty)
                            | Just ms => pure $ conflictMatch ms
                        pure True
              _ => pure False
  where
    mutual
      conflictArgs : Int -> List (Closure vars) -> List (Closure []) ->
                     Core (Maybe (List (Name, Term vars)))
      conflictArgs _ [] [] = pure (Just [])
      conflictArgs i (c :: cs) (c' :: cs')
          = do cnf <- evalClosure defs NoLets c
               cnf' <- evalClosure defs NoLets c'
               Just ms <- conflictNF i cnf cnf'
                    | Nothing => pure Nothing
               Just ms' <- conflictArgs i cs cs'
                    | Nothing => pure Nothing
               pure (Just (ms ++ ms'))
      conflictArgs _ _ _ = pure (Just [])

      -- If the constructor type (the NF []) matches the variable type,
      -- then there may be a way to construct it, so return the matches in
      -- the indices.
      -- If any of those matches clash, the constructor is not valid
      -- e.g, Eq x x matches Eq Z (S Z), with x = Z and x = S Z
      -- conflictNF returns the list of matches, for checking
      conflictNF : Int -> NF vars -> NF [] ->
                   Core (Maybe (List (Name, Term vars)))
      conflictNF i t (NBind x b sc)
          -- invent a fresh name, in case a user has bound the same name
          -- twice somehow both references appear in the result  it's unlikely
          -- put possible
          = let x' = MN (show x) i in
                conflictNF (i + 1) t
                       !(sc defs (toClosure [] (Ref Bound x')))
      conflictNF i nf (NApp (NRef Bound n) [])
          = do empty <- clearDefs defs
               pure (Just [(n, !(quote empty NoLets env nf))])
      conflictNF i (NDCon n t a args) (NDCon n' t' a' args')
          = if t == t'
               then conflictArgs i (map snd args) (map snd args')
               else pure Nothing
      conflictNF i (NTCon _ n t a args) (NTCon _ n' t' a' args')
          = if n == n'
               then conflictArgs i (map snd args) (map snd args')
               else pure Nothing
      conflictNF _ _ _ = pure (Just [])

-- Need this to get a NF from a Term; the names are free in any case
freeEnv : (vs : List Name) -> Env Term vs
freeEnv [] = []
freeEnv (n :: ns) = PVar 0 Explicit Erased :: freeEnv ns

-- Find unbound names in a term
export
freeVars : {vars : _} ->
           {auto c : Ref Ctxt Defs} ->
           Env Term vars -> Term vars -> List Name
freeVars env (Ref Bound n) = [n]
freeVars env (Ref nt n) = []
freeVars env (Local idx p) = []
freeVars env (Meta x xs) = []
freeVars env (Bind n b scope) = freeVars (b :: env) scope
freeVars env (App i f a) = freeVars env f ++ freeVars env a
freeVars env TType = []
freeVars env Erased = []
freeVars env (Quote _ x) = freeVars env x
freeVars env (TCode x) = freeVars env x
freeVars env (Eval x) = freeVars env x
freeVars env (Escape x) = freeVars env x

-- Return whether the given type is definitely empty (due to there being
-- no constructors which can possibly match it.)
export
isEmpty : {vars : _} ->
          {auto c : Ref Ctxt Defs} ->
          Defs -> Env Term vars -> NF vars -> Core Bool
isEmpty defs env (NTCon n i t a args)
  = do Just gdef <- lookupDef n defs
         | Nothing => pure False
       case definition gdef of
         TCon _ _ _ cons => allM (conflict defs env (NTCon n i t a args)) cons
         _ => pure False
isEmpty defs env _ = pure False

-- Given a normalised type, get all the possible constructors for that
-- type family, with their type, name, tag, and arity
getCons : {auto c : Ref Ctxt Defs} ->
          {vars : _} ->
          Defs -> NF vars -> Core (List (NF [], Name, Int, Nat))
getCons defs (NTCon tn _ _ _ _)
  = case map definition !(lookupDef tn defs) of
      Just (TCon _ _ _ cons) =>
        do cs' <- traverse addTy cons
           pure (mapMaybe id cs')
      _ => throw (InternalError "Called `getCons` on something that is not a Type constructor")
  where
  addTy : Name -> Core (Maybe (NF [], Name, Int, Nat))
  addTy cn
    = do Just gdef <- lookupDef cn defs
           | _ => pure Nothing
         case (definition gdef, type gdef) of
           (DCon t arity, ty) =>
              pure (Just (!(nf defs NoLets [] ty), cn, t, arity))
           _ => pure Nothing
getCons defs nty = pure []

emptyRHS : CaseTree vars -> CaseTree vars
emptyRHS (Case idx el sc alts) = Case idx el sc (map emptyRHSalt alts)
  where
  emptyRHSalt : CaseAlt vars -> CaseAlt vars
  emptyRHSalt (ConCase n t args sc) = ConCase n t args (emptyRHS sc)
  emptyRHSalt (QuoteCase ty arg sc) = QuoteCase ty arg (emptyRHS sc)
  emptyRHSalt (DefaultCase sc) = DefaultCase (emptyRHS sc)
emptyRHS (STerm s) = STerm Erased
emptyRHS sc = sc

mkAlt : {vars : _} ->
        CaseTree vars -> (Name, Int, Nat) -> CaseAlt vars
mkAlt sc (cn, t, ar)
  = let varnames = (map (MN "_proj") (take ar [0..]))
    in ConCase cn t varnames
         (weakenNs varnames (emptyRHS sc))

altMatch : CaseAlt vars -> CaseAlt vars -> Bool
altMatch _ (DefaultCase _) = True
altMatch (ConCase _ t _ _) (ConCase _ t' _ _) = t == t'
altMatch (QuoteCase _ _ _) (QuoteCase _ _ _) = True
altMatch _ _ = False

-- Given a type and a list of case alternatives, return the
-- well-typed alternatives which were *not* in the list
getMissingAlts : {auto c : Ref Ctxt Defs} ->
                 {vars : _} ->
                 Defs -> NF vars -> List (CaseAlt vars) ->
                 Core (List (CaseAlt vars))
-- If it's a type, there's too many to reasonably check, so require a catch all
getMissingAlts defs (NType) alts
    = do if any isDefault alts
           then pure []
           else pure [DefaultCase (Unmatched "Coverage check")]
getMissingAlts defs nfty alts
    = do allCons <- getCons defs nfty
         pure (filter (noneOf alts)
                 (map (mkAlt (Unmatched "Coverage check") . snd) allCons))
  where
    -- Return whether the alternative c matches none of the given cases in alts
    noneOf : List (CaseAlt vars) -> CaseAlt vars -> Bool
    noneOf alts c = not $ any (altMatch c) alts

-- Mapping of variable to constructor tag already matched for it
KnownVars : List Name -> Type -> Type
KnownVars vars a = List (Var vars, a)

getName : {idx : Nat} -> {vars : List Name} -> (0 p : IsVar n idx vars) -> Name
getName {vars = v :: _} First = v
getName (Later p) = getName p

showK : {ns : _} ->
        Show a => KnownVars ns a -> String
showK {a} xs = show (map aString xs)
  where
  aString : {vars : _} ->
            (Var vars, a) -> (Name, a)
  aString (MkVar v, t) = (getName v, t)

weakenNs : {vars:_} -> (args : List Name) -> KnownVars vars a -> KnownVars (args ++ vars) a
weakenNs args [] = []
weakenNs args ((v, t) :: xs)
  = (weakenNs args v, t) :: weakenNs args xs

findTag : {idx, vars : _} ->
          (0 p : IsVar n idx vars) -> KnownVars vars a -> Maybe a
findTag v [] = Nothing
findTag v ((v', t) :: xs)
  = if sameVar (MkVar v) v'
       then Just t
       else findTag v xs

addNot : {idx, vars : _} ->
         (0 p : IsVar n idx vars) -> Int -> KnownVars vars (List Int) ->
         KnownVars vars (List Int)
addNot v t [] = [(MkVar v, [t])]
addNot v t ((v', ts) :: xs)
  = if sameVar (MkVar v) v'
       then ((v', t :: ts) :: xs)
       else ((v', ts) :: addNot v t xs)

tagIs : Int -> CaseAlt vars -> Bool
tagIs t (ConCase _ t' _ _) = t == t'
tagIs t (QuoteCase _ _ _) = False
tagIs t (DefaultCase _) = True

tagIsNot : List Int -> CaseAlt vars -> Bool
tagIsNot ts (ConCase _ t' _ _) = not (t' `elem` ts)
tagIsNot ts (QuoteCase _ _ _) = True
tagIsNot ts (DefaultCase _) = False

-- Replace a default case with explicit branches for the constructors.
-- This is easier than checking whether a default is needed when traversing
-- the tree (just one constructor lookup up front).
replaceDefaults : {auto c : Ref Ctxt Defs} ->
                  {vars : _} ->
                  Defs -> NF vars -> List (CaseAlt vars) ->
                  Core (List (CaseAlt vars))
-- Leave it alone if it's a type though, since we need the catch
-- all case there
replaceDefaults defs (NType) cs = pure cs
replaceDefaults defs nfty cs
    = do cs' <- traverse rep cs
         pure (dropRep (concat cs'))
  where
    rep : CaseAlt vars -> Core (List (CaseAlt vars))
    rep (DefaultCase sc)
        = do allCons <- getCons defs nfty
             pure (map (mkAlt sc . snd) allCons)
    rep c = pure [c]

    dropRep : List (CaseAlt vars) -> List (CaseAlt vars)
    dropRep [] = []
    dropRep (c@(ConCase n t args sc) :: rest)
          -- assumption is that there's no defaultcase in 'rest' because
          -- we've just removed it
        = c :: dropRep (filter (not . tagIs t) rest)
    dropRep (c :: rest) = c :: dropRep rest

getNameInfos : Defs -> Name -> Core (List AppInfo)
getNameInfos defs n = do Just ty <- lookupDefType n defs
                           | Nothing => throw $ InternalError $ "Couldn't find type for name " ++ show n ++ " in context while building missing clause terms."
                         pure $ getInfos ty
  where getInfos : Term vars -> List AppInfo
        getInfos (Bind x b sc)
          = let info = case binderInfo b of
                              Just Explicit => AExplicit
                              Just Implicit => AImplicit
                              Nothing       => AExplicit
            in info :: getInfos sc
        getInfos tm = []

applyInferInfo : Defs -> Term vars -> List (Term vars) -> Core (Term vars)
applyInferInfo defs fn [] = pure fn
applyInferInfo defs (Ref Func n) args
  = do infos <- getNameInfos defs n
       pure $ apply (Ref Func n) (zip infos args)
applyInferInfo defs (Ref (DataCon tag arity) n) args
  = do infos <- getNameInfos defs n
       pure $ apply (Ref (DataCon tag arity) n) (zip infos args)
applyInferInfo defs (Bind x y scope) (a :: args)
  = let info = case binderInfo y of -- Infer from binder info
                 Just Explicit => AExplicit
                 Just Implicit => AImplicit
                 Nothing       => AExplicit
    in applyInferInfo defs (App info (Bind x y scope) a) args
applyInferInfo defs fn (a :: args) -- Default to implicit
  = applyInferInfo defs (App AImplicit fn a) args


-- Traverse a case tree and refine the arguments while matching, so that
-- when we reach a leaf we know what patterns were used to get there,
-- and return those patterns.
-- The returned patterns are those arising from the *missing* cases
buildArgs : {auto c : Ref Ctxt Defs} ->
            {vars : _} ->
            Defs ->
            KnownVars vars Int -> -- Things which have definitely match
            KnownVars vars (List Int) -> -- Things an argument *can't* be
                                    -- (because a previous case matches)
            List (Term []) -> -- ^ arguments, with explicit names
            CaseTree vars -> Core (List (List (Term [])))
buildArgs defs known not ps cs@(Case {name = var} idx el ty altsIn)
  -- If we've already matched on 'el' in this branch, restrict the alternatives
  -- to the tag we already know. Otherwise, add missing cases and filter out
  -- the ones it can't possibly be (the 'not') because a previous case
  -- has matched.
    = do let fenv = freeEnv _
         nfty <- nf defs NoLets fenv ty
         alts <- replaceDefaults defs nfty altsIn
         let alts' = alts ++ !(getMissingAlts defs nfty alts)
         let altsK = maybe alts' (\t => filter (tagIs t) alts')
                              (findTag el known)
         let altsN = maybe altsK (\ts => filter (tagIsNot ts) altsK)
                              (findTag el not)
         buildArgsAlt not altsN
  where
    buildArgAlt : KnownVars vars (List Int) ->
                  CaseAlt vars -> Core (List (List (Term [])))
    buildArgAlt not' (ConCase n t args sc)
        = do let con = Ref (DataCon t (length args)) n
             replaceTm <- applyInferInfo defs con (map (Ref Bound) args)
             let ps' = map (substName var replaceTm) ps
             buildArgs defs (weakenNs args ((MkVar el, t) :: known))
                               (weakenNs args not') ps' sc
    buildArgAlt not' (QuoteCase t a sc)
        = let ps' = map (substName var (Quote (Ref Bound t) (Ref Bound a))) ps
          in buildArgs defs (weakenNs [t, a] known) (weakenNs [t, a] not') ps' sc
    buildArgAlt not' (DefaultCase sc)
        = buildArgs defs known not' ps sc

    buildArgsAlt : KnownVars vars (List Int) -> List (CaseAlt vars) ->
                   Core (List (List (Term [])))
    buildArgsAlt not' [] = pure []
    buildArgsAlt not' (c@(ConCase _ t _ _) :: cs)
        = pure $ !(buildArgAlt not' c) ++
                 !(buildArgsAlt (addNot el t not') cs)
    buildArgsAlt not' (c :: cs)
        = pure $ !(buildArgAlt not' c) ++ !(buildArgsAlt not' cs)

buildArgs defs known not ps (STerm vs)
    = pure [] -- matched, so return nothing
buildArgs defs known not ps (Unmatched msg)
    = pure [ps] -- unmatched, so return it
buildArgs defs known not ps Impossible
    = pure [] -- not a possible match, so return nothing

-- Traverse a case tree and return pattern clauses which are not
-- matched. These might still be invalid patterns, or patterns which are covered
-- elsewhere (turning up due to overlapping clauses) so the results should be
-- checked
export
getMissing : {vars : _} ->
             {auto c : Ref Ctxt Defs} ->
             Name -> CaseTree vars ->
             Core (List (Term []))
getMissing n ctree
  = do defs <- get Ctxt
       let psIn = map (Ref Bound) vars
       patss <- buildArgs defs [] [] psIn ctree
       traverse (applyInferInfo defs (Ref Func n)) (nub patss)


-- Does the second term match against the first?
-- 'Erased' matches against anything, we assume that's a Rig0 argument that
-- we don't care about
match : Term vs -> Term vs -> Bool
match (Local i _) _ = True
match (Ref Bound n) _ = True
match (Ref _ n) (Ref _ n') = n == n'
match (App _ f a) (App _ f' a') = match f f' && match a a'
match (TCode tm) (TCode tm') = match tm tm'
match (Quote _ tm) (Quote _ tm') = match tm tm'
match (Eval tm)  (Eval tm')  = match tm tm'
match (Escape tm) (Escape tm') = match tm tm'
match (Erased) _ = True
match _ (Erased) = True
match (Meta _ _) _ = True
match _ (Meta _ _) = True
match (TType) (TType) = True
match _ _ = False

-- if tm would be matched by trylhs, then it's not an impossible case
-- because we've already got it. Ignore anything in erased position.
clauseMatches : {vars : _} ->
                {auto c : Ref Ctxt Defs} ->
                Env Term vars -> Term vars ->
                Term [] -> Core Bool
clauseMatches env tm trylhs
  = let lhs = close env tm in -- TODO maybe ignore erased args
    pure $ match lhs trylhs
  where
  mkSubstEnv : {vars : _} ->
               Int -> Env Term vars -> SubstEnv vars []
  mkSubstEnv i [] = Nil
  mkSubstEnv i (v :: vs)
    = Ref Bound (MN "cov" i) :: mkSubstEnv (i + 1) vs

  close : {vars : _} ->
          Env Term vars -> Term vars -> Term []
  close {vars} env tm
    = substs (mkSubstEnv 0 env)
             (rewrite appendNilRightNeutral vars in tm)


export
checkMatched : {auto c : Ref Ctxt Defs} ->
               List Clause -> Term [] -> Core (Maybe (Term []))
checkMatched cs ulhs
  = do -- TODO maybe ignore erased args?
       tryClauses cs ulhs
  where
  tryClauses : List Clause -> Term [] -> Core (Maybe (Term []))
  tryClauses [] ulhs
    = pure $ Just ulhs
  tryClauses (MkClause env lhs _ :: cs) ulhs
  = if !(clauseMatches env lhs ulhs)
       then pure Nothing -- something matches, discard it
       else tryClauses cs ulhs
