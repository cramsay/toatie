module TTImp.ProcessDef

import Core.CaseBuilder
import Core.CaseTree
import Core.Context
import Core.Coverage
import Core.Env
import Core.Extraction
import Core.Normalise
import Core.TT
import Core.UnifyState
import Core.Value
import Core.Unify

import TTImp.Elab.Check
import TTImp.TTImp
import TTImp.Impossible

import Data.Either
import Data.Maybe
import Data.List
import Data.SortedMap
import Data.SortedSet
import Data.String

import Control.Monad.State

mutual
  mismatchNF : {auto c : Ref Ctxt Defs} ->
               {vars : _} ->
               Defs -> NF vars -> NF vars -> Core Bool
  mismatchNF defs (NTCon xn _ xt _ xargs) (NTCon yn _ yt _ yargs)
      = if xn /= yn
           then pure True
           else anyM (mismatch defs) (zipWith (curry $ mapHom snd) xargs yargs)
  mismatchNF defs (NDCon _ xt _ xargs) (NDCon _ yt _ yargs)
      = if xt /= yt
           then pure True
           else anyM (mismatch defs) (zipWith (curry $ mapHom snd) xargs yargs)
  mismatchNF defs (NCode  x) (NCode  y) = mismatchNF defs x y
  mismatchNF defs (NQuote _ x) (NQuote _ y) = mismatchNF defs !(evalClosure defs NoLets x) !(evalClosure defs NoLets y)
  mismatchNF defs (NEscape x xargs) (NEscape y yargs)
       = do False <- mismatchNF defs x y
              | True => pure True
            anyM (mismatch defs) (zipWith (curry $ mapHom snd) xargs yargs)
  mismatchNF _ _ _ = pure False

  mismatch : {auto c : Ref Ctxt Defs} ->
             {vars : _} ->
             Defs -> (Closure vars, Closure vars) -> Core Bool
  mismatch defs (x, y)
      = mismatchNF defs !(evalClosure defs NoLets x) !(evalClosure defs NoLets y)

-- If the terms have the same type constructor at the head, and one of
-- the argument positions has different constructors at its head, then this
-- is an impossible case, so return True
export
impossibleOK : {auto c : Ref Ctxt Defs} ->
               {vars : _} ->
               Defs -> NF vars -> NF vars -> Core Bool
impossibleOK defs (NTCon xn _ xt xa xargs) (NTCon yn _ yt ya yargs)
    = if xn == yn
         then anyM (mismatch defs) (zipWith (curry $ mapHom snd) xargs yargs)
         else pure False
-- If it's a data constructor, any mismatch will do
impossibleOK defs (NDCon _ xt _ xargs) (NDCon _ yt _ yargs)
    = if xt /= yt
         then pure True
         else anyM (mismatch defs) (zipWith (curry $ mapHom snd) xargs yargs)
impossibleOK defs (NTCon _ _ _ _ _) (NType) = pure True
impossibleOK defs (NType) (NTCon _ _ _ _ _) = pure True
impossibleOK defs x y = pure False

export
impossibleErrOK : {auto c : Ref Ctxt Defs} ->
                  Defs -> Error -> Core Bool
impossibleErrOK defs (CantConvert env l r)
    = impossibleOK defs !(nf defs NoLets env l)
                        !(nf defs NoLets env r)
{-
-- TODO Throw suitable errors and handle them here
impossibleErrOK defs (BadDotPattern _ _ _) = pure True
impossibleErrOK defs (CantSolveEq fc env l r)
    = impossibleOK defs !(nf defs env l)
                        !(nf defs env r)
impossibleErrOK defs (CyclicMeta _ _ _ _) = pure True
impossibleErrOK defs (AllFailed errs)
    = anyM (impossibleErrOK defs) (map snd errs)
impossibleErrOK defs (WhenUnifying _ _ _ _ err)
    = impossibleErrOK defs err
-}
impossibleErrOK defs _ = pure False

-- If it's a clause we've generated, see if the error is recoverable. That
-- is, if we have a concrete thing, and we're expecting the same concrete
-- thing, or a function of something, then we might have a match.
export
recoverable : {auto c : Ref Ctxt Defs} ->
              {vars : _} ->
              Defs -> NF vars -> NF vars -> Core Bool
-- Unlike the above, any mismatch will do

-- TYPE CONSTRUCTORS
recoverable defs (NTCon xn _ xt xa xargs) (NTCon yn _ yt ya yargs)
    = if xn /= yn
         then pure False
         else pure $ not !(anyM (mismatch defs) (zipWith (curry $ mapHom snd) xargs yargs))
-- Type constructor vs. type
recoverable defs (NTCon _ _ _ _ _) (NType) = pure False
recoverable defs (NType) (NTCon _ _ _ _ _) = pure False
recoverable defs (NTCon _ _ _ _ _) _ = pure True
recoverable defs _ (NTCon _ _ _ _ _) = pure True

-- DATA CONSTRUCTORS
recoverable defs (NDCon _ xt _ xargs) (NDCon _ yt _ yargs)
    = if xt /= yt
         then pure False
         else pure $ not !(anyM (mismatch defs) (zipWith (curry $ mapHom snd) xargs yargs))
recoverable defs (NDCon _ _ _ _) _ = pure True
recoverable defs _ (NDCon _ _ _ _) = pure True

-- FUNCTION CALLS
recoverable defs (NApp (NRef _ f) fargs) (NApp (NRef _ g) gargs)
    = pure True -- both functions; recoverable

-- OTHERWISE: no
recoverable defs x y = pure False

export
recoverableErr : {auto c : Ref Ctxt Defs} ->
                 Defs -> Error -> Core Bool
recoverableErr defs (CantConvert env l r)
  = do l <- nf defs NoLets env l
       r <- nf defs NoLets env r
       log "coverage.recover" 10 $ unlines
         [ "Recovering from CantConvert?"
         , "Checking:"
         , "  " ++ show l
         , "  " ++ show r
         ]
       recoverable defs l r
{-
-- TODO Throw suitable errors and handle them here
recoverableErr defs (CantSolveEq env l r)
    = recoverable defs !(nf defs env l)
                       !(nf defs env r)
recoverableErr defs (BadDotPattern _ _ ErasedArg _ _) = pure True
recoverableErr defs (CyclicMeta _ _ _ _) = pure True
recoverableErr defs (AllFailed errs)
    = anyM (recoverableErr defs) (map snd errs)
recoverableErr defs (WhenUnifying _ _ _ _ err)
    = recoverableErr defs err
-}
recoverableErr defs _ = pure False

getRHSEnv : {vars : _} ->
            Env Term vars -> Term vars -> Term vars ->
            Core (vars' ** (Env Term vars', Term vars', Term vars'))
-- The names have to match here, and if type checking is implemented correctly
-- they will, but we don't have a way to express that! So we need to check.
getRHSEnv env (Bind n (PVar stage i ty) sc) (Bind n' (PVTy _ _) scty) with (nameEq n n')
  getRHSEnv env (Bind n (PVar stage i ty) sc) (Bind n' (PVTy _ _) scty) | Nothing
      = throw (GenericMsg "Can't happen: names don't match in getRHSEnv")
  getRHSEnv env (Bind n (PVar stage i ty) sc) (Bind n (PVTy _ _) scty) | (Just Refl)
      = getRHSEnv (PVar stage i ty :: env) sc scty
getRHSEnv env lhs ty = pure (vars ** (env, lhs, ty))

-- List all of the PVar names which are used explicit positions (once or more) in the LHS
-- Based on idris2's findLinear function
findExp : {vars : _} ->
             {auto c : Ref Ctxt Defs} ->
             (lhsenv : Term vars) ->
             Core (List Name)
findExp (Bind n b sc)
    = findExp sc
findExp tm
    = case getFnInfoArgs tm of
           (Ref _  n, []) => pure []
           (Ref nt n, args)
              => do defs <- get Ctxt
                    Just (MkGlobalDef nty _ _) <- lookupDef n (defs)
                         | Nothing => pure []
                    findExpArg nty args
           (Quote ty tm, []) => findExp tm
           _ => pure []
    where
      findExpArg : {vars : _} ->
                   Term [] -> List (AppInfo, Term vars) ->
                   Core (List Name)
      findExpArg (Bind x (Pi _ Explicit _ ) sc) ((_, Local {name=a} idx prf) :: as)
          = do defs <- get Ctxt
               let a = nameAt idx prf
               let sc' = subst (Ref Bound x) sc
               pure $ a :: !(findExpArg sc' as)
      findExpArg (Bind x (Pi _ Explicit _) sc) ((_, a) :: as)
          = do defs <- get Ctxt
               pure $ !(findExp a) ++
                      !(findExpArg (subst (Ref Bound x) sc) as)
      findExpArg (Bind x (Pi _ Implicit _) sc) ((_, a) :: as) --TODO unsure
          = do defs <- get Ctxt
               pure !(findExpArg (subst (Ref Bound x) sc) as)
      findExpArg _ _ = pure []

-- Easy interface into findExp
export
findExpTop : {vars : _} ->
             {auto c : Ref Ctxt Defs} ->
             Term vars ->
             Core (List Name)
findExpTop tm = do imps <- findExp tm
                   pure $ nub imps

-- Wrap a given rhs term with the binders for all names in env, giving each the accessibility
-- defined by their presence in the list of explicitly used names
wrapRHSWithLams : {vars: _} -> Env Term vars -> (exps : List Name) -> (rhs : Term vars) -> Term (vars)
wrapRHSWithLams [] _ rhs = rhs
wrapRHSWithLams {vars=v::vs} (b :: bs) exps rhs
  = let ty = binderType b
        info : PiInfo = if elem v exps then Explicit else Implicit
        rec = wrapRHSWithLams bs exps $ Bind v (Lam (binderStage b) info ty) rhs
    in weaken $ rec

-- Similar to wrapRHSWithLams but for the _type_ of the RHS
-- TODO should just combind these two functions
rhsTypeToPi : {vars: _} -> Env Term vars -> (exps : List Name) -> (rhsty : Term vars) -> Term vars
rhsTypeToPi [] _ rhsty = rhsty
rhsTypeToPi {vars=v::vs} (b :: bs) exps rhsty
  = let ty = binderType b
        info : PiInfo = if elem v exps then Explicit else Implicit
        rec = rhsTypeToPi bs exps $ Bind v (Pi (binderStage b) info ty) rhsty
    in weaken rec

processImplicitUse : {auto c : Ref Ctxt Defs} ->
                     {auto u : Ref UST UState} ->
                     {auto s : Ref Stg Stage} ->
                     {vars:_} -> Env Term vars -> (lhstm : Term vars) -> (rhstm : Term vars) -> (exprhsty : Term vars) -> Core ()
processImplicitUse env lhstm rhstm exprhsty
  = do exps <- findExpTop lhstm
       --coreLift $ putStrLn $ "IMPS: ENV = " ++ show env
       --coreLift $ putStrLn $ "IMPS: EXPS = " ++ show exps
       let rhstm'    = wrapRHSWithLams env exps rhstm
       let exprhsty' = rhsTypeToPi env exps exprhsty
       case toTTImp rhstm' of
         Nothing      => throw $ GenericMsg "Can't convert back to TTImp"
         Just rhswrap => do (rhstm', rhsty')
                               <- check env rhswrap (Just (gnf NoLets env exprhsty'))
                            pure ()

-- Insert dots for any pattern variables after they have appeared once in the LHS
-- State is tuple of set of bound pattern names and set of pattern names found in lhs already
addDots : RawImp -> State (SortedSet Name, SortedSet Name) RawImp
addDots IType    = pure IType
addDots Implicit = pure Implicit
addDots (IPi Implicit mn ms argTy retTy)  = pure $ IPi Implicit mn ms argTy retTy
addDots (IPi Explicit mn ms argTy retTy)  = pure $ IPi Explicit mn ms argTy retTy
addDots (ILet n margTy argVal scope)   = pure $ ILet n margTy argVal scope -- Can't have ILet on LHS...
addDots (IMustUnify x) = pure $ IMustUnify x
addDots (IQuote x)     = pure $ --IQuote (IMustUnify x)
                                IQuote !(addDots x)
addDots (ICode x)      = pure $ ICode   !(addDots x)
addDots (IEval x)      = pure $ IEval   !(addDots x)
addDots (IEscape x)    = pure $ IEscape !(addDots x)
addDots (IPatvar n ms ty scope) = do (pats, founds) <- get
                                     put (insert n pats, founds)
                                     pure $ IPatvar n ms ty !(addDots scope)
addDots (ILam Implicit mn ms argTy scope) = pure $ ILam Implicit mn ms argTy !(addDots scope)--(IMustUnify $ addDots scope)
addDots (ILam Explicit mn ms argTy scope) = pure $ ILam Explicit mn ms argTy !(addDots scope)
addDots (IApp AImplicit f a) = pure $ IApp AImplicit !(addDots f) !(addDots a)
addDots (IApp AExplicit f a) = pure $ IApp AExplicit !(addDots f) !(addDots a)
addDots (IVar x) = do (pats, founds) <- get
                      case contains x pats of
                        True =>
                          case contains x founds of
                            True => pure $ IMustUnify $ IVar x
                            False => do put (pats, insert x founds)
                                        pure $ IVar x
                        False => pure $ IVar x
addDots (ICase scr scrty alts) = pure $ ICase !(addDots scr) !(addDots scrty) alts

-- Patch up LHS pattern implicitness
-- Sometimes we get this wrong during elaboration if the LHS still has unsolved metavars while we're elaborating
-- This function will repair that, if all the metavars have been solved.
fixLHSPatImplicitness : {vars : _} ->
                        {auto c : Ref Ctxt Defs} ->
                        Env Term vars -> Term vars -> Core (Term vars)
fixLHSPatImplicitness env (Bind n (PVar s i ty) sc)
  = do expPatNs <- findExpTop sc
       let i' = if n `elem` expPatNs
                   then Explicit
                   else Implicit
       sc' <- fixLHSPatImplicitness (PVar s i' ty :: env) sc
       pure $ Bind n (PVar s i' ty) sc'
fixLHSPatImplicitness env tm = pure tm

processLHS :  {auto c : Ref Ctxt Defs} ->
              {auto u : Ref UST UState} ->
              {auto s : Ref Stg Stage} ->
              {vars : _} ->
              Env Term vars -> RawImp ->
              Core (RawImp, -- checkedLHS with implicits added
                    (vars' ** (Env Term vars'
                              ,Term vars'
                              ,Term vars')))
processLHS {vars} env lhs
  = do defs <- get Ctxt

       let lhs = evalState (empty,empty) (addDots lhs)
       (lhstm, lhstyg) <- elabTerm InLHS env lhs Nothing

       lhstm <- normalise defs NoLets env lhstm
       lhsty <- normalise defs NoLets env !(getTerm lhstyg)

       checkDots

       defs <- get Ctxt
       lhstm <- normalise defs NoLets env lhstm
       lhsty <- normalise defs NoLets env !(getTerm lhstyg)

       --coreLift $ putStrLn $ "PROCLHS: ENV = " ++ show env
       --coreLift $ putStrLn $ "PROCLHS: LHSTM = " ++ show lhstm
       --coreLift $ putStrLn $ "PROCLHS: LHSTY = " ++ show lhsty

       solveConstraints InLHS
       ust <- get UST
       let [] = SortedSet.toList $ holes ust
            | (h::hs) => throw $ GenericMsg $ "HOLES PRESENT IN LHS! " ++ show (h :: hs)
       let [] = SortedMap.toList $ constraints ust
            | (h::hs) => throw $ GenericMsg $ "CONSTRS PRESENT IN LHS! " ++ show (h :: hs)

       lhstm <- fixLHSPatImplicitness env lhstm

       ret <-  getRHSEnv env lhstm lhsty
       pure (lhs, ret)

-- Return whether any of the pattern variables are in a trivially empty
-- type, where trivally empty means one of:
--  * No constructors
--  * Every constructor of the family has a return type which conflicts with
--    the given constructor's type
hasEmptyPat : {vars : _} ->
              {auto c : Ref Ctxt Defs} ->
              Defs -> Env Term vars -> Term vars -> Core Bool
hasEmptyPat defs env (Meta n _)
  = do Just ty <- lookupDefType n defs
         | Nothing => throw $ InternalError $ "Couldn't find type for meta: " ++ show n
       pure $ !(isEmpty defs [] !(nf defs NoLets [] ty))
hasEmptyPat defs env (App _ f a) = pure $ !(hasEmptyPat defs env f) || !(hasEmptyPat defs env a)
hasEmptyPat defs env _ = pure False

processClause : {auto c : Ref Ctxt Defs} ->
                {auto u : Ref UST UState} ->
                {auto s : Ref Stg Stage} ->
                ImpClause -> Core (Either RawImp Clause)
processClause (ImpossibleClause lhs_raw)
    = do -- Don't let failures affect staging
         stage <- get Stg
         ust <- get UST
         defs <- get Ctxt
         handleUnify
           (do
              (lhstm, lhstyg) <- elabTerm InLHS [] lhs_raw Nothing
              defs' <- get Ctxt
              lhstm <- normalise defs' NoLets [] lhstm
              if !(hasEmptyPat defs' [] lhstm)
                 then do put UST ust
                         put Ctxt defs
                         put Stg stage
                         pure (Left lhs_raw)
                 else throw (ValidCase [] (Left lhstm))
           )
           (\err => case err of
                         ValidCase _ _ => throw err
                         _ => do defs' <- get Ctxt
                                 put Stg stage
                                 put UST ust
                                 put Ctxt defs
                                 if !(impossibleErrOK defs' err)
                                    then pure (Left lhs_raw)
                                    else throw (ValidCase [] (Right err))
           )
processClause (PatClause lhs_in rhs)
    = do -- Check the LHS
         (lhs, (vars ** (env, lhsenv, rhsexp))) <- processLHS [] lhs_in

         -- TODO I want to check this with the correct implicitness in env
         -- from the get go! --- or at least have a way of working out which
         -- patvar binders are implicit or explicit!
         (rhstm, rhsty) <- check env rhs (Just (gnf KeepLets env rhsexp))

         -- Check that implicit/explicit arg use is correct on the RHS
         processImplicitUse env lhsenv rhstm rhsexp
         defs <- get Ctxt
         rhsnf <- normalise defs KeepLets env rhstm

         solveConstraints InLHS
         ust <- get UST
         let [] = SortedSet.toList $ holes ust
                | (h::hs) => do defs <- get Ctxt
                                --coreLift $ putStrLn $ show defs
                                holeStrings <- traverse (dumpHole defs) (h :: hs)
                                throw $ GenericMsg $ "Unresolved holes in clause " ++ show lhsenv ++ " = " ++ show rhstm ++ "\n"
                                  ++ "\nHoles:\n" ++ unlines holeStrings
                                  ++ "\nConstraints:\n" ++ unlines (nub $ map (show. snd) $ toList $ constraints ust)

         pure (Right $ MkClause env lhsenv rhsnf)
  where
  splitPis : {vars : _} -> Name -> Term vars -> List String
  splitPis n (Bind x@(UN _) (Pi s i ty) sc) = (show x ++ ":_" ++ show s ++ " " ++ show ty) :: splitPis n sc
  splitPis n tm = "--------------------------------" :: (show n ++ " : " ++ show tm) :: []

  dumpHole : Defs -> Name -> Core String
  dumpHole defs n = do Just htype <- lookupDefType n defs
                         | Nothing => throw $ GenericMsg "Unresolved hole has no type"
                       pure $ unlines $ splitPis n !(normalise defs NoLets [] htype)

nameListEq : (xs : List Name) -> (ys : List Name) -> Maybe (xs = ys)
nameListEq [] [] = Just Refl
nameListEq (x :: xs) (y :: ys) with (nameEq x y)
  nameListEq (x :: xs) (x :: ys) | (Just Refl) with (nameListEq xs ys)
    nameListEq (x :: xs) (x :: xs) | (Just Refl) | Just Refl= Just Refl
    nameListEq (x :: xs) (x :: ys) | (Just Refl) | Nothing = Nothing
  nameListEq (x :: xs) (y :: ys) | Nothing = Nothing
nameListEq _ _ = Nothing


-- Return names of arguments in implicit positions (nonrecursively)
-- given a list of arg names and a function's type
filterImplicitArgs : List Name -> (ty : Term vars) -> List Name
filterImplicitArgs (arg::args) (Bind _ (Pi s Implicit _) scope) = arg :: filterImplicitArgs args scope
filterImplicitArgs (arg::args) (Bind _ (Pi s Explicit _) scope) =        filterImplicitArgs args scope
filterImplicitArgs args ty = []

mutual
  -- A case alternative respects implicitness if it's nested case tree does
  -- (just need bookkeeping for any implicit arguments introduced by constructor matching)
  checkImplicitUsageAlt : {vars : _} ->
                        {auto c : Ref Ctxt Defs} ->
                        List Name -> CaseAlt vars ->
                        Core ()
  checkImplicitUsageAlt implicits (ConCase n tag args ct)
    = do defs <- get Ctxt
         Just cty <- lookupDefType n defs
           | Nothing => throw (InternalError $ "Undefined constructor name " ++ show n)
         checkImplicitUsageCase (implicits ++ filterImplicitArgs args cty) ct
  checkImplicitUsageAlt implicits (QuoteCase t a ct) = checkImplicitUsageCase implicits ct
  checkImplicitUsageAlt implicits (DefaultCase ct) = checkImplicitUsageCase implicits ct

  -- A case tree respects implicitness if when we match on an implicit argument, there are
  -- only zero or one alternatives... anything more than one would cause ambiguity at run-time
  -- when the implicits are erased. This rule allows single constructor types such as Refl.
  checkImplicitUsageCase : {vars : _} ->
                         {auto c : Ref Ctxt Defs} ->
                         List Name -> CaseTree vars ->
                         Core ()
  checkImplicitUsageCase implicits (Case idx p scTy alts)
    = do if elem (nameAt idx p) implicits
            then when (length alts > 1)
                      (throw (GenericMsg $ "Case tree requires ambiguous pattern match on implicit arg " ++ show (nameAt idx p)))
            else traverse_ (checkImplicitUsageAlt implicits) alts
  checkImplicitUsageCase _ _ = pure ()

  checkQuoteUsageAlt : {vars : _} ->
                       List (Name, Name) ->
                       CaseAlt vars ->
                       Core ()
  checkQuoteUsageAlt quotes (ConCase x tag args ct) = checkQuoteUsageCase quotes ct
  checkQuoteUsageAlt quotes (QuoteCase ty arg ct) = checkQuoteUsageCase quotes ct
  checkQuoteUsageAlt quotes (DefaultCase ct) = checkQuoteUsageCase quotes ct

  checkQuoteUsageCase : {vars : _} ->
                        List (Name, Name) -> -- (quoted name, name or arg)
                        CaseTree vars ->
                        Core ()
  checkQuoteUsageCase quotes (Case idx p scTy ((QuoteCase ty arg sc) :: []))
    = do let quotes' = (arg, nameAt idx p) :: quotes
         checkQuoteUsageAlt quotes' (QuoteCase ty arg sc)
  checkQuoteUsageCase quotes (Case idx p scTy alts)
    = case lookup (nameAt idx p) quotes of
        Just quotedName => do when (length alts > 1)
                                        (throw (GenericMsg $ "Case tree requires ambiguous pattern match on quoted arg, " ++ show quotedName))
                              traverse_ (checkQuoteUsageAlt quotes) alts
        Nothing => traverse_ (checkQuoteUsageAlt quotes) alts
  checkQuoteUsageCase quotes _ = pure ()

toPats : Clause -> (vs ** (Env Term vs, Term vs, Term vs))
toPats (MkClause {vars} env lhs rhs)
  = (_ ** (env, lhs, rhs))

eraseImps : {vars:_} -> Env Term vars -> Term vars -> Term vars
eraseImps env (Local idx p) = case binderInfo (getBinder p env) of
                                Just Implicit => Erased
                                _             => Local idx p
eraseImps env (Ref nt n) = Ref nt n
eraseImps env (Meta x xs) = Meta x xs
eraseImps env (Bind x b scope) = Bind x (map (eraseImps env) b) (eraseImps (b::env) scope)
eraseImps env (App AImplicit f a) = App AImplicit (eraseImps env f) Erased
eraseImps env (App AExplicit f a) = App AExplicit (eraseImps env f) (eraseImps env a)
eraseImps env TType = TType
eraseImps env Erased = Erased
eraseImps env (Quote ty tm) = Quote (eraseImps env ty) (eraseImps env tm)
eraseImps env (TCode x) = TCode (eraseImps env x)
eraseImps env (Eval x) = Eval (eraseImps env x)
eraseImps env (Escape x) = Escape (eraseImps env x)

mkRunTime : {auto c : Ref Ctxt Defs} ->
            {auto u : Ref UST UState} ->
            {auto s : Ref Stg Stage} ->
            Name -> Core Def
mkRunTime n
  = do defs <- get Ctxt
       Just (MkGlobalDef ty (PMDef args treect _ pats) _) <- lookupDef n defs
         | _ => throw $ InternalError $ "Undefined case tree name when building run-time version: " ++ show n

       pats' <- traverse toErased pats
       let clauses = map toClause pats'

       (rargs ** treert) <- getPMDef n ty clauses

       let Just Refl = nameListEq args rargs
         | Nothing => throw (InternalError "WAT")
       --                                   ^^^
       -- This is a quote from the Idris2 source and it deserves to live on here

       pure $ PMDef args treect treert pats
  where
    toErased : (vars ** (Env Term vars, Term vars, Term vars)) ->
               Core (vars ** (Env Term vars, Term vars, Term vars))
    toErased (vars ** (env, lhs, rhs))
      = do let lhs' = eraseImps env lhs
           let rhs' = eraseImps env rhs
           pure $ (vars ** (env, lhs', rhs'))

    toClause : (vars ** (Env Term vars, Term vars, Term vars)) -> Clause
    toClause (_ ** (env, lhs, rhs)) = MkClause env lhs rhs

export
processDef : {auto c : Ref Ctxt Defs} ->
             {auto u : Ref UST UState} ->
             {auto s : Ref Stg Stage} ->
             Name -> List ImpClause -> Core ()
processDef n clauses
    = do defs <- get Ctxt
         Just gdef <- lookupDef n defs
              | Nothing => throw (GenericMsg ("No type declaration for " ++ show n))
         let None = definition gdef
           | _ => throw (GenericMsg ("Multiple bodies definied for " ++ show n))

         chkcs <- traverse processClause clauses

         -- Now we have all the clauses, make a case tree
         (cargs ** tree_ct) <- getPMDef n (type gdef) (rights chkcs)
         -- TODO warn for unreachable clauses

         -- Update the definition with the compiled tree
         let pats = map toPats (rights chkcs)
         updateDef n (record { definition = None })

         -- check coverage
         IsCovering <- checkCoverage n (type gdef) chkcs
           | cov => throw $ GenericMsg (show cov)

         updateDef n (record { definition = PMDef cargs tree_ct tree_ct pats})

         -- check final case tree for ambiguous matching on implicit args
         defs <- get Ctxt
         topFnArity <- getArity defs NoLets [] (type gdef)
         let topImplicitArgs = filterImplicitArgs (map (\n => MN "arg" n)
                                                       [0 .. cast topFnArity])
                                                  (type gdef)
         checkImplicitUsageCase topImplicitArgs tree_ct
         checkQuoteUsageCase [] tree_ct

         -- check that we've solved all RHS holes too
         solveConstraints InTerm
         ust <- get UST
         let [] = SortedMap.toList $ constraints ust
                | cs => throw (GenericMsg $ "Constraints present after processing def: "
                                            ++ show n ++ " " ++ show (map snd cs))
         -- TODO want to 1) show term with holes, 2) show environment and types, 3) error on MN holes
         let [] = SortedSet.toList $ holes ust
                | hs => throw $ GenericMsg $ "Unresolved holes in " ++ show n ++ " "
                                ++ show hs ++ "\nTerm is " ++ show tree_ct

         -- Patch in our run-time tree
         PMDef cargs tree_ct tree_rt pats <- mkRunTime n
           | _ => throw $ InternalError $ "Compilation of run-time tree didn't return a tree definition!"
         updateDef n (record { definition = PMDef cargs tree_ct tree_rt pats})

         --coreLift $ putStrLn $ "Complete ----------------------"
         --coreLift $ putStrLn $ "Stage: " ++ show !(get Stg)
         --coreLift $ putStrLn $ "Args = " ++ show cargs
         --coreLift $ putStrLn $ "Tree = " ++ show tree_ct
         --coreLift $ putStrLn $ "Type = " ++ show (type gdef)
         --coreLift $ putStrLn $ "RTree = " ++ show tree_rt
         coreLift $ putStrLn $ "Processed " ++ show n
  where

  simplePat : forall vars . Term vars -> Bool
  simplePat (Local _ _) = True
  simplePat (Erased) = True
  simplePat _ = False

  -- Is the clause returned from 'checkClause' a catch all clause, i.e.
  -- one where all the arguments are variables? If so, no need to do the
  -- (potentially expensive) coverage check
  catchAll : Clause -> Bool
  catchAll (MkClause env lhs _)
    = all simplePat (getArgs lhs)

  -- Return 'Nothing' if the clause is impossible, otherwise return the
  -- checked clause (with implicits filled in, so that we can see if they
  -- match any of the given clauses)
  checkImpossible : List Name -> Name -> Term [] ->
                    Core (Maybe (Term []))
  checkImpossible ns n tm
    = do -- We're checking closed terms that, thanks to Core.Coverage, will
         -- sometimes contain free variables.
         -- We need to resolve this before checking
         -- FIXME Also we don't respect implicitness of arguments...
         let fvs = freeVars [] tm
         --let tmImps = foldl (\tm => \n => substName n Erased tm) tm fvs
         itm <- toTTImpClosed $ weakenNs [] tm--Imps
         -- Don't let failures affect staging
         stage <- get Stg
         ust <- get UST
         defs <- get Ctxt

         handleUnify
           (do ctxt <- get Ctxt
               log "checkimpossible" 10 ("About to unelab term: " ++ show tm)
               log "checkimpossible" 10 ("With local names: " ++ show ns)
               log "checkimpossible" 10 ("to ttimp: " ++ show itm)
               (lhstm, _) <- elabTerm InLHS [] itm Nothing
               --let lhstm = tmImps
               defs' <- get Ctxt
               lhs <- normalise defs' NoLets [] lhstm
               newust <- get UST
               let [] = Data.SortedMap.toList $ constraints newust
                   | _ => do put UST ust
                             put Stg stage
                             put Ctxt defs
                             pure Nothing
               --let lhs = lhstm
               log "checkimpossible" 10 ("Checking for empty pats: " ++ show lhs)
               if !(hasEmptyPat defs' [] lhs)
                 then do put Ctxt ctxt
                         pure Nothing
                 else do empty <- clearDefs ctxt
                         rtm <- normalise empty NoLets [] lhs --TODO Maybe I need closeEnv here to strip patvar bindings?
                         --let rtm = lhs
                         put Ctxt ctxt
                         put UST ust
                         pure (Just rtm)
           )
           (\err => do log "checkimpossible catch" 10 (show err)
                       defs <- get Ctxt
                       put Stg stage
                       put UST ust
                       if not !(recoverableErr defs err)
                          then pure Nothing
                          else pure (Just tm)
           )

  getClause : Either RawImp Clause -> Core (Maybe Clause)
  getClause (Left rawlhs)
    = catch (do lhsp <- getImpossibleTerm rawlhs
                pure $ Just $ MkClause [] lhsp Erased)
            (\e => do log "getclause left" 10 $ "Caught error: " ++ show e
                      pure Nothing)
  getClause (Right c) = pure (Just c)

  checkCoverage : Name -> Term [] -> List (Either RawImp Clause) -> Core Covering
  checkCoverage n ty cs
    = do covcs' <- traverse getClause cs
         let covcs = mapMaybe id covcs'
         (cargs ** ctree) <- getPMDef n ty covcs
         missCase <- if any catchAll covcs
                        then pure []
                        else getMissing n ctree
         log "checkcoverage" 10 ("Initial tree: " ++ show ctree)
         log "checkcoverage" 10 ("Initial missing: " ++ unlines (map show missCase))
         -- Filter out out impossible clauses
         missImp <- traverse (checkImpossible cargs n) missCase
         log "checkcoverage" 10 ("After impossible filtering: " ++ unlines (map show missImp))
         -- Filter out matches clauses (perhapsed having come up due to some overlapping patterns)
         missMatch <- traverse (checkMatched covcs) (mapMaybe id missImp)
         log "checkcoverage" 10 ("After overlap filtering: " ++ unlines (map show missMatch))
         let miss = mapMaybe id missMatch
         defs <- get Ctxt
         if isNil miss
            then pure IsCovering --TODO check that we don't call any functions which are non covering!
            else pure (MissingCases miss)
