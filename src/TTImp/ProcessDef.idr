module TTImp.ProcessDef

import Core.CaseBuilder
import Core.CaseTree
import Core.Context
import Core.Env
import Core.Normalise
import Core.TT
import Core.UnifyState
import Core.Value
import Core.Unify

import TTImp.Elab.Term
import TTImp.TTImp

import Data.Maybe
import Data.List
import Data.SortedMap
import Data.SortedSet
import Data.String

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
  mismatchNF defs (NQuote x) (NQuote y) = mismatchNF defs !(evalClosure defs x) !(evalClosure defs y)
  mismatchNF defs (NEscape x) (NEscape y) = mismatchNF defs x y
  mismatchNF _ _ _ = pure False

  mismatch : {auto c : Ref Ctxt Defs} ->
             {vars : _} ->
             Defs -> (Closure vars, Closure vars) -> Core Bool
  mismatch defs (x, y)
      = mismatchNF defs !(evalClosure defs x) !(evalClosure defs y)

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
    = impossibleOK defs !(nf defs env l)
                        !(nf defs env r)
{-
-- TODO Throw suitable errors and handle them here
impossibleErrOK defs (CantSolveEq fc env l r)
    = impossibleOK defs !(nf defs env l)
                        !(nf defs env r)
impossibleErrOK defs (BadDotPattern _ _ ErasedArg _ _) = pure True
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
  = do l <- nf defs env l
       r <- nf defs env r
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
getRHSEnv env (Bind n (PVar stage ty) sc) (Bind n' (PVTy _ _) scty) with (nameEq n n')
  getRHSEnv env (Bind n (PVar stage ty) sc) (Bind n' (PVTy _ _) scty) | Nothing
      = throw (GenericMsg "Can't happen: names don't match in getRHSEnv")
  getRHSEnv env (Bind n (PVar stage ty) sc) (Bind n (PVTy _ _) scty) | (Just Refl)
      = getRHSEnv (PVar stage ty :: env) sc scty
getRHSEnv env lhs ty = pure (vars ** (env, lhs, ty))

-- TODO I don't bother with the find/set/combineLinear functions...
--      I just find names used in an Explicit position at least once
--      and call it a day. Bad move?

-- List all of the PVar names which are used explicit positions (once or more) in the LHS
-- Based on idris2's findLinear function
findExp : {vars : _} ->
             {auto c : Ref Ctxt Defs} ->
             Nat -> (lhsenv : Term vars) ->
             Core (List Name)
findExp bound (Bind n b sc)
    = findExp (S bound) sc
findExp bound tm
    = case getFnInfoArgs tm of
           (Ref _  n, []) => pure []
           (Ref nt n, args)
              => do defs <- get Ctxt
                    Just (MkGlobalDef nty _) <- lookupDef n (defs)
                         | Nothing => pure []
                    findExpArg !(nf defs [] nty) args
           _ => pure []
    where
      findExpArg : {vars : _} ->
                   NF [] -> List (AppInfo, Term vars) ->
                   Core (List Name)
      findExpArg (NBind x (Pi _ Explicit _ ) sc) ((_, Local {name=a} idx prf) :: as)
          = do defs <- get Ctxt
               let a = nameAt idx prf
               if idx < bound
                 then do sc' <- sc defs (toClosure [] (Ref Bound x))
                         pure $ a :: !(findExpArg sc' as)
                 else do sc' <- sc defs (toClosure [] (Ref Bound x))
                         findExpArg sc' as
      findExpArg (NBind x (Pi _ Explicit _) sc) ((_, a) :: as)
          = do defs <- get Ctxt
               pure $ !(findExp bound a) ++
                      !(findExpArg !(sc defs (toClosure [] (Ref Bound x))) as)
      findExpArg (NBind x (Pi _ Implicit _) sc) ((_, a) :: as) --TODO unsure
          = do defs <- get Ctxt
               pure !(findExpArg !(sc defs (toClosure [] (Ref Bound x))) as)
      findExpArg ty ((ia, a) :: as)
          = pure $ !(findExp bound a) ++ !(findExpArg ty as)
      findExpArg _ [] = pure []

-- Easy interface into findExp
findExpTop : {vars : _} ->
             {auto c : Ref Ctxt Defs} ->
             Term vars ->
             Core (List Name)
findExpTop tm = do imps <- findExp (length vars) tm
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
       let rhstm'    = wrapRHSWithLams env exps rhstm
       let exprhsty' = rhsTypeToPi env exps exprhsty
       case toTTImp rhstm' of
         Nothing      => throw $ GenericMsg "Can't convert back to TTImp"
         Just rhswrap => do (rhstm', rhsty')
                               <- checkTerm env rhswrap (Just (gnf env exprhsty'))
                            pure ()

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

       (lhstm, lhstyg) <- elabTerm InLHS env (wrapDot lhs) Nothing

       lhstm <- normalise defs env lhstm
       lhsty <- normalise defs env !(getTerm lhstyg)

       -- TODO Maybe tag patterns with IMust unify, etc?

       ret <-  getRHSEnv env lhstm lhsty
       pure (lhs, ret)
  where
  wrapDot : RawImp -> RawImp
  wrapDot (ILet n margTy argVal scope) = ILet n margTy (wrapDot argVal) (wrapDot scope)
  wrapDot (IPi Implicit mn argTy retTy) = IPi Implicit mn argTy retTy
  wrapDot (IPi Explicit mn argTy retTy) = IPi Explicit mn argTy retTy
  wrapDot (ILam Implicit mn argTy scope) = ILam Implicit mn argTy (wrapDot scope)--(IMustUnify $ wrapDot scope)
  wrapDot (ILam Explicit mn argTy scope) = ILam Explicit mn argTy (wrapDot scope)
  wrapDot (IPatvar n ty scope) = IPatvar n ty (wrapDot scope)
  wrapDot (IApp AImplicit f a) = IApp AImplicit (wrapDot f) (IMustUnify a)
  wrapDot (IApp AExplicit f a) = IApp AExplicit (wrapDot f) (wrapDot a)
  wrapDot (IVar x) = IVar x
  wrapDot (IMustUnify x) = IMustUnify x
  wrapDot (IQuote x) = IQuote $ wrapDot x
  wrapDot (ICode x) = ICode $ wrapDot x
  wrapDot (IEval x) = IEval $ wrapDot x
  wrapDot (IEscape x) = IEscape $ wrapDot x
  wrapDot IType = IType
  wrapDot Implicit = Implicit



processClause : {auto c : Ref Ctxt Defs} ->
                {auto u : Ref UST UState} ->
                {auto s : Ref Stg Stage} ->
                ImpClause -> Core Clause
processClause (ImpossibleClause lhs_in)
    = do ?processImpossibleClause -- TODO also parse the impossible clause
processClause (PatClause lhs_in rhs)
    = do -- Check the LHS
         (lhs, (vars ** (env, lhsenv, rhsexp))) <- processLHS [] lhs_in

         ust <- get UST
         coreLift $ putStrLn $ "dot constrs are " ++ show (dotConstraints ust)
         defs <- get Ctxt
         coreLift $ putStrLn $ "defs are " ++ show (defs)
         checkDots
         ust <- get UST
         coreLift $ putStrLn $ "dot constrs are " ++ show (dotConstraints ust)
         defs <- get Ctxt
         coreLift $ putStrLn $ "defs are " ++ show (defs)

         ust <- get UST
         coreLift $ putStrLn $ "guesses are " ++ show (guesses ust)
         coreLift $ putStrLn $ "holes are " ++ show (holes ust)
         let [] = SortedMap.toList $ constraints ust
                | cs => throw (GenericMsg $ "Constraints present after processing clause: "
                               ++ show (map snd cs))

         (rhstm, rhsty) <- checkTerm env rhs (Just (gnf env rhsexp))

         defs <- get Ctxt
         rhsnf <- normalise defs env rhstm

         -- Check that implicit/explicit arg use is correct on the RHS
         processImplicitUse env lhsenv rhstm rhsexp


         pure (MkClause env lhsenv rhstm) --rhsnf)

nameListEq : (xs : List Name) -> (ys : List Name) -> Maybe (xs = ys)
nameListEq [] [] = Just Refl
nameListEq (x :: xs) (y :: ys) with (nameEq x y)
  nameListEq (x :: xs) (x :: ys) | (Just Refl) with (nameListEq xs ys)
    nameListEq (x :: xs) (x :: xs) | (Just Refl) | Just Refl= Just Refl
    nameListEq (x :: xs) (x :: ys) | (Just Refl) | Nothing = Nothing
  nameListEq (x :: xs) (y :: ys) | Nothing = Nothing
nameListEq _ _ = Nothing

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
         (args ** tree) <- getPMDef n (type gdef) chkcs

         -- Update the definition with the compiled tree
         updateDef n (record { definition = PMDef args tree })

         coreLift $ putStrLn $ "Complete ----------------------"
         coreLift $ putStrLn $ "Args = " ++ show args
         coreLift $ putStrLn $ "Tree = " ++ show tree
         coreLift $ putStrLn $ "Processed " ++ show n
