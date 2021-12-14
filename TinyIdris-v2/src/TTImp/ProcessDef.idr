module TTImp.ProcessDef

import Core.CaseBuilder
import Core.CaseTree
import Core.Context
import Core.Env
import Core.Normalise
import Core.TT
import Core.UnifyState
import Core.Value

import TTImp.Elab.Term
import TTImp.TTImp

import Data.Maybe
import Data.List

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

-- List all of the PVar names which are used implicitly in the LHS
-- Based on idris2's findLinear function
findImp : {vars : _} ->
             {auto c : Ref Ctxt Defs} ->
             Bool -> Nat -> (lhsenv : Term vars) ->
             Core (List Name)
findImp inImp bound (Bind n b sc)
    = findImp inImp (S bound) sc
findImp inImp bound tm
    = case getFnInfoArgs tm of
           (Ref _  n, []) => pure []
           (Ref nt n, args)
              => do defs <- get Ctxt
                    Just (MkGlobalDef nty _) <- lookupDef n (defs)
                         | Nothing => pure []
                    findImpArg !(nf defs [] nty) args
           _ => pure []
    where

      findImpArg : {vars : _} ->
                   NF [] -> List (AppInfo, Term vars) ->
                   Core (List Name)
      findImpArg (NBind x (Pi _ Implicit _ ) sc) ((_, Local {name=a} idx prf) :: as)
          = do defs <- get Ctxt
               let a = nameAt idx prf
               if idx < bound
                 then do sc' <- sc defs (toClosure [] (Ref Bound x))
                         pure $ a :: !(findImpArg sc' as)
                 else do sc' <- sc defs (toClosure [] (Ref Bound x))
                         findImpArg sc' as
      findImpArg (NBind x (Pi _ Implicit _) sc) ((_, a) :: as)
          = do defs <- get Ctxt
               pure $ !(findImp True bound a) ++
                      !(findImpArg !(sc defs (toClosure [] (Ref Bound x))) as)
      findImpArg ty ((ia, a) :: as)
          = pure $ !(findImp (inImp || AImplicit == ia) bound a) ++ !(findImpArg ty as)
      findImpArg _ [] = pure []

findImpTop : {vars : _} ->
             {auto c : Ref Ctxt Defs} ->
             Term vars ->
             Core (List Name)
findImpTop tm = do imps <- findImp False (length vars) tm
                   pure $ nub imps

wrapRHSWithLams : {vars: _} -> Env Term vars -> (imps : List Name) -> (rhs : Term vars) -> Term (vars)
wrapRHSWithLams [] _ rhs = rhs
wrapRHSWithLams {vars=v::vs} (b :: bs) imps rhs
  = let ty = binderType b
        info : PiInfo = if elem v imps then Implicit else Explicit
        rec = wrapRHSWithLams bs imps $ Bind v (Lam (binderStage b) info ty) rhs
    in weaken $ rec

implicitPVarsToLams : {vars : _} -> (imps : List Name) -> Env Term vars -> Env Term vars
implicitPVarsToLams imps [] = []
implicitPVarsToLams {vars = v :: vs} imps ((PVar s ty) :: bs)
  = if elem v imps then (Lam s Implicit ty) :: implicitPVarsToLams imps bs
                   else (PVar s ty)          :: implicitPVarsToLams imps bs
implicitPVarsToLams imps (b :: bs)           = b :: implicitPVarsToLams imps bs

rhsTypeToPi : {vars: _} -> Env Term vars -> (imps : List Name) -> (rhsty : Term vars) -> Term vars
rhsTypeToPi [] _ rhsty = rhsty
rhsTypeToPi {vars=v::vs} (b :: bs) imps rhsty
  = let ty = binderType b
        info : PiInfo = if elem v imps then Implicit else Explicit
        rec = rhsTypeToPi bs imps $ Bind v (Pi (binderStage b) info ty) rhsty
    in weaken rec

processClause : {auto c : Ref Ctxt Defs} ->
                {auto u : Ref UST UState} ->
                {auto s : Ref Stg Stage} ->
                ImpClause -> Core Clause
processClause (PatClause lhs rhs)
    = do -- Check the LHS
         (lhstm, lhsty) <- checkTerm [] lhs Nothing
         --coreLift $ putStrLn $ show lhstm
         -- Get the pattern variables from the LHS, and the expected type, 
         -- and check the RHS in that context

         (vars ** (env, lhsenv, rhsexp)) <-
             getRHSEnv [] lhstm !(getTerm lhsty)
         --coreLift $ putStrLn $ "Env <- " ++ show vars
         --coreLift $ putStrLn $ "LHS env tm = " ++ show lhsenv
         --coreLift $ putStrLn $ "Implicit patvars in LHS are " ++ show !(findImpTop lhsenv)
         --coreLift $ putStrLn $ "LHS got ty = " ++ show !(getTerm lhsty)
         --coreLift $ putStrLn $ "RHS exp ty = " ++ show rhsexp

         --let env' = implicitPVarsToLams !(findImpTop lhsenv) env
         -- Check the RHS in that context
         (rhstm, rhsty) <- checkTerm env rhs (Just (gnf env rhsexp))

         -- Wrap rhs in lambdas defining the implicitness of each patvar, and apply
         -- TODO Can't wrap on Terms since we want to check (with RawImp)
         --        Try 1) convert Terms back to rawimp?! Madness
         --        or  2) Can we replace PVars with Lams in env? Does that fuck up the case tree stuff?
         --                 Nope because body of `wrong` is just a ref, not an application
         let wrappedRhs = wrapRHSWithLams env !(findImpTop lhsenv) rhstm
         let wrappedRhsExp = rhsTypeToPi env !(findImpTop lhsenv) rhsexp
         case toTTImp wrappedRhs of
           Nothing => coreLift $ putStrLn $ "Can't convert to TTImp"
           Just rhswrap => do (rhstm', rhsty') <- checkTerm env rhswrap (Just (gnf env wrappedRhsExp))
                              pure ()

         --coreLift $ putStrLn $ "RHS tm = " ++ show rhstm
         pure (MkClause env lhsenv rhstm)

export
processDef : {auto c : Ref Ctxt Defs} ->
             {auto u : Ref UST UState} ->
             {auto s : Ref Stg Stage} ->
             Name -> List ImpClause -> Core ()
processDef n clauses
    = do defs <- get Ctxt
         Just gdef <- lookupDef n defs
              | Nothing => throw (GenericMsg ("No type declaration for " ++ show n))
         chkcs <- traverse processClause clauses

         -- Now we have all the clauses, make a case tree
         (args ** tree) <- getPMDef n (type gdef) chkcs

         -- Update the definition with the compiled tree
         updateDef n (record { definition = PMDef args tree })
         --coreLift $ putStrLn $ "With gdef type = " ++ show (type gdef)
         coreLift $ putStrLn $ "Processed " ++ show n
