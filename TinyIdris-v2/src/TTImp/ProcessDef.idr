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

-- List all of the PVar names which are used explicit positions in the LHS
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

findExpTop : {vars : _} ->
             {auto c : Ref Ctxt Defs} ->
             Term vars ->
             Core (List Name)
findExpTop tm = do imps <- findExp (length vars) tm
                   pure $ nub imps

wrapRHSWithLams : {vars: _} -> Env Term vars -> (exps : List Name) -> (rhs : Term vars) -> Term (vars)
wrapRHSWithLams [] _ rhs = rhs
wrapRHSWithLams {vars=v::vs} (b :: bs) exps rhs
  = let ty = binderType b
        info : PiInfo = if elem v exps then Explicit else Implicit
        rec = wrapRHSWithLams bs exps $ Bind v (Lam (binderStage b) info ty) rhs
    in weaken $ rec

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

processClause : {auto c : Ref Ctxt Defs} ->
                {auto u : Ref UST UState} ->
                {auto s : Ref Stg Stage} ->
                ImpClause -> Core Clause
processClause (PatClause lhs rhs)
    = do -- Check the LHS
         (lhstm, lhsty) <- checkTerm [] lhs Nothing

         -- Get the pattern variables from the LHS, and the expected type, 
         -- and check the RHS in that context
         (vars ** (env, lhsenv, rhsexp)) <-
             getRHSEnv [] lhstm !(getTerm lhsty)

         (rhstm, rhsty) <- checkTerm env rhs (Just (gnf env rhsexp))

         -- Check that implicit/explicit arg use is correct on the RHS
         processImplicitUse env lhsenv rhstm rhsexp

         defs <- get Ctxt
         rhsnf <- normalise defs env rhstm

         pure (MkClause env lhsenv rhstm) --rhsnf)

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

         --coreLift $ putStrLn $ "Complete ----------------------"
         --coreLift $ putStrLn $ "Args = " ++ show args
         --coreLift $ putStrLn $ "Tree = " ++ show tree
         coreLift $ putStrLn $ "Processed " ++ show n
