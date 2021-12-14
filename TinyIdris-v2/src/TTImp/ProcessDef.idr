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

{- Old code from when I was trying to wrap each RHS up in lambdas and apply the pat vars to it
patName : Name -> Name
patName (UN n) = UN (n++"_pat")
patName (MN n i) = MN (n++"_pat") i

patNameEq : Name -> Name -> Name
patNameEq a b = if a==b then patName b else b

renameIVar : Name -> RawImp -> RawImp
renameIVar n (IVar x) = IVar $ patNameEq n x
renameIVar n (ILet x margTy argVal scope)
  = ILet (patNameEq n x) (map (renameIVar n) margTy) (renameIVar n argVal) (renameIVar n scope)
renameIVar n (IPi i x argTy retTy)
  = IPi i (map (patNameEq n) x) (renameIVar n argTy) (renameIVar n retTy)
renameIVar n (ILam i x argTy scope)
  = ILam i (map (patNameEq n) x) (renameIVar n argTy) (renameIVar n scope)
renameIVar n (IPatvar x ty scope)
  = IPatvar (patNameEq n x) (renameIVar n ty) (renameIVar n scope)
renameIVar n (IApp i f a) = IApp i (renameIVar n f) (renameIVar n a)
renameIVar n Implicit = Implicit
renameIVar n IType = IType
renameIVar n (IQuote  tm) = IQuote  $ renameIVar n tm
renameIVar n (ICode   tm) = ICode   $ renameIVar n tm
renameIVar n (IEval   tm) = IEval   $ renameIVar n tm
renameIVar n (IEscape tm) = IEscape $ renameIVar n tm

wrapRHSWithLams : {vars: _} -> Env Term vars -> (imps : List Name) -> RawImp -> RawImp
wrapRHSWithLams [] _ rhs = rhs
wrapRHSWithLams {vars=v::vs} (b :: bs) imps rhs
  = let ty = fromMaybe Implicit (toTTImp $ binderType b)
        info : PiInfo = if elem v imps then Implicit else Explicit
        ainfo : AppInfo = if info == Implicit then AImplicit else AExplicit
        lambind = ILam info (Just $ patName v) ty (renameIVar v rhs)
        var     = IVar v
    in wrapRHSWithLams bs imps $ IApp ainfo lambind var
-}

wrapRHSWithLams : {vars: _} -> Env Term vars -> (imps : List Name) -> (rhs : Term vars) -> Term (vars)
wrapRHSWithLams [] _ rhs = rhs
wrapRHSWithLams {vars=v::vs} (b :: bs) imps rhs
  = let ty = binderType b
        info : PiInfo = if elem v imps then Implicit else Explicit
        rec = wrapRHSWithLams bs imps $ Bind v (Lam (binderStage b) info ty) rhs
    in weaken $ rec

rhsTypeToPi : {vars: _} -> Env Term vars -> (imps : List Name) -> (rhsty : Term vars) -> Term vars
rhsTypeToPi [] _ rhsty = rhsty
rhsTypeToPi {vars=v::vs} (b :: bs) imps rhsty
  = let ty = binderType b
        info : PiInfo = if elem v imps then Implicit else Explicit
        rec = rhsTypeToPi bs imps $ Bind v (Pi (binderStage b) info ty) rhsty
    in weaken rec

processImplicitUse : {auto c : Ref Ctxt Defs} ->
                     {auto u : Ref UST UState} ->
                     {auto s : Ref Stg Stage} ->
                     {vars:_} -> Env Term vars -> (lhstm : Term vars) -> (rhstm : Term vars) -> (exprhsty : Term vars) -> Core ()
processImplicitUse env lhstm rhstm exprhsty
  = do imps <- findImpTop lhstm
       let rhstm'    = wrapRHSWithLams env imps rhstm
       let exprhsty' = rhsTypeToPi env imps exprhsty
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
         coreLift $ putStrLn $ "Processed " ++ show n
