module TTImp.Elab.Term

import Core.Context
import Core.Core
import Core.Env
import Core.Normalise
import Core.TT
import Core.Unify
import Core.Value

import TTImp.TTImp

import Data.Maybe

checkExp : {vars : _} ->
           {auto c : Ref Ctxt Defs} ->
           {auto u : Ref UST UState} ->
           Env Term vars ->
           (term : Term vars) ->
           (got : Glued vars) ->
           (expected : Maybe (Glued vars)) ->
           Core (Term vars, Glued vars)
checkExp env term got Nothing = pure (term, got)
checkExp env term got (Just exp)
   = -- 'got' had better unify with exp. This might solve some of the
     -- metavariables. If so, recheck any existing constraints.
     do defs <- get Ctxt
        ures <- unify env !(getNF got) !(getNF exp)

        -- If there are constraints, return a guarded definition. Otherwise,
        -- we've won.
        case constraints ures of
             [] => do -- Success: if any holes were solved, rerun unification
                      -- for any existing constraints
                      when (holesSolved ures) $
                           solveConstraints
                      pure (term, exp)
             cs => do cty <- getTerm exp
                      ctm <- newConstant env term cty cs
                      pure (ctm, got)

weakenExp : {x, vars : _} ->
            Env Term (x :: vars) ->
            Maybe (Glued vars) -> Core (Maybe (Glued (x :: vars)))
weakenExp env Nothing = pure Nothing
weakenExp env (Just gtm)
    = do tm <- getTerm gtm
         pure (Just (gnf env (weaken tm)))

-- Check a raw term, given (possibly) the current environment and its expected 
-- type, if known.
-- Returns a pair of checked term and its type.
-- A type is 'Glued', that is, a pair of a term and its normal form, though
-- typically only one has been computed, and the other will be computed if
-- needed.
export
checkTerm : {vars : _} ->
            {auto c : Ref Ctxt Defs} ->
            {auto u : Ref UST UState} ->
            {auto s : Ref Stg Stage} ->
            Env Term vars -> RawImp -> Maybe (Glued vars) ->
            Core (Term vars, Glued vars)
-- If the n exists in 'env', that's its type.
-- Otherwise, if it exists in the Defs, that's its type.
-- Otherwise, it's undefined.
checkTerm env (IVar n) exp
    = case defined n env of
           Just (MkIsDefined p) =>
             do let binder = getBinder p env
                let stageBound = binderStage binder
                stageNow <- get Stg
                if stageNow < stageBound
                  then throw (GenericMsg $ "Stage error: var " ++ show n ++ " is bound at stage "
                                            ++ show stageBound ++ " but used at stage " ++ show stageNow)
                  else checkExp env (Local _ p)
                                    (gnf env (binderType binder))
                                     exp
           Nothing =>
             do defs <- get Ctxt
                Just gdef <- lookupDef n defs
                     | Nothing => throw (UndefinedName n)
                let nt = case definition gdef of
                              DCon t a => DataCon t a
                              TCon i t a => TyCon i t a
                              _ => Func
                checkExp env (Ref nt n) (gnf env (embed (type gdef))) exp
-- Let binding with explicit type
checkTerm env (ILet n (Just argTy) argVal scope) exp
    = do (argTytm , _) <- checkTerm env argTy (Just gType)
         (argValtm, _) <- checkTerm env argVal (Just $ gnf env argTytm)
         stage <- get Stg
         let env' : Env Term (n :: vars)
                  = Lam stage Implicit argTytm :: env
         expScopeTy <- weakenExp env' exp
         (scopetm, gscopetmTy) <- checkTerm env' scope expScopeTy
         scopeTyTerm <- getTerm gscopetmTy
         pure (Bind n (Let stage argValtm argTytm) scopetm
              ,gnf env (Bind n (Let stage argValtm argTytm) scopeTyTerm))
-- Let binding with implicit type
checkTerm env (ILet n Nothing argVal scope) exp
    = do (argValtm, gargValty) <- checkTerm env argVal Nothing
         argTytm <- getTerm gargValty
         stage <- get Stg
         let env' : Env Term (n :: vars)
                  = Lam stage Implicit argTytm :: env
         expScopeTy <- weakenExp env' exp
         (scopetm, gscopetmTy) <- checkTerm env' scope expScopeTy
         scopeTyTerm <- getTerm gscopetmTy
         pure (Bind n (Let stage argValtm argTytm) scopetm
              ,gnf env (Bind n (Let stage argValtm argTytm) scopeTyTerm))
checkTerm env (IPi p mn argTy retTy) exp
    = do let n = fromMaybe (MN "_" 0) mn
         (argTytm, gargTyty) <- checkTerm env argTy (Just gType)
         stage <- get Stg
         let env' : Env Term (n :: vars)
                  = Pi stage p argTytm :: env
         (retTytm, gretTyty) <- checkTerm env' retTy (Just gType)
         checkExp env (Bind n (Pi stage p argTytm) retTytm) gType exp
checkTerm env (ILam p mn argTy scope) Nothing
    = throw (GenericMsg "Can't infer type for lambda")
checkTerm env (ILam p mn argTy scope) (Just exp)
    = do let n = fromMaybe (MN "_" 0) mn
         (argTytm, gargTyty) <- checkTerm env argTy (Just gType)
         stage <- get Stg
         let env' : Env Term (n :: vars)
                  = Lam stage p argTytm :: env
         expTyNF <- getNF exp
         defs <- get Ctxt
         case !(quote defs env expTyNF) of
              Bind _ (Pi _ _ ty) sc =>
                 do let env' : Env Term (n :: vars)
                             = Lam stage p argTytm :: env
                    let scty = renameTop n sc
                    (scopetm, gscopety) <-
                              checkTerm env' scope (Just (gnf env' scty))
                    checkExp env (Bind n (Lam stage p argTytm) scopetm)
                                 (gnf env (Bind n (Pi stage p argTytm) !(getTerm gscopety)))
                                 (Just exp)
              _ => throw (GenericMsg "Lambda must have a function type")
checkTerm env (IPatvar n ty scope) exp
    = do (ty, gTyty) <- checkTerm env ty (Just gType)
         stage <- get Stg
         let env' : Env Term (n :: vars)
                  = PVar stage ty :: env
         (scopetm, gscopety) <- checkTerm env' scope Nothing
         checkExp env (Bind n (PVar stage ty) scopetm)
                      (gnf env (Bind n (PVTy stage ty) !(getTerm gscopety)))
                      exp
checkTerm env (IApp f a) exp
    = do -- Get the function type (we don't have an expected type)
         (ftm, gfty) <- checkTerm env f Nothing
         fty <- getNF gfty
         -- We can only proceed if it really does have a function type
         case fty of
              -- Ignoring the implicitness for now
              NBind x (Pi stage _ ty) sc =>
                    do defs <- get Ctxt
                       -- Check the argument type, given the expected argument
                       -- type
                       (atm, gaty) <- checkTerm env a
                                                (Just (glueBack defs env ty))
                       -- Calculate the type of the application by continuing
                       -- to evaluate the scope with 'atm'
                       sc' <- sc defs (toClosure env atm)
                       checkExp env (App ftm atm) (glueBack defs env sc') exp
              _ => throw (GenericMsg $ "Not a function type: " ++
                          show ftm ++ " of type " ++ show !(getTerm gfty))
checkTerm env Implicit Nothing
    = throw (GenericMsg "Unknown type for implicit")
checkTerm env Implicit (Just exp)
    = do expty <- getTerm exp
         nm <- genName "_"
         -- Create a metavariable, and hope that it gets solved via
         -- checkExp later
         metaval <- newMeta env nm expty Hole
         pure (metaval, exp)
checkTerm env IType exp = checkExp env TType gType exp
checkTerm env (IQuote  sc) exp
  = do -- Increment stage so we can typecheck the scope
       stage <- get Stg
       put Stg (stage+1)
       -- Check type of our scope
       (sctm, gscty) <- checkTerm env sc Nothing
       sctytm <- getTerm gscty
       -- Decrement stage again to check whole term
       put Stg stage
       -- Does our expected type match the Code equiv of our scope's type?
       checkExp env (Quote sctm) (gnf env $ TCode sctytm) exp
checkTerm env (ICode scty) exp
  = do -- Is scty of type Type?
       (sctytm, gsctyTy) <- checkTerm env scty (Just gType)
       -- Then so is our Code type
       checkExp env (TCode sctytm) gType exp
checkTerm env (IEval code) exp
  = do -- Only eval in stage 0
       Z <- get Stg
        | _ => throw (GenericMsg "Eval appears in non-zero stage")
       -- Only eval closed terms with type TCode A
       (codetm, gcodety) <- checkTerm env code Nothing
       codetyNF <- getNF gcodety
       defs <- get Ctxt
       TCode aty <- quote defs env codetyNF
             | _ => throw (GenericMsg "Cannot eval non-code type")
       -- TODO How do we check for closed terms?! For now, I'm just checking
       -- that the NF doesn't start on a bind, but I think that's not quite
       -- right
       case !(nf defs env codetm) of
         NBind _ _ _ => throw (GenericMsg "Maybe trying to eval something with free variables?")
                        -- Then we're good to go by returning the inner term with it's inner type
         _           => checkExp env (Eval codetm) (gnf env aty) exp
checkTerm env (IEscape code) exp
  = do -- Are we in a non-zero stage?
       S n <- get Stg
         | _ => throw (GenericMsg "Cannot escape in stage zero")
       -- Check if `code` has type Code A in stage n-1
       put Stg n
       (codetm, gcodety) <- checkTerm env code Nothing
       codetyNF <- getNF gcodety
       defs <- get Ctxt
       TCode aty <- quote defs env codetyNF
         | _ => throw (GenericMsg "Cannot escape non-code type")
       put Stg (S n)
       -- We're good to go with the code's inner term and it's original type
       checkExp env (Escape codetm) (gnf env aty) exp

-- TODO Have a second pass at the staging rules and make sure we're not doing
-- too much extra work (evaluating normal forms twice for glued, etc.)
