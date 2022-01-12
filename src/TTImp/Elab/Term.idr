module TTImp.Elab.Term

import Core.Context
import Core.Core
import Core.Env
import Core.Extraction
import Core.Normalise
import Core.TT
import Core.Unify
import Core.UnifyState
import Core.Value

import TTImp.TTImp

import Data.Maybe
import Data.SortedSet

public export
data ElabMode = InType | InLHS | InExpr | InTransform -- TODO InLHS might need some sort of erasure tag

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

        -- First convert our terms to their extractions
        let gotExt = extraction !(getTerm got)
        let expExt = extraction !(getTerm exp)

        ures <- unify env !(nf defs env gotExt) !(nf defs env expExt)
        --ures <- unify env !(getNF got) !(getNF exp)

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
                      -- For now, throw error if we generate extra constraints
                      -- This might impact more involved proofs later on!!
                      --throw (CantConvert env !(getTerm got) !(getTerm exp))
                      pure (ctm, got)

weakenExp : {x, vars : _} ->
            Env Term (x :: vars) ->
            Maybe (Glued vars) -> Core (Maybe (Glued (x :: vars)))
weakenExp env Nothing = pure Nothing
weakenExp env (Just gtm)
    = do tm <- getTerm gtm
         pure (Just (gnf env (weaken tm)))

-- Check that the implicitness of a binder is compatible with the implicitness of an application
checkImplicitness : PiInfo -> AppInfo -> Core Bool
checkImplicitness Implicit AImplicit         = pure True -- TODO not sure if we should match exactly explicit to explicit, maybe!
checkImplicitness Explicit AExplicit = pure True
checkImplicitness _        _         = pure False

checkLamFV : {vars:_} -> (n:Name) -> PiInfo -> (scope: Term (n::vars)) -> Core ()
checkLamFV n Explicit scopetm = pure ()
checkLamFV n Implicit scopetm
  = let scopetmE = extraction scopetm in
    if isFreeVar {outer=[]} n scopetmE
       then throw (GenericMsg $ "Var bound by implicit lambda exists in the extraction of it's body; " ++ show n ++ " in " ++ show scopetmE)
       else pure ()

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
    = do let n = fromMaybe (MN "_" 0) mn
         (argTytm, gargTyty) <- checkTerm env argTy (Just gType)
         stage <- get Stg
         let env' : Env Term (n :: vars)
                  = Lam stage p argTytm :: env
         (scopetm, gscopety) <- checkTerm env' scope Nothing

         -- If implicit, check that name isn't free var in extraction of scope
         checkLamFV n p scopetm

         checkExp env (Bind n (Lam stage p argTytm) scopetm)
                      (gnf env (Bind n (Pi stage p argTytm) !(getTerm gscopety)))
                      Nothing
checkTerm env (ILam p mn argTy scope) (Just exp)
    = do let n = fromMaybe (MN "_" 0) mn
         (argTytm, gargTyty) <- checkTerm env argTy (Just gType)
         stage <- get Stg
         let env' : Env Term (n :: vars)
                  = Lam stage p argTytm :: env
         expTyNF <- getNF exp
         defs <- get Ctxt
         case !(quote defs env expTyNF) of
              Bind _ (Pi _ p' ty) sc =>
                 do let env' : Env Term (n :: vars)
                             = Lam stage p argTytm :: env
                    let scty = renameTop n sc
                    (scopetm, gscopety) <-
                              checkTerm env' scope (Just (gnf env' scty))
                    let True = p == p'
                          | _ => throw (GenericMsg "Lambda binding does not have same implicitness as its type")
                    checkLamFV n p scopetm
                    
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
checkTerm env (IApp i f a) exp
    = do -- Get the function type (we don't have an expected type)
         (ftm, gfty) <- checkTerm env f Nothing
         fty <- getNF gfty
         -- We can only proceed if it really does have a function type
         case fty of
              -- Ignoring the implicitness for now
              NBind x (Pi stage bInfo ty) sc =>
                    do defs <- get Ctxt
                       -- Check the argument type, given the expected argument
                       -- type
                       (atm, gaty) <- checkTerm env a
                                                (Just (glueBack defs env ty))

                       -- Check implicitness of application and binder match
                       True <- checkImplicitness bInfo i
                         | _ => throw (GenericMsg $ "Can't apply " ++ show i ++
                                       " argument (" ++ show atm ++ ") to " ++
                                       show bInfo ++ " binder (" ++ show x ++ ")" )
                       -- Calculate the type of the application by continuing
                       -- to evaluate the scope with 'atm'
                       sc' <- sc defs (toClosure env atm)
                       checkExp env (App i ftm atm) (glueBack defs env sc') exp
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
       stage <- get Stg
       put Stg $ S stage
       (sctytm, gsctyTy) <- checkTerm env scty (Just gType)
       put Stg stage
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

export
normaliseHoleTypes : {auto c : Ref Ctxt Defs} ->
                     {auto u : Ref UST UState} ->
                     Core ()
normaliseHoleTypes
  = do ust <- get UST
       let hs = Data.SortedSet.toList (holes ust)
       defs <- get Ctxt
       traverse_ (normaliseH defs) hs
  where
    updateType : Defs -> Name -> GlobalDef -> Core ()
    updateType defs n def
      = do ty' <- normalise defs [] (type def) -- TODO only need to normalise holes... we're doing the full thing
           ignore $ addDef n (record { type = ty' } def)

    normaliseH : Defs -> Name -> Core ()
    normaliseH defs n
      = do Just gdef <- lookupDef n defs
             | Nothing => pure ()
           case definition gdef of
             Hole => updateType defs n gdef
             _ => pure ()

export
elabTerm : {vars : _} ->
           {auto c : Ref Ctxt Defs} ->
           {auto s : Ref Stg Stage} ->
           {auto u : Ref UST UState} ->
           ElabMode ->
           Env Term vars -> RawImp -> Maybe (Glued vars) ->
           Core (Term vars, Glued vars)
elabTerm {vars} mode env tm ty
  = do -- Record existing hole state
       oldhs <- saveHoles
       ust <- get UST
       let constart = nextConstraint ust
       defs <- get Ctxt

       -- check term as usual
       (chktm, chkty) <- checkTerm env tm ty

       -- Final retry of solving constraints
       solveConstraints --TODO pass in InLHS as a mode


       defs <- get Ctxt
       chktm <- normalise defs env chktm

       hs <- getHoles
       restoreHoles (union hs oldhs)

       pure (chktm, chkty)