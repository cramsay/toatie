module TTImp.PartialEval

import Core.CaseTree
import Core.Context
import Core.Core
import Core.TT
import Core.Env
import Core.Hash
import Core.Normalise
import Core.Value
import Core.UnifyState

import TTImp.Elab.Check
import TTImp.TTImp

import Data.List
import Data.SortedSet
import Data.SortedMap

%default covering

data ArgMode = Static AppInfo (Term []) | Dynamic AppInfo

NameMap : Type -> Type
NameMap = SortedMap Name

Show ArgMode where
  show (Static i tm) = "Static " ++ show i ++ " " ++ show tm
  show (Dynamic i) = "Dynamic " ++ show i

getStatic : ArgMode -> Maybe (Term [])
getStatic (Dynamic _) = Nothing
getStatic (Static _ t) = Just t

specialiseTy : {vars : _} ->
               Nat -> List (Nat, Term []) -> Term vars -> Term vars
specialiseTy i specs (Bind x (Pi s info ty) sc)
  = case lookup i specs of
      Nothing => Bind x (Pi s info ty) $ specialiseTy (S i) specs sc
      Just tm => specialiseTy (S i) specs (subst (embed tm) sc)
specialiseTy i specs ty = ty

substLoc : {vs : _} ->
           Nat -> Term vs -> Term vs -> Term vs
substLoc i tm (Local idx p)
    = if i == idx then tm else (Local idx p)
substLoc i tm (Bind x b sc)
    = Bind x (map (substLoc i tm) b) (substLoc (1 + i) (weaken tm) sc)
substLoc i tm (Meta n args)
    = Meta n (map (substLoc i tm) args)
substLoc i tm (App ai f a) = App ai (substLoc i tm f) (substLoc i tm a)
substLoc i tm (TCode ty) = TCode (substLoc i tm ty)
substLoc i tm (Quote ty x) = Quote (substLoc i tm ty) (substLoc i tm x)
substLoc i tm (Escape x) = Escape (substLoc i tm x)
substLoc i tm (Eval x) = Eval (substLoc i tm x)
substLoc i tm x = x

substLocs : {vs : _} ->
            List (Nat, Term vs) -> Term vs -> Term vs
substLocs [] tm = tm
substLocs ((i, tm') :: subs) tm = substLocs subs (substLoc i tm' tm)

mkSubsts : Nat -> List (Nat, Term []) ->
           List (Term vs) -> Term vs -> Maybe (List (Nat, Term vs))
mkSubsts i specs [] rhs = Just []
mkSubsts i specs (arg :: args) rhs
    = do subs <- mkSubsts (1 + i) specs args rhs
         case lookup i specs of
              Nothing => Just subs
              Just tm => case arg of
                              Local idx _ =>
                                   Just ((idx, embed tm) :: subs)
                              _ => Nothing

-- In the case where all the specialised positions are variables on the LHS,
-- substitute the term in on the RHS
specPatByVar : List (Nat, Term []) ->
                (vs ** (Env Term vs, Term vs, Term vs)) ->
                Maybe (vs ** (Env Term vs, Term vs, Term vs))
specPatByVar specs (vs ** (env, lhs, rhs))
    = do let (fn, args) = getFnInfoArgs lhs
         psubs <- mkSubsts 0 specs (map snd args) rhs
         let lhs' = apply fn args
         pure (vs ** (env, substLocs psubs lhs', substLocs psubs rhs))

specByVar : List (Nat, Term []) ->
            List (vs ** (Env Term vs, Term vs, Term vs)) ->
            Maybe (List (vs ** (Env Term vs, Term vs, Term vs)))
specByVar specs [] = pure []
specByVar specs (p :: ps)
  = do p' <- specPatByVar specs p
       ps' <- specByVar specs ps
       pure (p' :: ps')

dropSpec : Nat -> List (Nat, Term []) -> List a -> List a
dropSpec i sargs [] = []
dropSpec i sargs (x :: xs)
  = case lookup i sargs of
      Nothing => x :: dropSpec (1 + i) sargs xs
      Just _ => dropSpec (1 + i) sargs xs

addRefs : Name -> SortedSet Name -> Term vars -> SortedSet Name
addRefs at ns (Local _ _) = ns
addRefs at ns (Ref x name) = insert name ns
addRefs at ns (Meta x xs) = addRefsArgs ns xs
  where addRefsArgs : SortedSet Name -> List (Term vars) -> SortedSet Name
        addRefsArgs ns [] = ns
        addRefsArgs ns (t :: ts) = addRefsArgs (addRefs at ns t) ts
addRefs at ns (Bind x b scope) = addRefs at (addRefs at ns (binderType b)) scope
addRefs at ns (App _ (App _ (Ref _ name) x) y)
  = if name == at
       then addRefs at (insert name ns) y
       else addRefs at (addRefs at (insert name ns) x) y
addRefs at ns (App i f a) = addRefs at (addRefs at ns f) a
addRefs at ns TType = ns
addRefs at ns Erased = ns
addRefs at ns (Quote ty tm) = addRefs at (addRefs at ns tm) ty
addRefs at ns (TCode x) = addRefs at ns x
addRefs at ns (Eval x) = addRefs at ns x
addRefs at ns (Escape x) = addRefs at ns x

getDefRefs : Name -> GlobalDef -> SortedSet Name -> SortedSet Name
getDefRefs at (MkGlobalDef type (PMDef _ _ _ cls) _) ns = foldl union empty $ map (getClauseRefs at ns) cls
  where getClauseRefs : Name -> SortedSet Name -> (vs ** (Env Term vs, Term vs, Term vs)) -> SortedSet Name
        getClauseRefs at ns (_ ** (_, _, rhs)) = addRefs at ns rhs
getDefRefs at (MkGlobalDef type _ _) ns = addRefs at empty type

-- Get the reducible names in a function to be partially evaluated. In practice,
-- that's all the functions it refers to
getReducible : List Name -> -- calls to check
               NameMap Nat -> -- which nodes have been visited. If the entry is
               -- present, it's visited
               Defs -> Core (NameMap Nat)
getReducible [] refs defs = pure refs
getReducible (n :: rest) refs defs
  = do let Nothing = lookup n refs
             | Just _ => getReducible rest refs defs
       case !(lookupDef n defs) of
         Nothing => getReducible rest refs defs
         Just def =>
           do let refs' = insert n 65536 refs
              let calls = getDefRefs n def empty
              getReducible (Data.SortedSet.toList calls ++ rest) refs' defs

getSpecPats : {auto c : Ref Ctxt Defs} ->
              {auto s : Ref Stg  Stage} ->
              Name ->
              (fn : Name) -> (stk : List (AppInfo, Term vars)) ->
              NF [] -> -- Type of 'fn'
              List (Nat, ArgMode) -> -- All the arguments
              List (Nat, Term []) -> -- Just the static ones
              List (vs ** (Env Term vs, Term vs, Term vs)) ->
              Core (Maybe (List ImpClause))
getSpecPats pename fn stk fnty args sargs pats
  = do -- First, see if all the specialised positions are variables. If so,
       -- substitute the arguments directly into the RHS
       let Nothing = specByVar sargs pats
           | Just specpats =>
                  do ps <- traverse (unelabPat pename) specpats
                     pure (Just ps)
       -- Otherwise, build a new definition by taking the remaining arguments
       -- on the lhs, and using the specialised function application on the rhs.
       -- Then, this will get evaluated on elaboration.
       let dynnames = mkDynNames 0 args
       let lhs = apply (IVar pename) (map (\(i,n)=>(i, IVar n)) dynnames)
       rhs <- mkRHSargs fnty (IVar fn) (map snd dynnames) args
       pure (Just [PatClause lhs rhs])
  where
    mkDynNames : Int -> List (Nat, ArgMode) -> List (AppInfo, Name)
    mkDynNames i [] = []
    mkDynNames i ((_, Dynamic ai) :: as)
      = (ai, UN $ "_pe" ++ show i) :: mkDynNames (1 + i) as
    mkDynNames i (_ :: as) = mkDynNames i as

    -- Build a RHS from the type of the function to be specialised, the
    -- dynamic argument names, and the list of given arguments. We assume
    -- the latter two correspond appropriately.
    mkRHSargs : NF [] -> RawImp -> List Name -> List (Nat, ArgMode) ->
                Core RawImp
    mkRHSargs (NBind x (Pi _ _ _) sc) app (a :: as) ((_, Dynamic ai) :: ds)
      = do defs <- get Ctxt
           sc' <- sc defs (toClosure [] Erased)
           mkRHSargs sc' (IApp ai app (IVar a)) as ds
    mkRHSargs (NBind x (Pi _ _ _) sc) app as ((_, Static ai tm) :: ds)
      = do defs <- get Ctxt
           sc' <- sc defs (toClosure [] Erased)
           let Just tm' = toTTImp tm
                 | Nothing => throw $ InternalError $ "Couldn't unelaborate term during partial elaboration: " ++ show tm
           mkRHSargs sc' (IApp ai app tm') as ds
    -- Type will depend on the value here (we assume a variadic function) but
    -- the argument names are still needed
    mkRHSargs ty app (a :: as) ((_, Dynamic ai) :: ds)
      = mkRHSargs ty (IApp ai app (IVar a)) as ds
    mkRHSargs _ app _ _
      = pure app

    closeTerm : {vs' : _} -> Env Term vs' -> Term vs' -> Term []
    closeTerm {vs'=v::vs} (b::env) tm = closeTerm env $ Bind v b tm
    closeTerm [] tm = tm

    dropArgs : Name -> Term vs' -> Term vs'
    dropArgs pename tm = apply (Ref Func pename) (dropSpec 0 sargs (snd $ getFnInfoArgs tm))

    unelabPat : Name -> (vs ** (Env Term vs, Term vs, Term vs)) ->
                Core ImpClause
    unelabPat pename (vs ** (env, lhs, rhs))
      = do let clhs = closeTerm env $ dropArgs pename lhs
           let Just lhs' = toTTImp clhs
                 | Nothing => throw $ InternalError $ "Couldn't unelaborate LHS during partial elaboration: " ++ show clhs
           defs <- get Ctxt
           rhsnf <- normalise defs env rhs
           let Just rhs' = toTTImp rhsnf
                 | Nothing => throw $ InternalError $ "Couldn't unelaborate RHS during partial elaboration: " ++ show rhsnf
           pure $ PatClause lhs' rhs'

mkSpecDef : {auto c : Ref Ctxt Defs} ->
            {auto s : Ref Stg  Stage} ->
            {auto u : Ref UST UState} ->
            GlobalDef ->
            Name -> List (Nat, ArgMode) -> Name -> List (AppInfo, Term vars) ->
            Core (Term vars)
mkSpecDef {vars} gdef pename sargs fn stk
  = handleUnify
      (do defs <- get Ctxt
          let staticargs
                = mapMaybe (\(x,s) => case s of
                                Dynamic _ => Nothing
                                Static _ t => Just (x,t)
                           ) sargs
          let peapp = apply (Ref Func pename) (dropSpec 0 staticargs stk)
          Nothing <- lookupDef pename defs
            | Just _ => -- already specialised
                        pure peapp
          let sty = specialiseTy 0 staticargs (type gdef)


          -- Reduce function to be specialised and reduce any name in the arguments at
          -- most once (so that recursive definitions aren't unfolded forever)
          -- TODO Should I follow this for unrolling with a heuristic to prevent stuck recursions?
          let specnames = getAllRefs empty (map snd sargs)
          let specLimits = Data.SortedSet.fromList . map (\n => (n, 1)) $ Data.SortedSet.toList specnames
          defs <- get Ctxt
          reds <- getReducible [fn] empty defs

          let PMDef pmargs ct tr pats = definition gdef
              | _ => pure (apply (Ref Func fn) stk)
          Just newpats <- getSpecPats pename fn stk !(nf defs [] (type gdef))
                                      sargs staticargs pats
            | Nothing => pure (apply (Ref Func fn) stk)

          addDef pename (newDef sty None)
          processDecl {m = !(newRef Mods [])} [] (IDef pename newpats)
          pure peapp
      )
      -- If the partially evaluated definition fails, just use the initial
      -- application. It might indicates a bug in the P.E. function generation
      -- if it fails, but I don't want the whole system to be dependent on
      -- the correctness of PE!
      (\err => do log "PE" 10 $ "Failed during partial evaluation of " ++ show fn
                  pure (apply (Ref Func fn) stk))
  where
    getAllRefs : SortedSet Name -> List ArgMode -> SortedSet Name
    getAllRefs ns (Dynamic _ :: xs) = getAllRefs ns xs
    getAllRefs ns (Static _ t :: xs)
      = addRefs (UN "_") (getAllRefs ns xs) t
    getAllRefs ns [] = ns

-- Specialise a function name according to arguments. Return the specialised
-- application on success, or Nothing if it's not specialisable (due to static
-- arguments not being concrete)
specialise : {vars : _} ->
             {auto c : Ref Ctxt Defs} ->
             {auto s : Ref Stg  Stage} ->
             {auto u : Ref UST UState} ->
             Env Term vars -> GlobalDef ->
             Name -> List (AppInfo, Term vars) ->
             Core (Maybe (Term vars))
specialise {vars} env gdef fn stk
  = do Just sargs <- getSpecArgs 0 stk
         | Nothing => pure Nothing
       -- Make a name for the new PE function based on the hash of the static args
       let nhash = hash (mapMaybe getStatic (map snd sargs)) `hashWithSalt` fn
       let pename = UN $ "PE_" ++ show fn ++ "_" ++ show nhash
       defs <- get Ctxt
       case !(lookupDef pename defs) of
         Nothing => Just <$> mkSpecDef gdef pename sargs fn stk
         Just _  => pure Nothing
  where
    dropAll : {vs : _} -> SubVars [] vs
    dropAll {vs = []} = SubRefl
    dropAll {vs = v :: vs} = DropCons dropAll

    concrete : {vars : _} ->
               Term vars -> Maybe (Term [])
    concrete tm = shrinkTerm tm dropAll

    getSpecArgs : Nat -> List (AppInfo, Term vars) -> Core (Maybe (List (Nat, ArgMode)))
    getSpecArgs i [] = pure (Just [])
    getSpecArgs i ((ai, x) :: xs)
      = do Just xs' <- getSpecArgs (S i) xs
             | Nothing => pure Nothing
           defs <- get Ctxt
           x' <- normalise defs env x
           -- TODO erase inferred?
           let Just xok = concrete x
             | Nothing => pure . Just $ (i, Dynamic ai) :: xs'
           pure . Just $ (i, Static ai xok) :: xs'

findSpecs : {vars : _} ->
            {auto c : Ref Ctxt Defs} ->
            {auto s : Ref Stg  Stage} ->
            {auto u : Ref UST UState} ->
            Env Term vars -> List (AppInfo, Term vars) -> Term vars ->
            Core (Term vars)
findSpecs env stk (Ref Func fn)
  = do defs <- get Ctxt
       Just gdef <- lookupDef fn defs
         | Nothing => pure $ apply (Ref Func fn) stk
       Just r <- specialise env gdef fn stk
         | Nothing => pure $ apply (Ref Func fn) stk
       pure r
findSpecs env stk (Meta n args)
  = do args' <- traverse (findSpecs env []) args
       pure $ apply (Meta n args') stk
findSpecs env stk (Bind x b sc)
  = do b' <- traverse (findSpecs env []) b
       sc' <- findSpecs (b' :: env) [] sc
       pure $ apply (Bind x b' sc') stk
findSpecs env stk (App i fn arg)
    = do arg' <- findSpecs env [] arg
         findSpecs env ((i, arg') :: stk) fn
findSpecs env stk (TCode ty)  = pure $ apply (TCode !(findSpecs env [] ty))  stk
findSpecs env stk (Eval tm)   = pure $ apply (Eval !(findSpecs env [] tm))   stk
findSpecs env stk (Escape tm) = pure $ apply (Escape !(findSpecs env [] tm)) stk
findSpecs env stk (Quote ty tm)
  = do ty' <- findSpecs env [] tm
       tm' <- findSpecs env [] tm
       pure $ apply (Quote ty' tm') stk
findSpecs env stk tm = pure $ apply tm stk


bName : {auto q : Ref QVar Int} -> String -> Core Name
bName n
    = do i <- get QVar
         put QVar (i + 1)
         pure (MN n i)

--------------------------------------------------------------------------------
-- QUOTE START

mutual
  quoteArgs : {bound, free : _} ->
              {auto c : Ref Ctxt Defs} ->
              {auto s : Ref Stg  Stage} ->
              {auto u : Ref UST UState} ->
              Ref QVar Int -> Defs -> Bounds bound ->
              Env Term free -> List (AppInfo, Closure free) ->
              Core (List (AppInfo, Term (bound ++ free)))
  quoteArgs q defs bounds env [] = pure []
  quoteArgs q defs bounds env ((ia,a) :: args)
      = pure $ ( (ia, !(quoteGenNF q defs bounds env !(evalClosure defs a))) ::
                !(quoteArgs q defs bounds env args))

  quoteHead : {bound, free : _} ->
              {auto c : Ref Ctxt Defs} ->
              {auto s : Ref Stg  Stage} ->
              {auto u : Ref UST UState} ->
              Ref QVar Int -> Defs ->
              Bounds bound -> Env Term free -> NHead free ->
              Core (Term (bound ++ free))
  quoteHead {bound} q defs bounds env (NLocal _ prf)
      = let  MkVar prf' = addLater bound prf in
            pure $ Local _ prf'
    where
      addLater : {idx : _} ->
                 (ys : List Name) -> (0 p : IsVar n idx xs) ->
                 Var (ys ++ xs)
      addLater [] isv = MkVar isv
      addLater (x :: xs) isv
          = let MkVar isv' = addLater xs isv in
                MkVar (Later isv')
  quoteHead q defs bounds env (NRef Bound (MN n i))
      = case findName bounds of
             Just (MkVar p) => pure $ Local _ (varExtend p)
             Nothing => pure $ Ref Bound (MN n i)
    where
      findName : Bounds bound' -> Maybe (Var bound')
      findName None = Nothing
      findName (Add x (MN n' i') ns)
          = if i == i' -- this uniquely identifies it, given how we
                       -- generated the names, and is a faster test!
               then Just (MkVar First)
               else do MkVar p <-findName ns
                       Just (MkVar (Later p))
      findName (Add x _ ns)
          = do MkVar p <- findName ns
               Just (MkVar (Later p))
  quoteHead q defs bounds env (NRef nt n) = pure $ Ref nt n
  quoteHead q defs bounds env (NMeta n args)
      = do args' <- quoteArgs q defs bounds env (map (\x=>(AExplicit,x)) args)
           pure $ Meta n (map snd args')

  quoteBinder : {bound, free : _} ->
                {auto c : Ref Ctxt Defs} ->
                {auto s : Ref Stg  Stage} ->
                {auto u : Ref UST UState} ->
                Ref QVar Int -> Defs -> Bounds bound ->
                Env Term free -> Binder (Closure free) ->
                Core (Binder (Term (bound ++ free)))
  quoteBinder q defs bounds env (Lam s p ty)
      = do ty' <- quoteGenNF q defs bounds env !(evalClosure defs ty)
           pure (Lam s p ty')
  quoteBinder q defs bounds env (Pi s p ty)
      = do ty' <- quoteGenNF q defs bounds env !(evalClosure defs ty)
           pure (Pi s p ty')
  quoteBinder q defs bounds env (Let s val ty)
      = do val' <- quoteGenNF q defs bounds env !(evalClosure defs val)
           ty'  <- quoteGenNF q defs bounds env !(evalClosure defs ty)
           pure (Let s val' ty')
  quoteBinder q defs bounds env (PVar s i ty)
      = do ty' <- quoteGenNF q defs bounds env !(evalClosure defs ty)
           pure (PVar s i ty')
  quoteBinder q defs bounds env (PVTy s ty)
      = do ty' <- quoteGenNF q defs bounds env !(evalClosure defs ty)
           pure (PVTy s ty')

  quoteGenNF : {bound, vars : _} ->
               {auto c : Ref Ctxt Defs} ->
               {auto s : Ref Stg  Stage} ->
               {auto u : Ref UST UState} ->
               Ref QVar Int ->
               Defs -> Bounds bound ->
               Env Term vars -> NF vars -> Core (Term (bound ++ vars))
  quoteGenNF q defs bound env (NBind n b sc)
      = do var <- bName "qv"
           sc' <- quoteGenNF q defs (Add n var bound) env
                       !(sc defs (toClosure env (Ref Bound var)))
           b' <- quoteBinder q defs bound env b
           pure (Bind n b' sc')
  -- IMPORTANT CASE HERE
  -- If fn is to be specialised, quote the args directly (no further
  -- reduction) then call specialise. Otherwise, quote as normal
  quoteGenNF q defs bound env (NApp (NRef Func fn) args)
      = do Just gdef <- lookupDef fn defs
             | Nothing => do args' <- quoteArgs q defs bound env args
                             pure $ apply (Ref Func fn) args'
           empty <- clearDefs defs
           args' <- quoteArgs q defs bound env args
           Just r <- specialise (extendEnv bound env) gdef fn args'
             | Nothing =>
                 -- can't specialise, keep the arguments
                 -- unreduced
                 do args' <- quoteArgs q empty bound env args
                    pure $ apply (Ref Func fn) args'
           pure r
    where
       extendEnv : Bounds bs -> Env Term vs -> Env Term (bs ++ vs)
       extendEnv None env = env
       extendEnv (Add x n bs) env
           -- We're just using this to evaluate holes in the right scope, so
           -- a placeholder binder is fine
           = Lam 0 Explicit Erased :: extendEnv bs env
  quoteGenNF q defs bound env (NApp f args)
      = do f' <- quoteHead q defs bound env f
           args' <- quoteArgs q defs bound env args
           pure $ apply f' args'
  quoteGenNF q defs bound env (NDCon n t ar args)
      = do args' <- quoteArgs q defs bound env args
           pure $ apply (Ref (DataCon t ar) n) args'
  quoteGenNF q defs bound env (NTCon n info t ar args)
      = do args' <- quoteArgs q defs bound env args
           pure $ apply (Ref (TyCon info t ar) n) args'
  quoteGenNF q defs bound env NErased = pure Erased
  quoteGenNF q defs bound env NType = pure TType
  quoteGenNF q defs bound env (NQuote ty tm)
      = do tmNf <- evalClosure defs tm
           tm' <- quoteGenNF q defs bound env tmNf
           tyNf <- evalClosure defs ty
           ty' <- quoteGenNF q defs bound env tyNf
           pure $ Quote ty' tm'
  quoteGenNF q defs bound env (NCode  tm)
      = pure $ TCode !(quoteGenNF q defs bound env tm)
  quoteGenNF q defs bound env (NEscape tm args)
      = do args' <- quoteArgs q defs bound env args
           case tm of
             NQuote ty arg => do argNf <- evalClosure defs arg
                                 pure $ apply !(quoteGenNF q defs bound env argNf) args'
             otherwise => pure $ apply (Escape !(quoteGenNF q defs bound env tm)) args'

-- QUOTE END
--------------------------------------------------------------------------------

evalRHS : {vars : _} ->
          {auto c : Ref Ctxt Defs} ->
          {auto s : Ref Stg  Stage} ->
          {auto u : Ref UST UState} ->
          Env Term vars -> NF vars -> Core (Term vars)
evalRHS env nf
    = do q <- newRef QVar 0
         defs <- get Ctxt
         quoteGenNF q defs None env nf

export
applySpecialise : {vars : _} ->
                  {auto c : Ref Ctxt Defs} ->
                  {auto s : Ref Stg  Stage} ->
                  {auto u : Ref UST UState} ->
                  Env Term vars ->
                  Maybe (List (Name, Nat)) ->
                        -- ^ If we're specialising, names to reduce in the RHS
                        -- with their reduction limits
                  Term vars -> -- initial RHS
                  Core (Term vars)
applySpecialise env Nothing tm
    = findSpecs env [] tm -- not specialising, just search through RHS
applySpecialise env (Just ls) tm -- specialising, evaluate RHS while looking
                                 -- for names to specialise
    = do defs <- get Ctxt
         nf <- nf defs env tm
         evalRHS env nf
