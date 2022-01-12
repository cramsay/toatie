module Core.Unify

import Core.CaseTree
import Core.Context
import Core.Core
import Core.Env
import Core.Normalise
import Core.TT
import public Core.UnifyState
import Core.Value

import Data.Bool.Extra
import Data.List
import Data.SortedMap
import Data.SortedSet

public export
record UnifyResult where
  constructor MkUnifyResult
  constraints : List Int -- new constraints generated
  holesSolved : Bool -- did we solve any holes on the way?

public export
interface Unify (0 tm : List Name -> Type) where
  unify : {vars : _} ->
          {auto c : Ref Ctxt Defs} ->
          {auto u : Ref UST UState} ->
          Env Term vars ->
          tm vars -> tm vars ->
          Core UnifyResult

union : UnifyResult -> UnifyResult -> UnifyResult
union u1 u2 = MkUnifyResult (union (constraints u1) (constraints u2))
                            (holesSolved u1 || holesSolved u2)

unionAll : List UnifyResult -> UnifyResult
unionAll [] = MkUnifyResult [] False
unionAll [c] = c
unionAll (c :: cs) = union c (unionAll cs)

constrain : Int -> UnifyResult
constrain c = MkUnifyResult [c] False

success : UnifyResult
success = MkUnifyResult [] False

solvedHole : UnifyResult
solvedHole = MkUnifyResult [] True

ufail : String -> Core a
ufail msg = throw (GenericMsg msg)

unifyArgs : (Unify tm, Quote tm) =>
            {vars : _} ->
            {auto c : Ref Ctxt Defs} ->
            {auto u : Ref UST UState} ->
            Env Term vars ->
            List (AppInfo, tm vars) -> List (AppInfo, tm vars) ->
            Core UnifyResult
unifyArgs env [] [] = pure success
unifyArgs env ((ix,cx) :: cxs) ((iy,cy) :: cys)
    = do -- Do later arguments first, since they may depend on earlier
         -- arguments and use their solutions.
         cs <- unifyArgs env cxs cys
         res <- unify env cx cy
         pure (union res cs)
unifyArgs env _ _ = ufail ""

convertError : {vars : _} ->
               {auto c : Ref Ctxt Defs} ->
               Env Term vars -> NF vars -> NF vars -> Core a
convertError env x y
    = do defs <- get Ctxt
         empty <- clearDefs defs
         throw (CantConvert env !(quote empty env x)
                                !(quote empty env y))


postpone : {vars : _} ->
           {auto c : Ref Ctxt Defs} ->
           {auto u : Ref UST UState} ->
           Env Term vars -> NF vars -> NF vars -> Core UnifyResult
postpone env x y
    = do defs <- get Ctxt
         empty <- clearDefs defs

         xtm <- quote empty env x
         ytm <- quote empty env y
         c <- addConstraint (MkConstraint env xtm ytm)
         pure (constrain c)

-- Get the variables in an application argument list; fail if any arguments
-- are not variables, fail if there's any repetition of variables
-- We use this to check that the pattern unification rule is applicable
-- when solving a metavariable applied to arguments
getVars : {vars : _} ->
          List Nat -> List (NF vars) -> Maybe (List (Var vars))
getVars got [] = Just []
getVars got (NApp (NLocal idx v) [] :: xs)
    = if inArgs idx got then Nothing
         else do xs' <- getVars (idx :: got) xs
                 pure (MkVar v :: xs')
  where
    -- Inlined 'elem' by hand - this was a tiny cost saving in Idris 1!
    inArgs : Nat -> List Nat -> Bool
    inArgs n [] = False
    inArgs n (n' :: ns)
        = natToInteger n == natToInteger n' || inArgs n ns
getVars _ (_ :: xs) = Nothing

-- Make a sublist representing the variables used in the application.
-- We'll use this to ensure that local variables which appear in a term
-- are all arguments to a metavariable application for pattern unification
toSubVars : (vars : List Name) -> List (Var vars) ->
            (newvars ** SubVars newvars vars)
toSubVars [] xs = ([] ** SubRefl)
toSubVars (n :: ns) xs
     -- If there's a proof 'First' in 'xs', then 'n' should be kept,
     -- otherwise dropped
     -- (Remember: 'n' might be shadowed; looking for 'First' ensures we
     -- get the *right* proof that the name is in scope!)
     = let (_ ** svs) = toSubVars ns (dropFirst xs) in
           if anyFirst xs
              then (_ ** KeepCons svs)
              else (_ ** DropCons svs)
  where
    anyFirst : List (Var (n :: ns)) -> Bool
    anyFirst [] = False
    anyFirst (MkVar First :: xs) = True
    anyFirst (MkVar (Later p) :: xs) = anyFirst xs

{- Applying the pattern unification rule is okay if:
   * Arguments are all distinct local variables
   * The metavariable name doesn't appear in the unifying term
   * The local variables which appear in the term are all arguments to
     the metavariable application (not checked here, checked with the
     result of `patternEnv`)

   Return the subset of the environment used in the arguments
   to which the metavariable is applied. If this environment is enough
   to check the term we're unifying with, and that term doesn't use the
   metavariable name, we can safely apply the rule.

   Also, return the list of arguments the metavariable was applied to, to
   make sure we use them in the right order when we build the solution.
-}
patternEnv : {auto c : Ref Ctxt Defs} ->
             {auto u : Ref UST UState} ->
             {vars : _} ->
             Env Term vars -> List (Closure vars) ->
             Core (Maybe (newvars ** (List (Var newvars),
                                     SubVars newvars vars)))
patternEnv {vars} env args
    = do defs <- get Ctxt
         empty <- clearDefs defs
         args' <- traverse (evalClosure empty) args
         case getVars [] args' of
              Nothing => pure Nothing
              Just vs =>
                 let (newvars ** svs) = toSubVars _ vs in
                     pure (Just (newvars **
                                     (updateVars vs svs, svs)))
  where
    -- Update the variable list to point into the sub environment
    -- (All of these will succeed because the SubVars we have comes from
    -- the list of variable uses! It's not stated in the type, though.)
    updateVars : List (Var vars) -> SubVars newvars vars -> List (Var newvars)
    updateVars [] svs = []
    updateVars (MkVar p :: ps) svs
        = case subElem p svs of
               Nothing => updateVars ps svs
               Just p' => p' :: updateVars ps svs

-- How the variables in a metavariable definition map to the variables in
-- the solution term (the Var newvars)
data IVars : List Name -> List Name -> Type where
     INil : IVars [] newvars
     ICons : Maybe (Var newvars) -> IVars vs newvars ->
             IVars (v :: vs) newvars

Weaken (IVars vs) where
  weaken INil = INil
  weaken (ICons Nothing ts) = ICons Nothing (weaken ts)
  weaken (ICons (Just t) ts) = ICons (Just (weaken t)) (weaken ts)

getIVars : IVars vs ns -> List (Maybe (Var ns))
getIVars INil = []
getIVars (ICons v vs) = v :: getIVars vs

-- Instantiate a metavariable by binding the variables in 'newvars'
-- and solving the given metavariable with the resulting term.
-- If the type of the metavariable doesn't have enough arguments, fail, because
-- this wasn't valid for pattern unification
instantiate : {auto c : Ref Ctxt Defs} ->
              {auto u : Ref UST UState} ->
              {vars, newvars : _} ->
              Env Term vars ->
              (metavar : Name) -> -- Metavariable we're solving
              (mdef : GlobalDef) -> -- Current definition (for its type)
              List (Var newvars) -> -- Variable each argument maps to
              Term newvars -> -- Term to instantiate, in the environment
                              -- required by the metavariable
              Core ()
instantiate {newvars} env mname mdef locs tm
    = do let ty = type mdef -- assume all pi binders we need are there since
                            -- it was built from an environment, so no need
                            -- to normalise
         defs <- get Ctxt
         rhs <- mkDef locs INil tm ty

         let newdef = record { definition = PMDef [] (STerm rhs) } mdef
         addDef mname newdef
         removeHole mname
  where
    updateIVar : {v : Nat} ->
                 forall vs, newvars . IVars vs newvars -> (0 p : IsVar name v newvars) ->
                 Maybe (Var vs)
    updateIVar {v} (ICons Nothing rest) prf
        = do MkVar prf' <- updateIVar rest prf
             Just (MkVar (Later prf'))
    updateIVar {v} (ICons (Just (MkVar {i} p)) rest) prf
        = if v == i
             then Just (MkVar First)
             else do MkVar prf' <- updateIVar rest prf
                     Just (MkVar (Later prf'))
    updateIVar _ _ = Nothing

    updateIVars : {vs, newvars : _} ->
                  IVars vs newvars -> Term newvars -> Maybe (Term vs)
    updateIVars ivs (Local idx p)
        = do MkVar p' <- updateIVar ivs p
             Just (Local _ p')
    updateIVars ivs (Ref nt n) = pure $ Ref nt n
    updateIVars ivs (Meta n args)
        = pure $ Meta n !(traverse (updateIVars ivs) args)
    updateIVars {vs} ivs (Bind x b sc)
        = do b' <- updateIVarsB ivs b
             sc' <- updateIVars (ICons (Just (MkVar First)) (weaken ivs)) sc
             Just (Bind x b' sc')
      where
        updateIVarsB : {vs, newvars : _} ->
                       IVars vs newvars -> Binder (Term newvars) -> Maybe (Binder (Term vs))
        updateIVarsB ivs (Lam s p t)
            = Just (Lam s p !(updateIVars ivs t))
        updateIVarsB ivs (Pi s p t)
            = Just (Pi s p !(updateIVars ivs t))
        updateIVarsB ivs (Let s val t)
            = Just (Let s !(updateIVars ivs val) !(updateIVars ivs t))
        updateIVarsB ivs (PVar s t)
            = Just (PVar s !(updateIVars ivs t))
        updateIVarsB ivs (PVTy s t)
            = Just (PVTy s !(updateIVars ivs t))
    updateIVars ivs (App info f a)
        = Just (App info !(updateIVars ivs f) !(updateIVars ivs a))
    updateIVars ivs Erased = Just Erased
    updateIVars ivs TType = Just TType
    updateIVars ivs (Quote  a)  = Just (Quote  !(updateIVars ivs a))
    updateIVars ivs (TCode  a)  = Just (TCode  !(updateIVars ivs a))
    updateIVars ivs (Eval   a)  = Just (Eval   !(updateIVars ivs a))
    updateIVars ivs (Escape a)  = Just (Escape !(updateIVars ivs a))

    mkDef : {vs, newvars : _} ->
            List (Var newvars) ->
            IVars vs newvars -> Term newvars -> Term vs ->
            Core (Term vs)
    mkDef (v :: vs) vars soln (Bind x (Pi s _ ty) sc)
       = do sc' <- mkDef vs (ICons (Just v) vars) soln sc
            pure $ Bind x (Lam s Explicit Erased) sc'
    mkDef vs vars soln (Bind x b@(Let _ val ty) sc)
      = do sc' <- mkDef vs (ICons Nothing vars) soln sc
           let Just scs = shrinkTerm sc' (DropCons SubRefl)
               | Nothing => pure $ Bind x b sc'
           pure scs
    mkDef [] vars soln ty
       = do let Just soln' = updateIVars vars soln
                | Nothing => ufail ("Can't make solution for " ++ show mname)
            pure soln'
    mkDef _ _ _ ty = ufail $ "Can't make solution for " ++ show mname
                                 ++ " at " ++ show ty

mutual
  unifyIfEq : {auto c : Ref Ctxt Defs} ->
              {auto u : Ref UST UState} ->
              {vars : _} ->
              Bool -> Env Term vars -> NF vars -> NF vars ->
              Core UnifyResult
  unifyIfEq post env x y
        = do defs <- get Ctxt
             if !(convert defs env x y)
                then pure success
                else if post
                        then postpone env x y
                        else convertError env x y

  unifyHole : {vars : _} ->
              {auto c : Ref Ctxt Defs} ->
              {auto u : Ref UST UState} ->
              Env Term vars ->
              (metaname : Name) -> List (AppInfo, Closure vars) ->
                                   List (AppInfo, Closure vars) ->
              (soln : NF vars) ->
              Core UnifyResult
  unifyHole env mname margs margs' tmnf = ?dunnoman

  unifyApp : {vars : _} ->
             {auto c : Ref Ctxt Defs} ->
             {auto u : Ref UST UState} ->
             Env Term vars ->
             NHead vars -> List (AppInfo, Closure vars) ->
             NF vars ->
             Core UnifyResult
  unifyApp env (NMeta n margs) fargs tmnf
      = do let args = margs ++ map snd fargs
           case !(patternEnv env args) of
                Nothing =>
                    -- not in pattern form so postpone
                    postpone env (NApp (NMeta n margs) fargs) tmnf
                Just (newvars ** (locs, submv)) =>
                    -- In pattern form, using the 'submv' fragment of the
                    -- environment
                    do -- TODO (Exercise): We need to do an occurs check here
                       -- Check the the result is well scoped in the
                       -- metavariable's environment
                       defs <- get Ctxt
                       empty <- clearDefs defs
                       tm <- quote empty env tmnf
                       case shrinkTerm tm submv of
                            Nothing =>
                              do tm' <- quote defs env tmnf
                                 case shrinkTerm tm' submv of
                                   Nothing => postpone env (NApp (NMeta n margs) fargs) tmnf
                                   Just stm => do Just gdef <- lookupDef n defs
                                                    | Nothing => throw (UndefinedName n)
                                                  instantiate env n gdef locs stm
                                                  pure solvedHole
                            Just stm =>
                                 do Just gdef <- lookupDef n defs
                                         | Nothing => throw (UndefinedName n)
                                    instantiate env n gdef locs stm
                                    pure solvedHole

  unifyApp env f args tm
      = do defs <- get Ctxt
           if !(convert defs env (NApp f args) tm)
              then pure success
              else postpone env (NApp f args) tm

  unifyBothBinders: {auto c : Ref Ctxt Defs} ->
                    {auto u : Ref UST UState} ->
                    {vars : _} ->
                    Env Term vars ->
                    Name -> Binder (NF vars) ->
                    (Defs -> Closure vars -> Core (NF vars)) ->
                    Name -> Binder (NF vars) ->
                   (Defs -> Closure vars -> Core (NF vars)) ->
                    Core UnifyResult
  unifyBothBinders env x (Pi sx ix tx) scx y (Pi sy iy ty) scy
    = do defs <- get Ctxt
         -- Don't unify if stages are different
         if sx /= sy
           then convertError env (NBind x (Pi sx ix tx) scx) (NBind y (Pi sy iy ty) scy)
           else
             do empty <- clearDefs defs
                -- Unify types of bound vars
                tx' <- quote empty env tx
                ty' <- quote empty env ty
                ct  <- unify env tx ty
                -- Make env' so we can unify scopes
                xn <- genName "x"
                let env' : Env Term (x :: _)
                         = Pi sy Explicit tx' :: env
                case constraints ct of
                  [] => -- no constraints, check scopes
                        do tscx <- scx defs (toClosure env (Ref Bound xn))
                           tscy <- scy defs (toClosure env (Ref Bound xn))
                           tmx <- quote empty env tscx
                           tmy <- quote empty env tscy
                           unify env'
                                 (refsToLocals (Add x xn None) tmx)
                                 (refsToLocals (Add x xn None) tmy)
                  cs => -- Constraints! Make new guarded constant
                        do txtm <- quote empty env tx
                           tytm <- quote empty env ty
                           c    <- newConstant env
                                     (Bind x (Lam sy Explicit txtm) (Local _ First))
                                     (Bind x (Pi  sy Explicit txtm) (weaken tytm))
                                     cs
                           tscx <- scx defs (toClosure env (Ref Bound xn))
                           tscy <- scy defs (toClosure env (App AExplicit c (Ref Bound xn)))
                           tmx <- quote empty env tscx
                           tmy <- quote empty env tscy
                           cs' <- unify env'
                                    (refsToLocals (Add x xn None) tmx)
                                    (refsToLocals (Add x xn None) tmy)
                           pure (union ct cs')
  unifyBothBinders env x (Lam sx ix tx) scx y (Lam sy iy ty) scy
                   = do defs <- get Ctxt
                        -- Check stages
                        if sx /= sy
                          then convertError env
                                 (NBind x (Lam sx ix tx) scx)
                                 (NBind y (Lam sy iy ty) scy)
                          else
                            do empty <- clearDefs defs
                               -- Unify types of our bound vars
                               ct <- unify env tx ty
                               -- Make env' so we can unify scopes
                               xn <- genName "x"
                               txtm <- quote empty env tx
                               let env' : Env Term (x :: _)
                                        = Lam sx Explicit txtm :: env
                               -- Unify scopes
                               tscx <- scx defs (toClosure env (Ref Bound xn))
                               tscy <- scy defs (toClosure env (Ref Bound xn))
                               tmx <- quote empty env tscx
                               tmy <- quote empty env tscy
                               cs' <- unify env' (refsToLocals (Add x xn None) tmx)
                                                 (refsToLocals (Add x xn None) tmy)
                               pure (union ct cs')
  unifyBothBinders env x bx scx y by scy = convertError env (NBind x bx scx) (NBind y by scy)

  unifyBothApps : {auto c : Ref Ctxt Defs} ->
                  {auto u : Ref UST UState} ->
                  {vars : _} ->
                  Env Term vars ->
                  NHead vars -> List (AppInfo, Closure vars) ->
                  NHead vars -> List (AppInfo, Closure vars) ->
                  Core UnifyResult
  unifyBothApps env (NLocal x xp) [] (NLocal y yp) []
    = if x == y
         then pure success
         else convertError env (NApp (NLocal x xp) [])
                               (NApp (NLocal y yp) [])
  -- TODO Once we can distinguish between unification in LHS and terms... we should deal with both heads being locals applied arguments as a unification problem for InTerm.
  unifyBothApps env (NLocal x xp) xs (NLocal y yp) ys
  = unifyIfEq True env (NApp (NLocal x xp) xs) (NApp (NLocal y yp) ys)
  -- TODO case for both heads are holes...
  unifyBothApps env (NMeta xn xs) xs' yh ys
    = unifyApp env (NMeta xn xs) xs' (NApp yh ys)
  unifyBothApps env xh xs (NMeta yn ys) ys'
    = unifyApp env (NMeta yn ys) ys' (NApp xh xs)
  unifyBothApps env xh xs yh ys = unifyApp env xh xs (NApp yh ys)

  export
  unifyNoEta :
               {auto c : Ref Ctxt Defs} ->
               {auto u : Ref UST UState} ->
               {vars :_} -> Env Term vars -> NF vars -> NF vars -> Core UnifyResult
  unifyNoEta env (NDCon x tagx ax xs) (NDCon y tagy ay ys)
    = do gam <- get Ctxt
         if tagx == tagy
           then unifyArgs env xs ys
           else convertError env (NDCon x tagx ax xs) (NDCon y tagy ay ys)
  unifyNoEta env (NTCon x ix tagx ax xs) (NTCon y iy tagy ay ys)
   = do gam <- get Ctxt
        if x == y
          then unifyArgs env xs ys
          else convertError env (NTCon x ix tagx ax xs) (NTCon y iy tagy ay ys)
  unifyNoEta env (NCode   x) (NCode   y) = unify env x y
  unifyNoEta env (NEscape x) (NEscape y) = unify env x y
  unifyNoEta env (NQuote  x) (NQuote  y) = unify env x y
  unifyNoEta env x@(NApp fx@(NMeta _ _) axs)
                 y@(NApp fy@(NMeta _ _) ays)
    = do defs <- get Ctxt
         if !(convert defs env x y)
           then pure success
           else unifyBothApps env fx axs fy ays
  unifyNoEta env (NApp fx axs) (NApp fy ays)
    = unifyBothApps env fx axs fy ays
  unifyNoEta env (NApp hd args) y
    = unifyApp env hd args y
  unifyNoEta env y (NApp hd args)
    = unifyApp env hd args y
  unifyNoEta env x y
  = do defs <- get Ctxt
       empty <- clearDefs defs
       --log "unify.noeta" 10 $ "Nothing else worked, unifyIfEq"
       unifyIfEq True env x y

  isHoleApp : NF vars -> Bool
  isHoleApp (NApp (NMeta _ _) _) = True
  isHoleApp _ = False

  -- This gives the minimal rules for unification of constructor forms,
  -- solving metavariables in constructor arguments. There's more to do in
  -- general!
  export
  Unify NF where
    -- If we have two pi binders, check the arguments and scope
    unify env (NBind x b sc) (NBind x' b' sc') = unifyBothBinders env x b sc x' b' sc'
    -- TODO Idris2 has option for checking lambda against any tm too
    -- Matching constructors, reduces the problem to unifying the arguments
    unify env tmx@(NBind x (Lam sx ix tx) scx) tmy
        = do defs <- get Ctxt
             if isHoleApp tmy
                then if not !(convert defs env tmx tmy)
                        then unifyNoEta env tmx tmy
                        else pure success
                else do empty <- clearDefs defs
                        domty <- quote empty env tx
                        etay <- nf defs env
                                 $ Bind x (Lam sx Explicit domty)
                                 $ App AExplicit (weaken !(quote empty env tmy))
                                                 (Local 0 First)
                        unify env tmx etay
    unify env tmy tmx@(NBind x (Lam sx ix tx) scx) 
       = do defs <- get Ctxt
            if isHoleApp tmy
               then if not !(convert defs env tmx tmy)
                       then unifyNoEta env tmx tmy
                       else pure success
               else do empty <- clearDefs defs
                       domty <- quote empty env tx
                       etay <- nf defs env
                                $ Bind x (Lam sx Explicit domty)
                                $ App AExplicit (weaken !(quote empty env tmy))
                                                (Local 0 First)
                       unify env tmx etay
    -- Otherwise, unification succeeds if both sides are convertible
    unify env x y
        = unifyNoEta env x y

  export
  Unify Term where
    unify env x y
        = do defs <- get Ctxt
             xnf <- nf defs env x
             ynf <- nf defs env y
             unify env xnf ynf

  export
  Unify Closure where
    unify env x y
        = do defs <- get Ctxt
             xnf <- evalClosure defs x
             ynf <- evalClosure defs y
             unify env xnf ynf

-- Retry the given constraint, by constraint id
retry : {auto c : Ref Ctxt Defs} ->
        {auto u : Ref UST UState} ->
        Int -> Core UnifyResult
retry c
    = do ust <- get UST
         case lookup c (constraints ust) of
              Nothing => pure success
              Just Resolved => pure success
              Just (MkConstraint env x y) =>
                 do cs <- unify env x y
                    -- If the constraint is solved now, with no new constraints,
                    -- delete the constraint, otherwise come back to it later.
                    case (constraints cs) of
                         [] => do deleteConstraint c
                                  pure cs
                         _ => pure cs
              Just (MkSeqConstraint env xs ys) =>
                 do cs <- unifyArgs env (map (\x=>(AExplicit,x)) xs)
                                        (map (\x=>(AExplicit,x)) ys)
                    -- As above, check whether there are new contraints
                    case (constraints cs) of
                         [] => do deleteConstraint c
                                  pure cs
                         _ => pure cs

-- Retry the constraints for the given definition, return True if progress
-- was made
retryGuess : {auto c : Ref Ctxt Defs} ->
             {auto u : Ref UST UState} ->
             (hole : Name) ->
             Core Bool
retryGuess n
    = do defs <- get Ctxt
         case !(lookupDef n defs) of
              Nothing => pure False
              Just gdef =>
                case definition gdef of
                     Guess tm cs =>
                        do cs' <- traverse retry cs
                           let csAll = unionAll cs'
                           case constraints csAll of
                                [] => -- fine now, complete the definition
                                      do let gdef = record {
                                                      definition = PMDef [] (STerm tm)
                                                    } gdef
                                         updateDef n (const gdef)
                                         pure True
                                cs => -- still constraints, but might be new
                                      -- ones, so update the definition
                                      do let gdef = record {
                                                      definition = Guess tm cs
                                                    } gdef
                                         updateDef n (const gdef)
                                         pure False
                     _ => pure False

export
solveConstraints : {auto c : Ref Ctxt Defs} ->
                   {auto u : Ref UST UState} ->
                   Core ()
solveConstraints
    = do ust <- get UST
         progress <- traverse retryGuess (SortedSet.toList (guesses ust))
         when (anyTrue progress) $
               solveConstraints