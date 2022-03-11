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
import Data.Maybe

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
          UnifyMode ->
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
            UnifyMode ->
            Env Term vars ->
            List (AppInfo, tm vars) -> List (AppInfo, tm vars) ->
            Core UnifyResult
unifyArgs mode env [] [] = pure success
unifyArgs mode env ((ix,cx) :: cxs) ((iy,cy) :: cys)
    = do -- Do later arguments first, since they may depend on earlier
         -- arguments and use their solutions.
         cs <- unifyArgs mode env cxs cys
         res <- unify mode env cx cy
         pure (union res cs)
unifyArgs mode env _ _ = ufail ""

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
           UnifyMode ->
           Env Term vars -> NF vars -> NF vars -> Core UnifyResult
postpone mode env x y
    = do defs <- get Ctxt
         empty <- clearDefs defs

         xtm <- quote empty env x
         ytm <- quote empty env y
         c <- addConstraint (MkConstraint mode env xtm ytm)
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
              Core Bool
instantiate {newvars} env mname mdef locs tm
    = do let ty = type mdef -- assume all pi binders we need are there since
                            -- it was built from an environment, so no need
                            -- to normalise
         defs <- get Ctxt
         Just rhs <- mkDef locs INil tm ty
           | _ => pure False
         let newdef = record { definition = PMDef [] (STerm rhs) } mdef
         addDef mname newdef
         removeHole mname
         pure True
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
        updateIVarsB ivs (PVar s i t)
            = Just (PVar s i !(updateIVars ivs t))
        updateIVarsB ivs (PVTy s t)
            = Just (PVTy s !(updateIVars ivs t))
    updateIVars ivs (App info f a)
        = Just (App info !(updateIVars ivs f) !(updateIVars ivs a))
    updateIVars ivs Erased = Just Erased
    updateIVars ivs TType = Just TType
    updateIVars ivs (Quote ty a)  = Just (Quote !(updateIVars ivs ty) !(updateIVars ivs a))
    updateIVars ivs (TCode  a)  = Just (TCode  !(updateIVars ivs a))
    updateIVars ivs (Eval   a)  = Just (Eval   !(updateIVars ivs a))
    updateIVars ivs (Escape a)  = Just (Escape !(updateIVars ivs a))

    mkDef : {vs, newvars : _} ->
            List (Var newvars) ->
            IVars vs newvars -> Term newvars -> Term vs ->
            Core (Maybe (Term vs))
    mkDef (v :: vs) vars soln (Bind x (Pi s _ ty) sc)
       = do sc' <- mkDef vs (ICons (Just v) vars) soln sc
            pure $ Bind x (Lam s Explicit Erased) <$> sc'
    mkDef vs vars soln (Bind x b@(Let _ val ty) sc)
      = do mbsc' <- mkDef vs (ICons Nothing vars) soln sc
           flip traverseOpt mbsc' $ \sc' =>
             do let Just scs = shrinkTerm sc' (DropCons SubRefl)
                     | Nothing => pure $ Bind x b sc'
                pure scs
    mkDef [] vars soln ty
       = do let Just soln' = updateIVars vars soln
                  | Nothing => ufail ("Can't make solution for " ++ show mname)
            pure $ Just soln'
    mkDef _ _ _ ty = pure Nothing

getArgTypes : {vars : _} ->
              {auto c : Ref Ctxt Defs} ->
              Defs -> (fnType : NF vars) -> List (Closure vars) ->
              Core (Maybe (List (NF vars)))
getArgTypes defs (NBind n (Pi _ _ ty) sc) (a :: as)
  = do Just scTys <- getArgTypes defs !(sc defs a) as
         | Nothing => pure Nothing
       pure (Just (ty :: scTys))
getArgTypes _ _ [] = pure (Just [])
getArgTypes _ _ _ = pure Nothing

mutual

  headsConvert : {vars : _} ->
                 {auto c : Ref Ctxt Defs} ->
                 {auto u : Ref UST UState} ->
                 UnifyMode ->
                 Env Term vars ->
                 Maybe (List (NF vars)) -> Maybe (List (NF vars)) ->
                 Core Bool
  headsConvert mode env (Just vs) (Just ns)
    = case (reverse vs, reverse ns) of
        (v :: _, n :: _) =>
          do res <- unify mode env v n
             pure (isNil (constraints res))
        _ => pure False
  headsConvert mode env _ _ = pure True

  unifyIfEq : {auto c : Ref Ctxt Defs} ->
              {auto u : Ref UST UState} ->
              {vars : _} ->
              Bool -> UnifyMode -> Env Term vars -> NF vars -> NF vars ->
              Core UnifyResult
  unifyIfEq post mode env x y
        = do defs <- get Ctxt
             if !(convert defs env x y)
                then pure success
                else if post
                        then postpone mode env x y
                        else convertError env x y


  unifyInvertible : {auto c : Ref Ctxt Defs} ->
                    {auto u : Ref UST UState} ->
                    {vars : _} ->
                    UnifyMode -> Env Term vars ->
                    (metaname : Name) ->
                    (margs : List (AppInfo, Closure vars)) ->
                    (margs' : List (AppInfo, Closure vars)) ->
                    Maybe (Term []) ->
                    (List (AppInfo, Closure vars) -> NF vars) ->
                    List (AppInfo, Closure vars) ->
                    Core UnifyResult
  unifyInvertible mode env mname margs margs' nty con args'
    = do defs <- get Ctxt
         Just vty <- lookupDefType mname defs
           | Nothing => ufail $ "No such metavariable" ++ show mname
         vargTys <- getArgTypes defs !(nf defs env (embed vty)) (map snd $ margs ++ margs')
         nargTys <- maybe (pure Nothing)
                           (\ty => getArgTypes defs !(nf defs env (embed ty)) $ map snd args')
                           nty
         if !(headsConvert mode env vargTys nargTys)
            then
              -- Unify rightmost arguments with the goal of turning the
              -- hole application into a pattern form
              case (reverse margs', reverse args') of
                ((aih, h) :: hargs, (aif,f) :: fargs) =>
                  tryUnify
                    ( do ures <- unify mode env h f
                         uargs <- unify mode env
                                    (NApp (NMeta mname $ map snd margs) (reverse hargs))
                                    (con (reverse fargs))
                         pure $ union ures uargs
                    )
                    (postpone mode env (NApp (NMeta mname $ map snd margs) margs') (con args'))
                _ => postpone mode env (NApp (NMeta mname $ map snd margs) margs') (con args')
            else
              postpone mode env (NApp (NMeta mname $ map snd margs) margs') (con args')

  -- TODO Got to be careful about when we assume our hole is invertible
  -- Should probably tag this in the global def of the hole
  unifyHoleApp : {auto c : Ref Ctxt Defs} ->
                 {auto u : Ref UST UState} ->
                 {vars : _} ->
                 UnifyMode -> Env Term vars ->
                 (metaname : Name) ->
                 (margs : List (AppInfo, Closure vars)) ->
                 (margs' : List (AppInfo, Closure vars)) ->
                 NF vars ->
                 Core UnifyResult
  unifyHoleApp mode env mname margs margs' (NTCon n i t a args')
      = do defs <- get Ctxt
           mty <- lookupDefType n defs
           unifyInvertible mode env mname margs margs' mty (NTCon n i t a) args'
  unifyHoleApp mode env mname margs margs' (NDCon n t a args')
      = do defs <- get Ctxt
           mty <- lookupDefType n defs
           unifyInvertible mode env mname margs margs' mty (NDCon n t a) args'
  unifyHoleApp mode env mname margs margs' (NApp (NLocal idx p) args')
      = unifyInvertible mode env mname margs margs' Nothing
                        (NApp (NLocal idx p)) args'
  unifyHoleApp mode env mname margs margs' tm@(NApp (NMeta n margs2) args2')
      = do defs <- get Ctxt
           Just mdef <- lookupDef n defs
                | Nothing => throw $ GenericMsg $ "Undefined name: " ++ show n
           -- TODO let inv = isPatName n || invertible mdef
           let inv = True
           if inv
              then unifyInvertible mode env mname margs margs' Nothing
                                   (NApp (NMeta n margs2)) args2'
              else postpone mode env
                             (NApp (NMeta mname $ map snd margs) margs') tm
    --where
    --  isPatName : Name -> Bool -- TODO could probably look this up in the env
    --  isPatName (PV _ _) = True
    --  isPatName _ = False

  unifyHoleApp mode env mname margs margs' tm
      = postpone mode env
                 (NApp (NMeta mname $ map snd margs) margs') tm

  solveHole : {auto c : Ref Ctxt Defs} ->
              {auto u : Ref UST UState} ->
              {newvars, vars : _} ->
              UnifyMode -> Env Term vars ->
              (metaname : Name) ->
              (margs : List (AppInfo, Closure vars)) ->
              (margs' : List (AppInfo, Closure vars)) ->
              List (Var newvars) ->
              SubVars newvars vars ->
              (solfull : Term vars) -> -- Original solution
              (soln : Term newvars) -> -- Solution with shrunk environment
              (solnf : NF vars) ->
              Core (Maybe UnifyResult)
  solveHole mode env mname margs margs' locs submv solfull stm solnf
      = do defs <- get Ctxt
           ust <- get UST
           empty <- clearDefs defs
           if solutionHeadSame solnf -- TODO consider inNoSolve?
              then pure $ Just success
              else do Just gdef <- lookupDef mname defs
                        | _ => throw (GenericMsg $ "We lost track of a hole!")
                      progress <- instantiate env mname gdef locs stm
                      pure $ toMaybe progress solvedHole
    where
    solutionHeadSame : NF vars -> Bool
    solutionHeadSame (NApp (NMeta shead _) _) = shead == mname
    solutionHeadSame _ = False

  unifyHole : {vars : _} ->
              {auto c : Ref Ctxt Defs} ->
              {auto u : Ref UST UState} ->
              UnifyMode ->
              Env Term vars ->
              (metaname : Name) -> List (AppInfo, Closure vars) ->
                                   List (AppInfo, Closure vars) ->
              (soln : NF vars) ->
              Core UnifyResult
  unifyHole mode env mname margs margs' tmnf
      = do
           let args = if isNil margs' then margs else margs ++ margs'
           case !(patternEnv env (map snd args)) of
                Nothing =>
                    -- not in pattern form so postpone
                    do --coreLift $ putStrLn $ "Hole not in pat form"
                       -- TODO if it's an invertible hole, unifyHoleApp
                       --coreLift $ putStrLn $ "GOTCHA " ++ show mname
                       unifyHoleApp mode env mname margs margs' tmnf
                       --unifyIfEq True mode env (NApp (NMeta mname $ map snd margs) margs') tmnf
                Just (newvars ** (locs, submv)) =>
                    -- In pattern form, using the 'submv' fragment of the
                    -- environment
                    do -- TODO (Exercise): We need to do an occurs check here
                       -- Check the the result is well scoped in the
                       -- metavariable's environment
                       defs <- get Ctxt
                       empty <- clearDefs defs
                       tm <- quote empty env tmnf

                       let solveOrElsePostpone : Term newvars -> Core UnifyResult
                           solveOrElsePostpone stm = do
                             mbResult <- solveHole mode env mname
                                                   margs margs' locs submv
                                                   tm stm tmnf
                             flip fromMaybe (pure <$> mbResult) $
                               postpone mode env
                                       (NApp (NMeta mname $ map snd margs) $ margs') tmnf

                       case shrinkTerm tm submv of
                            Just stm => solveOrElsePostpone stm
                            Nothing  =>
                              do tm' <- quote defs env tmnf
                                 case shrinkTerm tm' submv of
                                   Nothing => postpone mode env (NApp (NMeta mname $ map snd margs) margs') tmnf
                                   Just stm => solveOrElsePostpone stm

  unifyApp : {vars : _} ->
             {auto c : Ref Ctxt Defs} ->
             {auto u : Ref UST UState} ->
             UnifyMode ->
             Env Term vars ->
             NHead vars -> List (AppInfo, Closure vars) ->
             NF vars ->
             Core UnifyResult
  unifyApp mode env (NMeta n margs) fargs tmnf
      = unifyHole mode env n (map (\a=>(AExplicit,a)) margs) fargs tmnf
  unifyApp mode env hd args (NApp (NMeta n margs) margs')
      = unifyHole mode env n (map (\a=>(AExplicit,a)) margs) margs' (NApp hd args)
  unifyApp mode env (NRef nt n) args tm
      = unifyIfEq True mode env (NApp (NRef nt n) args) tm
  unifyApp mode env (NLocal x xp) [] (NApp (NLocal y yp) [])
      = do gam <- get Ctxt
           if x == y
              then pure success
              else postpone mode
                   env (NApp (NLocal x xp) [])
                       (NApp (NLocal y yp) [])
  unifyApp mode env  (NLocal x xp) args y@(NBind _ _ _)
      = convertError env (NApp  (NLocal x xp) args) y
  unifyApp mode env  (NLocal x xp) args y@(NDCon _ _ _ _)
      = convertError env (NApp  (NLocal x xp) args) y
  unifyApp mode env  (NLocal x xp) args y@(NTCon _ _ _ _ _)
      = convertError env (NApp  (NLocal x xp) args) y
  unifyApp mode env  (NLocal x xp) args y@(NType)
      = convertError env (NApp  (NLocal x xp) args) y
  unifyApp mode env f args tm
      = do defs <- get Ctxt
           if !(convert defs env (NApp f args) tm)
              then pure success
              else postpone mode env (NApp f args) tm

  unifyBothBinders: {auto c : Ref Ctxt Defs} ->
                    {auto u : Ref UST UState} ->
                    {vars : _} ->
                    UnifyMode ->
                    Env Term vars ->
                    Name -> Binder (NF vars) ->
                    (Defs -> Closure vars -> Core (NF vars)) ->
                    Name -> Binder (NF vars) ->
                   (Defs -> Closure vars -> Core (NF vars)) ->
                    Core UnifyResult
  unifyBothBinders mode env x (Pi sx ix tx) scx y (Pi sy iy ty) scy
    = do defs <- get Ctxt
         -- Don't unify if stages are incompatible
         if sx > sy
           then convertError env (NBind x (Pi sx ix tx) scx) (NBind y (Pi sy iy ty) scy)
           else
             do empty <- clearDefs defs
                -- Unify types of bound vars
                tx' <- quote empty env tx
                ty' <- quote empty env ty
                ct  <- unify mode env tx ty
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
                           unify mode env'
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
                           cs' <- unify mode env'
                                    (refsToLocals (Add x xn None) tmx)
                                    (refsToLocals (Add x xn None) tmy)
                           pure (union ct cs')
  unifyBothBinders mode env x (Lam sx ix tx) scx y (Lam sy iy ty) scy
                   = do defs <- get Ctxt
                        -- Check stages
                        if sx > sy
                          then convertError env
                                 (NBind x (Lam sx ix tx) scx)
                                 (NBind y (Lam sy iy ty) scy)
                          else
                            do empty <- clearDefs defs
                               -- Unify types of our bound vars
                               ct <- unify mode env tx ty
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
                               cs' <- unify mode env' (refsToLocals (Add x xn None) tmx)
                                                      (refsToLocals (Add x xn None) tmy)
                               pure (union ct cs')
  unifyBothBinders mode env x bx scx y by scy = convertError env (NBind x bx scx) (NBind y by scy)

  unifyBothApps : {auto c : Ref Ctxt Defs} ->
                  {auto u : Ref UST UState} ->
                  {vars : _} ->
                  UnifyMode ->
                  Env Term vars ->
                  NHead vars -> List (AppInfo, Closure vars) ->
                  NHead vars -> List (AppInfo, Closure vars) ->
                  Core UnifyResult
  unifyBothApps mode env (NLocal x xp) [] (NLocal y yp) []
    = if x == y
         then pure success
         else convertError env (NApp (NLocal x xp) [])
                               (NApp (NLocal y yp) [])
  unifyBothApps InTerm env (NLocal x xp) xs (NLocal y yp) ys
    = if x == y
         then unifyArgs InTerm env xs ys
         else postpone InTerm env
                       (NApp (NLocal x xp) xs)
                       (NApp (NLocal y yp) ys)
  unifyBothApps mode env (NLocal x xp) xs (NLocal y yp) ys
    = unifyIfEq True mode env (NApp (NLocal x xp) xs) (NApp (NLocal y yp) ys)
  unifyBothApps mode env (NMeta xn xs) xs' (NMeta yn ys) ys'
    = if xn == yn -- TODO we also need x to be invertible!
         then unifyArgs mode env (map (\a=>(AExplicit,a)) xs ++ xs')
                                 (map (\a=>(AExplicit,a)) ys ++ ys')
         else do xlocs <- localsIn xs
                 ylocs <- localsIn ys
                 -- Solve the one with the bigger context, and if they're
                 -- equal, the one that's applied to fewest things (because
                 -- then they arguments get substituted in)
                 let xbigger = xlocs > ylocs
                                 || (xlocs == ylocs && length xs' <= length ys')
                 if (xbigger) -- TODO x shouldn't be a pattern var
                    then unifyApp mode env (NMeta xn xs) xs'
                                           (NApp (NMeta yn ys) ys')
                    else unifyApp mode env (NMeta yn ys) ys'
                                           (NApp (NMeta xn xs) xs')
    where
      localsIn : List (Closure vars) -> Core Nat
      localsIn [] = pure 0
      localsIn (c :: cs)
          = do defs <- get Ctxt
               case !(evalClosure defs c) of
                 NApp (NLocal _ _) _ => pure $ S !(localsIn cs)
                 _ => localsIn cs
  unifyBothApps mode env (NMeta xn xs) xs' yh ys
    = unifyApp mode env (NMeta xn xs) xs' (NApp yh ys)
  unifyBothApps mode env xh xs (NMeta yn ys) ys'
    = unifyApp mode env (NMeta yn ys) ys' (NApp xh xs)
  unifyBothApps mode env fx@(NRef xt hdx) xargs fy@(NRef yt hdy) yargs
    = if hdx == hdy
         then unifyArgs mode env xargs yargs
         else unifyApp  mode env fx xargs (NApp fy yargs)
  unifyBothApps mode env xh xs yh ys = unifyApp mode env xh xs (NApp yh ys)

  export
  unifyNoEta :
               {auto c : Ref Ctxt Defs} ->
               {auto u : Ref UST UState} ->
               {vars :_} ->
               UnifyMode -> Env Term vars ->
               NF vars -> NF vars -> Core UnifyResult
  unifyNoEta mode env (NDCon x tagx ax xs) (NDCon y tagy ay ys)
    = do gam <- get Ctxt
         if tagx == tagy
           then unifyArgs mode env xs ys
           else convertError env (NDCon x tagx ax xs) (NDCon y tagy ay ys)
  unifyNoEta mode env (NTCon x ix tagx ax xs) (NTCon y iy tagy ay ys)
   = do gam <- get Ctxt
        if x == y
          then unifyArgs mode env xs ys
          else convertError env (NTCon x ix tagx ax xs) (NTCon y iy tagy ay ys)
  unifyNoEta mode env (NCode   x) (NCode   y) = unify mode env x y
  unifyNoEta mode env (NEscape x) (NEscape y) = unify mode env x y
  unifyNoEta mode env (NQuote ty x) (NQuote ty' y) = unifyArgs mode env [(AExplicit, ty) ,(AExplicit, x)]
                                                                        [(AExplicit, ty'),(AExplicit, y)]
  unifyNoEta mode env x@(NApp fx@(NMeta _ _) axs)
                      y@(NApp fy@(NMeta _ _) ays)
    = do defs <- get Ctxt
         if !(convert defs env x y)
           then pure success
           else unifyBothApps mode env fx axs fy ays
  unifyNoEta mode env (NApp fx axs) (NApp fy ays)
    = unifyBothApps mode env fx axs fy ays
  unifyNoEta mode env (NApp hd args) y
    = unifyApp mode env hd args y
  unifyNoEta mode env y (NApp hd args)
    = unifyApp mode env hd args y
  unifyNoEta mode env x y
  = do defs <- get Ctxt
       empty <- clearDefs defs
       --log "unify.noeta" 10 $ "Nothing else worked, unifyIfEq"
       unifyIfEq True mode env x y

  isHoleApp : NF vars -> Bool
  isHoleApp (NApp (NMeta _ _) _) = True
  isHoleApp _ = False

  -- This gives the minimal rules for unification of constructor forms,
  -- solving metavariables in constructor arguments. There's more to do in
  -- general!
  export
  Unify NF where
    -- If we have two pi binders, check the arguments and scope
    unify mode env (NBind x b sc) (NBind x' b' sc') = unifyBothBinders mode env x b sc x' b' sc'
    unify mode env tmx@(NBind x (Lam sx ix tx) scx) tmy
        = do defs <- get Ctxt
             if isHoleApp tmy
                then if not !(convert defs env tmx tmy)
                        then unifyNoEta mode env tmx tmy
                        else pure success
                else do empty <- clearDefs defs
                        domty <- quote empty env tx
                        etay <- nf defs env
                                 $ Bind x (Lam sx Explicit domty)
                                 $ App AExplicit (weaken !(quote empty env tmy))
                                                 (Local 0 First)
                        unify mode env tmx etay
    unify mode env tmy tmx@(NBind x (Lam sx ix tx) scx) 
       = do defs <- get Ctxt
            if isHoleApp tmy
               then if not !(convert defs env tmx tmy)
                       then unifyNoEta mode env tmx tmy
                       else pure success
               else do empty <- clearDefs defs
                       domty <- quote empty env tx
                       etay <- nf defs env
                                $ Bind x (Lam sx Explicit domty)
                                $ App AExplicit (weaken !(quote empty env tmy))
                                                (Local 0 First)
                       unify mode env tmx etay
    -- Otherwise, unification succeeds if both sides are convertible
    unify mode env x y
        = unifyNoEta mode env x y

  export
  Unify Term where
    unify mode env x y
        = do defs <- get Ctxt
             xnf <- nf defs env x
             ynf <- nf defs env y
             unify mode env xnf ynf

  export
  Unify Closure where
    unify mode env x y
        = do defs <- get Ctxt
             xnf <- evalClosure defs x
             ynf <- evalClosure defs y
             unify mode env xnf ynf

-- Retry the given constraint, by constraint id
retry : {auto c : Ref Ctxt Defs} ->
        {auto u : Ref UST UState} ->
        UnifyMode -> Int -> Core UnifyResult
retry mode c
    = do ust <- get UST
         case lookup c (constraints ust) of
              Nothing => pure success
              Just Resolved => pure success
              Just (MkConstraint _ env x y) =>
                 do cs <- unify mode env x y
                    -- If the constraint is solved now, with no new constraints,
                    -- delete the constraint, otherwise come back to it later.
                    case (constraints cs) of
                         [] => do deleteConstraint c
                                  pure cs
                         _ => pure cs
              Just (MkSeqConstraint env xs ys) =>
                 do cs <- unifyArgs mode env (map (\x=>(AExplicit,x)) xs)
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
             UnifyMode ->
             (hole : Name) ->
             Core Bool
retryGuess mode n
    = do defs <- get Ctxt
         case !(lookupDef n defs) of
              Nothing => pure False
              Just gdef =>
                case definition gdef of
                     Guess tm cs =>
                        do cs' <- traverse (retry mode) cs
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
                   UnifyMode -> Core ()
solveConstraints mode
    = do ust <- get UST
         progress <- traverse (retryGuess mode) (SortedSet.toList (guesses ust))
         when (anyTrue progress) $
               solveConstraints mode

export
checkDots : {auto u : Ref UST UState} ->
            {auto c : Ref Ctxt Defs} ->
            Core ()
checkDots
  = do ust <- get UST
       traverse_ checkConstraint (reverse (dotConstraints ust))
       ust <- get UST
       put UST (record { dotConstraints = [] } ust)
  where
    getHoleName : Term [] -> Core (Maybe Name)
    getHoleName tm
      = do defs <- get Ctxt
           NApp (NMeta n' args) _ <- nf defs [] tm
             | _ => pure Nothing
           pure (Just n')

    undefinedName : Name -> Error
    undefinedName n = GenericMsg $ "Undefined name: " ++ show n

    checkConstraint : (Name, Constraint) -> Core ()
    checkConstraint (n, MkConstraint mode env xold yold)
      = do defs <- get Ctxt
           x <- nf defs env xold
           y <- nf defs env yold

           -- A dot is okay if the constraint is solvable *without solving
           -- any additional holes*
           ust <- get UST
           handleUnify

             (do
                 oldholen <- getHoleName (Meta n [])

                 -- Check that what was given (x) matches what was
                 -- solved by unification (y).
                 -- In 'InMatch' mode, only metavariables in 'x' can
                 -- be solved, so everything in the dotted metavariable
                 -- must be complete.
                 cs <- unify InMatch env x y
                 defs <- get Ctxt
                 dotSolved <-
                   maybe (pure False)
                         (\n => do Just gdef <- lookupDef n defs
                                     | Nothing => throw $ undefinedName n
                                   pure $ case definition gdef of
                                            Hole => False
                                            _    => True
                         )
                         oldholen
                 -- TODO check "namesSolved" in cs?

                 when (not (isNil (constraints cs)) || dotSolved)
                      (throw (InternalError "Dot pattern match fail"))
             )
             (\err => case err of
                           InternalError _ =>
                             do defs <- get Ctxt
                                Just dty <- lookupDefType n defs
                                  | Nothing => throw $ undefinedName n
                                put UST (record { dotConstraints = [] } ust)
                                empty <- clearDefs defs
                                throw (BadDotPattern env
                                         !(quote empty env x)
                                         !(quote empty env y))
                           _ => do put UST (record { dotConstraints = [] } ust)
                                   throw err
             )

    checkConstraint _ = pure ()
