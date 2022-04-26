module TTImp.ProcessData

import Core.Context
import Core.Env
import Core.Normalise
import Core.Extraction
import Core.TT
import Core.CaseTree
import Core.UnifyState
import Core.Unify

import TTImp.Elab.Check
import TTImp.TTImp

import Data.Maybe
import Data.List
import Data.SortedMap
import Data.SortedSet

import Utils.Bits

appendInnerAssoc : (left: List a) -> (centre : a) -> (right : List a) -> (left ++ [centre]) ++ right = left ++ (centre :: right)
appendInnerAssoc [] centre right = Refl
appendInnerAssoc (x :: xs) centre right = let h = appendInnerAssoc xs centre right in cong (x ::) h

-- Get the return type of a type definition
getRetTy : {vars :_} -> Term vars -> (bs ** Term (bs ++ vars))
getRetTy (Bind n (Pi _ _ _) sc)
  = let (bs ** rec) = getRetTy sc
        rec' : Term ((bs ++ [n]) ++ vars)
             = rewrite (appendInnerAssoc bs n vars) in rec
    in (bs ++ [n] ** rec')
getRetTy tm = ([] ** tm)

-- Get the return type of a type definition
getRetTyWithEnv : {vars :_} -> Env Term vars -> Term vars -> (bs ** (Env Term (bs ++ vars), Term (bs ++ vars)))
getRetTyWithEnv env (Bind n b@(Pi _ _ _) sc)
  = let (bs ** (env',tm')) = getRetTyWithEnv (b :: env) sc
        rec' : (Env Term ((bs ++ [n]) ++ vars), Term ((bs ++ [n]) ++ vars))
             = rewrite (appendInnerAssoc bs n vars) in (env',tm')
    in (bs ++ [n] ** rec')
getRetTyWithEnv env tm = ([] ** (env,tm))

-- Try to retrieve the type con name from its type
export
getTyConName : {vars :_} -> Term vars -> Maybe Name
getTyConName (TCode ty) = getTyConName ty
getTyConName (App _ f _) = getTyConName f
getTyConName (Ref (TyCon _ _ _) n) = Just n
getTyConName tm = Nothing

-- Try to retrieve the data con name from a term
getDConName : {vars :_} -> Term vars -> Maybe Name
getDConName (App _ f _) = getDConName f
getDConName (Ref (DataCon _ _) n) = Just n
getDConName tm = Nothing

export
typeForDataCon : {auto c : Ref Ctxt Defs} ->
                 {auto u : Ref UST UState} ->
                 Name -> (argTys : List (Term [])) -> Core (Term [])
typeForDataCon n argTys
  = do defs <- get Ctxt
       Just conTy <- lookupDefType n defs
         | Nothing => throw $ InternalError $ "Couldn't find data constructor in context: " ++ show n
       expConTy <- impsToMetas [] conTy
       retTy <- unifyArgTys [] expConTy argTys
       let (tycon, retArgs) = getFnInfoArgs retTy
       retArgs' <- traverse (\(i,a)=>pure (i, !(substSolvedMetaArgs a))) $
                            filter ((==AExplicit) . fst) retArgs
       pure $ apply tycon retArgs'
  where
  impsToMetas : {vars : _} -> Env Term vars -> Term vars -> Core (Term vars)
  impsToMetas env (Bind x (Pi _ Implicit ty) sc)
    = do nmeta <- genName "_dconarg"
         meta <- newMeta env nmeta ty Hole
         impsToMetas env $ subst meta sc
  impsToMetas env (Bind x b@(Pi s Explicit ty) sc)
    = pure $ Bind x b !(impsToMetas (b::env) sc)
  impsToMetas _ tm = pure tm
  -- TODO have a better look at erasure of implicits here

  unifyArgTys : {vars : _} -> Env Term vars -> Term vars -> List (Term []) -> Core (Term vars)
  unifyArgTys env fty [] = do solveConstraints InTerm
                              pure fty
  unifyArgTys env (Bind _ b sc) (aty::atys)
    = do res <- unify InTerm env (binderType b) (rewrite sym (appendNilRightNeutral vars)
                                                  in weakenNs vars aty)
         unifyArgTys env (subst Erased sc) atys
  unifyArgTys _ fty args = throw $ InternalError $ "Mismatched number of args for constructor unification: "
                                     ++ show fty ++ " and " ++ show args

  substSolvedMetaArgs : (ty : Term []) -> Core (Term [])
  substSolvedMetaArgs (Meta n _)
    = do -- check if this meta has been solved
         defs <- get Ctxt
         Just (MkGlobalDef _ (PMDef [] _ (STerm tm) _) _) <- lookupDef n defs
           | _ => -- Wasn't solved
                  pure Erased
         substSolvedMetaArgs tm
  substSolvedMetaArgs ty
    = do let (tycon, retArgs) = getFnInfoArgs ty
         retArgs' <- traverse (\(i,a)=>pure (i, !(substSolvedMetaArgs a))) $ filter ((==AExplicit) . fst) retArgs
         -- Simplify any applications with an erased arg
         if (any (\(_,a)=>a==Erased) retArgs')
            then pure Erased
            else pure $ apply tycon retArgs'

-- Get a list of the data constructors which could have produced a given type,
-- along with their specialised constructor types after unification with our
-- given type
export
dataConsForType : {auto c : Ref Ctxt Defs} ->
                  {auto u : Ref UST UState} ->
                  {vars : _} ->
                  Env Term vars -> (ty : Term vars) -> Core (List (Name, Term []))
dataConsForType env (Bind x b sc) = dataConsForType (b :: env) sc
dataConsForType env ty
  = do let Just ntcon = getTyConName ty
           | Nothing => throw $ GenericMsg $ "Couldn't determine the type constructor name for type: " ++ show ty
       defs <- get Ctxt
       Just (MkGlobalDef _ (TCon _ _ _ dcons) _) <- lookupDef ntcon defs
         | _ => throw $ InternalError $ "Type constructor name wasn't found in context: " ++ show ntcon
       possibleDCons <- traverse checkConRetTy dcons
       pure $ mapMaybe id possibleDCons
  where

  wrapMetaEnv : {vars' : _} -> Env Term vars' -> (ty : Term vars') -> Core (Term [])
  wrapMetaEnv [] ty = pure ty
  wrapMetaEnv {vars' = n::vs} (b::env) ty
    = do nmeta <- genName "_dconarg"
         meta <- newMeta env nmeta (binderType b) Hole
         wrapMetaEnv env (subst meta ty)

  wrapMetaArgs : {vars' : _} -> Env Term vars' -> (ty : Term vars') -> Core (Term vars', List Name)
  wrapMetaArgs env (Bind n b@(Pi _ i ty) sc)
    = do nmeta <- genName "_dconarg"
         meta <- newMeta env nmeta ty Hole
         (tm, ns) <- wrapMetaArgs env (subst meta sc)
         pure (tm, nmeta :: ns)
  wrapMetaArgs env ty = pure (ty, [])

  substSolvedMetaArgs : {vars' : _} -> (ty : Term vars') -> List Name -> Core (Term vars')
  substSolvedMetaArgs (Bind n b@(Pi s i ty) sc) (m :: metas)
    = do -- check if this meta has been solved
         defs <- get Ctxt
         Just (MkGlobalDef _ (PMDef [] _ (STerm tm) _) _) <- lookupDef m defs -- TODO Should I be assuming that args is empty?! Works for most of my examples so far...
           | _ => -- Wasn't solved, so continue
                  do sc' <- substSolvedMetaArgs sc metas
                     pure $ Bind n b sc'
         let weakTm = rewrite sym (appendNilRightNeutral vars') in weakenNs vars' tm
         let rest = subst weakTm sc
         pure $ Bind n b !(substSolvedMetaArgs (weaken rest) metas)
  substSolvedMetaArgs ty metas = pure ty

  checkConRetTy : Name -> Core (Maybe (Name, Term []))
  checkConRetTy dcon = do defs <- get Ctxt
                          oldUST <- get UST
                          oldDefs <- get Ctxt
                          -- Lookup the data constructor type
                          Just (MkGlobalDef dconty (DCon tag arity) _) <- lookupDef dcon defs
                            | _ => throw $ InternalError $ "Data constructor name wasn't found in context: " ++ show dcon

                          -- Replace all the args with new metavars
                          tcty <- wrapMetaEnv env ty
                          (ty',tyArgNames) <- wrapMetaArgs [] dconty

                          -- Try to unify with our expected type.
                          -- Constraints are allowable -- better to include
                          -- possibly wrong constructors than ignore possibly correct ones.
                          res <- handleUnify (do res <- unify InTerm [] tcty ty'
                                                 solveConstraints InTerm
                                                 defs <- get Ctxt
                                                 dconty' <- substSolvedMetaArgs dconty tyArgNames
                                                 pure $ Just (dcon, dconty'))
                                             (\err => pure Nothing)

                          -- Undo damage to UST and CTXT
                          put UST oldUST
                          put Ctxt defs
                          pure res

clog2 : Nat -> Nat -- TODO should really define this on nats properly so we can prove things about it!
clog2 x = cast . ceiling $ (log $ cast x) / (log 2)

-- A type's tag width is ceil . log2 of the number of unique constructors.
export
tyTagWidth : {auto c : Ref Ctxt Defs} ->
             {auto u : Ref UST UState} ->
             {vars : _} ->
             Env Term vars -> (ty : Term vars) -> Core Nat
tyTagWidth env ty
  = do dcons <- dataConsForType env ty
       case length dcons of
         0 => throw $ InternalError $ "Attempted to find tag width for uninhabited type: " ++ show ty
         1 => pure 0
         n => pure $ clog2 n

-- A type's field width is the maximum width for any valid constructor using the
-- sum of each explicit argument's tag and field width
export
tyFieldWidth : {auto c : Ref Ctxt Defs} ->
             {auto u : Ref UST UState} ->
             {vars : _} ->
             Env Term vars -> (ty : Term vars) -> Core Nat
tyFieldWidth env ty
  = do dcons <- dataConsForType env ty
       dconsWidth <- traverse dataConFieldWidth dcons
       pure $ foldr max 0 dconsWidth
  where

  argsFieldWidth : {vars' : _} -> Nat -> Env Term vars' -> (ty : Term vars') -> Core Nat
  -- Ignore implicit args and continue
  argsFieldWidth w env (Bind n b@(Pi s Implicit ty) sc) = argsFieldWidth w (b::env) sc
  -- Count explicit args and continue
  argsFieldWidth w env (Bind n b@(Pi s Explicit ty) sc)
    = do hereTag <- tyTagWidth env ty
         hereField <- tyFieldWidth env ty
         rest <- argsFieldWidth w (b :: env) sc
         pure $ hereTag + hereField + rest
  -- We've reached the end of the telescope
  argsFieldWidth w env ty = pure w

  dataConFieldWidth : (Name, Term[]) -> Core Nat
  dataConFieldWidth (dcon, dconty)
    = argsFieldWidth 0 [] dconty

export
getTagPos : {auto c : Ref Ctxt Defs} ->
              {auto u : Ref UST UState} ->
              {vars : _} ->
              Env Term vars -> (ty : Term vars) -> Core (Nat, Nat)
getTagPos env ty
  = do dcons <- dataConsForType env ty
       fieldsWidth <- tyFieldWidth env ty
       tagWidth <- tyTagWidth env ty
       pure ((plus fieldsWidth tagWidth) `minus` 1, fieldsWidth)

export
getConsPadding : {auto c : Ref Ctxt Defs} ->
                {auto u : Ref UST UState} ->
                {vars : _} ->
                Env Term vars -> (ty : Term vars) -> Name -> Core Nat
getConsPadding env ty conn
  = do dcons <- dataConsForType env ty
       fieldsWidth <- tyFieldWidth env ty
       let [(_,dconty)] = filter (\(dn,dty) => dn == conn) dcons
             | _ => throw $ InternalError $ "Couldn't find expected data con name in list of valid constructors: " ++ show conn ++ " in " ++ show dcons
       let weakDconTy = rewrite sym (appendNilRightNeutral vars) in weakenNs vars dconty
       thisWidth <- decomposeArgs env weakDconTy
       pure $ fieldsWidth `minus` thisWidth
  where
    decomposeArgs : {vars' : _} -> Env Term vars' -> (ty : Term vars') -> Core Nat
    decomposeArgs env (Bind n b@(Pi _ Implicit _) sc)
      = decomposeArgs (b :: env) sc
    decomposeArgs env (Bind n b@(Pi _ Explicit ty) sc)
      = do fwidth <- tyFieldWidth env ty
           twidth <- tyTagWidth env ty
           let width = fwidth  `plus` twidth
           pure $ plus width !(decomposeArgs (b::env) sc)
    decomposeArgs env ty = pure 0

export
getFieldPos : {auto c : Ref Ctxt Defs} ->
              {auto u : Ref UST UState} ->
              {vars : _} ->
              Env Term vars -> (ty : Term vars) -> Name -> Nat -> Core (Maybe (Nat, Nat))
getFieldPos env ty conn field
  = do dcons <- dataConsForType env ty
       fieldsWidth <- tyFieldWidth env ty
       let [(_,dconty)] = filter (\(dn,dty) => dn == conn) dcons
             | _ => throw $ InternalError $ "Couldn't find expected data con name in list of valid constructors: " ++ show conn ++ " in " ++ show dcons
       let weakDconTy = rewrite sym (appendNilRightNeutral vars) in weakenNs vars dconty
       decomposeArgs field (fieldsWidth `minus` 1) env weakDconTy
  where
    decomposeArgs : {vars' : _} -> Nat -> Nat -> Env Term vars' -> (ty : Term vars') -> Core (Maybe (Nat, Nat))
    decomposeArgs field i env (Bind n b@(Pi _ Implicit _) sc)
      = decomposeArgs field i (b :: env) sc
    decomposeArgs Z i env (Bind n b@(Pi _ Explicit ty) sc)
      = do fwidth <- tyFieldWidth env ty
           twidth <- tyTagWidth env ty
           let width = fwidth `plus` twidth
           case width of
             Z => pure Nothing
             _ => pure $ Just (i, i `minus` (width `minus` 1))
    decomposeArgs (S field) i env (Bind n b@(Pi _ Explicit ty) sc)
      = do fwidth <- tyFieldWidth env ty
           twidth <- tyTagWidth env ty
           let width = fwidth `plus` twidth
           decomposeArgs field (i `minus` width) (b::env) sc
    decomposeArgs field i env ty = do throw $ InternalError $ "Failed to find field " ++ show field ++ " into constructor's type: " ++ show ty

export
getFieldType : {auto c : Ref Ctxt Defs} ->
               {auto u : Ref UST UState} ->
               {vars : _} ->
               Env Term vars -> (ty : Term vars) -> Name -> Nat -> Core (Term [])
getFieldType env ty conn field
  = do dcons <- dataConsForType env ty
       let [(_,dconty)] = filter (\(dn,dty) => dn == conn) dcons
             | _ => throw $ InternalError $ "Couldn't find expected data con name in list of valid constructors: " ++ show conn ++ " in " ++ show dcons
       decomposeArgs field dconty
  where
    decomposeArgs : Nat -> (ty : Term []) -> Core (Term [])
    decomposeArgs field (Bind n b@(Pi _ Implicit _) sc)
      = decomposeArgs field $ subst Erased sc
    decomposeArgs Z (Bind n b@(Pi _ Explicit ty) sc)
      = pure ty
    decomposeArgs (S field) (Bind n b@(Pi _ Explicit ty) sc)
      = decomposeArgs field $ subst Erased sc
    decomposeArgs field ty = do throw $ InternalError $ "Failed to find field " ++ show field ++ " into constructor's type: " ++ show ty


-- Equal for the purposes of size change means, ignoring as patterns, all
-- non-metavariable positions are equal
scEq : Term vars -> Term vars -> Bool
scEq (Local idx _) (Local idx' _) = idx == idx'
scEq (Ref _ n) (Ref _ n') = n == n'
scEq (Meta i args) _ = True
scEq _ (Meta i args) = True
scEq (Bind _ b sc) (Bind _ b' sc') = False -- not checkable
scEq (App _ f a) (App _ f' a') = scEq f f' && scEq a a'
scEq (Erased) (Erased) = True
scEq (TType) (TType) = True
scEq (TCode t) (TCode t') = scEq t t'
scEq (Escape t) (Escape t') = scEq t t'
scEq (Eval t) (Eval t') = scEq t t'
scEq (Quote ty t) (Quote ty' t') = scEq t t' && scEq ty ty'
scEq _ _ = False

mutual
  -- Return whether first argument is structurally smaller than the second.
  smaller : Bool -> -- Have we gone under a constructor yet?
            Defs ->
            Maybe (Term vars) -> -- Asserted bigger thing
            Term vars -> -- Term we're checking
            Term vars -> -- Argument it might be smaller than
            Bool
  smaller inc defs big _ Erased = False -- Never smaller than an erased thing!
  smaller True defs big s t
      = s == t || smallerArg True defs big s t
  smaller inc defs big s t = smallerArg inc defs big s t

  assertedSmaller : Maybe (Term vars) -> Term vars -> Bool
  assertedSmaller (Just b) a = scEq b a
  assertedSmaller _ _ = False

  smallerArg : Bool -> Defs ->
               Maybe (Term vars) -> Term vars -> Term vars -> Bool
  smallerArg inc defs big s tm
        -- If we hit a pattern that is equal to a thing we've asserted_smaller,
        -- the argument must be smaller
      = assertedSmaller big tm ||
                case getFnArgs tm of
                     (Ref (TyCon _ t a) cn, args)
                         => any (smaller True defs big s) args
                     (Ref (DataCon t a) cn, args)
                         => any (smaller True defs big s) args
                     _ => case s of
                               App _ f _ => smaller inc defs big f tm
                                            -- Higher order recursive argument
                               _ => False

splitAtVar : (ns : List Name) -> {idx : Nat} ->
          (0 p : IsVar name idx ns) -> (List Name, Name, List Name)
splitAtVar (n :: xs) First = ([], n, xs)
splitAtVar (n :: xs) (Later p) = let (outer,v,inner) = splitAtVar xs p
                                 in (n :: outer, v, inner)

mutual
  -- Is the first term a subterm of the second? If so, return the argument positions that are subterms
  isSubTerm : {vars: _} -> Term vars -> Term vars -> Maybe (List Nat)
  isSubTerm tm@(App _ f a) tm'@(App _ f' a') =
    let (n , args ) = getFnArgs tm
          | _ => Nothing
        (n', args') = getFnArgs tm'
          | _ => Nothing
        subTermArgs = map (\(a,b)=> isSubTermArgs a b) (zip args args')
        reduceds = map fst . filter ((==True) . snd) $ zip [0 .. length args] subTermArgs
    in if n==n' && any (==True) subTermArgs
         then Just reduceds
         else Nothing
  isSubTerm _ _ = Nothing

  isSubTermArgs : {vars: _} -> Term vars -> Term vars -> Bool
  isSubTermArgs (Local idx _) (Local idx' _) = False -- idx == idx'
  isSubTermArgs (Meta i args) _ = False
  isSubTermArgs _ (Meta i args) = False
  isSubTermArgs (Bind _ b sc) (Bind _ b' sc') = False -- not checkable
  isSubTermArgs tm@(App _ f a) tm'@(App _ f' a') =
    let (n , args ) = getFnArgs tm
          | _ => False
        (n', args') = getFnArgs tm'
          | _ => False
    in n==n' && any (==True) (map (uncurry isSubTermArgs) (zip args args'))
  isSubTermArgs (TCode t) (TCode t') = isSubTermArgs t t'
  isSubTermArgs (Escape t) (Escape t') = isSubTermArgs t t'
  isSubTermArgs (Eval t) (Eval t') = isSubTermArgs t t'
  isSubTermArgs (Quote ty t) (Quote ty' t') = isSubTermArgs t t' && isSubTermArgs ty ty'
  isSubTermArgs (Local idx p) tm = let (outer,var,inner) = splitAtVar vars p in
                               isConApp tm && isFreeVar {outer=outer} var (the (Term (outer ++ var :: inner)) (believe_me tm)) -- Yuck!
    where -- TODO Remove?
    isConApp : Term vars -> Bool
    isConApp tm = case getFnArgs tm of
      (Ref (TyCon _ _ _) _, _) => True
      (Ref (DataCon _ _) _, _) => True
      _                        => False
  isSubTermArgs _ _ = False

-- Join lists of structurally smaller argument positions with an intersection
intersectionOfRecArgs : List (Maybe (List Nat)) -> Maybe (List Nat)
intersectionOfRecArgs margs = case mapMaybe id margs of
                                [] => Nothing
                                [args] => Just args
                                (args::argss) => Just $ foldr intersect args argss

export
checkConRec : {auto c : Ref Ctxt Defs} ->
              {auto u : Ref UST UState} ->
              {auto s : Ref Stg Stage} ->
              Name -> Name -> Term [] -> Core (Maybe (List Nat))
checkConRec ntycon ndcon ty
  = do let (bs ** (env, retTy)) = getRetTyWithEnv [] ty
       defs <- get Ctxt
       let (isBadRec, tyArgIds) = findRecArgs defs env retTy
       when isBadRec
            (throw $ GenericMsg $ "Non-parameter type " ++ show ntycon ++ " (likely) has unbounded recursion")
       pure tyArgIds
  where

    -- Flag if the constructor has a recursive argument, and (possibly) which of its
    -- argument positions are structurally smaller than the return type's
    findRecArgs : {vs : _} -> Defs -> Env Term vs -> Term vs -> (Bool, Maybe (List Nat))
    findRecArgs defs [] ty = (False, Nothing)
    findRecArgs {vs = v :: vs'} defs (b::env) ty
      = let (recFlag, recArgs) = findRecArgs defs env (subst (Ref Bound v) ty)

            argTy = (binderType b)
            (bFlag, bArgs) = case getTyConName argTy of
                               Just argTyCon => if (argTyCon == ntycon)
                                          then (let subs = isSubTerm (weaken argTy) ty
                                                in (not $ isJust subs, subs))
                                          else (False, Nothing)
                               Nothing => (False, Nothing)

        in (bFlag || recFlag, intersectionOfRecArgs [bArgs, recArgs])

export
processCon : {auto c : Ref Ctxt Defs} ->
             {auto u : Ref UST UState} ->
             {auto s : Ref Stg Stage} ->
             Name -> TyConInfo -> ImpTy -> Core (Name, Term [])
processCon tyName tyInfo (MkImpTy n ty)
    = do (tychk, _) <- check [] ty (Just gType)

         -- Check the data con name hasn't been defined already
         defs <- get Ctxt
         Nothing <- lookupDef n defs
           | Just gdef => throw (GenericMsg ("Multiple type declarations for " ++ show n))

         -- Check the constructor actually returns something in the correct family
         checkTyConName tyName (snd $ getRetTy tychk)

         pure (n, tychk)
  where
  checkTyConName : {vars :_} -> Name -> Term vars -> Core ()
  checkTyConName tyn tm
    = do let Just n' = getTyConName tm
             | Nothing => throw $ GenericMsg $ "Couldn't find type constructor returned by data constructor: " ++ show n
         let True = (tyn == n')
             | False => throw $ GenericMsg $ "Data constructor " ++ show n ++
                          " doesn't return expected type constructor: " ++ show tyn
         pure ()

export
processData : {auto c : Ref Ctxt Defs} ->
              {auto u : Ref UST UState} ->
              {auto s : Ref Stg Stage} ->
              ImpData -> Core ()
processData (MkImpData n info tycon datacons)
    = do -- Check if we've already defined this name
         defs <- get Ctxt
         Nothing <- lookupDef n defs
           | Just gdef => throw (GenericMsg ("Multiple declarations for " ++ show n))

         (tychk, _) <- check [] tycon (Just gType)
         -- Add it to the context before checking data constructors
         -- Exercise: We should also check whether it's already defined!
         defs <- get Ctxt
         arity <- getArity defs [] tychk
         let info' = convTyConInfo info
         addDef n (newDef tychk (TCon info' 0 arity []))
         chkcons <- traverse (processCon n info') datacons

         -- Check for obvious recursion in any non-parameter types
         when (not $ isParam info')
              (do -- Ensure any recursive data cons have at least one structurally decreasing argument
                  recargs <- traverse (uncurry $ checkConRec n) chkcons

                  -- Check for at least one base case
                  when (not $ any (==Nothing) recargs)
                       (throw $ GenericMsg $ "Non-parameter type constructor " ++ show n ++ " is recursive but has no terminating case")

                  -- Check that there is at least one arg position shared between _all_ dcons for our structurally decreasing positions
                  case intersectionOfRecArgs recargs of
                    Nothing => pure () -- Non-recursive is OK
                    Just [] => throw $ GenericMsg $ "Non-parameter type constructor " ++ show n ++ " is recursive but not all recursive constructors are structurally decreasing on the same argument"
                    Just xs => pure () -- Recursive with shared structurally decreasing arg is OK
              )

         defs <- get Ctxt
         traverse_ (\ (i, (cn, ty)) =>
                       do carity <- getArity defs [] ty
                          addDef cn (newDef ty (DCon (cast i) carity)))
                   (zip [0..(length chkcons)] chkcons)

         -- Idris 2 has to do a bit more work here to relate the type constructor
         -- and data constructors (e.g. for totality checking, interactive
         -- editing) but this is enough for our purposes
         updateDef n (addConNames (map fst chkcons))

         coreLift $ putStrLn $ "Processed " ++ show n
  where convTyConInfo : ImpTyConInfo -> TyConInfo
        convTyConInfo ITyCParam = TyConParam
        convTyConInfo ITyCObj   = TyConObj
        convTyConInfo ITyCSimp  = TyConSimp

        addConNames : List Name -> GlobalDef -> GlobalDef
        addConNames cons (MkGlobalDef type (TCon x tag arity _) compexpr) = MkGlobalDef type (TCon x tag arity cons) compexpr
        addConNames cons gdef = gdef

{-
TODO

Need to check that recursive simple types are terminating

On point of use, we'll need to check that each explicit argument is a simple type

-}
