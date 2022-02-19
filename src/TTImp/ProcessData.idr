module TTImp.ProcessData

import Core.Context
import Core.Env
import Core.Normalise
import Core.TT
import Core.CaseTree
import Core.UnifyState
import Core.Unify

import TTImp.Elab.Term
import TTImp.TTImp

import Data.List
import Data.SortedMap
import Data.SortedSet

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

-- Try to retrieve the type con name from its type
getTyConName : {vars :_} -> Term vars -> Maybe Name
getTyConName (App _ f _) = getTyConName f
getTyConName (Ref (TyCon _ _ _) n) = Just n
getTyConName tm = Nothing

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
       Just (MkGlobalDef _ (TCon _ _ _ dcons)) <- lookupDef ntcon defs
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

  substSolvedMetaArgs : {vars' : _} -> Env Term vars' -> (ty : Term vars') -> List Name -> Core (Term vars')
  substSolvedMetaArgs env (Bind n b@(Pi s i ty) sc) (m :: metas)
    = do -- check if this meta has been solved
         defs <- get Ctxt
         Just (MkGlobalDef _ (PMDef [] (STerm tm))) <- lookupDef m defs -- TODO Should I be assuming that args is empty?! Works for most of my examples so far...
           | _ => -- Wasn't solved, so continue
                  do sc' <- substSolvedMetaArgs (b::env) sc metas
                     pure $ Bind n b sc'
         let weakTm = rewrite sym (appendNilRightNeutral vars') in weakenNs vars' tm
         let rest = subst weakTm sc
         pure $ Bind n b !(substSolvedMetaArgs (b :: env) (weaken rest) metas)

  substSolvedMetaArgs env ty metas = pure ty

  checkConRetTy : Name -> Core (Maybe (Name, Term []))
  checkConRetTy dcon = do defs <- get Ctxt
                          -- Lookup the data constructor type
                          Just (MkGlobalDef dconty (DCon tag arity)) <- lookupDef dcon defs
                            | _ => throw $ InternalError $ "Data constructor name wasn't found in context: " ++ show dcon
                          --let dcontyWeaken = rewrite sym (appendNilRightNeutral vars) in weakenNs vars dconty


                          -- Replace all the args with new metavars
                          tcty <- wrapMetaEnv env ty
                          (ty',tyArgNames) <- wrapMetaArgs [] dconty

                          --coreLift $ putStrLn $ "Comparing " ++ show ty ++ " and " ++ show ty'

                          -- Try to unify with our expected type.
                          -- Constraints are allowable -- better to include
                          -- possibly wrong constructors than ignore possibly correct ones.
                          oldUST <- get UST
                          res <- handleUnify (do res <- unify InLHS [] tcty ty'
                                                 solveConstraints InLHS
                                                 defs <- get Ctxt
                                                 dconty' <- substSolvedMetaArgs [] dconty tyArgNames
                                                 --coreLift $ putStrLn $ "Could be " ++ show dcon ++ " with sig : " ++ show dconty'
                                                 pure $ Just (dcon, dconty'))
                                             (\err => do --coreLift $ putStrLn $ show err
                                                         pure Nothing)

                          -- Undo damage to UST and CTXT
                          put UST oldUST
                          put Ctxt defs
                          pure res

clog2 : Nat -> Nat
clog2 x = cast . ceiling $ (log $ cast x) / (log 2)

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
    = do defs <- get Ctxt
         --Just (MkGlobalDef dconty (DCon tag arity)) <- lookupDef dcon defs
         --  | _ => throw $ InternalError $ "Data constructor name wasn't found in context: " ++ show dcon
         argsFieldWidth 0 [] dconty

export
processCon : {auto c : Ref Ctxt Defs} ->
             {auto u : Ref UST UState} ->
             {auto s : Ref Stg Stage} ->
             Name -> ImpTy -> Core (Name, Term [])
processCon tyName (MkImpTy n ty)
    = do (tychk, _) <- checkTerm [] ty (Just gType)

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

         (tychk, _) <- checkTerm [] tycon (Just gType)
         -- Add it to the context before checking data constructors
         -- Exercise: We should also check whether it's already defined!
         defs <- get Ctxt
         arity <- getArity defs [] tychk
         addDef n (newDef tychk (TCon (convTyConInfo info) 0 arity []))
         chkcons <- traverse (processCon n) datacons

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
        addConNames cons (MkGlobalDef type (TCon x tag arity _)) = MkGlobalDef type (TCon x tag arity cons)
        addConNames cons gdef = gdef


