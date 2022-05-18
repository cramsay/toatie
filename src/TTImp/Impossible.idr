module TTImp.Impossible

import Core.Context
import Core.Env
import Core.Normalise
import Core.TT
import Core.Value

import TTImp.TTImp

import Data.List
import Data.List1

%default covering

-- This file contains support for building a guess at the term on the LHS of an
-- 'impossible' case, in order to help build a tree of covered cases for
-- coverage checking. Since the LHS by definition won't be well typed, we are
-- only guessing!

badClause : Term [] -> List RawImp -> Core a
badClause fn args
  = throw (GenericMsg ("Badly formed impossible clause in " ++ show (fn))) -- TODO display RawImp args too

nextVar : {auto q : Ref QVar Int} -> Core (Term [])
nextVar = do i <- get QVar
             put QVar (i + 1)
             pure (Ref Bound (MN "imp" i))

piInfoToAppInfo : PiInfo -> AppInfo
piInfoToAppInfo Implicit = AImplicit
piInfoToAppInfo Explicit = AExplicit

nfToClosure : {auto c : Ref Ctxt Defs} -> NF [] -> Core (Closure [])
nfToClosure nf = do defs <- get Ctxt
                    tm <- quote defs NoLets [] nf
                    pure $ toClosure [] tm

mutual
  processArgs : {auto c : Ref Ctxt Defs} ->
                {auto q : Ref QVar Int} ->
                Term [] -> NF [] ->
                (pvs : List (Name, RawImp)) ->
                (args : List RawImp) ->
                Core (Term [])
  processArgs fn (NBind x (Pi s i ty) sc) pvs (a::args)
    = do defs <- get Ctxt
         a' <- mkTerm a (Just $ ty) pvs []
         processArgs (App (piInfoToAppInfo i) fn a') !(sc defs (toClosure [] a')) pvs args
  processArgs fn nty pvs [] = pure fn
  processArgs fn nty pvs args = badClause fn args

  buildApp : {auto c : Ref Ctxt Defs} -> {auto q : Ref QVar Int} ->
             Name -> Maybe (Closure []) ->
             (pvs : List (Name, RawImp)) ->
             (args : List RawImp) ->
             Core (Term [])
  buildApp n mty pvs args
    = do let Nothing = lookup n pvs
               | Just pty => processArgs (Ref Bound n) NErased pvs args
         defs <- get Ctxt
         Just gdef <- lookupDef n defs
           | Nothing => throw $ GenericMsg $ "Undefined name " ++ show n
         tynf <- nf defs NoLets [] (type gdef)
         let head = case definition gdef of
                      DCon t a => DataCon t a
                      TCon i t a _ => TyCon i t a
                      _            => Func
         processArgs (Ref head n) tynf pvs args

  mkTerm : {auto c : Ref Ctxt Defs} -> {auto q : Ref QVar Int} ->
           RawImp -> Maybe (Closure []) ->
           (pvs : List (Name, RawImp)) ->
           (args : List RawImp) ->
           Core (Term [])
  mkTerm (IVar n)        mty pvs args = buildApp n mty pvs args
  mkTerm (IApp _ fn arg) mty pvs args = mkTerm fn mty pvs (arg :: args)
  mkTerm (IPatvar n ty sc) mty pvs args = mkTerm sc mty ((n,ty)::pvs) args
  mkTerm tm _ _ _                  = nextVar

  -- Given an LHS that is declared 'impossible', build a term to match from,
  -- so that when we build the case tree for checking coverage, we take into
  -- account the impossible clauses
  export
  getImpossibleTerm : {auto c : Ref Ctxt Defs} ->
                      RawImp -> Core (Term [])
  getImpossibleTerm tm = do q <- newRef QVar (the Int 0)
                            tm' <- mkTerm tm Nothing [] []
                            pure tm'

