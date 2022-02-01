module TTImp.Elab.Check

import Core.TT
import Core.Value
import Core.Env
import Core.Context
import Core.UnifyState
import Core.Normalise
import TTImp.TTImp

public export
data ElabMode = InType | InLHS | InExpr | InTransform -- TODO InLHS might need some sort of erasure tag

export
Eq ElabMode where
  InType      == InType = True
  InLHS       == InLHS  = True
  InExpr      == InExpr = True
  InTransform == InTransform = True
  _ == _ = False

export
check : {vars : _} ->
  {auto c : Ref Ctxt Defs} ->
  {auto u : Ref UST UState} ->
  {auto s : Ref Stg Stage} ->
  Env Term vars -> RawImp -> Maybe (Glued vars) ->
  Core (Term vars, Glued vars)

export
elabTerm : {vars : _} ->
  {auto c : Ref Ctxt Defs} ->
  {auto s : Ref Stg Stage} ->
  {auto u : Ref UST UState} ->
  ElabMode ->
  Env Term vars -> RawImp -> Maybe (Glued vars) ->
  Core (Term vars, Glued vars)
