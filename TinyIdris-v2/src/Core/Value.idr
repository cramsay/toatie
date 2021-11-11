module Core.Value

import Core.Context
import Core.Env
import Core.TT

mutual
  public export
  data LocalEnv : List Name -> List Name -> Type where
       Nil  : LocalEnv free []
       (::) : Closure free -> LocalEnv free vars -> LocalEnv free (x :: vars)

  public export
  data Closure : List Name -> Type where
       MkClosure : {vars : _} ->
                   LocalEnv free vars ->
                   Env Term free ->
                   Term (vars ++ free) -> Closure free

  -- The head of a value: things you can apply arguments to
  public export
  data NHead : List Name -> Type where
       NLocal : (idx : Nat) -> (0 p : IsVar name idx vars) ->
                NHead vars
       NRef   : NameType -> Name -> NHead vars
       NMeta  : Name -> List (Closure vars) -> NHead vars

  -- Values themselves. 'Closure' is an unevaluated thunk, which means
  -- we can wait until necessary to reduce constructor arguments
  public export
  data NF : List Name -> Type where
       NBind    : (x : Name) -> Binder (NF vars) ->
                  (Defs -> Closure vars -> Core (NF vars)) -> NF vars
       NApp     : NHead vars -> List (Closure vars) -> NF vars
       NDCon    : Name -> (tag : Int) -> (arity : Nat) ->
                  List (Closure vars) -> NF vars
       NTCon    : Name -> TyConInfo -> (tag : Int) -> (arity : Nat) ->
                  List (Closure vars) -> NF vars
       NType    : NF vars
       NErased  : NF vars
       NQuote   : Closure vars -> NF vars
       NCode    : Closure vars -> NF vars

export
{free : _} -> Show (NHead free) where
  show (NLocal idx p) = show (nameAt idx p) ++ "[" ++ show idx ++ "]"
  show (NRef _ n) = show n
  show (NMeta n args) = "?" ++ show n ++ "_[" ++ show (length args) ++ " closures]"

export
{free : _} -> Show (Closure free) where
  show (MkClosure locs env tm) = "[closure for term = " ++ show tm ++ "]"

export
{free : _} -> Show (LocalEnv free vars) where
  show [] = "[]"
  show (x :: y) = show x ++ " :: " ++ show y

export
{free : _} -> Show (NF free) where
  show (NBind x (Lam s info ty) _)
    = "\\" ++ show s ++ show x ++ " : " ++ show ty ++
      " => [closure]"
  show (NBind x (Let s val ty) _)
    = "let " ++ show s ++ show x ++ " : " ++ show ty ++
      " = " ++ show val ++ " in [closure]"
  show (NBind x (Pi s info ty) _)
    = show s ++ show x ++ " : " ++ show ty ++
      " -> [closure]"
  show (NBind x (PVar s ty) _)
    = "pat " ++ show s ++ show x ++ " : " ++ show ty ++
      " => [closure]"
  show (NBind x (PVTy s ty) _)
    = "pty " ++ show s ++ show x ++ " : " ++ show ty ++
      " => [closure]"
  show (NApp hd args) = show hd ++ " [" ++ show (length args) ++ " closures]"
  show (NDCon n _ _ args) = show n ++ " [" ++ show (length args) ++ " closures]"
  show (NTCon n _ _ _ args) = show n ++ " [" ++ show (length args) ++ " closures]"
  show (NErased) = "[__]"
  show (NType) = "Type"
  show (NQuote _) = "NQuote [closure]"
  show (NCode  x) = "NCode " ++ show x
