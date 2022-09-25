module Core.Context

import Core.CaseTree
import public Core.Core
import Core.Env
import Core.CompileExpr
import public Core.TT

import Data.SortedMap
import Data.String
import Data.List

public export
data Def : Type where
    None : Def -- Not yet defined
    PMDef : (args : List Name) -> (treeCT : CaseTree args) ->
                                  (treeRT : CaseTree args) ->
           (pats : List (vs ** (Env Term vs, Term vs, Term vs))) ->
            Def -- Ordinary function definition
    DCon :              (tag : Int) -> (arity : Nat) -> Def -- data constructor
    TCon : TyConInfo -> (tag : Int) -> (arity : Nat) -> (cons : List Name) -> Def
    Hole : Def
    Guess : (guess : Term []) ->
            (constraints : List Int) -> Def -- unification constraints

-- Idris 2 holds a lot more information about names than just their
-- type and definition, but that's enough for us here
public export
record GlobalDef where
  constructor MkGlobalDef
  type : Term []
  definition : Def
  compexpr : Maybe CDef

export
newDef : Term [] -> Def -> GlobalDef
newDef ty d = MkGlobalDef ty d Nothing

-- A mapping from names to definitions
-- Again there's more to this in Idris 2 since we need to deal with namespaces,
-- and there's also an array to map "resolved" name ids, which is much faster
-- for name lookups in general.
export
Defs : Type
Defs = SortedMap Name GlobalDef

-- This doesn't actually need to be in Core in this system, but it is in
-- Idris 2, because:
--  * the context is an IO array underneath, for O(1) lookup
--  * definitions can be updated on lookup, since we actually store things
--    as a binary encoded form that's stored on disk, and only decode when
--    first used.
-- So, it's in Core here so that there's a more clear mapping to the full
-- version.
export
lookupDef : Name -> Defs -> Core (Maybe GlobalDef)
lookupDef n defs = pure (SortedMap.lookup n defs)

export
lookupDefPure : Name -> Defs -> Maybe GlobalDef
lookupDefPure n defs = SortedMap.lookup n defs

export
lookupDefType : Name -> Defs -> Core (Maybe (Term []))
lookupDefType n defs = pure (map type $ SortedMap.lookup n defs)

export
lookupDefDConParent : Name -> Defs -> Core (Maybe Name)
lookupDefDConParent n defs
  = do let ms = map match $ Data.SortedMap.toList defs
       let [m] = mapMaybe id ms
           | _ => pure Nothing
       pure $ Just m
  where
    match : (Name, GlobalDef) -> Maybe Name
    match (tc, MkGlobalDef _ (TCon _ _ _ dcons) _) = if elem n dcons
                                                       then Just tc
                                                       else Nothing
    match (_, _) = Nothing

export
initDefs : Core Defs
initDefs = pure empty

export
clearDefs : Defs -> Core Defs
clearDefs d = pure empty

export
mapDefs : Defs -> (GlobalDef -> GlobalDef) -> Core Defs
mapDefs d f = pure . fromList $ map (\(k,v) => (k, f v)) (Data.SortedMap.toList d)

export
traverseDefs : Defs -> ((Name, GlobalDef) -> Core (Name, GlobalDef)) -> Core Defs
traverseDefs d f = pure $ Data.SortedMap.fromList !(traverse f $ Data.SortedMap.toList d)

export
traverseDefs_ : Defs -> ((Name, GlobalDef) -> Core ()) -> Core ()
traverseDefs_ d f = traverse_ f $ Data.SortedMap.toList d

-- A phantom type for finding references to the context
export
data Ctxt : Type where

-- A program consists of a series of data declarations, function type
-- declarations, and function clauses. Even in full Idris 2, this is what
-- everything translates down to. The following types represent well-type
-- data declarations and clauses, ready for adding to the context.

public export
record Constructor where
  constructor MkCon
  cname : Name
  arity : Nat
  type : Term []

-- Well typed data declaration
public export
data DataDef : Type where
     MkData : (tycon : Constructor) -> (datacons : List Constructor) ->
              DataDef

-- A well typed pattern clause
public export
data Clause : Type where
     MkClause : {vars : _} ->
                (env : Env Term vars) ->
                (lhs : Term vars) -> (rhs : Term vars) -> Clause

-- Add (or replace) a definition
export
addDef : {auto c : Ref Ctxt Defs} ->
         Name -> GlobalDef -> Core ()
addDef n d
    = do defs <- get Ctxt
         put Ctxt (insert n d defs)

export
updateDef : {auto c : Ref Ctxt Defs} ->
            Name -> (GlobalDef -> GlobalDef) -> Core ()
updateDef n upd
    = do defs <- get Ctxt
         Just gdef <- lookupDef n defs
              | Nothing => throw (UndefinedName n)
         addDef n (upd gdef)

export
setCompiled : {auto c : Ref Ctxt Defs} ->
              Name -> CDef -> Core ()
setCompiled n cexp
  = do defs <- get Ctxt
       Just gdef <- lookupDef n defs
       | Nothing => pure ()
       ignore $ addDef n (record { compexpr = Just cexp } gdef)

-- Call this before trying alternative elaborations, so that updates to the
-- context are put in the staging area rather than writing over the mutable
-- array of definitions.
-- Returns the old context (the one we'll go back to if the branch fails)
export
branch : {auto c : Ref Ctxt Defs} ->
         Core Defs
branch
  = do ctxt <- get Ctxt
       let gam' = ctxt
       put Ctxt gam'
       pure ctxt

export
Show Def where
  show None = "None"
  show (PMDef args treeCT _ _) = "PMDef [" ++ show args ++ "] " ++ show treeCT
  show (DCon tag arity) = "DCon " ++ show tag ++ " " ++ show arity
  show (TCon x tag arity cons) = "TCon " ++ show x ++ " " ++ show tag ++ " " ++ show arity
  show Hole = "Hole"
  show (Guess guess constraints) = "Guess " ++ show guess ++ " " ++ show constraints

export
Show GlobalDef where
  show (MkGlobalDef type definition compexpr) = show definition ++ " : " ++ show type

export
Show Defs where
  show d = unlines . map show $ Data.SortedMap.toList d
