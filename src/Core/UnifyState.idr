module Core.UnifyState

import Core.Context
import Core.Core
import Core.Env
import Core.Normalise
import Core.TT

import Data.List
import Data.SortedMap
import Data.SortedSet
import Data.Maybe

public export
data UnifyMode = InLHS
               | InMatch
               | InTerm

export
Eq UnifyMode where
  InLHS == InLHS     = True
  InMatch == InMatch = True
  InTerm == InTerm   = True
  _ == _             = False

public export
data Constraint : Type where
     -- An unsolved constraint, noting two terms which need to be convertible
     -- in a particular environment
     MkConstraint : {vars : _} ->
                    UnifyMode ->
                    (env : Env Term vars) ->
                    (x : Term vars) -> (y : Term vars) ->
                    Constraint
     -- An unsolved sequence of constraints, arising from arguments in an
     -- application where solving later constraints relies on solving earlier
     -- ones
     MkSeqConstraint : {vars : _} ->
                       (env : Env Term vars) ->
                       (xs : List (Term vars)) ->
                       (ys : List (Term vars)) ->
                       Constraint
     -- A resolved constraint
     Resolved : Constraint

public export
record UState where
  constructor MkUState
  holes : SortedSet Name
  guesses : SortedSet Name
  constraints : SortedMap Int Constraint -- map for finding constraints by ID
  dotConstraints : List (Name, Constraint) -- dot pattern constraints
  nextName : Int
  nextConstraint : Int

export
initUState : UState
initUState = MkUState empty empty empty [] 0 0

export
data UST : Type where

export
resetNextVar : {auto u : Ref UST UState} ->
               Core ()
resetNextVar
    = do ust <- get UST
         put UST (record { nextName = 0 } ust)

-- Generate a global name based on the given root, in the current namespace
export
genName : {auto u : Ref UST UState} ->
          String -> Core Name
genName str
    = do ust <- get UST
         put UST (record { nextName $= (+1) } ust)
         pure (MN str (nextName ust))

addHoleName : {auto u : Ref UST UState} ->
              Name -> Core ()
addHoleName n
    = do ust <- get UST
         put UST (record { holes $= insert n } ust)

addGuessName : {auto u : Ref UST UState} ->
               Name -> Core ()
addGuessName n
    = do ust <- get UST
         put UST (record { guesses $= insert n  } ust)

export
removeHole : {auto u : Ref UST UState} ->
             Name -> Core ()
removeHole n
    = do ust <- get UST
         put UST (record { holes $= delete n } ust)

export
saveHoles : {auto u : Ref UST UState} ->
            Core (SortedSet Name)
saveHoles
  = do ust <- get UST
       put UST (record { holes = empty } ust)
       pure (holes ust)

export
getHoles : {auto u : Ref UST UState} ->
            Core (SortedSet Name)
getHoles
  = do ust <- get UST
       pure (holes ust)

export
restoreHoles : {auto u : Ref UST UState} ->
               SortedSet Name -> Core ()
restoreHoles hs
  = do ust <- get UST
       put UST (record { holes = hs } ust)

export
addConstraint : {auto u : Ref UST UState} ->
                Constraint -> Core Int
addConstraint constr
    = do ust <- get UST
         let cid = nextConstraint ust
         put UST (record { constraints $= insert cid constr,
                           nextConstraint = cid+1 } ust)
         pure cid

export
deleteConstraint : {auto u : Ref UST UState} ->
                Int -> Core ()
deleteConstraint cid
    = do ust <- get UST
         put UST (record { constraints $= delete cid } ust)

-- Make a type which abstracts over an environment
-- Don't include 'let' bindings, since they have a concrete value and
-- shouldn't be generalised
export
abstractEnvType : {vars : _} ->
                  Env Term vars -> (tm : Term vars) -> Term []
abstractEnvType [] tm = tm
abstractEnvType (Let s val ty :: env) tm
    = abstractEnvType env (Bind _ (Let s val ty) tm)
abstractEnvType (Pi s e ty :: env) tm
    = abstractEnvType env (Bind _ (Pi s e ty) tm)
abstractEnvType (b :: env) tm
    = abstractEnvType env (Bind _ (Pi (binderStage b) (fromMaybe Explicit $ binderInfo b) (binderType b)) tm)

mkConstantAppArgs : {vars : _} ->
                    Env Term vars ->
                    (wkns : List Name) ->
                    List (Term (wkns ++ (vars ++ done)))
mkConstantAppArgs [] wkns = []
mkConstantAppArgs {done} {vars = x :: xs} (b :: env) wkns
    = let rec = mkConstantAppArgs {done} env (wkns ++ [x]) in
          Local (length wkns) (mkVar wkns) ::
                  rewrite (appendAssociative wkns [x] (xs ++ done)) in rec
  where
    mkVar : (wkns : List Name) ->
            IsVar name (length wkns) (wkns ++ name :: vars ++ done)
    mkVar [] = First
    mkVar (w :: ws) = Later (mkVar ws)

-- Create a new metavariable with the given name and return type,
-- and return a term which is the metavariable applied to the environment
-- (and which has the given type)
export
newMeta : {vars : _} ->
          {auto c : Ref Ctxt Defs} ->
          {auto u : Ref UST UState} ->
          Env Term vars -> Name -> Term vars -> Def ->
          Core (Term vars)
newMeta {vars} env n ty def
    = do let hty = abstractEnvType env ty
         let hole = newDef hty def
         addDef n hole
         addHoleName n
         pure (Meta n envArgs)
  where
    envArgs : List (Term vars)
    envArgs = let args = reverse (mkConstantAppArgs {done = []} env []) in
                  rewrite sym (appendNilRightNeutral vars) in args

-- Apply an environment to a term, respecting application implicitness
export
applyTo : {vars : _} -> Term vars -> Env Term vars -> Term vars
applyTo tm env
  = let args = reverse (mkConstantAppArgs' {done = []} env [])
    in apply tm (rewrite sym (appendNilRightNeutral vars) in args)

  where
  mkConstantAppArgs' : {vars : _} ->
                      Env Term vars ->
                      (wkns : List Name) ->
                      List (AppInfo, Term (wkns ++ (vars ++ done)))
  mkConstantAppArgs' [] wkns = []
  mkConstantAppArgs' {done} {vars = x :: xs} (b :: env) wkns
    = let rec = mkConstantAppArgs' {done} env (wkns ++ [x])
          i = case binderInfo b of
                (Just Implicit) => AImplicit
                _               => AExplicit
      in (i, Local (length wkns) (mkVar {name=x} {vars=xs} wkns)) ::
            rewrite (appendAssociative wkns [x] (xs ++ done)) in rec

    where
    mkVar : {name:_} -> {vars:_} -> (wkns : List Name) ->
            IsVar name (length wkns) (wkns ++ name :: vars ++ done)
    mkVar [] = First
    mkVar (w :: ws) = Later (mkVar ws)


mkConstant : {vars : _} ->
             Env Term vars -> Term vars -> Term []
mkConstant [] tm = tm
mkConstant {vars = x :: _} (b :: env) tm
    = let ty = binderType b
          s  = binderStage b in
          mkConstant env (Bind x (Lam s Explicit ty) tm)

-- Given a term and a type, add a new guarded constant to the global context
-- by applying the term to the current environment
-- Return the replacement term (the name applied to the environment)
export
newConstant : {vars : _} ->
              {auto u : Ref UST UState} ->
              {auto c : Ref Ctxt Defs} ->
              Env Term vars ->
              (tm : Term vars) -> (ty : Term vars) ->
              (constrs : List Int) ->
              Core (Term vars)
newConstant {vars} env tm ty constrs
    = do let def = mkConstant env tm
         let defty = abstractEnvType env ty
         cn <- genName "postpone"
         let guess = newDef defty (Guess def constrs)
         addDef cn guess
         addGuessName cn
         pure (Meta cn envArgs)
  where
    envArgs : List (Term vars)
    envArgs = let args = reverse (mkConstantAppArgs {done = []} env []) in
                  rewrite sym (appendNilRightNeutral vars) in args

export
Show Constraint where
  show (MkConstraint mode env x y) = show x ++ " ~~~ " ++ show y
  show (MkSeqConstraint env xs ys) = show $ map (\(x,y)=>show x ++ " ~~~ " ++ show y) (zip xs ys)
  show Resolved = "Resolved!"

export
tryErrorUnify : {auto c : Ref Ctxt Defs} ->
                {auto u : Ref UST UState} ->
                Core a -> Core (Either Error a)
tryErrorUnify elab
  = do ust <- get UST
       defs <- get Ctxt
       catch (do res <- elab
                 pure (Right res))
             (\err => do put Ctxt defs
                         put UST ust
                         pure (Left err))

export
tryUnify : {auto c : Ref Ctxt Defs} ->
           {auto u : Ref UST UState} ->
           Core a -> Core a -> Core a
tryUnify elab1 elab2
  = do Right ok <- tryErrorUnify elab1
         | Left err => elab2
       pure ok

export
handleUnify : {auto c : Ref Ctxt Defs} ->
              {auto u : Ref UST UState} ->
              Core a -> (Error -> Core a) -> Core a
handleUnify elab1 elab2
  = do Right ok <- tryErrorUnify elab1
         | Left err => elab2 err
       pure ok

export
addDot : {vars : _} ->
         {auto c : Ref Ctxt Defs} ->
         {auto u : Ref UST UState} ->
         Env Term vars -> Name -> Term vars -> Term vars ->
         Core ()
addDot env dotarg x y
  = do ust <- get UST
       defs <- get Ctxt
       xnf <- normalise defs env x
       ynf <- normalise defs env y
       put UST (record { dotConstraints $=
                           ((dotarg, MkConstraint InMatch env xnf ynf) ::)
                       } ust)
