module Compiler.Inline

import Compiler.CompileExpr

import Core.CompileExpr
import Core.Context
import Core.Hash
import Core.TT

import Data.Maybe
import Data.List
import Data.Vect
import Data.SortedSet
import Libraries.Data.LengthMatch

%default covering

NameSet : Type
NameSet = SortedSet Name

data Progress : Type where

data EEnv : List Name -> List Name -> Type where
     Nil : EEnv free []
     (::) : CExp free -> EEnv free vars -> EEnv free (x :: vars)

extend : EEnv free vars -> (args : List (CExp free)) -> (args' : List Name) ->
         LengthMatch args args' -> EEnv free (args' ++ vars)
extend env [] [] NilMatch = env
extend env (a :: xs) (n :: ns) (ConsMatch w)
    = a :: extend env xs ns w

Stack : List Name -> Type
Stack vars = List (CExp vars)

unload : Stack vars -> CExp vars -> CExp vars
unload [] e = e
unload (a :: args) e = unload args (CApp e [a])

unloadApp : Nat -> Stack vars -> CExp vars -> CExp vars
unloadApp n args e = unload (drop n args) (CApp e (take n args))

getArity : CDef -> Nat
getArity (MkFun args _ _) = length args
getArity (MkCon _ arity) = arity

takeFromStack : EEnv free vars -> Stack free -> (args : List Name) ->
                Maybe (EEnv free (args ++ vars), Stack free)
takeFromStack env (e :: es) (a :: as)
  = do (env', stk') <- takeFromStack env es as
       pure (e :: env', stk')
takeFromStack env stk [] = pure (env, stk)
takeFromStack env [] args = Nothing

data LVar : Type where

genName : {auto l : Ref LVar Int} ->
          String -> Core Name
genName n
    = do i <- get LVar
         put LVar (i + 1)
         pure (MN n i)

refToLocal : Name -> (x : Name) -> CExp vars -> CExp (x :: vars)
refToLocal x new tm = refsToLocals (Add new x None) tm

largest : Ord a => a -> List a -> a
largest x [] = x
largest x (y :: ys)
    = if y > x
         then largest y ys
         else largest x ys

mutual
  used : {free : _} ->
         {idx : Nat} -> (0 p : IsVar n idx free) -> CExp free -> Int
  used p (CLocal {idx=pidx} x) = if idx == pidx then 1 else 0
  used p (CLam _ ty sc) = used p ty + used (Later p) sc
  used p (CPi  _ ty sc) = used p ty + used (Later p) sc
  used p (CLet x val ty sc) = used p val + used p ty + used (Later p) sc
  used p (CApp f args) = foldr (+) (used p f) (map (used p) args)
  used p (CCon x args) = foldr (+) 0          (map (used p) args)
  used p (CConCase scr alts def) = used p scr +
                                   largest (maybe 0 (used p) def)
                                           (map (usedCon p) alts)
  used p (CPrj con field x) = used p x
  used p tm = 0

  usedCon : {free : _} ->
            {idx : Nat} -> (0 p : IsVar n idx free) -> CConAlt free -> Int
  usedCon n (MkConAlt _ args sc)
  = let MkVar n' = weakenNs args (MkVar n)
    in used n' sc

mutual
  evalLocal : {vars, free : _} ->
              {auto c : Ref Ctxt Defs} ->
              {auto p : Ref Progress Bool} ->
              {auto l : Ref LVar Int} ->
              List Name -> Stack free ->
              EEnv free vars ->
              {idx : Nat} -> (0 p : IsVar x idx (vars ++ free)) ->
              Core (CExp free)
  evalLocal {vars=[]} rec stk env p = pure $ unload stk (CLocal p)
  evalLocal {vars=x::xs} rec stk (v::env) First
    = case stk of
        [] => pure v
        _  => eval rec env stk (weakenNs xs v)
  evalLocal {vars=x::xs} rec stk (v::env) (Later y)
    = evalLocal rec stk env y

  tryApply : {vars, free : _} ->
             {auto c : Ref Ctxt Defs} ->
             {auto p : Ref Progress Bool} ->
             {auto l : Ref LVar Int} ->
             List Name -> Stack free -> EEnv free vars -> CDef ->
             Core (Maybe (CExp free))
  tryApply {free} {vars} rec stk env (MkFun args ty exp)
      = do let Just (env', stk') = takeFromStack env stk args
               | Nothing => pure Nothing
           res <- eval rec env' stk'
                     (rewrite sym (appendAssociative args vars free) in
                              embed {vars = vars ++ free} exp)
           pure (Just res)
  tryApply rec stk env _ = pure Nothing


  eval : {vars, free : _} ->
         {auto c : Ref Ctxt Defs} ->
         {auto p : Ref Progress Bool} ->
         {auto l : Ref LVar Int} ->
         List Name -> EEnv free vars -> Stack free -> CExp (vars ++ free) ->
         Core (CExp free)
  eval rec env stk (CLocal p) = evalLocal rec stk env p
  eval rec env stk (CRef n)
    = do defs <- get Ctxt
         Just gdef <- lookupDef n defs
           | Nothing => pure (unload stk (CRef n))
         let Just def = compexpr gdef
               | Nothing => pure (unload stk (CRef n))
         let arity = getArity def
         if (not (n `elem` rec))
            then do Just ap <- tryApply (n :: rec) stk env def
                      | Nothing => pure $ unloadApp arity stk (CRef n)
                    put Progress True
                    pure ap
            else pure $ unloadApp arity stk (CRef n)
  eval rec env [] (CLam x ty sc)
    = do xn <- genName "lamv"
         sc' <- eval rec (CRef xn :: env) [] sc
         ty' <- eval rec env [] ty
         pure $ CLam x ty' (refToLocal xn x sc')
  eval rec env (e :: stk) (CLam x ty sc) = eval rec (e :: env) stk sc
  eval rec env [] (CPi x ty sc)
    = do xn <- genName "lamv"
         sc' <- eval rec (CRef xn :: env) [] sc
         ty' <- eval rec env [] ty
         pure $ CPi x ty' (refToLocal xn x sc')
  eval rec env (e :: stk) (CPi x ty sc) = eval rec (e :: env) stk sc
  eval rec env stk (CLet x val ty sc)
    = do xn <- genName "lamv"
         sc' <- eval rec (CRef xn :: env) [] sc
         val' <- eval rec env [] val
         ty'  <- eval rec env [] ty
         pure $ CLet x val' ty' (refToLocal xn x sc')
  eval rec env stk (CApp f args) = eval rec env (!(traverse (eval rec env []) args) ++ stk) f
  eval rec env stk (CCon x args) = pure $ unload stk $ CCon x !(traverse (eval rec env []) args)
  eval rec env stk (CPrj con field sc)
    = do sc' <- eval rec env [] sc
         case sc' of
           CCon scname args => if scname == con
                                  then getIth field args
                                  else pure $ CPrj con field sc'
                                  -- It's OK for scname and con to not match since we specutively
                                  -- project out terms from clauses
           _ => pure $ CPrj con field sc'
    where
    getIth : Nat -> List (CExp vs) -> Core (CExp vs)
    getIth Z (arg::args) = do put Progress True
                              pure arg
    getIth (S n) (arg::args) = getIth n args
    getIth _ [] = throw $ InternalError $
                    "Projection term pointing beyond end of arg list: " ++
                    show (CPrj con field sc)
  eval rec env stk CErased = pure $ unload stk $ CErased
  eval rec env stk (CConCase scr alts def)
    = do scr' <- eval rec env [] scr
         let env' = update scr env scr'
         Nothing <- pickAlt rec env' stk scr' alts def
           | Just val => do put Progress True
                            pure val
         def' <- traverseOpt (eval rec env' stk) def
         -- TODO Just before returning, we could apply all the case transformations (see CaseOpt.idr in Idris2)
         pure $ CConCase scr' !(traverse (evalAlt rec env' stk) alts) def'
    where
      updateLoc : {idx, vs : _} ->
                  (0 p : IsVar x idx (vs ++ free)) ->
                  EEnv free vs -> CExp free -> EEnv free vs
      updateLoc {vs = []} p env val = env
      updateLoc {vs = (x::xs)} First (e :: env) val = val :: env
      updateLoc {vs = (y::xs)} (Later p) (e :: env) val = e :: updateLoc p env val

      update : {vs : _} ->
               CExp (vs ++ free) -> EEnv free vs -> CExp free -> EEnv free vs
      update (CLocal p) env sc = updateLoc p env sc
      update _ env _ = env

  extendLoc : {auto l : Ref LVar Int} ->
              EEnv free vars -> (args' : List Name) ->
              Core (Bounds args', EEnv free (args' ++ vars))
  extendLoc env [] = pure (None, env)
  extendLoc env (n :: ns)
    = do xn <- genName "cv"
         (bs', env') <- extendLoc env ns
         pure (Add n xn bs', CRef xn :: env')

  evalAlt : {vars, free : _} ->
            {auto c : Ref Ctxt Defs} ->
            {auto p : Ref Progress Bool} ->
            {auto l : Ref LVar Int} ->
            List Name -> EEnv free vars -> Stack free -> CConAlt (vars ++ free) ->
            Core (CConAlt free)
  evalAlt {free} {vars} rec env stk (MkConAlt n args sc)
    = do (bs, env') <- extendLoc env args
         scEval <- eval rec env' stk
                   (rewrite sym (appendAssociative args vars free) in sc)
         pure $ MkConAlt n args (refsToLocals bs scEval)

  pickAlt : {vars, free : _} ->
            {auto c : Ref Ctxt Defs} ->
            {auto p : Ref Progress Bool} ->
            {auto l : Ref LVar Int} ->
            List Name -> EEnv free vars -> Stack free ->
            CExp free -> List (CConAlt (vars ++ free)) ->
            Maybe (CExp (vars ++ free)) ->
            Core (Maybe (CExp free))
  pickAlt rec env stk (CCon n args) [] def
    = traverseOpt (eval rec env stk) def
  pickAlt {vars} {free} rec env stk con@(CCon n args) (MkConAlt n' args' sc :: alts) def
    = if n == n'
         then case checkLengthMatch args args' of
                Nothing => pure Nothing
                Just m =>
                  do let env' : EEnv free (args' ++ vars)
                              = extend env args args' m
                     pure $ Just !(eval rec env' stk
                             (rewrite sym (appendAssociative args' vars free) in
                              sc))
         else pickAlt rec env stk con alts def
  pickAlt rec env stk _ _ _ = pure Nothing

-- Inlining may have messed with function arity (e.g. by adding lambdas to
-- the LHS to avoid needlessly making a closure) so fix them up here. This
-- needs to be right because typically back ends need to know whether a
-- name is under- or over-applied
fixArityTm : {vars : _} ->
             {auto c : Ref Ctxt Defs} ->
             CExp vars -> List (CExp vars) -> Core (CExp vars)
fixArityTm (CRef n) args
    = do defs <- get Ctxt
         Just gdef <- lookupDef n defs
              | Nothing => pure (unload args (CRef n))
         let arity = case compexpr gdef of
                          Just def => getArity def
                          _ => 0
         pure $ expandToArity arity (CApp (CRef n) []) args
fixArityTm (CLam x ty sc) args
    = pure $ expandToArity Z (CLam x ty !(fixArityTm sc [])) args
fixArityTm (CPi  x ty sc) args
    = pure $ expandToArity Z (CPi  x ty !(fixArityTm sc [])) args
fixArityTm (CLet x val ty sc) args
    = pure $ expandToArity Z
                 (CLet x !(fixArityTm val []) ty !(fixArityTm sc [])) args
fixArityTm (CApp f fargs) args
    = fixArityTm f (!(traverse (\tm => fixArityTm tm []) fargs) ++ args)
fixArityTm (CCon n args) []
    = pure $ CCon n !(traverse (\tm => fixArityTm tm []) args)
fixArityTm (CConCase scr alts def) args
    = pure $ expandToArity Z
              (CConCase !(fixArityTm scr [])
                        !(traverse fixArityAlt alts)
                        !(traverseOpt (\tm => fixArityTm tm []) def)) args
  where
    fixArityAlt : CConAlt vars -> Core (CConAlt vars)
    fixArityAlt (MkConAlt n a sc)
        = pure $ MkConAlt n a !(fixArityTm sc [])
fixArityTm (CPrj con field x) args = pure $ expandToArity Z (CPrj con field !(fixArityTm x [])) args
fixArityTm t [] = pure t
fixArityTm t args = pure $ expandToArity Z t args

export
fixArityExp : {vars : _} ->
              {auto c : Ref Ctxt Defs} ->
              CExp vars -> Core (CExp vars)
fixArityExp tm = fixArityTm tm []

fixArity : {auto c : Ref Ctxt Defs} ->
           CDef -> Core CDef
fixArity (MkFun args ty exp) = pure $ MkFun args ty !(fixArityTm exp [])
fixArity d = pure d

getLams : {done : _} ->
          Int -> SubstCEnv done args -> CExp (done ++ args) ->
          Core (args' ** (SubstCEnv args' args, CExp (args' ++ args)))
getLams {done} i env (CLam x ty sc)
    = getLams {done = x :: done} (i + 1) (CRef (MN "ext" i) :: env) sc
getLams {done} i env sc = pure (done ** (env, sc))

mkBounds : (xs : _) -> Bounds xs
mkBounds [] = None
mkBounds (x :: xs) = Add x x (mkBounds xs)

getNewArgs : {done : _} ->
             SubstCEnv done args -> List Name
getNewArgs [] = []
getNewArgs (CRef n :: xs) = n :: getNewArgs xs
getNewArgs {done = x :: xs} (_ :: sub) = x :: getNewArgs sub

-- Move any lambdas in the body of the definition into the lhs list of vars.
-- Annoyingly, the indices will need fixing up because the order in the top
-- level definition goes left to right (i.e. first argument has lowest index,
-- not the highest, as you'd expect if they were all lambdas).
mergeLambdas : (args : List Name) -> CExp args -> Core (args' ** CExp args')
mergeLambdas args (CLam x ty sc)
    = do (args' ** (env, exp')) <- getLams 0 [] (CLam x ty sc)
         let expNs = substs env exp'
             newArgs = reverse $ getNewArgs env
             expLocs = mkLocals {outer=args} {vars = []} (mkBounds newArgs)
                        (rewrite appendNilRightNeutral args in expNs)
         pure (_ ** expLocs)
mergeLambdas args exp = pure (args ** exp)

doEval : {args : _} ->
         {auto c : Ref Ctxt Defs} ->
         {auto p : Ref Progress Bool} ->
         Name -> CExp args -> Core (CExp args)
doEval n exp
    = do l <- newRef LVar (the Int 0)
         log "compiler.inline.eval" 10 (show n ++ ": " ++ show exp)
         exp' <- eval [] [] [] exp
         log "compiler.inline.eval" 10 ("Inlined: " ++ show exp')
         pure exp'

inline : {auto c : Ref Ctxt Defs} ->
         {auto p : Ref Progress Bool} ->
         Name -> CDef -> Core CDef
inline n (MkFun args ty def)
    = pure $ MkFun args ty !(doEval n def)
inline n d = pure d

-- merge lambdas from expression into top level arguments
mergeLam : {auto c : Ref Ctxt Defs} ->
           CDef -> Core CDef
mergeLam (MkFun args ty def)
    = do (args' ** exp') <- mergeLambdas args def
         pure $ MkFun args' CErased exp' -- TODO merge types too!
mergeLam d = pure d

mutual
  addRefs : NameSet -> CExp vars -> NameSet
  addRefs ds (CRef n) = insert n ds
  addRefs ds (CLam _ _ sc) = addRefs ds sc
  addRefs ds (CPi  _ _ sc) = addRefs ds sc
  addRefs ds (CLet _ val _ sc) = addRefs (addRefs ds val) sc
  addRefs ds (CApp f args) = addRefsArgs (addRefs ds f) args
  addRefs ds (CCon n args) = addRefsArgs (insert n ds) args
  addRefs ds (CConCase sc alts def)
      = let ds' = maybe ds (addRefs ds) def in
            addRefsConAlts (addRefs ds' sc) alts
  addRefs ds (CPrj con field x) = addRefs (insert con ds) x
  addRefs ds tm = ds

  addRefsArgs : NameSet -> List (CExp vars) -> NameSet
  addRefsArgs ds [] = ds
  addRefsArgs ds (a :: as) = addRefsArgs (addRefs ds a) as

  addRefsConAlts : NameSet -> List (CConAlt vars) -> NameSet
  addRefsConAlts ds [] = ds
  addRefsConAlts ds (MkConAlt _ _ sc :: rest)
      = addRefsConAlts (addRefs ds sc) rest

getRefs : CDef -> NameSet
getRefs (MkFun args _ exp) = addRefs empty exp
getRefs _ = empty


export
inlineDef : {auto c : Ref Ctxt Defs} ->
            {auto p : Ref Progress Bool} ->
            Name -> Core ()
inlineDef n
    = do defs <- get Ctxt
         Just def <- lookupDef n defs   | Nothing => pure ()
         let Just cexpr = compexpr def  | Nothing => pure ()
         setCompiled n !(inline n cexpr)

export
fixArityDef : {auto c : Ref Ctxt Defs} ->
              Name -> Core ()
fixArityDef n
    = do defs <- get Ctxt
         Just def <- lookupDef n defs   | Nothing => pure ()
         let Just cexpr =  compexpr def | Nothing => pure ()
         setCompiled n !(fixArity cexpr)

export
mergeLamDef : {auto c : Ref Ctxt Defs} ->
              Name -> Core ()
mergeLamDef n
    = do defs <- get Ctxt
         Just def <- lookupDef n defs
              | Nothing => pure ()
         let PMDef _ _ _ _ = definition def
              | _ => pure ()
         let Just cexpr =  compexpr def
              | Nothing => pure ()
         setCompiled n !(mergeLam cexpr)

export
compileAndInline : {auto c : Ref Ctxt Defs} ->
                   List Name ->
                   Core ()
compileAndInline ns
    = do defs <- get Ctxt
         traverse_ compileDef ns
         -- TODO Should I not transform until no progress is made? And limit it by
         -- a global inliner limit option, like clash
         transform 128 ns
  where
    getDefs : List Name -> Core (List (Maybe CDef))
    getDefs = traverse (\c => do defs <- get Ctxt
                                 mgdef <- lookupDef c defs
                                 pure $ fromMaybe Nothing $ map compexpr mgdef)
    transform : Nat -> List Name -> Core ()
    transform Z cns = pure ()
    transform (S k) cns
        = do p <- newRef Progress False
             traverse_ inlineDef cns
             -- We assume that merging lambdas in definitions, and fixing their
             -- arity, do not create any more opportunities for reduction
             -- here... we only check if `inlineDef` has made progress
             traverse_ mergeLamDef cns
             --traverse_ caseLamDef cns
             traverse_ fixArityDef cns
             -- Exit early if no progress was made
             True <- get Progress
               | False => pure ()
             transform k cns

{-
-- TODO Let's lay off the case statement optimisations in toCExp and implement them in something
        like CaseOpt.idr instead. May be easier since we'll have already reduced con cases with a
        matching scrutinee. If we remove our let binding code that exists already, what rules do:

        1) The clash folk actually implement?
        2) The idris2 codebase already implement?
-}
