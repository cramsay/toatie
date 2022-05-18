module Core.Normalise

import Core.CaseTree
import Core.Context
import Core.Env
import Core.TT
import Core.Value

import Data.Nat
import Data.Vect

public export
data EvalMode = NoLets | KeepLets

-- A pair of a term and its normal form. This could be constructed either
-- from a term (via 'gnf') or a normal form (via 'glueBack') but the other
-- part will only be constructed when needed, because it's in Core.
public export
data Glued : List Name -> Type where
     MkGlue : Core (Term vars) ->
              (Ref Ctxt Defs -> Core (NF vars)) -> Glued vars

export
getTerm : Glued vars -> Core (Term vars)
getTerm (MkGlue tm _) = tm

export
getNF : {auto c : Ref Ctxt Defs} -> Glued vars -> Core (NF vars)
getNF {c} (MkGlue _ nf) = nf c

Stack : List Name -> Type
Stack vars = List (AppInfo, Closure vars)

export
evalClosure : {free : _} -> Defs -> EvalMode -> Closure free -> Core (NF free)

export
toClosure : Env Term outer -> Term outer -> Closure outer
toClosure env tm = MkClosure [] env tm

data CaseResult a
     = Result a
     | NoMatch -- case alternative didn't match anything
     | GotStuck -- alternative matched, but got stuck later

-- So that we can call 'eval' with new defs
evalTop : {free, vars : _} ->
          Defs -> EvalMode -> Env Term free -> LocalEnv free vars ->
          Term (vars ++ free) -> Stack free -> Core (NF free)

export
data QVar : Type where

quoteGenNF : {bound, vars : _} ->
             Ref QVar Int ->
             Defs -> EvalMode -> Bounds bound ->
             Env Term vars -> NF vars -> Core (Term (bound ++ vars))

parameters (defs : Defs)
  mutual
    eval : {free, vars : _} ->
           EvalMode ->
           Env Term free -> LocalEnv free vars ->
           Term (vars ++ free) -> Stack free -> Core (NF free)
    eval mode env locs (Local idx prf) stk
        = evalLocal mode env idx prf stk locs
    eval mode env locs (Ref nt fn) stk
        = evalRef mode env nt fn stk (NApp (NRef nt fn) stk)
    eval mode {vars} {free} env locs (Meta name args) stk
        = evalMeta mode env name (map (MkClosure locs env) args) stk
    eval mode env locs (Bind x (Lam s _ ty) scope) (thunk :: stk)
        = eval mode env (snd thunk :: locs) scope stk
    eval KeepLets env locs (Bind x b@(Let s tm ty) scope) stk
        = do let b' = map (MkClosure locs env) b
             pure $ NBind x b' (\defs', arg => evalTop defs' KeepLets env (arg :: locs) scope stk)
    eval NoLets env locs (Bind x b@(Let s tm ty) scope) stk
        = eval NoLets env (MkClosure locs env tm :: locs) scope stk
    eval mode env locs (Bind x b scope) stk
        = do let b' = map (MkClosure locs env) b
             pure $ NBind x b'
                      (\defs', arg => evalTop defs' mode env (arg :: locs) scope stk)
    eval mode env locs (App info fn arg) stk
        = eval mode env locs fn ((info, MkClosure locs env arg) :: stk)
    eval mode env locs TType stk = pure NType
    eval mode env locs Erased stk = pure NErased
    eval mode env locs (Quote ty tm) stk -- Quote defers evaluation
        = pure $ NQuote (MkClosure locs env ty) (MkClosure locs env tm)
    eval mode env locs (TCode  tm) stk
        = do tm' <- eval mode env locs tm stk
             pure $ NCode tm'
    eval mode env locs (Eval tm) stk -- Keep Eval Mode simple since we only want this for closed terms
        = do (NQuote _ tm') <- eval mode env locs tm stk
               | tm' => throw (GenericMsg $ "Eval Mode on unquoted term: " ++ show tm')
             evalLocClosure mode env stk tm'
    eval mode env locs (Escape tm) stk
        = do -- Version for single eval mode on escaped term
             tm' <- eval mode env locs tm []
             ---- Version for full eval.quote.eval mode on escaped term
             --tmNorm <- quoteGenNF !(newRef QVar 0) defs None env !(eval mode env locs tm [])
             --tm' <- eval mode env locs (weakenNs vars tmNorm) stk
             case tm' of
               -- Resolve Escaped NQuote to new local var
               (NQuote _ arg) => eval mode env (arg :: locs) (Local {name = UN "fvar"} _ First) stk
               -- Keep NEscape tag for any other (probably stuck) terms
               otherwise    => pure $ NEscape tm' stk

    evalLocClosure : {free : _} ->
                     EvalMode ->
                     Env Term free ->
                     Stack free ->
                     Closure free ->
                     Core (NF free)
    evalLocClosure mode env stk (MkClosure locs' env' tm')
        = eval mode env' locs' tm' stk

    evalLocal : {free, vars : _} ->
                EvalMode ->
                Env Term free ->
                (idx : Nat) -> (0 p : IsVar name idx (vars ++ free)) ->
                Stack free ->
                LocalEnv free vars ->
                Core (NF free)
    -- If it's one of the free variables, we are done
    -- (Idris 2 has Let bindings, which we'd need to check and evaluate here)
    evalLocal {vars = []} mode env idx prf stk locs
        = case getBinder prf env of
                 Let _ val _ => eval mode env [] val stk
                 _           => pure $ NApp (NLocal idx prf) stk
    evalLocal mode env Z First stk (x :: locs)
        = evalLocClosure mode env stk x
    evalLocal {vars = x :: xs} {free}
              mode env (S idx) (Later p) stk (_ :: locs)
        = evalLocal {vars = xs} mode env idx p stk locs

    evalMeta : {free : _} ->
               EvalMode ->
               Env Term free ->
               Name -> List (Closure free) ->
               Stack free -> Core (NF free)
    evalMeta mode env nm args stk
        = evalRef mode env Func nm ((map (\x=>(AExplicit,x)) args) ++ stk) (NApp (NMeta nm args) stk)
          -- TODO, I don't think we should be assuming Meta vars use their args explicitly here

    evalRef : {free : _} ->
              EvalMode ->
              Env Term free ->
              NameType -> Name -> Stack free -> (def : Lazy (NF free)) ->
              Core (NF free)
    -- if it's a constructor, no need to look it up
    evalRef mode env (DataCon tag arity) fn stk def
        = pure $ NDCon fn tag arity stk
    evalRef mode env (TyCon info tag arity) fn stk def
        = pure $ NTCon fn info tag arity stk
    evalRef mode env Bound fn stk def
        = pure def
    evalRef mode env nt n stk def
        = do Just res <- lookupDef n defs
                  | Nothing => pure def
             evalDef mode env (definition res) stk def

    getCaseBound : List (AppInfo, Closure free) ->
                   (args : List Name) ->
                   LocalEnv free more ->
                   Maybe (LocalEnv free (args ++ more))
    getCaseBound []            []        loc = Just loc
    getCaseBound []            (_ :: _)  loc = Nothing -- mismatched arg length
    getCaseBound (arg :: args) []        loc = Nothing -- mismatched arg length
    getCaseBound (arg :: args) (n :: ns) loc = (snd arg ::) <$> getCaseBound args ns loc

    evalConAlt : {more, free : _} ->
                 EvalMode ->
                 Env Term free ->
                 LocalEnv free more ->
                 Stack free ->
                 (args : List Name) ->
                 List (AppInfo, Closure free) ->
                 CaseTree (args ++ more) ->
                 Core (CaseResult (NF free))
    evalConAlt mode env loc stk args args' sc
         = do let Just bound = getCaseBound args' args loc
                   | Nothing => pure GotStuck
              evalTree mode env bound stk sc

    tryAlt : {free, more : _} ->
             EvalMode ->
             Env Term free ->
             LocalEnv free more ->
             Stack free -> NF free -> CaseAlt more ->
             Core (CaseResult (NF free))
    -- Ordinary constructor matching
    tryAlt {more} mode env loc stk (NDCon nm tag' arity args') (ConCase x tag args sc)
         = if tag == tag'
              then evalConAlt mode env loc stk args args' sc
              else pure NoMatch
    -- Quote matching
    tryAlt {more} mode env loc stk (NQuote ty arg) (QuoteCase tyn argn sc)
        = evalTree mode env (ty :: arg :: loc) stk sc
    -- Default case matches against any *concrete* value
    tryAlt mode env loc stk val (DefaultCase sc)
         = if concrete val
              then evalTree mode env loc stk sc
              else pure GotStuck
      where
        concrete : NF free -> Bool
        concrete (NDCon _ _ _ _) = True
        concrete _ = False
    tryAlt _ _ _ _ _ _ = pure GotStuck

    findAlt : {args, free : _} ->
              EvalMode ->
              Env Term free ->
              LocalEnv free args ->
              Stack free -> NF free -> List (CaseAlt args) ->
              Core (CaseResult (NF free))
    findAlt mode env loc stk val [] = pure GotStuck
    findAlt mode env loc stk val (x :: xs)
         = do Result val <- tryAlt mode env loc stk val x
                   | NoMatch => findAlt mode env loc stk val xs
                   | GotStuck => pure GotStuck
              pure (Result val)

    evalTree : {args, free : _} -> EvalMode -> Env Term free -> LocalEnv free args ->
               Stack free -> CaseTree args ->
               Core (CaseResult (NF free))
    evalTree mode env loc stk (Case idx x _ alts)
      = do xval <- evalLocal mode env idx (varExtend x) [] loc
           -- Idris 2 also updates the local environment here, to save
           -- recomputing, but it involves a slightly trickier definition
           -- of closures, so we'll just carry on
           findAlt mode env loc stk xval alts
    evalTree mode env loc stk (STerm tm)
          = do res <- eval mode env loc (embed tm) stk
               pure (Result res)
    evalTree mode env loc stk _ = pure GotStuck

    -- Take arguments from the stack, as long as there's enough.
    -- Returns the arguments, and the rest of the stack
    takeFromStack : (arity : Nat) -> Stack free ->
                    Maybe (Vect arity (AppInfo, Closure free), Stack free)
    takeFromStack arity stk = takeStk arity stk []
      where
        takeStk : (remain : Nat) -> Stack free ->
                  Vect got (AppInfo, Closure free) ->
                  Maybe (Vect (got + remain) (AppInfo, Closure free), Stack free)
        takeStk {got} Z stk acc = Just (rewrite plusZeroRightNeutral got in
                                    reverse acc, stk)
        takeStk (S k) [] acc = Nothing
        takeStk {got} (S k) (arg :: stk) acc
           = rewrite sym (plusSuccRightSucc got k) in
                     takeStk k stk (arg :: acc)

    argsFromStack : (args : List Name) ->
                    Stack free ->
                    Maybe (LocalEnv free args, Stack free)
    argsFromStack [] stk = Just ([], stk)
    argsFromStack (n :: ns) [] = Nothing
    argsFromStack (n :: ns) (arg :: args)
         = do (loc', stk') <- argsFromStack ns args
              pure (snd arg :: loc', stk')

    export
    evalDef : {free : _} ->
              EvalMode ->
              Env Term free ->
              Def ->
              Stack free -> (def : Lazy (NF free)) ->
              Core (NF free)
    evalDef mode env (PMDef args treect _ _) stk def
        = case argsFromStack args stk of
               Nothing => pure def
               Just (locs', stk') =>
                    do Result res <- evalTree mode env locs' stk' treect
                            | _ => pure def
                       pure res
    evalDef mode env _ stk def = pure def

evalClosure mode defs (MkClosure locs env tm)
    = eval mode defs env locs tm []

evalTop defs mode = eval defs mode

export
nf : {vars : _} ->
     Defs -> EvalMode -> Env Term vars -> Term vars -> Core (NF vars)
nf defs mode env tm = eval defs mode env [] tm []

export
gnf : {vars : _} ->
      EvalMode -> Env Term vars -> Term vars -> Glued vars
gnf mode env tm
    = MkGlue (pure tm)
             (\c => do defs <- get Ctxt
                       nf defs mode env tm)
export
gType : Glued vars
gType = MkGlue (pure TType) (const (pure NType))

public export
interface Quote (0 tm : List Name -> Type) where
    quote : {vars : _} ->
            Defs -> EvalMode -> Env Term vars -> tm vars -> Core (Term vars)
    quoteGen : {vars : _} ->
               Ref QVar Int -> Defs -> EvalMode -> Env Term vars ->
               tm vars -> Core (Term vars)

    quote defs mode env tm
        = do q <- newRef QVar 0
             quoteGen q defs mode env tm

genName : {auto q : Ref QVar Int} -> String -> Core Name
genName n
    = do i <- get QVar
         put QVar (i + 1)
         pure (MN n i)

mutual
  quoteArgs : {bound, free : _} ->
              Ref QVar Int -> Defs -> EvalMode -> Bounds bound ->
              Env Term free -> List (AppInfo, Closure free) ->
              Core (List (AppInfo, Term (bound ++ free)))
  quoteArgs q defs mode bounds env [] = pure []
  quoteArgs q defs mode bounds env ((ia,a) :: args)
      = pure $ ( (ia, !(quoteGenNF q defs mode bounds env !(evalClosure defs mode a))) ::
                !(quoteArgs q defs mode bounds env args))

  quoteHead : {bound, free : _} ->
              Ref QVar Int -> Defs ->
              EvalMode ->
              Bounds bound -> Env Term free -> NHead free ->
              Core (Term (bound ++ free))
  quoteHead {bound} q defs mode bounds env (NLocal _ prf)
      = let MkVar prf' = addLater bound prf in
            pure $ Local _ prf'
    where
      addLater : {idx : _} ->
                 (ys : List Name) -> (0 p : IsVar n idx xs) ->
                 Var (ys ++ xs)
      addLater [] isv = MkVar isv
      addLater (x :: xs) isv
          = let MkVar isv' = addLater xs isv in
                MkVar (Later isv')
  quoteHead q defs mode bounds env (NRef Bound (MN n i))
      = case findName bounds of
             Just (MkVar p) => pure $ Local _ (varExtend p)
             Nothing => pure $ Ref Bound (MN n i)
    where
      findName : Bounds bound' -> Maybe (Var bound')
      findName None = Nothing
      findName (Add x (MN n' i') ns)
          = if i == i' -- this uniquely identifies it, given how we
                       -- generated the names, and is a faster test!
               then Just (MkVar First)
               else do MkVar p <-findName ns
                       Just (MkVar (Later p))
      findName (Add x _ ns)
          = do MkVar p <- findName ns
               Just (MkVar (Later p))
  quoteHead q defs mode bounds env (NRef nt n) = pure $ Ref nt n
  quoteHead q defs mode bounds env (NMeta n args)
      = do args' <- quoteArgs q defs mode bounds env (map (\x=>(AExplicit,x)) args)
           pure $ Meta n (map snd args')

  quoteBinder : {bound, free : _} ->
                Ref QVar Int -> Defs -> EvalMode -> Bounds bound ->
                Env Term free -> Binder (Closure free) ->
                Core (Binder (Term (bound ++ free)))
  quoteBinder q defs mode bounds env (Lam s p ty)
      = do ty' <- quoteGenNF q defs mode bounds env !(evalClosure defs mode ty)
           pure (Lam s p ty')
  quoteBinder q defs mode bounds env (Pi s p ty)
      = do ty' <- quoteGenNF q defs mode bounds env !(evalClosure defs mode ty)
           pure (Pi s p ty')
  quoteBinder q defs mode bounds env (Let s val ty)
      = do val' <- quoteGenNF q defs mode bounds env !(evalClosure defs mode val)
           ty'  <- quoteGenNF q defs mode bounds env !(evalClosure defs mode ty)
           pure (Let s val' ty')
  quoteBinder q defs mode bounds env (PVar s i ty)
      = do ty' <- quoteGenNF q defs mode bounds env !(evalClosure defs mode ty)
           pure (PVar s i ty')
  quoteBinder q defs mode bounds env (PVTy s ty)
      = do ty' <- quoteGenNF q defs mode bounds env !(evalClosure defs mode ty)
           pure (PVTy s ty')

  quoteGenNF q defs mode bound env (NBind n b sc)
      = do var <- genName "qv"
           sc' <- quoteGenNF q defs mode (Add n var bound) env
                       !(sc defs (toClosure env (Ref Bound var)))
           b' <- quoteBinder q defs mode bound env b
           pure (Bind n b' sc')
  quoteGenNF q defs mode bound env (NApp f args)
      = do f' <- quoteHead q defs mode bound env f
           args' <- quoteArgs q defs mode bound env args
           pure $ apply f' args'
  quoteGenNF q defs mode bound env (NDCon n t ar args)
      = do args' <- quoteArgs q defs mode bound env args
           pure $ apply (Ref (DataCon t ar) n) args'
  quoteGenNF q defs mode bound env (NTCon n info t ar args)
      = do args' <- quoteArgs q defs mode bound env args
           pure $ apply (Ref (TyCon info t ar) n) args'
  quoteGenNF q defs _ bound env NErased = pure Erased
  quoteGenNF q defs _ bound env NType = pure TType
  quoteGenNF q defs mode bound env (NQuote ty tm)
      = do tmNf <- evalClosure defs mode tm
           tm' <- quoteGenNF q defs mode bound env tmNf
           tyNf <- evalClosure defs mode ty
           ty' <- quoteGenNF q defs mode bound env tyNf
           pure $ Quote ty' tm'
  quoteGenNF q defs mode bound env (NCode  tm)
      = pure $ TCode !(quoteGenNF q defs mode bound env tm)
  quoteGenNF q defs mode bound env (NEscape tm args)
      = do args' <- quoteArgs q defs mode bound env args
           case tm of
             NQuote ty arg => do argNf <- evalClosure defs mode arg
                                 pure $ apply !(quoteGenNF q defs mode bound env argNf) args'
             otherwise => pure $ apply (Escape !(quoteGenNF q defs mode bound env tm)) args'

export
Quote NF where
  quoteGen q defs mode env tm = quoteGenNF q defs mode None env tm

export
Quote Term where
  quoteGen q defs mode env tm = pure tm

export
Quote Closure where
  quoteGen q defs mode env c = quoteGen q defs mode env !(evalClosure defs mode c)

export
glueBack : {vars : _} ->
           Defs -> EvalMode -> Env Term vars -> NF vars -> Glued vars
glueBack defs mode env nf
    = MkGlue (do empty <- clearDefs defs
                 quote empty mode env nf)
             (const (pure nf))

export
normalise : {free : _} ->
            Defs -> EvalMode -> Env Term free -> Term free -> Core (Term free)
normalise defs mode env tm = quote defs mode env !(nf defs mode env tm)

public export
interface Convert (tm : List Name -> Type) where
  convert : {vars : _} ->
            Defs -> EvalMode -> Env Term vars ->
            tm vars -> tm vars -> Core Bool
  convGen : {vars : _} ->
            Ref QVar Int ->
            Defs -> EvalMode -> Env Term vars ->
            tm vars -> tm vars -> Core Bool

  convert defs mode env tm tm'
      = do q <- newRef QVar 0
           convGen q defs mode env tm tm'


mutual
  allConv : {vars : _} ->
            Ref QVar Int -> Defs -> EvalMode -> Env Term vars ->
            List (AppInfo, Closure vars) -> List (AppInfo, Closure vars) -> Core Bool
  allConv q defs mode env [] [] = pure True
  allConv q defs mode env ((ix,x) :: xs) ((iy,y) :: ys)
      = pure $ ix == iy &&
               !(convGen q defs mode env x y) && !(allConv q defs mode env xs ys)
  allConv q defs _ env _ _ = pure False

  chkConvHead : {vars : _} ->
                Ref QVar Int -> Defs -> EvalMode -> Env Term vars ->
                NHead vars -> NHead vars -> Core Bool
  chkConvHead q defs mode env (NLocal idx _) (NLocal idx' _) = pure $ idx == idx'
  chkConvHead q defs mode env (NRef _ n) (NRef _ n') = pure $ n == n'
  chkConvHead q defs mode env (NMeta n args) (NMeta n' args')
     = if n == n'
          then allConv q defs mode env (map (\x=>(AExplicit,x)) args)
                                       (map (\x=>(AExplicit,x)) args')
          else pure False
  chkConvHead q defs _ env _ _ = pure False

  convBinders : {vars : _} ->
                Ref QVar Int -> Defs -> EvalMode -> Env Term vars ->
                Binder (Closure vars) -> Binder (Closure vars) -> Core Bool
  convBinders q defs mode env (Pi _ ix tx) (Pi _ iy ty)
      = convGen q defs mode env tx ty
  convBinders q defs mode env (Lam _ ix tx) (Lam _ iy ty)
      = convGen q defs mode env tx ty
  convBinders q defs mode env bx by
      = pure False

  export
  Convert NF where
    convGen q defs mode env (NBind x b sc) (NBind x' b' sc')
        = do var <- genName "conv"
             let c = MkClosure [] env (Ref Bound var)
             bok <- convBinders q defs mode env b b'
             if bok
                then do bsc <- sc defs c
                        bsc' <- sc' defs c
                        convGen q defs mode env bsc bsc'
                else pure False
    -- Can also do eta conversion here, but let's skip that for simplicity
    -- EXERCISE (Medium): How would you add it? How would you test it?

    convGen q defs mode env (NApp val args) (NApp val' args')
        = if !(chkConvHead q defs mode env val val')
             then allConv q defs mode env args args'
             else pure False

    convGen q defs mode env (NDCon nm tag _ args) (NDCon nm' tag' _ args')
        = if tag == tag'
             then allConv q defs mode env args args'
             else pure False
    convGen q defs mode env (NTCon info nm tag _ args) (NTCon info' nm' tag' _ args')
        = if nm == nm' && info == info'
             then allConv q defs mode env args args'
             else pure False
    convGen q defs mode env NErased _ = pure True
    convGen q defs mode env _ NErased = pure True
    convGen q defs mode env NType NType = pure True
    convGen q defs mode env (NQuote _ x) (NQuote _ y) = convGen q defs mode env x y
    convGen q defs mode env (NCode  x) (NCode  y) = convGen q defs mode env x y
    convGen q defs mode env x y = pure False

  export
  Convert Term where
    convGen q defs mode env x y
        = convGen q defs mode env !(nf defs mode env x) !(nf defs mode env y)

  export
  Convert Closure where
    convGen q defs mode env x y
        = convGen q defs mode env !(evalClosure defs mode x) !(evalClosure defs mode y)

export
getValArity : {vars : _} ->
              Defs -> Env Term vars -> NF vars -> Core Nat
getValArity defs env (NBind x (Pi _ _ _) sc)
    = pure (S !(getValArity defs env !(sc defs (toClosure env Erased))))
getValArity defs env val = pure 0

export
getArity : {vars : _} ->
           Defs -> EvalMode -> Env Term vars -> Term vars -> Core Nat
getArity defs mode env tm = getValArity defs env !(nf defs mode env tm)

