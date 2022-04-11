module Compiler.CompileExpr

import Core.CaseTree
import public Core.CompileExpr
import Core.Context
import Core.Env
import Core.Normalise
import Core.TT
import Core.Value
import Core.Extraction
import Core.UnifyState

import TTImp.ProcessData

import Data.List
import Data.Maybe
import Data.Vect

%default covering

||| Extract the number of arguments from a term, or return that it's
||| a newtype by a given argument position
numArgs : Defs -> Term vars -> Core Nat
numArgs defs (Ref _ n)
  = do Just gdef <- lookupDef n defs
         | Nothing => pure 0
       case definition gdef of
         (PMDef _ _ _ _)    => pure . extractionArity $ type gdef
         (DCon  _ _)    => pure . extractionArity $ type gdef
         (TCon _ _ _ _) => pure . extractionArity $ type gdef
         _ => pure 0
numArgs _ tm = pure 0

weakenVar : Var ns -> Var (a :: ns)
weakenVar (MkVar p) = (MkVar (Later p))

etaExpand : {vars : _} ->
            (name : Int) -> Nat -> CExp vars -> List (Var vars) -> CExp vars
etaExpand ni 0 exp args = mkApp exp (map mkLocal $ reverse args)
  where
  mkLocal : Var vars -> CExp vars
  mkLocal (MkVar p) = CLocal p
  mkApp : CExp vars -> List (CExp vars) -> CExp vars
  mkApp tm [] = tm
  mkApp (CApp f xs) args' = CApp f (xs ++ args')
  mkApp (CCon x xs) args' = CCon x (xs ++ args')
  mkApp tm args' = CApp tm args'
etaExpand ni (S k) exp args
  = CLam (MN "eta" ni)
         (etaExpand (ni+1) k (weaken exp) (MkVar First :: map weakenVar args))

export
expandToArity : {vars : _} ->
                Nat -> CExp vars -> List (CExp vars) -> CExp vars
-- No point in applying to anything
expandToArity _ CErased _ = CErased
-- Overapplied; apply everything as single arguments
expandToArity Z f args = applyAll f args
  where
  applyAll : CExp vars -> List (CExp vars) -> CExp vars
  applyAll fn [] = fn
  applyAll fn (a :: args) = applyAll (CApp fn [a]) args
expandToArity (S k) f (a :: args) = expandToArity k (addArg f a) args
  where
  addArg : CExp vars -> CExp vars -> CExp vars
  addArg (CApp fn args) a = CApp fn (args ++ [a])
  addArg (CCon n args) a = CCon n (args ++ [a])
  addArg f a = CApp f [a]
-- Underapplied, saturate with lambdas
expandToArity num fn [] = etaExpand 0 num fn []

erasedArgs : (ty : Term []) -> List Nat
erasedArgs ty = go 0 [] ty
  where
  go : Nat -> List Nat -> Term vars -> List Nat
  go i xs (Bind x (Pi k Implicit z) scope) = go (S i) (i :: xs) scope
  go i xs (Bind x (Pi k Explicit z) scope) = go (S i)       xs  scope
  go _ xs ty = xs

erasedArgsClosed : (ty : Term []) -> List Nat
erasedArgsClosed ty = go 0 [] ty
  where
  go : Nat -> List Nat -> Term vars -> List Nat
  go i xs (Bind x (Pi k _ z) scope) = go (S i) (i :: xs) scope
  go _ xs ty = xs

mkSub : Nat -> (ns : List Name) -> List Nat -> (ns' ** SubVars ns' ns)
mkSub i _ [] = (_ ** SubRefl)
mkSub i [] ns = (_ ** SubRefl)
mkSub i (x :: xs) es
  = let (ns' ** p) = mkSub (S i) xs es in
    if i `elem` es
       then (ns' ** DropCons p)
       else (x :: ns' ** KeepCons p)

mkDropSubst : Nat -> List Nat ->
             (rest : List Name) ->
             (vars : List Name) ->
             (vars' ** SubVars (vars' ++ rest) (vars ++ rest))
mkDropSubst i es rest [] = ([] ** SubRefl)
mkDropSubst i es rest (x :: xs)
  = let (vs ** sub) = mkDropSubst (1 + i) es rest xs in
    if i `elem` es
       then (vs ** DropCons sub)
       else (x :: vs ** KeepCons sub)

mutual
  toCExpTm : {vars : _} ->
             {auto c : Ref Ctxt Defs} ->
             Name -> Term vars ->
             Core (CExp vars)
  toCExpTm n (Local idx p) = pure $ CLocal p
  toCExpTm n (Meta x xs)
    = throw $ GenericMsg $ "Cannot compile unsolved metavar into CExp: " ++ show x
      -- Can return CErased if this causes problems
  toCExpTm n (App i f arg) = pure $ CApp !(toCExp n f) [!(toCExp n arg)]
  toCExpTm n TType = pure $ CCon (UN "Type") []
  toCExpTm n Erased = pure CErased
  toCExpTm n (Quote ty tm) = toCExp n tm
  toCExpTm n (TCode x) = toCExp n x
  toCExpTm n (Eval x) = toCExp n x
  toCExpTm n (Escape x) = toCExp n x
  toCExpTm n (Bind x (Lam _ _ ty) scope)
    = pure $ CLam x !(toCExp n scope)
  toCExpTm n (Bind x (Let _ val _) scope)
    = pure $ CLet x !(toCExp n val) Erased !(toCExp n scope)
  toCExpTm n (Bind x _ scope) = pure CErased -- Ignore pat vars, etc.
  toCExpTm n (Ref nt nm) = toCExpRef nm

  toCExpRef : {vars : _} ->
              {auto c : Ref Ctxt Defs} ->
              Name ->
              Core (CExp vars)
  toCExpRef n
    = do defs <- get Ctxt
         Just gdef <- lookupDef n defs
           | Nothing => throw $ GenericMsg $ "Name undefined in context: " ++ show n
         when (isNothing $ compexpr gdef)
              (compileDef False n)
         case definition gdef of
           (PMDef args _ treeCT _) => pure $ CRef n
           (DCon tag arity) =>  pure $ CCon n []
           (TCon x tag arity cons) => pure $ CCon n []
           def => throw $ GenericMsg $ "Cannot compile definition to CExp: " ++ show def

  toCExp : {vars : _} ->
           {auto c : Ref Ctxt Defs} ->
           Name -> Term vars ->
           Core (CExp vars)
  toCExp n tm
    = do let (f,args) = getFnArgs tm
         args' <- traverse (toCExp n) args
         defs <- get Ctxt
         f' <- toCExpTm n f
         a <- numArgs defs f
         pure $ expandToArity a f' args'

  conCases : {vars : _} ->
             {auto c : Ref Ctxt Defs} ->
             Name -> List (CaseAlt vars) ->
             Core (List (CConAlt vars))
  conCases n [] = pure []
  conCases n ((ConCase x tag args sc) :: xs)
    = do defs <- get Ctxt
         Just gdef <- lookupDef x defs
           | Nothing => throw $ InternalError $
               "Constructor name used in case alt not found in context: " ++ show x
         gdef <- extractionGlobalDef gdef
         let (args' ** sub)
              = mkDropSubst 0 (erasedArgs $ type gdef) vars args
         sc' <- toCExpTree n sc
         xs' <- conCases n xs
         let erasedSc = shrinkCExp sub sc'
         pure $ MkConAlt x args' erasedSc :: xs'
    where

  conCases n ((QuoteCase ty arg x) :: xs) = conCases n xs
  conCases n ((DefaultCase x) :: xs) = conCases n xs

  getDefault : {vars : _} ->
               {auto c : Ref Ctxt Defs} ->
               Name -> List (CaseAlt vars) ->
               Core (Maybe (CExp vars))
  getDefault n [] = pure Nothing
  getDefault n (DefaultCase sc :: ns)
    = pure $ Just !(toCExpTree n sc)
  getDefault n (_ :: ns) = getDefault n ns

  toCExpTree : {vars : _} ->
               {auto c : Ref Ctxt Defs} ->
               Name -> CaseTree vars ->
               Core (CExp vars)
  toCExpTree n (STerm x) = toCExp n x
  toCExpTree n Impossible = pure CErased
  toCExpTree n (Unmatched msg) = throw $ InternalError $
    "Encountered unnmatched case when compiling: " ++ show n
  toCExpTree n (Case idx p scTy []) = throw $ InternalError $
    "Encountered unnmatched case when compiling: " ++ show n
  toCExpTree n (Case idx p scTy alts@((ConCase _ _ _ _) :: _))
    = do cases <- conCases n alts
         def <- getDefault n alts
         case cases of
           [] => pure $ fromMaybe CErased def
           _ => do pure $ CConCase (CLocal p) cases def
  toCExpTree n (Case idx p scTy alts@((QuoteCase ty arg sc) :: _))
    = do sc' <- toCExpTree n sc
         let scNoType = shrinkCExp (DropCons SubRefl) sc'
         let scNoPrjArg = substs [CLocal p] scNoType
         pure scNoPrjArg
  toCExpTree n (Case idx p scTy alts@((DefaultCase sc) :: _)) = toCExpTree n sc

  toCDef : {auto c : Ref Ctxt Defs} ->
           Bool -> Name -> Term [] -> Def ->
           Core CDef
  toCDef topLevel n ty (PMDef args _ treeCT _)
    = do let erased = if topLevel
                         then erasedArgsClosed ty
                         else erasedArgs ty
         let (args' ** p) = mkSub 0  args erased
         comptree <- toCExpTree n treeCT
         pure $ MkFun args' (shrinkCExp p comptree)
  toCDef _ n ty (DCon tag _)
    = do let arity = extractionArity ty
         pure $ MkCon (Just tag) arity
  toCDef _ n ty (TCon x tag _ cons)
    = do let arity = extractionArity ty
         pure $ MkCon (Just tag) arity
  toCDef _ n ty Hole
    = throw $ GenericMsg $ "Cannot compile a Hole to CDef: " ++ show n
  toCDef _ n ty (Guess guess constraints)
    = throw $ GenericMsg $ "Cannot compile a Guess to CDef: " ++ show n
  toCDef _ n ty None
    = throw $ GenericMsg $ "Cannot compile a None to CDef: " ++ show n

  ||| Given a name, look up an expression, and compile it to a CExp in the environment
  export
  compileDef : {auto c : Ref Ctxt Defs} -> Bool -> Name -> Core ()
  compileDef topLevel n
    = do defs <- get Ctxt
         Just gdef <- lookupDef n defs
           | Nothing => throw $ InternalError $ "Cannot compile unkonwn name: " ++ show n

         when (isJust $ compexpr gdef)
              (pure ())

         gdef <- extractionGlobalDef gdef
         -- Set placeholder compiled expression to prevent loops with mutually recursive definitions
         setCompiled n (MkCon Nothing 0)
         compexpr <- toCDef topLevel n (type gdef) (definition gdef)
         setCompiled n compexpr

export
closedQuoteType : Term [] -> Core (List (Term []),Term[])
--       ^ Arg types    ^ Ret type
closedQuoteType (Bind _ _ sc) = closedQuoteType $ subst Erased sc
closedQuoteType (TCode ty) = getTys [] ty
  where
  getTys : List (Term []) -> Term [] -> Core (List (Term []), Term [])
  getTys args (Bind _ (Pi _ Explicit ty) sc) = getTys (ty::args) (subst Erased sc)
  getTys args (Bind _ (Pi _ Implicit ty) sc) = getTys args (subst Erased sc)
  getTys args tm                      = pure (args, tm)
closedQuoteType ty = throw $ InternalError $ "Expected scope to be a quoted function but got: " ++ show ty

export
checkSynthesisableArgTy : {auto c : Ref Ctxt Defs} ->
                          {auto u : Ref UST UState} ->
                          List (Term []) -> Term [] -> Core ()
checkSynthesisableArgTy recTys ty
  = do when (ty `elem` recTys)
            (throw $ GenericMsg $ "Unbounded recursion in argument type: " ++ show ty)

       -- Is our argument a simple type constructor
       let Just tyconn = getTyConName ty
             | Nothing => throw $ GenericMsg $ "Arguement type is not synthesisable: " ++ show ty
       defs <- get Ctxt
       Just (MkGlobalDef _ (TCon info _ _  _) _) <- lookupDef tyconn defs
         | _ => throw $ GenericMsg $ "Argument type is not a type constructor: " ++ show ty
       when (isParam info)
            (throw $ GenericMsg $ "Argument is a parameter type: " ++ show ty)

       -- Are all explicit args of all data constructors also synthesisable?
       -- We need spot non-terminating recursion by tracking generated return types too
       dcons <- dataConsForType [] ty
       traverse_ (allArgsSynth (ty :: recTys)) $ map snd dcons
  where
  allArgsSynth : List (Term []) -> (ty : Term []) -> Core ()
  allArgsSynth recTys (Bind n b@(Pi s Implicit ty) sc) = allArgsSynth recTys (subst Erased sc)
  allArgsSynth recTys (Bind n b@(Pi s Explicit ty) sc)
    = do checkSynthesisableArgTy recTys ty
         allArgsSynth recTys (subst Erased sc)
  allArgsSynth recTys ty = pure ()

export
checkSynthesisable : {auto c : Ref Ctxt Defs} -> Name -> Core ()
checkSynthesisable n
  = do defs <- get Ctxt
       Just ty <- lookupDefType n defs
         | Nothing => throw $ GenericMsg $ "Couldn't find name in context: " ++ show n
       -- Check that each codefn arg is synthesisable
       (args, ret) <- closedQuoteType ty
       u <- newRef UST initUState
       traverse_ (checkSynthesisableArgTy []) (ret :: args)
