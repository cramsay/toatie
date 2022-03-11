module Core.Extraction

import Core.TT
import Core.CaseTree
import Core.Context
import Core.Env

-- Extraction, as defined by Barras in "The Implicit Calculus of Constructions
-- as a Programming Language with Dependent Types"
export
extraction : {vars:_} -> Term vars -> Term vars

-- Binders
extraction (Bind n (Lam s Implicit ty) scope)
  = subst Erased (extraction scope) -- Forcing the type a little by substituting any lam-bound names with Erased...
                                    -- Paper says this function is only for well-typed terms, so -\_(`,`)_/-
extraction (Bind n (Lam s Explicit ty) scope)
  = Bind n (Lam s Explicit (extraction ty)) (extraction scope)
extraction (Bind n (Pi  s Implicit ty) scope)
    -- We're not going to ICC, so just keep implicit Pi instead of forall
  = Bind n (Pi s Implicit (extraction ty)) (extraction scope)
extraction (Bind n (Pi  s Explicit ty) scope)
  = Bind n (Pi s Explicit (extraction ty)) (extraction scope)
extraction (Bind n (Let s val ty) scope)
  = Bind n (Let s (extraction val) (extraction ty)) (extraction scope)
extraction (Bind n (PVar s i ty) scope)
  = Bind n (PVar s i (extraction ty)) (extraction scope)
extraction (Bind n (PVTy s ty) scope)
  = Bind n (PVTy s (extraction ty)) (extraction scope)

-- Application
extraction (App AImplicit f a) = extraction f
extraction (App AExplicit f a) = App AExplicit (extraction f) (extraction a)

extraction (Local idx p) = Local idx p -- Should I be doing this with reference to an env/stack?
extraction (Ref nt n) = Ref nt n       -- Same as above
extraction (Meta n args) = Meta n (map extraction args)
extraction TType = TType
extraction Erased = Erased
extraction (Quote ty tm) = Quote (extraction ty) (extraction tm)
extraction (TCode  tm) = TCode  (extraction tm)
extraction (Eval   tm) = Eval   (extraction tm)
extraction (Escape tm) = Escape (extraction tm)

export
extractionArity : Term vars -> Nat
extractionArity (Bind x (Lam k Implicit z) scope) = extractionArity scope
extractionArity (Bind x (Lam k Explicit z) scope) = S $ extractionArity scope
extractionArity (Bind x (Pi k Implicit z) scope) = extractionArity scope
extractionArity (Bind x (Pi k Explicit z) scope) = S $ extractionArity scope
extractionArity _ = 0

erasedVars : Nat -> Term vars -> List Nat
erasedVars i (Bind _ b sc) = i :: erasedVars (S i) sc
erasedVars i tm = []

mutual
  extractionDef : (ty : Term []) -> Def -> Core Def
  extractionDef _  None = pure None
  extractionDef ty (DCon   tag arity     ) = pure $ DCon   tag (extractionArity ty)
  extractionDef ty (TCon x tag arity cons) = pure $ TCon x tag (extractionArity ty) cons
  extractionDef _  Hole = pure Hole
  extractionDef _  (Guess guess constraints) = pure $ Guess (extraction guess) constraints -- TODO update constraints or forbid this
  extractionDef ty (PMDef args ct rt pats) = pure $ PMDef args ct !(extractTree (erasedVars 0 ty) rt) pats

  extractTree : {args : _} -> List Nat -> CaseTree args -> Core (CaseTree args)
  extractTree es (Case idx p scTy xs)
    = if idx `elem` es
         then case xs of
                [(ConCase n tag args sc)]
                  => do -- substitute args as eraseds and call sc
                        let es' = [0 .. length args] ++ map (+(length args)) es
                        sc' <- extractTree es' sc
                        ?extractTreeC --pure $ substsTree (substsEnvArgs args) sc'
                [(QuoteCase ty arg sc)]
                  => -- substitute ty and arg as erased args and call sc
                     do let es' = 0 :: 1 :: map (+2) es
                        sc' <- extractTree es' sc
                        ?extractTreeQ --pure $ substsTree [Erased, Erased] sc'
                [(DefaultCase sc)]
                  => extractTree es sc -- We don't introduce any new projected vars here, so we're all good
                _ => throw $ InternalError $ "Case on erased argument doesn't have only one branch: " ++ show (nameAt idx p)
         else do alts' <- traverse (extractAlt es) xs
                 -- TODO check which constructor args are implicit and be sure to mark them as implicit
                 pure $ Case idx p (extraction scTy) alts'
    where
    substsEnvArgs : (args : List Name) -> SubstEnv args var
    substsEnvArgs [] = []
    substsEnvArgs (a::as) = Erased :: substsEnvArgs as
  extractTree es (STerm x)            = pure . STerm $ extraction x
  extractTree es (Unmatched msg)      = pure $ Unmatched msg
  extractTree es Impossible           = pure $ Impossible

  extractAlt : {args : _} -> List Nat -> CaseAlt args -> Core (CaseAlt args)
  extractAlt es (ConCase x tag ys y) = pure $ ConCase x tag ys !(extractTree es y)
  extractAlt es (QuoteCase ty x ct)  = pure $ QuoteCase ty x !(extractTree es ct)
  extractAlt es (DefaultCase x     ) = pure $ DefaultCase !(extractTree es x)

export
extractionGlobalDef : GlobalDef -> Core GlobalDef
extractionGlobalDef (MkGlobalDef ty def) = pure $ MkGlobalDef (extraction ty) !(extractionDef ty def)

export
extractCtxt : Defs -> Core Defs
extractCtxt ds = traverseDefs ds (\(n,d) => do d' <- extractionGlobalDef d
                                               pure (n, d'))

-- Is n the names of a free variable in the _term_ of our arg?
-- (Ignores presence in types)
export
isFreeVar : {outer:_} -> (n : Name) -> Term (outer++n::vars) -> Bool
isFreeVar {outer=[]} n (Local 0 First) = True
isFreeVar {outer=[]} n (Local (S i) (Later x)) = False
isFreeVar {outer = o::os} n (Local 0 First) = False
isFreeVar {outer = o::os} n (Local (S i) (Later x)) = isFreeVar {outer=os} n (Local i x)
isFreeVar n (Ref Bound n') = n==n'
isFreeVar n (Ref _ _) = False
isFreeVar n (Meta x xs) = False --Hmmm can/how do we handle metavars?
isFreeVar n (Bind n' (Let _ val _) scope) = isFreeVar n val || isFreeVar {outer=n'::outer} n scope
isFreeVar n (Bind n' b scope) = isFreeVar {outer=n'::outer} n scope
isFreeVar n (App _ f a) = isFreeVar n f || isFreeVar n a
isFreeVar n TType = False
isFreeVar n Erased = False
isFreeVar n (Quote ty tm) = isFreeVar n tm
isFreeVar n (TCode  tm) = isFreeVar n tm
isFreeVar n (Eval   tm) = isFreeVar n tm
isFreeVar n (Escape tm) = isFreeVar n tm
