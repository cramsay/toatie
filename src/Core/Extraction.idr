module Core.Extraction

import Core.TT
import Core.CaseTree
import Core.Context

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
extraction (Quote  tm) = Quote  (extraction tm)
extraction (TCode  tm) = TCode  (extraction tm)
extraction (Eval   tm) = Eval   (extraction tm)
extraction (Escape tm) = Escape (extraction tm)

extractionArity : Term vars -> Nat
extractionArity (Bind x (Lam k Implicit z) scope) = extractionArity scope
extractionArity (Bind x (Lam k Explicit z) scope) = S $ extractionArity scope
extractionArity (Bind x (Pi k Implicit z) scope) = extractionArity scope
extractionArity (Bind x (Pi k Explicit z) scope) = S $ extractionArity scope
extractionArity _ = 0

mutual
  extractionDef : (ty : Term []) -> Def -> Def
  extractionDef _  None = None
  extractionDef ty (DCon   tag arity     ) = DCon   tag (extractionArity ty)
  extractionDef ty (TCon x tag arity cons) = TCon x tag (extractionArity ty) cons
  extractionDef _  Hole = Hole
  extractionDef _  (Guess guess constraints) = Guess (extraction guess) constraints -- TODO update constraints or forbid this
  extractionDef _  (PMDef args ct) = PMDef args (extractTree ct)

  extractTree : {args : _} -> CaseTree args -> CaseTree args
  extractTree (Case idx p scTy xs) = Case idx p (extraction scTy) (map extractAlt xs)
  extractTree (STerm x)            = STerm $ extraction x
  extractTree (Unmatched msg)      = Unmatched msg
  extractTree Impossible           = Impossible

  extractAlt : {args : _} -> CaseAlt args -> CaseAlt args
  extractAlt (ConCase x tag ys y) = ConCase x tag ys $ extractTree y
  extractAlt (DefaultCase x     ) = DefaultCase $ extractTree x

export
extractionGlobalDef : GlobalDef -> GlobalDef
extractionGlobalDef (MkGlobalDef ty def) = MkGlobalDef (extraction ty) (extractionDef ty def)

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
isFreeVar n (Quote  tm) = isFreeVar n tm
isFreeVar n (TCode  tm) = isFreeVar n tm
isFreeVar n (Eval   tm) = isFreeVar n tm
isFreeVar n (Escape tm) = isFreeVar n tm
