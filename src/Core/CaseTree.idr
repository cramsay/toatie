module Core.CaseTree

import Core.TT

import Data.List
import Data.SortedMap

mutual
  -- Case trees
  -- We may only dispatch on variables, not expressions
  public export
  data CaseTree : List Name -> Type where
       -- case x return scTy of { p1 => e1 ; ... }
       Case : {name, vars : _} ->
              (idx : Nat) ->
              (0 p : IsVar name idx vars) ->
              (scTy : Term vars) -> List (CaseAlt vars) ->
              CaseTree vars
       -- RHS: no need for further inspection
       STerm : Term vars -> CaseTree vars
       -- error from a partial match
       Unmatched : (msg : String) -> CaseTree vars
       -- Absurd context
       Impossible : CaseTree vars

  -- Case alternatives. Unlike arbitrary patterns, they can be at most
  -- one constructor deep.
  -- Idris2 also needs cases for 'Delay' and primitives.
  public export
  data CaseAlt : List Name -> Type where
       -- Constructor for a data type; bind the arguments and subterms.
       ConCase : Name -> (tag : Int) -> (args : List Name) -> -- TODO, do I need to track AppInfo here?
                 CaseTree (args ++ vars) -> CaseAlt vars
       -- Quote for a staged term
       QuoteCase : (ty : Name) -> (arg : Name) -> CaseTree (ty :: arg :: vars) -> CaseAlt vars
       -- Catch-all case
       DefaultCase : CaseTree vars -> CaseAlt vars

export
isDefault : CaseAlt vars -> Bool
isDefault (DefaultCase _) = True
isDefault _ = False

mutual
  insertCaseNames : {outer, inner : _} ->
                    (ns : List Name) -> CaseTree (outer ++ inner) ->
                    CaseTree (outer ++ (ns ++ inner))
  insertCaseNames {inner} {outer} ns (Case idx prf scTy alts)
      = let MkNVar prf' = insertNVarNames {outer} {inner} {ns} _ prf in
            Case _ prf' (insertNames {outer} ns scTy)
                (map (insertCaseAltNames {outer} {inner} ns) alts)
  insertCaseNames {outer} ns (STerm x) = STerm (insertNames {outer} ns x)
  insertCaseNames ns (Unmatched msg) = Unmatched msg
  insertCaseNames ns Impossible = Impossible

  insertCaseAltNames : {outer, inner : _} ->
                       (ns : List Name) ->
                       CaseAlt (outer ++ inner) ->
                       CaseAlt (outer ++ (ns ++ inner))
  insertCaseAltNames {outer} {inner} ns (ConCase x tag args ct)
      = ConCase x tag args
           (rewrite appendAssociative args outer (ns ++ inner) in
                    insertCaseNames {outer = args ++ outer} {inner} ns
                        (rewrite sym (appendAssociative args outer inner) in
                                 ct))
  insertCaseAltNames {outer} {inner} ns (QuoteCase ty x ct)
      = QuoteCase ty x
           (insertCaseNames {outer = ty :: x :: outer} {inner} ns ct)
  insertCaseAltNames ns (DefaultCase ct)
      = DefaultCase (insertCaseNames ns ct)

export
Weaken CaseTree where
  weakenNs ns t = insertCaseNames {outer = []} ns t

-- Patterns, which arise from LHS expressions, and are converted to
-- case trees
public export
data Pat : Type where
     PCon : AppInfo -> Name -> (tag : Int) -> (arity : Nat) ->
            List (AppInfo, Pat) -> Pat
     PQuote : AppInfo -> (ty : Pat) -> Pat -> Pat
     PLoc : AppInfo -> Name -> Pat
     PUnmatchable : Term [] -> Pat

export
Show Pat where
  show (PCon AExplicit n t a args) = show n ++ show (t, a) ++ show args
  show (PCon AImplicit n t a args) = "{" ++ show n ++ show (t, a) ++ show args ++ "}"
  show (PLoc AExplicit n) = "(" ++ show n ++ ")"
  show (PLoc AImplicit n) = "{" ++ show n ++ "}"
  show (PQuote AExplicit ty p) = "( [|" ++ show p ++ "|] )"
  show _ = "_"

export
mkPat' : AppInfo -> List (AppInfo, Pat) -> Term [] -> Term [] -> Pat
mkPat' i args orig (Ref Bound n) = PLoc i n
mkPat' i args orig (Ref (DataCon t a) n) = PCon i n t a args
mkPat' i args orig (Quote ty tm) = PQuote i (mkPat' i [] orig ty) (mkPat' i [] orig tm)
mkPat' i args orig (App info fn arg)
    = let parg = mkPat' (combineInfo info i) [] arg arg
      in mkPat' i ((combineInfo info i, parg) :: args) orig fn
  where
  combineInfo : AppInfo -> AppInfo -> AppInfo
  combineInfo AImplicit _ = AImplicit
  combineInfo _ AImplicit = AImplicit
  combineInfo _ _         = AExplicit
mkPat' i args orig tm = PUnmatchable orig

export
argToPat : (AppInfo, Term []) -> Pat
argToPat (i,tm)
    = mkPat' i [] tm tm

export
mkTerm : (vars : List Name) -> Pat -> Term vars
mkTerm vars (PCon i n tag arity xs)
    = apply (Ref (DataCon tag arity) n) (map (\(i,p)=>(i, mkTerm vars p)) xs)
mkTerm vars (PQuote i pty parg) = Quote (mkTerm vars pty) (mkTerm vars parg)
mkTerm vars (PLoc i n)
    = case isVar n vars of
           Just (MkVar prf) => Local _ prf
           _ => Ref Bound n
mkTerm vars (PUnmatchable tm) = embed tm

-- Show instances

showCT : {vars : _} -> (indent : String) -> CaseTree vars -> String
showCA : {vars : _} -> (indent : String) -> CaseAlt vars  -> String

showCT indent (Case {name} idx prf ty alts)
  = "case " ++ show name ++ "[" ++ show idx ++ "] : " ++ show ty ++ " of"
  ++ "\n" ++ indent ++ " { "
  ++ showSep ("\n" ++ indent ++ " | ")
             (assert_total (map (showCA ("  " ++ indent)) alts))
  ++ "\n" ++ indent ++ " }"
showCT indent (STerm tm) = show tm
showCT indent (Unmatched msg) = "Error: " ++ show msg
showCT indent Impossible = "Impossible"

showCA indent (ConCase n tag args sc)
        = showSep " " (map show (n :: args)) ++ " => " ++
          showCT indent sc
showCA indent (QuoteCase ty x sc)
        = "Quote " ++ show x ++ " => " ++ showCT indent sc
showCA indent (DefaultCase sc)
        = "_ => " ++ showCT indent sc

export
{vars : _} -> Show (CaseTree vars) where
  show = showCT ""

export
{vars : _} -> Show (CaseAlt vars) where
  show = showCA ""

{-
mutual
  export
  eqTree : CaseTree vs -> CaseTree vs' -> Bool
  eqTree (Case i _ _ alts) (Case i' _ _ alts')
      = i == i'
       && length alts == length alts'
       && all (uncurry eqAlt) (zip alts alts')
  eqTree (STerm t) (STerm t') = eqTerm t t'
  eqTree (Unmatched _) (Unmatched _) = True
  eqTree Impossible Impossible = True
  eqTree _ _ = False

  eqAlt : CaseAlt vs -> CaseAlt vs' -> Bool
  eqAlt (ConCase n t args tree) (ConCase n' t' args' tree')
      = n == n' && eqTree tree tree' -- assume arities match, since name does
  eqAlt (DefaultCase tree) (DefaultCase tree')
      = eqTree tree tree'
  eqAlt _ _ = False
-}


total
getNames : (forall vs . SortedMap Name Bool -> Term vs -> SortedMap Name Bool) ->
           SortedMap Name Bool -> CaseTree vars -> SortedMap Name Bool
getNames add ns sc = getSet ns sc
  where
    mutual
      getAltSet : SortedMap Name Bool -> CaseAlt vs -> SortedMap Name Bool
      getAltSet ns (ConCase n t args sc) = getSet ns sc
      getAltSet ns (QuoteCase ty x sc) = getSet ns sc
      getAltSet ns (DefaultCase sc) = getSet ns sc

      getAltSets : SortedMap Name Bool -> List (CaseAlt vs) -> SortedMap Name Bool
      getAltSets ns [] = ns
      getAltSets ns (a :: as) = getAltSets (getAltSet ns a) as

      getSet : SortedMap Name Bool -> CaseTree vs -> SortedMap Name Bool
      getSet ns (Case _ x ty xs) = getAltSets ns xs
      getSet ns (STerm tm) = add ns tm
      getSet ns (Unmatched msg) = ns
      getSet ns Impossible = ns

export
getRefs : (aTotal : Name) -> CaseTree vars -> SortedMap Name Bool
getRefs at = getNames (addRefs False at) empty

export
addRefs : (aTotal : Name) -> SortedMap Name Bool -> CaseTree vars -> SortedMap Name Bool
addRefs at ns = getNames (addRefs False at) ns

export
getMetas : CaseTree vars -> SortedMap Name Bool
getMetas = getNames addMetas empty
