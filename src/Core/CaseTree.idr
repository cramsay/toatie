module Core.CaseTree

import Core.TT

import Data.List

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
       -- Catch-all case
       DefaultCase : CaseTree vars -> CaseAlt vars

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
     PLoc : AppInfo -> Name -> Pat
     PUnmatchable : Term [] -> Pat

export
Show Pat where
  show (PCon AExplicit n t a args) = show n ++ show (t, a) ++ show args
  show (PCon AImplicit n t a args) = "{" ++ show n ++ show (t, a) ++ show args ++ "}"
  show (PLoc AExplicit n) = "(" ++ show n ++ ")"
  show (PLoc AImplicit n) = "{" ++ show n ++ "}"
  show _ = "_"

export
mkPat' : AppInfo -> List (AppInfo, Pat) -> Term [] -> Term [] -> Pat
mkPat' i args orig (Ref Bound n) = PLoc i n
mkPat' i args orig (Ref (DataCon t a) n) = PCon i n t a args
mkPat' i args orig (App info fn arg)
    = let parg = mkPat' i [] arg arg in
                 mkPat' i ((info, parg) :: args) orig fn
mkPat' i args orig tm = PUnmatchable orig

export
argToPat : (AppInfo, Term []) -> Pat
argToPat (i,tm)
    = mkPat' i [] tm tm

export
mkTerm : (vars : List Name) -> Pat -> Term vars
mkTerm vars (PCon i n tag arity xs)
    = apply (Ref (DataCon tag arity) n) (map (\(i,p)=>(i, mkTerm vars p)) xs)
mkTerm vars (PLoc i n)
    = case isVar n vars of
           Just (MkVar prf) => Local _ prf
           _ => Ref Bound n
mkTerm vars (PUnmatchable tm) = embed tm

-- Show instances

mutual
  export
  {vars : _} -> Show (CaseTree vars) where
    show (Case {name} idx prf ty alts)
        = "case " ++ show name ++ "[" ++ show idx ++ "] : " ++ show ty ++ " of { " ++
                showSep " | " (assert_total (map show alts)) ++ " }"
    show (STerm tm) = show tm
    show (Unmatched msg) = "Error: " ++ show msg
    show Impossible = "Impossible"

  export
  {vars : _} -> Show (CaseAlt vars) where
    show (ConCase n tag args sc)
        = show n ++ " " ++ showSep " " (map show args) ++ " => " ++
          show sc
    show (DefaultCase sc)
        = "_ => " ++ show sc
{-


  -- ORIGINAL CLAUSES

  [ ["(pat = {{pat0::2}}, name = {arg:0}, argType = Known Type)",
     "(pat = {Z(0, 0)[]}, name = {arg:1}, argType = Known Nat)",
     "(pat = {{pat0::1}}, name = {arg:2}, argType = Known Nat)",
     "(pat = VNil(0, 1)[(Implicit, ({pat0::2}))], name = {arg:3}, argType = Known (Vect {arg:1} {arg:0}))",
     "(pat = ({pat0::0}), name = {arg:4}, argType = Known (Vect {arg:2} {arg:0}))"
    ],

    ["(pat = {{pat1::5}}, name = {arg:0}, argType = Known Type)",
     "(pat = {S(1, 1)[(Explicit, {{pat1::4}})]}, name = {arg:1}, argType = Known Nat)",
     "(pat = {{pat1::3}}, name = {arg:2}, argType = Known Nat)",
     "(pat = VCons(1, 4)[(Implicit, ({pat1::5})), (Implicit, ({pat1::4})), (Explicit, ({pat1::2})), (Explicit, ({pat1::1}))], name = {arg:3}, argType = Known (Vect {arg:1} {arg:0}))",
     "(pat = ({pat1::0}), name = {arg:4}, argType = Known (Vect {arg:2} {arg:0}))"]]

  -- PASS 1
  [ ["(pat = {Z(0, 0)[]}, name = {arg:1}, argType = Known Nat)",
     "(pat = {{pat0::1}}, name = {arg:2}, argType = Known Nat)",
     "(pat = VNil(0, 1)[(Implicit, ({pat0::2}))], name = {arg:3}, argType = Known (Vect {arg:1} {arg:0}[0]))",
     "(pat = ({pat0::0}), name = {arg:4}, argType = Known (Vect {arg:2} {arg:0}[0]))"
    ],

    ["(pat = {S(1, 1)[(Explicit, {{pat1::4}})]}, name = {arg:1}, argType = Known Nat)",
     "(pat = {{pat1::3}}, name = {arg:2}, argType = Known Nat)",
     "(pat = VCons(1, 4)[(Implicit, ({pat1::5})), (Implicit, ({pat1::4})), (Explicit, ({pat1::2})), (Explicit, ({pat1::1}))], name = {arg:3}, argType = Known (Vect {arg:1} {arg:0}[0]))",
     "(pat = ({pat1::0}), name = {arg:4}, argType = Known (Vect {arg:2} {arg:0}[0]))"]
    ]

  Got rid of patterns for arg:0 (pat0::2 and pat1::5) via VAR


  -- PASS 2
    [["(pat = {{pat0::1}}, name = {arg:2}, argType = Known Nat)",
      "(pat = VNil(0, 1)[(Implicit, ({pat0::2}))], name = {arg:3}, argType = Known (Vect 0 {arg:0}[0]))",
      "(pat = ({pat0::0}), name = {arg:4}, argType = Known (Vect {arg:2} {arg:0}[0]))"],

     ["(pat = {{pat1::3}}, name = {arg:2}, argType = Known Nat)",
      "(pat = VCons(1, 4)[(Implicit, ({pat1::5})), (Implicit, ({pat1::4})), (Explicit, ({pat1::2})), (Explicit, ({pat1::1}))], name = {arg:3}, argType = Known (Vect (S {pat1::4}) {arg:0}[0]))",
      "(pat = ({pat1::0}), name = {arg:4}, argType = Known (Vect {arg:2} {arg:0}[0]))"]
      ]

  We're trying to VAR on the implicit length patterns...
    Z creeps into the first clause's vect type
    the second clause's vect type references pat1::4, which used to exist but we've just VARed on it! Should we be replacing (S pat1::4) with arg:1?

-}
