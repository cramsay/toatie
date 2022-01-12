module Core.TT

import Data.List
import Data.Maybe
import Data.SortedMap
import Decidable.Equality
import Debug.Trace

-- In Idris2, this is defined in Core.Name
public export
data Name : Type where
     UN : String -> Name -- user written name
     MN : String -> Int -> Name -- machine generated name

export
nameEq : (x : Name) -> (y : Name) -> Maybe (x = y)
nameEq (UN x) (UN y) with (decEq x y)
  nameEq (UN y) (UN y) | (Yes Refl) = Just Refl
  nameEq (UN x) (UN y) | (No contra) = Nothing
nameEq (MN x t) (MN x' t') with (decEq x x')
  nameEq (MN x t) (MN x t') | (Yes Refl) with (decEq t t')
    nameEq (MN x t) (MN x t) | (Yes Refl) | (Yes Refl) = Just Refl
    nameEq (MN x t) (MN x t') | (Yes Refl) | (No contra) = Nothing
  nameEq (MN x t) (MN x' t') | (No contra) = Nothing
nameEq _ _ = Nothing

export
Eq Name where
  (==) (UN x) (UN y) = x == y
  (==) (MN x i) (MN y j) = i == j && x == y
  (==) _ _ = False

nameTag : Name -> Int
nameTag (UN _) = 0
nameTag (MN _ _) = 1

export
Ord Name where
  compare (UN x) (UN y) = compare x y
  compare (MN x i) (MN y j)
      = case compare x y of
             EQ => compare i j
             t => t
  compare x y = compare (nameTag x) (nameTag y)

public export
data TyConInfo : Type where
  TyConParam : TyConInfo
  TyConObj   : TyConInfo
  TyConSimp  : TyConInfo

export
Show TyConInfo where
  show TyConParam = "Parameter"
  show TyConObj   = "Object"
  show TyConSimp  = "Simple"

export
Eq TyConInfo where
  (==) TyConParam TyConParam = True
  (==) TyConObj   TyConObj   = True
  (==) TyConSimp  TyConSimp  = True
  (==) _          _          = False

public export
data NameType : Type where
     Func : NameType
     Bound : NameType
     DataCon :            (tag : Int) -> (arity : Nat) -> NameType
     TyCon : TyConInfo -> (tag : Int) -> (arity : Nat) -> NameType

export
Show NameType where
  show Func = "Func"
  show (DataCon t a) = "DataCon " ++ show (t, a)
  show (TyCon i t a) = "TyCon " ++ show i ++ show (t, a)
  show Bound = "Bound"

public export
data IsVar : Name -> Nat -> List Name -> Type where
     First : IsVar n Z (n :: ns)
     Later : IsVar n i ns -> IsVar n (S i) (m :: ns)

public export
dropVar : (ns : List Name) -> {idx : Nat} ->
          (0 p : IsVar name idx ns) -> List Name
dropVar (n :: xs) First = xs
dropVar (n :: xs) (Later p) = n :: dropVar xs p

public export
data Var : List Name -> Type where
     MkVar : {i : Nat} -> (0 p : IsVar n i vars) -> Var vars

export
dropFirst : List (Var (v :: vs)) -> List (Var vs)
dropFirst [] = []
dropFirst (MkVar First :: vs) = dropFirst vs
dropFirst (MkVar (Later p) :: vs) = MkVar p :: dropFirst vs

public export
data NVar : Name -> List Name -> Type where
     MkNVar : {i : Nat} -> (0 p : IsVar n i vars) -> NVar n vars

export
weakenNVar : (ns : List Name) ->
             {idx : Nat} -> (0 p : IsVar name idx inner) ->
             NVar name (ns ++ inner)
weakenNVar [] x = MkNVar x
weakenNVar (y :: xs) x
   = let MkNVar x' = weakenNVar xs x in
         MkNVar (Later x')

public export
data PiInfo : Type where
     Implicit : PiInfo
     Explicit : PiInfo

public export
Stage : Type
Stage = Nat

-- Stage lookup reference
export
data Stg : Type where

public export
data Binder : Type -> Type where
     Lam : Stage -> PiInfo     -> ty -> Binder ty
     Pi  : Stage -> PiInfo     -> ty -> Binder ty
     Let : Stage -> (val : ty) -> ty -> Binder ty

     PVar : Stage -> ty -> Binder ty -- pattern bound variables ...
     PVTy : Stage -> ty -> Binder ty -- ... and their type

export
binderType : Binder tm -> tm
binderType (Lam _ x ty) = ty
binderType (Pi  _ x ty) = ty
binderType (Let _ _ ty) = ty
binderType (PVar _ ty) = ty
binderType (PVTy _ ty) = ty

export
binderStage : Binder tm -> Stage
binderStage (Lam s _ _) = s
binderStage (Pi  s _ _) = s
binderStage (Let s _ _) = s
binderStage (PVar s _) = s
binderStage (PVTy s _) = s

export
Functor Binder where
  map func (Lam s x ty) = Lam s x (func ty)
  map func (Pi s x ty) = Pi s x (func ty)
  map func (Let s val ty) = Let s (func val) (func ty)
  map func (PVar s ty) = PVar s (func ty)
  map func (PVTy s ty) = PVTy s (func ty)

public export
data AppInfo : Type where
  AImplicit : AppInfo
  AExplicit : AppInfo

export
Eq AppInfo where
  AImplicit == AImplicit = True
  AExplicit == AExplicit = True
  _         == _         = False

export
Eq PiInfo where
  Implicit == Implicit = True
  Explicit == Explicit = True
  _        == _        = False

public export
data Term : List Name -> Type where
     Local : (idx : Nat) -> -- de Bruijn index
             (0 p : IsVar name idx vars) -> -- proof that index is valid
             Term vars
     Ref : NameType -> Name -> Term vars -- a reference to a global name
     Meta : Name -> List (Term vars) -> Term vars
     Bind : (x : Name) -> -- any binder, e.g. lambda or pi
            Binder (Term vars) ->
            (scope : Term (x :: vars)) -> -- one more name in scope
            Term vars
     App : AppInfo -> Term vars -> Term vars -> Term vars -- function application
     TType : Term vars
     Erased : Term vars
     Quote  : Term vars -> Term vars
     TCode  : Term vars -> Term vars
     Eval   : Term vars -> Term vars -- TODO Worth enforcing eval is only on closed terms?
     Escape : Term vars -> Term vars

public export
interface Weaken (0 tm : List Name -> Type) where
  weaken : {n, vars : _} -> tm vars -> tm (n :: vars)
  weakenNs : {vars : _} -> (ns : List Name) -> tm vars -> tm (ns ++ vars)

  weakenNs [] t = t
  weakenNs (n :: ns) t = weaken (weakenNs ns t)

  weaken = weakenNs [_]

-- Term manipulation
export
apply : Term vars -> List (AppInfo, Term vars) -> Term vars
apply fn [] = fn
apply fn ((i,a) :: args) = apply (App i fn a) args

export
embed : Term vars -> Term (vars ++ more)
embed tm = believe_me tm -- Really??

export
getFnArgs : Term vars -> (Term vars, List (Term vars))
getFnArgs tm = getFA [] tm
  where
    getFA : List (Term vars) -> Term vars ->
            (Term vars, List (Term vars))
    getFA args (App info f a) = getFA (a :: args) f
    getFA args tm = (tm, args)

export
getFnInfoArgs : Term vars -> (Term vars, List (AppInfo, Term vars))
getFnInfoArgs tm = getFA [] tm
  where
  getFA : List (AppInfo, Term vars) -> Term vars ->
          (Term vars, List (AppInfo, Term vars))
  getFA args (App info f a) = getFA ((info, a) :: args) f
  getFA args tm = (tm, args)


export
isVar : (n : Name) -> (ns : List Name) -> Maybe (Var ns)
isVar n [] = Nothing
isVar n (m :: ms)
    = case nameEq n m of
           Nothing => do MkVar p <- isVar n ms
                         pure (MkVar (Later p))
           Just Refl => pure (MkVar First)

export
varExtend : IsVar x idx xs -> IsVar x idx (xs ++ ys)
varExtend p = believe_me p

export
insertNVarNames : {outer, ns : _} ->
                  (idx : Nat) ->
                  (0 p : IsVar name idx (outer ++ inner)) ->
                  NVar name (outer ++ (ns ++ inner))
insertNVarNames {ns} {outer = []} idx prf = weakenNVar ns prf
insertNVarNames {outer = (y :: xs)} Z First = MkNVar First
insertNVarNames {ns} {outer = (y :: xs)} (S i) (Later x)
    = let MkNVar prf = insertNVarNames {ns} i x in
          MkNVar (Later prf)

export
insertNames : {outer, inner : _} ->
              (ns : List Name) -> Term (outer ++ inner) ->
              Term (outer ++ (ns ++ inner))
insertNames ns (Local idx prf)
    = let MkNVar prf' = insertNVarNames {ns} idx prf in
          Local _ prf'
insertNames ns (Ref nt name) = Ref nt name
insertNames ns (Meta name args)
    = Meta name (map (insertNames ns) args)
insertNames {outer} {inner} ns (Bind x b scope)
    = Bind x (assert_total (map (insertNames ns) b))
           (insertNames {outer = x :: outer} {inner} ns scope)
insertNames ns (App info fn arg)
    = App info (insertNames ns fn) (insertNames ns arg)
insertNames ns Erased = Erased
insertNames ns TType = TType
insertNames ns (Quote tm) = Quote $ insertNames ns tm
insertNames ns (TCode tm) = TCode $ insertNames ns tm
insertNames ns (Eval tm) = Eval $ insertNames ns tm
insertNames ns (Escape tm) = Escape $ insertNames ns tm


export
Weaken Term where
  weakenNs ns tm = insertNames {outer = []} ns tm

export
Weaken Var where
  weaken (MkVar p) = MkVar (Later p)

namespace Bounds
  public export
  data Bounds : List Name -> Type where
       None : Bounds []
       Add : (x : Name) -> Name -> Bounds xs -> Bounds (x :: xs)

export
addVars : {later, bound : _} ->
          {idx : Nat} ->
          Bounds bound -> (0 p : IsVar name idx (later ++ vars)) ->
          NVar name (later ++ (bound ++ vars))
addVars {later = []} {bound} bs p = weakenNVar bound p
addVars {later = (x :: xs)} bs First = MkNVar First
addVars {later = (x :: xs)} bs (Later p)
  = let MkNVar p' = addVars {later = xs} bs p in
        MkNVar (Later p')

resolveRef : {later : _} ->
             (done : List Name) -> Bounds bound -> Name ->
             Maybe (Term (later ++ (done ++ bound ++ vars)))
resolveRef done None n = Nothing
resolveRef {later} {vars} done (Add {xs} new old bs) n
    = if n == old
         then rewrite appendAssociative later done (new :: xs ++ vars) in
              let MkNVar p = weakenNVar {inner = new :: xs ++ vars}
                                        (later ++ done) First in
                     Just (Local _ p)
         else rewrite appendAssociative done [new] (xs ++ vars)
                in resolveRef (done ++ [new]) bs n

mkLocals : {later, bound : _} ->
           Bounds bound ->
           Term (later ++ vars) -> Term (later ++ (bound ++ vars))
mkLocals bs (Local idx p)
    = let MkNVar p' = addVars bs p in Local _ p'
mkLocals bs (Ref Bound name)
    = maybe (Ref Bound name) id (resolveRef [] bs name)
mkLocals bs (Ref nt name)
    = Ref nt name
mkLocals bs (Meta name xs)
    = maybe (Meta name (map (mkLocals bs) xs))
            id (resolveRef [] bs name)
mkLocals {later} bs (Bind x b scope)
    = Bind x (map (mkLocals bs) b)
           (mkLocals {later = x :: later} bs scope)
mkLocals bs (App info fn arg)
    = App info (mkLocals bs fn) (mkLocals bs arg)
mkLocals bs Erased = Erased
mkLocals bs TType = TType
mkLocals bs (Quote tm)  = Quote  $ mkLocals bs tm
mkLocals bs (TCode tm)  = TCode  $ mkLocals bs tm
mkLocals bs (Eval tm)   = Eval   $ mkLocals bs tm
mkLocals bs (Escape tm) = Escape $ mkLocals bs tm

export
refsToLocals : {bound : _} ->
               Bounds bound -> Term vars -> Term (bound ++ vars)
refsToLocals None y = y
refsToLocals bs y = mkLocals {later = []} bs y

-- Replace any reference to 'x' with a locally bound name 'new'
export
refToLocal : (x : Name) -> (new : Name) -> Term vars -> Term (new :: vars)
refToLocal x new tm = refsToLocals (Add new x None) tm

-- Replace any Ref Bound in a type with appropriate local
export
resolveNames : (vars : List Name) -> Term vars -> Term vars
resolveNames vars (Ref Bound name)
    = case isVar name vars of
           Just (MkVar prf) => Local _ prf
           _ => Ref Bound name
resolveNames vars (Meta n xs)
    = Meta n (map (resolveNames vars) xs)
resolveNames vars (Bind x b scope)
    = Bind x (map (resolveNames vars) b) (resolveNames (x :: vars) scope)
resolveNames vars (App info fn arg)
    = App info (resolveNames vars fn) (resolveNames vars arg)
resolveNames vars (Quote tm)
    = Quote $ resolveNames vars tm
resolveNames vars (Escape tm)
  = Escape $ resolveNames vars tm
resolveNames vars (Eval tm)
  = Eval $ resolveNames vars tm
resolveNames vars (TCode tm)
  = TCode $ resolveNames vars tm
resolveNames vars tm = tm

-- Substitute some explicit terms for names in a term, and remove those
-- names from the scope
namespace SubstEnv
  public export
  data SubstEnv : List Name -> List Name -> Type where
       Nil : SubstEnv [] vars
       (::) : Term vars ->
              SubstEnv ds vars -> SubstEnv (d :: ds) vars

  findDrop : {drop : _} -> {idx : Nat} ->
             (0 p : IsVar name idx (drop ++ vars)) ->
             SubstEnv drop vars -> Term vars
  findDrop {drop = []} var env = Local _ var
  findDrop {drop = x :: xs} First (tm :: env) = tm
  findDrop {drop = x :: xs} (Later p) (tm :: env)
      = findDrop p env

  find : {drop, vars, outer : _} -> {idx : Nat} ->
         (0 p : IsVar name idx (outer ++ (drop ++ vars))) ->
         SubstEnv drop vars ->
         Term (outer ++ vars)
  find {outer = []} var env = findDrop var env
  find {outer = x :: xs} First env = Local _ First
  find {outer = x :: xs} (Later p) env = weaken (find p env)

  substEnv : {drop, vars, outer : _} ->
             SubstEnv drop vars -> Term (outer ++ (drop ++ vars)) ->
             Term (outer ++ vars)
  substEnv env (Local _ prf)
      = find prf env
  substEnv env (Ref x name) = Ref x name
  substEnv env (Meta n xs)
      = Meta n (map (substEnv env) xs)
  substEnv {outer} env (Bind x b scope)
      = Bind x (map (substEnv env) b)
               (substEnv {outer = x :: outer} env scope)
  substEnv env (App info fn arg)
      = App info (substEnv env fn) (substEnv env arg)
  substEnv env Erased = Erased
  substEnv env TType = TType
  substEnv env (Quote tm)  = Quote  $ substEnv env tm
  substEnv env (TCode tm)  = TCode  $ substEnv env tm
  substEnv env (Eval tm)   = Eval   $ substEnv env tm
  substEnv env (Escape tm) = Escape $ substEnv env tm

  export
  substs : {drop, vars : _} ->
           SubstEnv drop vars -> Term (drop ++ vars) -> Term vars
  substs env tm = substEnv {outer = []} env tm

  export
  subst : {vars, x : _} -> Term vars -> Term (x :: vars) -> Term vars
  subst val tm = substEnv {outer = []} {drop = [_]} [val] tm

-- Replace an explicit name with a term
export
substName : {vars : _} -> Name -> Term vars -> Term vars -> Term vars
substName x new (Ref nt name)
    = case nameEq x name of
           Nothing => Ref nt name
           Just Refl => new
substName x new (Meta n xs)
    = Meta n (map (substName x new) xs)
-- ASSUMPTION: When we substitute under binders, the name has always been
-- resolved to a Local, so no need to check that x isn't shadowing
substName x new (Bind y b scope)
    = Bind y (map (substName x new) b) (substName x (weaken new) scope)
substName x new (App info fn arg)
    = App info (substName x new fn) (substName x new arg)
substName x new (Quote tm) = Quote $ substName x new tm
substName x new (TCode tm) = TCode $ substName x new tm
substName x new (Eval tm) = Eval $ substName x new tm
substName x new (Escape tm) = Escape $ substName x new tm
substName x new tm = tm

export
addMetas : SortedMap Name Bool -> Term vars -> SortedMap Name Bool
addMetas ns (Local idx y) = ns
addMetas ns (Ref nt name) = ns
addMetas ns (Meta n xs) = addMetaArgs (insert n False ns) xs
  where
    addMetaArgs : SortedMap Name Bool -> List (Term vars) -> SortedMap Name Bool
    addMetaArgs ns [] = ns
    addMetaArgs ns (t :: ts) = addMetaArgs (addMetas ns t) ts
addMetas ns (Bind x (Let _ val ty) scope)
    = addMetas (addMetas (addMetas ns val) ty) scope
addMetas ns (Bind x b scope)
    = addMetas (addMetas ns (binderType b)) scope
addMetas ns (App i fn arg)
    = addMetas (addMetas ns fn) arg
addMetas ns (TCode tm) = addMetas ns tm
addMetas ns (Eval tm) = addMetas ns tm
addMetas ns (Quote tm) = addMetas ns tm
addMetas ns (Escape tm) = addMetas ns tm
addMetas ns (Erased) = ns
addMetas ns (TType) = ns

-- Get the metavariable names in a term
export
getMetas : Term vars -> SortedMap Name Bool
getMetas tm = addMetas empty tm

export
addRefs : (underAssert : Bool) -> (aTotal : Name) ->
          SortedMap Name Bool -> Term vars -> SortedMap Name Bool
addRefs ua at ns (Local idx y) = ns
addRefs ua at ns (Ref x name) = insert name ua ns
addRefs ua at ns (Meta n xs)
    = addRefsArgs ns xs
  where
    addRefsArgs : SortedMap Name Bool -> List (Term vars) -> SortedMap Name Bool
    addRefsArgs ns [] = ns
    addRefsArgs ns (t :: ts) = addRefsArgs (addRefs ua at ns t) ts
addRefs ua at ns (Bind x (Let _ val ty) scope)
    = addRefs ua at (addRefs ua at (addRefs ua at ns val) ty) scope
addRefs ua at ns (Bind x b scope)
    = addRefs ua at (addRefs ua at ns (binderType b)) scope
addRefs ua at ns (App _ (App _ (Ref _ name) x) y)
    = if name == at
         then addRefs True at (insert name True ns) y
         else addRefs ua at (addRefs ua at (insert name ua ns) x) y
addRefs ua at ns (App _ fn arg)
    = addRefs ua at (addRefs ua at ns fn) arg
addRefs ua at ns (TCode x) = addRefs ua at ns x
addRefs ua at ns (Quote x) = addRefs ua at ns x
addRefs ua at ns (Eval x) = addRefs ua at ns x
addRefs ua at ns (Escape x) = addRefs ua at ns x
addRefs ua at ns (Erased) = ns
addRefs ua at ns (TType) = ns

-- As above, but for references. Also flag whether a name is under an
-- 'assert_total' because we may need to know that in coverage/totality
-- checking
export
getRefs : (aTotal : Name) -> Term vars -> SortedMap Name Bool
getRefs at tm = addRefs False at empty tm

public export
data CompatibleVars : List Name -> List Name -> Type where
     CompatPre : CompatibleVars xs xs
     CompatExt : CompatibleVars xs ys -> CompatibleVars (n :: xs) (m :: ys)

export
areVarsCompatible : (xs : List Name) -> (ys : List Name) ->
                    Maybe (CompatibleVars xs ys)
areVarsCompatible [] [] = pure CompatPre
areVarsCompatible (x :: xs) (y :: ys)
    = do compat <- areVarsCompatible xs ys
         pure (CompatExt compat)
areVarsCompatible _ _ = Nothing

export
renameVars : CompatibleVars xs ys -> Term xs -> Term ys
renameVars compat tm = believe_me tm -- no names in term, so it's identity
-- But how would we would define it?

export
renameTop : (m : Name) -> Term (n :: vars) -> Term (m :: vars)
renameTop m tm = renameVars (CompatExt CompatPre) tm

public export
data SubVars : List Name -> List Name -> Type where
     SubRefl  : SubVars xs xs
     DropCons : SubVars xs ys -> SubVars xs (y :: ys)
     KeepCons : SubVars xs ys -> SubVars (x :: xs) (x :: ys)

export
subElem : {idx : Nat} -> (0 p : IsVar name idx xs) ->
          SubVars ys xs -> Maybe (Var ys)
subElem prf SubRefl = Just (MkVar prf)
subElem First (DropCons p) = Nothing
subElem (Later x) (DropCons p)
    = do MkVar prf' <- subElem x p
         Just (MkVar prf')
subElem First (KeepCons p) = Just (MkVar First)
subElem (Later x) (KeepCons p)
    = do MkVar prf' <- subElem x p
         Just (MkVar (Later prf'))

export
subExtend : (ns : List Name) -> SubVars xs ys -> SubVars (ns ++ xs) (ns ++ ys)
subExtend [] sub = sub
subExtend (x :: xs) sub = KeepCons (subExtend xs sub)

export
subInclude : (ns : List Name) -> SubVars xs ys -> SubVars (xs ++ ns) (ys ++ ns)
subInclude ns SubRefl = SubRefl
subInclude ns (DropCons p) = DropCons (subInclude ns p)
subInclude ns (KeepCons p) = KeepCons (subInclude ns p)

mutual
  export
  shrinkBinder : Binder (Term vars) -> SubVars newvars vars ->
                 Maybe (Binder (Term newvars))
  shrinkBinder (Lam s p ty) prf
      = Just (Lam s p !(shrinkTerm ty prf))
  shrinkBinder (Pi s p ty) prf
      = Just (Pi s p !(shrinkTerm ty prf))
  shrinkBinder (Let s val ty) prf
      = Just (Let s !(shrinkTerm val prf) !(shrinkTerm ty prf))
  shrinkBinder (PVar s ty) prf
      = Just (PVar s !(shrinkTerm ty prf))
  shrinkBinder (PVTy s ty) prf
      = Just (PVTy s !(shrinkTerm ty prf))

  export
  shrinkVar : Var vars -> SubVars newvars vars -> Maybe (Var newvars)
  shrinkVar (MkVar x) prf = subElem x prf

  export
  shrinkTerm : Term vars -> SubVars newvars vars -> Maybe (Term newvars)
  shrinkTerm (Local idx loc) prf
     = case subElem loc prf of
            Nothing => Nothing
            Just (MkVar loc') => Just (Local _ loc')
  shrinkTerm (Ref x name) prf = Just (Ref x name)
  shrinkTerm (Meta x xs) prf
     = do xs' <- traverse (\x => shrinkTerm x prf) xs
          Just (Meta x xs')
  shrinkTerm (Bind x b scope) prf
     = Just (Bind x !(shrinkBinder b prf) !(shrinkTerm scope (KeepCons prf)))
  shrinkTerm (App info fn arg) prf
     = Just (App info !(shrinkTerm fn prf) !(shrinkTerm arg prf))
  shrinkTerm Erased prf = Just Erased
  shrinkTerm TType prf = Just TType
  shrinkTerm (Quote tm)  prf = Just (Quote  !(shrinkTerm tm prf))
  shrinkTerm (TCode tm)  prf = Just (TCode  !(shrinkTerm tm prf))
  shrinkTerm (Eval tm)   prf = Just (Eval   !(shrinkTerm tm prf))
  shrinkTerm (Escape tm) prf = Just (Escape !(shrinkTerm tm prf))

--- Show instances

export
showSep : String -> List String -> String
showSep sep [] = ""
showSep sep [x] = x
showSep sep (x :: xs) = x ++ sep ++ showSep sep xs

export
Show Name where
  show (UN n) = n
  show (MN n i) = "{" ++ n ++ ":" ++ show i ++ "}"

export
nameAt : {vars : _} ->
         (idx : Nat) -> (0 p : IsVar n idx vars) -> Name
nameAt {vars = n :: ns} Z First = n
nameAt {vars = n :: ns} (S k) (Later p) = nameAt k p

export
{vars : _} -> Show (Bounds vars) where
  show None = "[]"
  show (Add x y z) = "Add (" ++ show x ++ ", " ++ show y ++ ") :: " ++ show z

export
Show PiInfo where
  show Implicit = "Implicit"
  show Explicit = "Explicit"

export
Show AppInfo where
  show AImplicit = "Implicit"
  show AExplicit = "Explicit"

export
{vars : _} -> Show (Term vars) where
  show tm = let (fn, args) = getFnInfoArgs tm in
            fromMaybe (showApp fn args) ( -- List of special case printers
                    tryShowNat tm
                <|> tryShowVect tm
                <|> tryShowList tm
            )
    where
      showArg : {vars : _} -> (AppInfo, Term vars) -> String
      showArg (AExplicit, arg) = show arg
      showArg (AImplicit, arg) = "{" ++ show arg ++ "}"

      showApp : {vars : _} -> Term vars -> List (AppInfo, Term vars) -> String
      showApp (Local {name} idx p) []
         = show (nameAt idx p) ++ "[" ++ show idx ++ "]"
      showApp (Ref _ n) [] = show n
      showApp (Meta n args) []
          = "?" ++ show n ++ "_" ++ show args
      showApp (Bind x (Lam s Explicit ty) sc) []
          = "\\" ++ show x ++ " :_" ++ show s ++ " " ++ show ty ++
            " => " ++ show sc
      showApp (Bind x (Lam s Implicit ty) sc) []
          = "\\{" ++ show x ++ "} :_" ++ show s ++ " " ++ show ty ++
            " => " ++ show sc
      showApp (Bind x (Pi s Explicit ty) sc) []
          = "((" ++ show x ++ " :_" ++ show s ++ " " ++ show ty ++
            ") -> " ++ show sc ++ ")"
      showApp (Bind x (Pi s Implicit ty) sc) []
          = "{" ++ show x ++ " :_" ++ show s ++ " " ++ show ty ++
            "} -> " ++ show sc
      showApp (Bind x (Let s val ty) sc) []
          = "let " ++ show x ++ " :_" ++ show s ++ " " ++ show ty ++
            " = "  ++ show val ++
            " in " ++ show sc
      showApp (Bind x (PVar s ty) sc) []
          = "pat " ++ show x ++ " :_" ++ show s ++ " " ++ show ty ++
            " => " ++ show sc
      showApp (Bind x (PVTy s ty) sc) []
          = "pty " ++ show x ++ " :_" ++ show s ++ " " ++ show ty ++
            " => " ++ show sc
      showApp (App _ _ _) [] = "[can't happen]"
      showApp TType [] = "Type"
      showApp Erased [] = "[_]"
      showApp (Quote sc) [] = "[|" ++ show sc ++ "|]"
      showApp (TCode sc) [] = "<" ++ show sc ++ ">"
      showApp (Eval  sc) [] = "!(" ++ show sc ++ ")"
      showApp (Escape sc) [] = "~(" ++ show sc ++ ")"
      showApp _ [] = "???"
      showApp f args = "(" ++ assert_total (show f) ++ " " ++
                              assert_total (showSep " " (map showArg args))
                       ++ ")"

      tryShowNat : Term vars -> Maybe String
      tryShowNat tm = map show $ go tm
        where
        go : Term vars -> Maybe Nat
        go (Ref (DataCon _ _) (UN "Z")) = Just Z
        go (App _ (Ref (DataCon _ _) (UN "S")) arg) = map S $ go arg
        go _         = Nothing

      tryShowVect : Term vars -> Maybe String
      tryShowVect tm = map show $ go tm
        where
        go : Term vars -> Maybe (List (Term vars))
        go (App _ (Ref (DataCon _ _) (UN "VNil")) xty) = Just []
        go (App _ (App _ (App _ (App _ (Ref (DataCon _ _) (UN "VCons")) xty) n) xtm) xs) = map (xtm ::) $ go xs
        go _ = Nothing

      tryShowList : Term vars -> Maybe String
      tryShowList tm = map (\x => "`" ++ show x) $ go tm
        where
        go : Term vars -> Maybe (List (Term vars))
        go (App _ (Ref (DataCon _ _) (UN "Nil")) xty) = Just []
        go (App _ (App _ (App _ (Ref (DataCon _ _) (UN "Cons")) xty) xtm) xs) = map (xtm ::) $ go xs
        go _ = Nothing
