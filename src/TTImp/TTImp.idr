module TTImp.TTImp

import Core.TT

public export
data RawImp : Type where
     IVar : Name -> RawImp
     ILet : Name -> (margTy : Maybe RawImp) -> (argVal : RawImp) -> (scope : RawImp) ->
            RawImp
     IPi : PiInfo -> Maybe Name ->
           (argTy : RawImp) -> (retTy : RawImp) -> RawImp
     ILam : PiInfo -> Maybe Name ->
            (argTy : RawImp) -> (scope : RawImp) -> RawImp
     IPatvar : Name -> (ty : RawImp) -> (scope : RawImp) -> RawImp
        -- ^ Idris doesn't need this since the pattern variable names are
        -- inferred, but in this initial version everything is explicit
     IApp : AppInfo -> RawImp -> RawImp -> RawImp

     IMustUnify : RawImp -> RawImp
     Implicit : RawImp
     IType : RawImp
     IQuote  : RawImp -> RawImp
     ICode   : RawImp -> RawImp
     IEval   : RawImp -> RawImp
     IEscape : RawImp -> RawImp

public export
data ImpTy : Type where
     MkImpTy : (n : Name) -> (ty : RawImp) -> ImpTy

public export
data ImpClause : Type where
     ImpossibleClause : (lhs : RawImp) -> ImpClause
     PatClause : (lhs : RawImp) -> (rhs : RawImp) -> ImpClause

public export
data ImpTyConInfo : Type where
     ITyCParam : ImpTyConInfo
     ITyCObj   : ImpTyConInfo
     ITyCSimp  : ImpTyConInfo

public export
data ImpData : Type where
     MkImpData : (n : Name) ->
                 ImpTyConInfo ->
                 (tycon : RawImp) -> -- type constructor type
                 (datacons : List ImpTy) -> -- constructor type declarations
                 ImpData

public export
data ImpDecl : Type where
     IClaim : ImpTy -> ImpDecl
     IData : ImpData -> ImpDecl
     IDef : Name -> List ImpClause -> ImpDecl
     IImport : String -> ImpDecl

export
apply : RawImp -> List (AppInfo, RawImp) -> RawImp
apply f [] = f
apply f ((i,x) :: xs) = apply (IApp i f x) xs

export
getFn : RawImp -> RawImp
getFn (IApp _ f arg) = getFn f
getFn f = f

export
toTTImp : {vars : _} -> Term vars -> Maybe RawImp
toTTImp (Local idx p) = Just $ IVar (nameAt idx p)
toTTImp (Ref   _   n) = Just $ IVar n
toTTImp (Meta n   args) = Just Implicit
toTTImp (Bind n (Lam s i ty) scope) = Just $ ILam i (Just n) !(toTTImp ty) !(toTTImp scope)
toTTImp (Bind n (Pi  s i ty) scope) = Just $ IPi  i (Just n) !(toTTImp ty) !(toTTImp scope)
toTTImp (Bind n (Let s val ty) scope) = Just $ ILet n (toTTImp ty) !(toTTImp val) !(toTTImp scope)
toTTImp (Bind n (PVar s ty) scope) = Just $ IPatvar n !(toTTImp ty) !(toTTImp scope)
toTTImp (Bind n (PVTy s ty) scope) = Nothing
toTTImp (App i f a) = Just $ IApp i !(toTTImp f) !(toTTImp a)
toTTImp (Quote  tm) = Just $ IQuote  !(toTTImp tm)
toTTImp (TCode  tm) = Just $ ICode   !(toTTImp tm)
toTTImp (Eval   tm) = Just $ IEval   !(toTTImp tm)
toTTImp (Escape tm) = Just $ IEscape !(toTTImp tm)
toTTImp TType  = Just IType
toTTImp Erased = Nothing
