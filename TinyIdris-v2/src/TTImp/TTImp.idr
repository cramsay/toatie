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

export
apply : RawImp -> List (AppInfo, RawImp) -> RawImp
apply f [] = f
apply f ((i,x) :: xs) = apply (IApp i f x) xs

export
getFn : RawImp -> RawImp
getFn (IApp _ f arg) = getFn f
getFn f = f
