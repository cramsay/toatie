module TTImp.TTImp

import Core.TT

mutual
  public export
  data RawImp : Type where
       IVar : Name -> RawImp
       ILet : Name -> (margTy : Maybe RawImp) -> (argVal : RawImp) -> (scope : RawImp) ->
              RawImp
       IPi : PiInfo -> Maybe Stage -> Maybe Name ->
             (argTy : RawImp) -> (retTy : RawImp) -> RawImp
       ILam : PiInfo -> Maybe Stage -> Maybe Name ->
              (argTy : RawImp) -> (scope : RawImp) -> RawImp
       IPatvar : Maybe Stage -> Name -> (ty : RawImp) -> (scope : RawImp) -> RawImp
          -- ^ Idris doesn't need this since the pattern variable names are
          -- inferred, but in this initial version everything is explicit
       IApp : AppInfo -> RawImp -> RawImp -> RawImp
       ICase : (scr : RawImp) -> (scrty : RawImp) -> List ImpClause -> RawImp

       IMustUnify : RawImp -> RawImp
       Implicit : RawImp
       IType : RawImp
       IQuote  : RawImp -> RawImp
       ICode   : RawImp -> RawImp
       IEval   : RawImp -> RawImp
       IEscape : RawImp -> RawImp

  public export
  data ImpClause : Type where
       ImpossibleClause : (lhs : RawImp) -> ImpClause
       PatClause : (lhs : RawImp) -> (rhs : RawImp) -> ImpClause

public export
data ImpTy : Type where
     MkImpTy : (n : Name) -> (ty : RawImp) -> ImpTy

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
toTTImp (Bind n (Lam s i ty) scope) = Just $ ILam i (Just s) (Just n) !(toTTImp ty) !(toTTImp scope)
toTTImp (Bind n (Pi  s i ty) scope) = Just $ IPi  i (Just s) (Just n) !(toTTImp ty) !(toTTImp scope)
toTTImp (Bind n (Let s val ty) scope) = Just $ ILet n (toTTImp ty) !(toTTImp val) !(toTTImp scope)
toTTImp (Bind n (PVar s i ty) scope) = Just $ IPatvar (Just s) n !(toTTImp ty) !(toTTImp scope)
toTTImp (Bind n (PVTy s ty) scope) = Nothing
toTTImp (App i f a) = Just $ IApp i !(toTTImp f) !(toTTImp a)
toTTImp (Quote _ tm) = Just $ IQuote  !(toTTImp tm)
toTTImp (TCode  tm) = Just $ ICode   !(toTTImp tm)
toTTImp (Eval   tm) = Just $ IEval   !(toTTImp tm)
toTTImp (Escape tm) = Just $ IEscape !(toTTImp tm)
toTTImp TType  = Just IType
toTTImp Erased = Just Implicit -- Nothing

mutual
  export
  Show ImpClause where
    show (ImpossibleClause lhs) = show lhs ++ " impossible"
    show (PatClause lhs rhs) = show lhs ++ " => " ++ show rhs

  export
  Show RawImp where
    show (IVar n) = show n
    show (ILet n margTy argVal scope) = "let " ++ show n ++ maybe "" (\ty=>" : " ++ show ty) margTy
                                        ++ " = " ++ show argVal ++ " in " ++ show scope
    show (IPi Implicit mstage mn argTy retTy) = "{" ++ maybe "" (\n=>show n ++ " : ") mn ++ "@" ++ show mstage
                                         ++ show argTy ++ "} -> " ++ show retTy
    show (IPi Explicit mstage mn argTy retTy) = "(" ++ maybe "" (\n=>show n ++ " : ") mn ++ "@" ++ show mstage
                                         ++ show argTy ++ ") -> " ++ show retTy
    show (ILam Implicit mstage mn argTy scope) = "\\{" ++ maybe "_" (\n=>show n) mn ++ " : @" ++ show mstage
                                                 ++ show argTy ++ "} => " ++ show scope
    show (ILam Explicit mstage mn argTy scope) = "\\" ++ maybe "_" (\n=>show n) mn ++ " : @" ++ show mstage
                                            ++ show argTy ++ " => " ++ show scope
    show (IPatvar ms n ty scope) = "pat " ++ show n ++ " : @" ++ show ms ++ " " ++ show ty ++ " => " ++ show scope
    show (IApp AImplicit f a) = show f ++ " {" ++ show a ++ "}"
    show (IApp AExplicit f a) = show f ++ " (" ++ show a ++ ")"
    show (ICase scr scrty alts) = "case " ++ show scr ++ " : " ++ show scrty ++ " of " ++ show alts
    show (IMustUnify tm) = ".(" ++ show tm ++ ")"
    show Implicit = "_"
    show IType = "Type"
    show (IQuote  tm) = "[|" ++ show tm ++ "|]"
    show (ICode   tm) = "<" ++ show tm ++ ">"
    show (IEval   tm) = "!(" ++ show tm ++ ")"
    show (IEscape tm) = "~(" ++ show tm ++ ")"
