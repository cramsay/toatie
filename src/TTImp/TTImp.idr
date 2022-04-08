module TTImp.TTImp

import Core.TT
import Core.Context

mutual
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
toTTImp (Bind n (Lam s i ty) scope) = Just $ ILam i (Just n) !(toTTImp ty) !(toTTImp scope)
toTTImp (Bind n (Pi  s i ty) scope) = Just $ IPi  i (Just n) !(toTTImp ty) !(toTTImp scope)
toTTImp (Bind n (Let s val ty) scope) = Just $ ILet n (toTTImp ty) !(toTTImp val) !(toTTImp scope)
toTTImp (Bind n (PVar s i ty) scope) = Just $ IPatvar n !(toTTImp ty) !(toTTImp scope)
toTTImp (Bind n (PVTy s ty) scope) = Nothing
toTTImp (App i f a) = Just $ IApp i !(toTTImp f) !(toTTImp a)
toTTImp (Quote _ tm) = Just $ IQuote  !(toTTImp tm)
toTTImp (TCode  tm) = Just $ ICode   !(toTTImp tm)
toTTImp (Eval   tm) = Just $ IEval   !(toTTImp tm)
toTTImp (Escape tm) = Just $ IEscape !(toTTImp tm)
toTTImp TType  = Just IType
toTTImp Erased = Just Implicit -- Nothing

export
toTTImpClosed : {vars : _} -> {auto c : Ref Ctxt Defs} -> Term vars -> Core RawImp
toTTImpClosed (Local idx p) = pure $ IVar (nameAt idx p)
toTTImpClosed (Ref   _   n) = if !(goodName n)
                                 then pure $ IVar n
                                 else pure Implicit
  where
  goodName : Name -> Core Bool
  goodName n = do let False = n `elem` vars
                        | True => pure True
                  defs <- get Ctxt
                  Just gdef <- lookupDef n defs
                    | _ => pure False
                  pure True
toTTImpClosed (Meta n   args) = pure Implicit
toTTImpClosed (Bind n (Lam s i ty) scope) = pure $ ILam i (pure n) !(toTTImpClosed ty) !(toTTImpClosed scope)
toTTImpClosed (Bind n (Pi  s i ty) scope) = pure $ IPi  i (pure n) !(toTTImpClosed ty) !(toTTImpClosed scope)
toTTImpClosed (Bind n (Let s val ty) scope) = pure $ ILet n (Just !(toTTImpClosed ty)) !(toTTImpClosed val) !(toTTImpClosed scope)
toTTImpClosed (Bind n (PVar s i ty) scope) = pure $ IPatvar n !(toTTImpClosed ty) !(toTTImpClosed scope)
toTTImpClosed (Bind n (PVTy s ty) scope) = pure Implicit
toTTImpClosed (App i f a) = pure $ IApp i !(toTTImpClosed f) !(toTTImpClosed a)
toTTImpClosed (Quote _ tm) = pure $ IQuote  !(toTTImpClosed tm)
toTTImpClosed (TCode  tm) = pure $ ICode   !(toTTImpClosed tm)
toTTImpClosed (Eval   tm) = pure $ IEval   !(toTTImpClosed tm)
toTTImpClosed (Escape tm) = pure $ IEscape !(toTTImpClosed tm)
toTTImpClosed TType  = pure IType
toTTImpClosed Erased = pure Implicit -- Nothing

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
    show (IPi Implicit mn argTy retTy) = "{" ++ maybe "" (\n=>show n ++ " : ") mn
                                         ++ show argTy ++ "} -> " ++ show retTy
    show (IPi Explicit mn argTy retTy) = "(" ++ maybe "" (\n=>show n ++ " : ") mn
                                         ++ show argTy ++ ") -> " ++ show retTy
    show (ILam Implicit mn argTy scope) = "\\{" ++ maybe "_" (\n=>show n) mn ++ " : "
                                            ++ show argTy ++ "} => " ++ show scope
    show (ILam Explicit mn argTy scope) = "\\" ++ maybe "_" (\n=>show n) mn ++ " : "
                                            ++ show argTy ++ " => " ++ show scope
    show (IPatvar n ty scope) = "pat " ++ show n ++ " : " ++ show ty ++ " => " ++ show scope
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
