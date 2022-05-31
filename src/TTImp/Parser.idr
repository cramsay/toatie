module TTImp.Parser

import Core.Context
import Core.Core
import Core.TT
import Parser.Source
import TTImp.TTImp

import public Text.Parser
import        Data.List
import        Data.List.Views
import        Data.List1
import        Data.String
import        Data.String.Extra

import Debug.Trace

-- This is adapted from the Idris 2 TTImp parser, with the irrelevant parts
-- taken out. If you find anything strange in here, it's probably because of
-- that! There is, generally, not much interesting to see here... (at least,
-- not in the implementation of the type theory)

public export
FileName : Type
FileName = String

topDecl : FileName -> IndentInfo -> Rule ImpDecl
-- All the clauses get parsed as one-clause definitions. Collect any
-- neighbouring clauses with the same function name into one definition.
export
collectDefs : List ImpDecl -> List ImpDecl

%default covering

%hide Prelude.(>>=)
%hide Core.Core.(>>=)
%hide Prelude.(>>)
%hide Core.Core.(>>)
%hide Prelude.pure
%hide Core.Core.pure

%hide Lexer.Core.(<|>)
%hide Prelude.(<|>)

natLit : FileName -> Rule RawImp
natLit fname
    = do i <- intLit
         pure $ natToImp (fromInteger i)
  where
  natToImp : Nat -> RawImp
  natToImp 0 = IVar (UN "Z")
  natToImp (S k) = IApp AExplicit (IVar (UN "S")) (natToImp k)

atom : FileName -> Rule RawImp
atom fname
    = do exactIdent "Type"
         pure IType
  <|> do symbol "_"
         pure Implicit
  <|> do x <- name
         pure (IVar x)
  <|> natLit fname

getRight : Either a b -> Maybe b
getRight (Left _) = Nothing
getRight (Right v) = Just v

bindSymbol : Rule PiInfo
bindSymbol
    = do symbol "->"
         pure Explicit

mutual
  listLit : FileName -> IndentInfo -> Rule RawImp
  listLit fname indents
      = do symbol "`["
           elems <- sepBy (symbol ",") (expr fname indents)
           symbol "]"
           pure $ elemsToImp elems
     where
     elemsToImp : List RawImp -> RawImp
     elemsToImp [] = IApp AImplicit (IVar (UN "Nil")) Implicit
     elemsToImp (x :: xs) = IApp AExplicit (IApp AExplicit (IApp AImplicit
                              (IVar (UN "Cons"))
                              Implicit)
                              x)
                              (elemsToImp xs)

  vecLit : FileName -> IndentInfo -> Rule RawImp
  vecLit fname indents
      = do symbol "["
           elems <- sepBy (symbol ",") (expr fname indents)
           symbol "]"
           pure $ elemsToImp elems
    where
    elemsToImp : List RawImp -> RawImp
    elemsToImp [] = IApp AImplicit (IVar (UN "VNil")) Implicit
    elemsToImp (x :: xs) = IApp AExplicit (IApp AExplicit (IApp AImplicit (IApp AImplicit
                             (IVar (UN "VCons"))
                             Implicit)
                             Implicit)
                             x)
                             (elemsToImp xs)

  appExpr : FileName -> IndentInfo -> Rule RawImp
  appExpr fname indents
      = case_ fname indents
    <|> do f <- simpleExpr fname indents
           args <- many (argExpr fname indents)
           pure (apply f args)

  argExpr : FileName -> IndentInfo -> Rule (AppInfo, RawImp)
  argExpr fname indents
      = do continue indents
           impArg <|> expArg
    where
      impArg : Rule (AppInfo, RawImp)
      impArg = do symbol "{"
                  arg <- expr fname indents
                  symbol "}"
                  pure (AImplicit, arg)
      expArg : Rule (AppInfo, RawImp)
      expArg = do arg <- simpleExpr fname indents
                  pure (AExplicit, arg)


  simpleExpr : FileName -> IndentInfo -> Rule RawImp
  simpleExpr fname indents
      = atom fname
    <|> quote        fname indents
    <|> code_type    fname indents
    <|> eval_quote   fname indents
    <|> escape_quote fname indents
    <|> binder       fname indents
    <|> listLit      fname indents
    <|> vecLit       fname indents
    <|> do symbol "("
           e <- expr fname indents
           symbol ")"
           pure e

  export
  expr : FileName -> IndentInfo -> Rule RawImp
  expr = typeExpr

  typeExpr : FileName -> IndentInfo -> Rule RawImp
  typeExpr fname indents
      = do arg <- appExpr fname indents
           (do continue indents
               rest <- some (do exp <- bindSymbol
                                op <- appExpr fname indents
                                pure (exp, op))
               pure (mkPi arg rest))
             <|> pure arg
    where
      mkPi : RawImp -> List (PiInfo, RawImp) -> RawImp
      mkPi arg [] = arg
      mkPi arg ((exp, a) :: as)
            = IPi exp Nothing Nothing arg (mkPi a as)

  pibindAll : PiInfo -> List (Maybe Name, RawImp) ->
              RawImp -> RawImp
  pibindAll p [] scope = scope
  pibindAll p ((n, ty) :: rest) scope
           = IPi p n Nothing ty (pibindAll p rest scope)

  bindList : FileName -> IndentInfo ->
             Rule (List (Name, RawImp))
  bindList fname indents
      = sepBy1 (symbol ",")
               (do n <- unqualifiedName
                   ty <- option
                            Implicit
                            (do symbol ":"
                                appExpr fname indents)
                   pure (UN n, ty))

  pibindListName : FileName -> IndentInfo ->
                   Rule (List (Name, RawImp))
  pibindListName fname indents
       = do ns <- sepBy1 (symbol ",") unqualifiedName
            symbol ":"
            ty <- expr fname indents
            atEnd indents
            pure (map (\n => (UN n, ty)) ns)
     <|> sepBy1 (symbol ",")
                (do n <- name
                    symbol ":"
                    ty <- expr fname indents
                    pure (n, ty))

  pibindList : FileName -> IndentInfo ->
               Rule (List (Maybe Name, RawImp))
  pibindList fname indents
    = do params <- pibindListName fname indents
         pure $ map (\(n, ty) => (Just n, ty)) params

  forall_ : FileName -> IndentInfo -> Rule RawImp
  forall_ fname indents
      = do keyword "forall"
           commit
           ns <- sepBy1 (symbol ",") unqualifiedName
           let binders = map (\n => (Just (UN n), Implicit)) ns
           symbol "."
           scope <- typeExpr fname indents
           pure (pibindAll Implicit binders scope)

  implicitPi : FileName -> IndentInfo -> Rule RawImp
  implicitPi fname indents
      = do symbol "{"
           binders <- pibindList fname indents
           symbol "}"
           symbol "->"
           scope <- typeExpr fname indents
           end <- location
           pure (pibindAll Implicit binders scope)

  explicitPi : FileName -> IndentInfo -> Rule RawImp
  explicitPi fname indents
      = do symbol "("
           binders <- pibindList fname indents
           symbol ")"
           exp <- bindSymbol
           scope <- typeExpr fname indents
           end <- location
           pure (pibindAll exp binders scope)

  explicitLam : FileName -> IndentInfo -> Rule RawImp
  explicitLam fname indents
    = do symbol "\\"
         binders <- bindList fname indents
         symbol "=>"
         mustContinue indents Nothing
         scope <- expr fname indents
         end <- location
         pure (bindAll binders scope)
    where
      bindAll : List (Name, RawImp) -> RawImp -> RawImp
      bindAll [] scope = scope
      bindAll ((n, ty) :: rest) scope
         = ILam Explicit (Just n) Nothing ty (bindAll rest scope)

  implicitLam : FileName -> IndentInfo -> Rule RawImp
  implicitLam fname indents
      = do symbol "\\"
           symbol "{"
           binders <- bindList fname indents
           symbol "}"
           symbol "=>"
           mustContinue indents Nothing
           scope <- expr fname indents
           end <- location
           pure (bindAll binders scope)
     where
       bindAll : List (Name, RawImp) -> RawImp -> RawImp
       bindAll [] scope = scope
       bindAll ((n, ty) :: rest) scope
           = ILam Implicit (Just n) Nothing ty (bindAll rest scope)

  let_ : FileName -> IndentInfo -> Rule RawImp
  let_ fname indents
       = do keyword "let"
            vars <- block (letVar fname)
            continue indents
            keyword "in"
            scope <- typeExpr fname indents
            end <- location
            pure (bindAll vars scope)
    where
    letVar : FileName -> IndentInfo -> Rule (Name, Maybe RawImp, RawImp)
    letVar fname indents =
      do n <- name
         mvalTy <- (do symbol ":"
                       nTy <- expr fname indents
                       pure $ Just nTy) <|>
                   (pure Nothing)
         symbol "="
         commit
         val <- expr fname indents
         pure (n, mvalTy, val)
    bindAll : List (Name, Maybe RawImp, RawImp) -> RawImp -> RawImp
    bindAll [] scope = scope
    bindAll ((n, mnTy, nTm)::xs) scope = ILet n mnTy nTm $ bindAll xs scope

  quote : FileName -> IndentInfo -> Rule RawImp
  quote fname indents
    = do symbol "[|"
         scope <- expr fname indents
         symbol "|]"
         end <- location
         pure (IQuote scope)

  code_type : FileName -> IndentInfo -> Rule RawImp
  code_type fname indents
    = do symbol "<"
         scope <- expr fname indents
         symbol ">"
         end <- location
         pure (ICode scope)

  eval_quote : FileName -> IndentInfo -> Rule RawImp
  eval_quote fname indents
    = do symbol "!"
         scope <- simpleExpr fname indents
         end <- location
         pure (IEval scope)

  escape_quote : FileName -> IndentInfo -> Rule RawImp
  escape_quote fname indents
    = do symbol "~"
         scope <- simpleExpr fname indents
         end <- location
         pure (IEscape scope)

  pat : FileName -> IndentInfo -> Rule RawImp
  pat fname indents
      = do keyword "pat"
           binders <- many (boundsImp <|> boundsExp)
           symbol "=>"
           mustContinue indents Nothing
           scope <- expr fname indents
           end <- location
           pure (bindAll (concat binders) scope)
     where
       boundsImp : Rule (List (PiInfo, Name, RawImp))
       boundsImp = do symbol "{"
                      bs <- bindList fname indents
                      symbol "}"
                      pure $ map (\(n,ri)=>(Implicit,n,ri)) bs
       boundsExp : Rule (List (PiInfo, Name, RawImp))
       boundsExp = do bs <- bindList fname indents
                      pure $ map (\(n,ri)=>(Explicit,n,ri)) bs
       bindAll : List (PiInfo, Name, RawImp) -> RawImp -> RawImp
       bindAll [] scope = scope
       bindAll ((p, n, ty) :: rest) scope
           = IPatvar n Nothing ty (bindAll rest scope)

  binder : FileName -> IndentInfo -> Rule RawImp
  binder fname indents
      = forall_ fname indents
    <|> implicitPi fname indents
    <|> explicitPi fname indents
    <|> implicitLam fname indents
    <|> explicitLam fname indents
    <|> pat fname indents
    <|> let_ fname indents

  caseRHS : FileName -> IndentInfo -> RawImp ->
            Rule ImpClause
  caseRHS fname indents lhs
      = do symbol "==>"
           commit
           rhs <- expr fname indents
           atEnd indents
           pure (PatClause lhs rhs)
    <|> do keyword "impossible"
           atEnd indents
           pure (ImpossibleClause lhs)

  caseClause : FileName -> IndentInfo -> Rule ImpClause
  caseClause fname indents
    = do lhs <- expr fname indents
         caseRHS fname indents lhs

  case_ : FileName -> IndentInfo -> Rule RawImp
  case_ fname indents
    = do keyword "case"
         scr <- expr fname indents
         keyword "of"
         alts <- block (caseClause fname)
         atEnd indents
         pure (ICase scr Implicit alts)

tyDecl : FileName -> IndentInfo -> Rule ImpTy
tyDecl fname indents
    = do n <- name
         symbol ":"
         ty <- expr fname indents
         atEnd indents
         pure (MkImpTy n ty)

parseRHS : FileName -> IndentInfo -> RawImp ->
           Rule (Name, ImpClause)
parseRHS fname indents lhs
    = do symbol "="
         commit
         rhs <- expr fname indents
         atEnd indents
         pure (!(getFn lhs), PatClause lhs rhs)
  <|> do keyword "impossible"
         atEnd indents
         pure (!(getFn lhs), ImpossibleClause lhs)
  where
    getFn : RawImp -> SourceEmptyRule Name
    getFn (IVar n) = pure n
    getFn (IApp _ f a) = getFn f
    getFn (IPatvar _ _ _ sc) = getFn sc
    getFn _ = fail "Not a function application"

ifThenElse : Bool -> Lazy t -> Lazy t -> t
ifThenElse True t e = t
ifThenElse False t e = e

clause : FileName -> IndentInfo -> Rule (Name, ImpClause)
clause fname indents
    = do lhs <- expr fname indents
         parseRHS fname indents lhs

definition : FileName -> IndentInfo -> Rule ImpDecl
definition fname indents
    = do nd <- clause fname indents
         pure (IDef (fst nd) [snd nd])

dataDecl : FileName -> IndentInfo -> Rule ImpData
dataDecl fname indents
    = do info <- (do keyword "data"
                     pure ITyCParam) <|>
                 (do keyword "simple"
                     pure ITyCSimp)  <|>
                 (do keyword "object"
                     pure ITyCObj)
         n <- name
         symbol ":"
         ty <- expr fname indents
         keyword "where"
         cs <- block (tyDecl fname)
         pure (MkImpData n info ty cs)

import_ : FileName -> IndentInfo -> Rule String
import_ fname indents
  = do keyword "import"
       ns <- namespacedIdent
       pure . join "." $ reverse ns

-- Declared at the top
-- topDecl : FileName -> IndentInfo -> Rule ImpDecl
topDecl fname indents
    = do dat <- dataDecl fname indents
         pure (IData dat)
  <|> do impstr <- import_ fname indents
         pure (IImport impstr)
  <|> do claim <- tyDecl fname indents
         pure (IClaim claim)
  <|> definition fname indents

-- Declared at the top
-- collectDefs : List ImpDecl -> List ImpDecl
collectDefs [] = []
collectDefs (IDef fn cs :: ds)
    = let (cs', rest) = spanMap (isClause fn) ds in
          IDef fn (cs ++ cs') :: assert_total (collectDefs rest)
  where
    spanMap : (a -> Maybe (List b)) -> List a -> (List b, List a)
    spanMap f [] = ([], [])
    spanMap f (x :: xs) = case f x of
                               Nothing => ([], x :: xs)
                               Just y => case spanMap f xs of
                                              (ys, zs) => (y ++ ys, zs)

    isClause : Name -> ImpDecl -> Maybe (List ImpClause)
    isClause n (IDef n' cs)
        = if n == n' then Just cs else Nothing
    isClause n _ = Nothing
collectDefs (d :: ds)
    = d :: collectDefs ds

-- full programs
export
prog : FileName -> Rule (List ImpDecl)
prog fname
    = do ds <- nonEmptyBlock (topDecl fname)
         pure (collectDefs ds)
