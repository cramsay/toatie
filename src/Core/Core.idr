module Core.Core

import Core.Env
import Core.TT

import public Data.IORef
import Data.List
import Data.List1
import Data.Vect

import System
import System.File

%default covering

public export
data TTCErrorMsg
    = Format String Int Int
    | EndOfBuffer String
    | Corrupt String

public export
data CaseError = DifferingArgNumbers
               | DifferingTypes
               | MatchErased (vars ** (Env Term vars, Term vars))
               | NotFullyApplied Name
               | UnknownType

-- All possible errors, carrying a location
public export
data Error : Type where
     CantConvert : {vars : _} ->
                   Env Term vars -> Term vars -> Term vars -> Error
     UndefinedName : Name -> Error
     CaseCompile : Name -> CaseError -> Error
     GenericMsg : String -> Error
     InternalError : String -> Error
     BadDotPattern : {vars : _} -> Env Term vars -> Term vars -> Term vars -> Error
     ValidCase : {vars : _} -> Env Term vars -> Either (Term vars) Error -> Error
     FileErr : String -> FileError -> Error

export
Show Error where
  show (CantConvert env x y)
      = "Type mismatch: " ++ show x ++ " and " ++ show y
  show (UndefinedName x) = "Undefined name " ++ show x
  show (GenericMsg str) = str
  show (InternalError str) = str
  show (BadDotPattern env x y) = "Bad dot pattern: " ++ show x ++ " and " ++ show y
  show (ValidCase _ prob) = case prob of
                              Left tm => show tm ++ " is not a valid impossible pattern because it typechecks"
                              Right err => "Not a valid impossible pattern: " ++ show err
  show (CaseCompile n DifferingArgNumbers)
      = "Patterns for " ++ show n ++ " have different numbers of arguments"
  show (CaseCompile n DifferingTypes)
      = "Patterns for " ++ show n ++ " require matching on different types"
  show (CaseCompile n UnknownType)
      = "Can't infer type to match in " ++ show n
  show (CaseCompile n (MatchErased (_ ** (env, tm))))
      = "Attempt to match on erased argument " ++ show tm ++
                   " in " ++ show n
  show (CaseCompile n (NotFullyApplied c))
      = "Constructor " ++ show c ++ " is not fully applied"

  show (FileErr fname err) = "File error (" ++ fname ++ "): " ++ show err

-- Core is a wrapper around IO that is specialised for efficiency.
export
record Core t where
  constructor MkCore
  runCore : IO (Either Error t)

export
coreRun : Core a ->
          (Error -> IO b) -> (a -> IO b) -> IO b
coreRun (MkCore act) err ok
    = either err ok !act

export
coreFail : Error -> Core a
coreFail e = MkCore (pure (Left e))

export
wrapError : (Error -> Error) -> Core a -> Core a
wrapError fe (MkCore prog)
    = MkCore (prog >>=
                 (\x => case x of
                             Left err => pure (Left (fe err))
                             Right val => pure (Right val)))

-- This would be better if we restrict it to a limited set of IO operations
export
%inline
coreLift : IO a -> Core a
coreLift op = MkCore (do op' <- op
                         pure (Right op'))

{- Monad, Applicative, Traversable are specialised by hand for Core.
In theory, this shouldn't be necessary, but it turns out that Idris 1 doesn't
specialise interfaces under 'case' expressions, and this has a significant
impact on both compile time and run time.
-}

-- Functor (specialised)
export %inline
map : (a -> b) -> Core a -> Core b
map f (MkCore a) = MkCore (map (map f) a)

-- Functor (specialised)
export %inline
ignore : Core a -> Core ()
ignore = map (\ _ => ())

export %inline
(<$>) : (a -> b) -> Core a -> Core b
(<$>) f (MkCore a) = MkCore (map (map f) a)

-- Monad (specialised)
export %inline
(>>=) : Core a -> (a -> Core b) -> Core b
(>>=) (MkCore act) f
    = MkCore (act >>=
                   (\x => case x of
                               Left err => pure (Left err)
                               Right val => runCore (f val)))

-- Monad (specialised)
export %inline
(>>) : Core () -> Core b -> Core b
ma >> mb = ma >>= \ () => mb

-- Applicative (specialised)
export %inline
pure : a -> Core a
pure x = MkCore (pure (pure x))

export
(<*>) : Core (a -> b) -> Core a -> Core b
(<*>) (MkCore f) (MkCore a) = MkCore [| f <*> a |]

export %inline
when : Bool -> Lazy (Core ()) -> Core ()
when True f = f
when False f = pure ()

-- Control.Catchable in Idris 1, just copied here (but maybe no need for
-- it since we'll only have the one instance for Core Error...)
public export
interface Catchable (m : Type -> Type) t | m where
    throw : t -> m a
    catch : m a -> (t -> m a) -> m a

export
Catchable Core Error where
  catch (MkCore prog) h
      = MkCore ( do p' <- prog
                    case p' of
                         Left e => let MkCore he = h e in he
                         Right val => pure (Right val))
  throw = coreFail

-- Traversable (specialised)
traverse' : (a -> Core b) -> List a -> List b -> Core (List b)
traverse' f [] acc = pure (reverse acc)
traverse' f (x :: xs) acc
    = traverse' f xs (!(f x) :: acc)

export
traverse : (a -> Core b) -> List a -> Core (List b)
traverse f xs = traverse' f xs []

export
traverseList1 : (a -> Core b) -> List1 a -> Core (List1 b)
traverseList1 f (x ::: xs) = [| f x ::: traverse f xs |]

export
traverseVect : (a -> Core b) -> Vect n a -> Core (Vect n b)
traverseVect f [] = pure []
traverseVect f (x :: xs) = [| f x :: traverseVect f xs |]

export
traverseOpt : (a -> Core b) -> Maybe a -> Core (Maybe b)
traverseOpt f Nothing = pure Nothing
traverseOpt f (Just x) = map Just (f x)

export
traverse_ : (a -> Core ()) -> List a -> Core ()
traverse_ f [] = pure ()
traverse_ f (x :: xs)
    = do f x
         traverse_ f xs

export
traverseList1_ : (a -> Core ()) -> List1 a -> Core ()
traverseList1_ f (x ::: xs) = do
  f x
  traverse_ f xs

namespace Binder
  export
  traverse : (a -> Core b) -> Binder a -> Core (Binder b)
  traverse f (Lam s p ty) = pure $ Lam s p !(f ty)
  traverse f (Pi s p ty) = pure $ Pi s p !(f ty)
  traverse f (Let s var ty) = pure $ Let s !(f var) !(f ty)
  traverse f (PVar s i ty) = pure $ PVar s i !(f ty)
  traverse f (PVTy s ty) = pure $ PVTy s !(f ty)

export
anyM : (a -> Core Bool) -> List a -> Core Bool
anyM f [] = pure False
anyM f (x :: xs)
    = if !(f x)
         then pure True
         else anyM f xs

export
allM : (a -> Core Bool) -> List a -> Core Bool
allM f [] = pure True
allM f (x :: xs)
    = if !(f x)
         then allM f xs
         else pure False

export
filterM : (a -> Core Bool) -> List a -> Core (List a)
filterM p [] = pure []
filterM p (x :: xs)
    = if !(p x)
         then do xs' <- filterM p xs
                 pure (x :: xs')
         else filterM p xs

export
data Ref : (l : label) -> Type -> Type where
     [search l]
	   MkRef : IORef a -> Ref x a

export
newRef : (x : label) -> t -> Core (Ref x t)
newRef x val
    = do ref <- coreLift (newIORef val)
         pure (MkRef ref)

export %inline
get : (x : label) -> {auto ref : Ref x a} -> Core a
get x {ref = MkRef io} = coreLift (readIORef io)

export %inline
put : (x : label) -> {auto ref : Ref x a} -> a -> Core ()
put x {ref = MkRef io} val = coreLift (writeIORef io val)

export
cond : List (Lazy Bool, Lazy a) -> a -> a
cond [] def = def
cond ((x, y) :: xs) def = if x then y else cond xs def

export
condC : List (Core Bool, Core a) -> Core a -> Core a
condC [] def = def
condC ((x, y) :: xs) def
    = if !x then y else condC xs def

export
log : String -> Int -> String -> Core ()
log src _ msg = coreLift . putStrLn $ src ++ " >>> " ++ msg
