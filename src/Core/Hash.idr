module Core.Hash

import Core.CaseTree
import Core.TT
import Core.CompileExpr

import Data.List
import Data.List1
import Data.String
import Data.Vect

-- Hashing functions over terms.
-- Unlike Idris2, we don't use this for binary storage, we just need it to make
-- sensible names for partially evaluated functions

%default covering

public export
interface Hashable a where
  hash : a -> Int
  hashWithSalt : Int -> a -> Int

  hash = hashWithSalt 5381
  hashWithSalt h i = h * 33 + hash i

infixl 5 `hashWithSalt`

export
Hashable Int where
  hash = id

export
Hashable Integer where
  hash = fromInteger

export
Hashable Nat where
  hash = cast

export
Hashable Char where
  hash = cast

export
Hashable a => Hashable (Vect n a) where
  hashWithSalt h [] = abs h
  hashWithSalt h (x :: xs) = hashWithSalt (h * 33 + hash x) xs

export
Hashable a => Hashable (List a) where
  hashWithSalt h [] = abs h
  hashWithSalt h (x :: xs) = hashWithSalt (h * 33 + hash x) xs

export
Hashable a => Hashable (List1 a) where
  hashWithSalt h xxs = hashWithSalt (h * 33 + hash (head xxs)) (tail xxs)

export
Hashable a => Hashable (Maybe a) where
  hashWithSalt h Nothing = abs h
  hashWithSalt h (Just x) = hashWithSalt h x

export
Hashable a => Hashable b => Hashable (a, b) where
  hashWithSalt h (x, y) = h `hashWithSalt` x `hashWithSalt` y

export
Hashable String where
  hashWithSalt h s = foldl hashWithSalt h $ unpack s

export
Hashable Double where
  hash = hash . show

export
Hashable Name where
  hashWithSalt h (UN n)   = hashWithSalt h n
  hashWithSalt h (MN n i) = h `hashWithSalt` n `hashWithSalt` i

export
Hashable PiInfo where
  hashWithSalt h Implicit = hashWithSalt h 0
  hashWithSalt h Explicit = hashWithSalt h 1

export
Hashable AppInfo where
  hashWithSalt h AImplicit = hashWithSalt h 0
  hashWithSalt h AExplicit = hashWithSalt h 1

export
Hashable ty => Hashable (Binder ty) where
  hashWithSalt h (Lam s i   ty) = h `hashWithSalt` 0 `hashWithSalt` i `hashWithSalt` ty
  hashWithSalt h (Pi  s i   ty) = h `hashWithSalt` 1 `hashWithSalt` i `hashWithSalt` ty
  hashWithSalt h (Let s val ty) = h `hashWithSalt` 2 `hashWithSalt` val `hashWithSalt` ty
  hashWithSalt h (PVar s i  ty) = h `hashWithSalt` 3 `hashWithSalt` i `hashWithSalt` ty
  hashWithSalt h (PVTy s    ty) = h `hashWithSalt` 4 `hashWithSalt` ty

Hashable (Var vars) where
  hashWithSalt h (MkVar {i} _) = hashWithSalt h i

mutual
  export
  Hashable (Term vars) where
    hashWithSalt h (Local idx p)    = h `hashWithSalt` 0  `hashWithSalt` idx
    hashWithSalt h (Ref x y)        = h `hashWithSalt` 1  `hashWithSalt` y
    hashWithSalt h (Meta x xs)      = h `hashWithSalt` 2  `hashWithSalt` x `hashWithSalt` xs
    hashWithSalt h (Bind x y scope) = h `hashWithSalt` 3  `hashWithSalt` y `hashWithSalt` scope
    hashWithSalt h (App x y z)      = h `hashWithSalt` 4  `hashWithSalt` y `hashWithSalt` z
    hashWithSalt h TType            = h `hashWithSalt` 5
    hashWithSalt h Erased           = h `hashWithSalt` 6
    hashWithSalt h (Quote ty tm)    = h `hashWithSalt` 7  `hashWithSalt` ty `hashWithSalt` tm
    hashWithSalt h (TCode x)        = h `hashWithSalt` 8  `hashWithSalt` x
    hashWithSalt h (Eval x)         = h `hashWithSalt` 9  `hashWithSalt` x
    hashWithSalt h (Escape x)       = h `hashWithSalt` 10 `hashWithSalt` x

  export
  Hashable Pat where
    hashWithSalt h (PCon x y tag arity xs) = h `hashWithSalt` 0 `hashWithSalt` x `hashWithSalt` xs
    hashWithSalt h (PQuote x ty tm)        = h `hashWithSalt` 1 `hashWithSalt` ty `hashWithSalt` tm
    hashWithSalt h (PLoc x tm)             = h `hashWithSalt` 2 `hashWithSalt` tm
    hashWithSalt h (PUnmatchable x)        = h `hashWithSalt` 3 `hashWithSalt` x
