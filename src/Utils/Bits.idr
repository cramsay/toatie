module Utils.Bits

import Data.Nat
import Data.Vect
import Data.String

export
data Bit : Type where
  O : Bit
  I : Bit

export
data Bits : Nat -> Type where
  Nil : Bits 0
  Snoc : Bits w -> Bit -> Bits (S w)

export
Show Bit where
  show O = "0"
  show I = "1"

export
{w : _} -> Show (Bits w) where
  show bs = show w ++ "b" ++ show' bs
    where
    show' : Bits w' -> String
    show' [] = ""
    show' (Snoc bs b) = show' bs ++ show b

export
fromNat : (width : Nat) -> (val : Nat) -> Maybe (Bits width)
fromNat 0 0 = Just []
fromNat 0 (S val) = Nothing
fromNat (S w) val
  = let lsb   = modNatNZ val 2 SIsNonZero
        msbs  = divNatNZ val 2 SIsNonZero
    in map (\rest => Snoc rest (if lsb == Z then O else I)) $ fromNat w msbs


public export
data BitRepTree : Type where
  BRNode : (width : Nat) -> (tag : Bits width) -> (fields : List BitRepTree) -> BitRepTree

export
Show BitRepTree where
  show tree = withIndents "" tree
    where
    withIndents : String -> BitRepTree -> String
    withIndents inds (BRNode _ tag []    ) = inds ++ show tag ++ "\n"
    withIndents inds (BRNode _ tag fields) = inds ++ show tag ++ " ->\n" ++
                                             foldl (++) "" (map (withIndents (inds ++ "  ")) fields)
