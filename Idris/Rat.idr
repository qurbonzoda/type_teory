module Rat

import MyInt

%default total
%access public export

data Rat : Type where
     MkRat : Int' -> Nat -> Rat

implementation Num Rat where
    (MkRat a b) + (MkRat c d) = MkRat (a *** S d + c *** S b) (b + d + b * d)

    (MkRat a b) * (MkRat c d) = MkRat (a * c) (b + d + b * d)

    fromInteger a = MkRat (fromInteger a) 0

implementation Neg Rat where
    negate (MkRat a b) = MkRat (negate a) b
    a - b = a + negate b
    abs (MkRat a b) = MkRat (abs a) b

data RatEq : Rat -> Rat -> Type where
    RatRefl : {a, c: Int'}
           -> {b, d: Nat}
           -> (eq : IntEq (a *** S d) (c *** S b))
           -> RatEq (MkRat a b) (MkRat c d)
