module Homework.MyInt

%default total
%access public export

data Int' : Type where
     MkInt : Nat -> Nat -> Int'

implementation Num Int' where
    (MkInt a b) + (MkInt c d) = MkInt (a + c) (b + d)

    (MkInt a b) * (MkInt c d) = MkInt (a * c + b * d) (a * d + b * c)

    fromInteger n = if n > 0
        then MkInt (fromInteger n) Z
        else MkInt Z $ fromInteger . abs $ n

implementation Neg Int' where
    negate (MkInt a b) = MkInt b a

    (MkInt a b) - (MkInt c d) = MkInt (a + d) (b + c)

    abs n@(MkInt a b) = if a < b then negate n else n

infixl 8 ***
(***) : Int' -> Nat -> Int'
(MkInt a b) *** n = MkInt (a * n) (b * n)

data IntEq : Int' -> Int' -> Type where
    IntRefl : (eq : a + d = c + b) -> IntEq (MkInt a b) (MkInt c d)
