import MyInt
import Setoid

%default total
%access public export

intReflexive : Reflexive IntEq
intReflexive (MkInt _ _) = IntRefl Refl

intSymmetric : Symmetric IntEq
intSymmetric (MkInt a b) (MkInt c d) (IntRefl eq) = IntRefl $ sym eq

{-  (a - b) = (c - d) -> (c - d) = (e - f) -> (a - b) = (e - f)
    (a + d) = (c + b) -> (c + f = e + d) -> (a + f = e + b)

    (a + d) + (c + f) = (c + b) + (e + d)
    (a + d) + (c + f) = (c + f) + (a + d)
    (c + f) + (a + d) = (c + f) + a + d
    (c + b) + (e + d) = (c + b) + e + d
    (c + f) + a + d = (c + b) + e + d
    c + f + a = c + b + e
    c + (f + a) = c + b + e
    f + a + c = c + b + e
    f + a + c = c + (b + e)
    f + a + c = b + e + c
    f + a = b + e
    a + f = b + e
    a + f = e + b
-}
intTransitive : Transitive IntEq
intTransitive (MkInt a b) (MkInt c d) (MkInt e f) (IntRefl eq1) (IntRefl eq2) =
    IntRefl rev2 where

    reflPlusRefl : {a : Nat} -> {b : Nat} -> {c : Nat} -> {d : Nat}
                -> (a = b)
                -> (c = d)
                -> (a + c = b + d)
    reflPlusRefl Refl Refl = Refl

    eq3  : (a + d) + (c + f) = (c + b) + (e + d)
    eq3  = reflPlusRefl eq1 eq2

    elD1 : (a + d) + (c + f) = (c + f) + (a + d)
    elD1 = plusCommutative (a + d) (c + f)

    elD2 : (c + f) + (a + d) = (c + f) + a + d
    elD2 = plusAssociative (c + f) a d

    elD3 : (c + b) + (e + d) = (c + b) + e + d
    elD3 = plusAssociative (c + b) e d

    elD4 : (c + f) + a + d = (c + b) + e + d
    elD4 = trans (sym elD2) $ trans (sym elD1) $ trans eq3 elD3

    elD  : c + f + a = c + b + e
    elD  = plusRightCancel ((c + f) + a) ((c + b) + e) d elD4

    elC1 : c + (f + a) = c + b + e
    elC1 = trans (plusAssociative c f a) elD

    elC2 : f + a + c = c + b + e
    elC2 = trans (plusCommutative (f + a) c) elC1

    elC3 : f + a + c = c + (b + e)
    elC3 = trans elC2 $ sym $ plusAssociative c b e

    elC4 : f + a + c = b + e + c
    elC4 = trans elC3 $ plusCommutative c (b + e)

    elC  : f + a = b + e
    elC  = plusRightCancel (f + a) (b + e) c elC4

    rev1 : a + f = b + e
    rev1 = trans (plusCommutative a f) elC

    rev2 : a + f = e + b
    rev2 = trans rev1 $ plusCommutative b e

IntSetoid : Setoid
IntSetoid =
    let prf = EqProof IntEq intReflexive intSymmetric intTransitive
    in MkSetoid Int' IntEq prf
