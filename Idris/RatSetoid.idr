module RatSetoid

import Setoid
import MyInt
import IntSetoid
import Rat

%default total

ratReflx : Reflexive RatEq
ratReflx (MkRat a b) = RatRefl $ intReflexive $ a *** S b

ratSym : Symmetric RatEq
ratSym (MkRat a b) (MkRat c d) (RatRefl eq) =
    RatRefl $ intSymmetric (a *** S d) (c *** S b) eq

{-
    (a1 * S d) + (c2 * S b) = (c1 * S b) + (a2 * S d)
    (c1 * S f) + (e2 * S d) = (e1 * S d) + (c2 * S f)
    =>
    (a1 * S d) * S f + (c2 * S b) * S f = (c1 * S b) * S f + (a2 * S d) * S f
    (c1 * S f) * S b + (e2 * S d) * S b = (e1 * S d) * S b + (c2 * S f) * S b
    =>
    (a1 * S d) * S f + (c2 * S b) * S f + (c1 * S f) * S b + (e2 * S d) * S b =
    (c1 * S b) * S f + (a2 * S d) * S f + (e1 * S d) * S b + (c2 * S f) * S b
    =>
    (a1 * S d) * S f + (e2 * S d) * S b =
    (a2 * S d) * S f + (e1 * S d) * S b
    =>
    S d * (a1 * S f + e2 * S b) = S d * (a2 * S f + e1 * S b)
    =>
    a1 * S f + e2 * S b = e1 * S b + a2 * S f
-}
ratTrans : Transitive RatEq
ratTrans
    (MkRat (MkInt a1 a2) b)
    (MkRat (MkInt c1 c2) d)
    (MkRat (MkInt e1 e2) f)
    (RatRefl (IntRefl eq1))
    (RatRefl (IntRefl eq2)) = RatRefl $ IntRefl transPrf
  where
    step1' : u1 * S y + v2 * S x = v1 * S x + u2 * S y
          -> u1 * S y * S z + v2 * S x * S z = v1 * S x * S z + u2 * S y * S z
    step1' prf {u1} {u2} {v1} {v2} {x} {y} {z} =
        rewrite sym $ multDistributesOverPlusLeft (u1 * S y) (v2 * S x) (S z)
        in rewrite sym $ multDistributesOverPlusLeft (v1 * S x) (u2 * S y) (S z)
        in cong {f = (* S z)} prf

    step1'eq1 : a1 * S d * S f + c2 * S b * S f = c1 * S b * S f + a2 * S d * S f
    step1'eq1 = step1' eq1

    step1'eq2 : c1 * S f * S b + e2 * S d * S b = e1 * S d * S b + c2 * S f * S b
    step1'eq2 = step1' eq2

    step2' : {u, v, x, y : Nat}
          -> u = v -> x = y
          -> u + x = v + y
    step2' prf1 prf2 = rewrite prf1 in rewrite prf2 in Refl

    step2 : (a1 * S d * S f + c2 * S b * S f) + (c1 * S f * S b + e2 * S d * S b) =
            (c1 * S b * S f + a2 * S d * S f) + (e1 * S d * S b + c2 * S f * S b)
    step2 = step2' step1'eq1 step1'eq2

    step3 : a1 * S d * S f + e2 * S d * S b =
            a2 * S d * S f + e1 * S d * S b
    step3 = rewrite plusCommutative (a1 * S d * S f) (e2 * S d * S b) in int5
      where
        int1Left : (a1 * S d * S f + c2 * S b * S f) + (c1 * S f * S b + e2 * S d * S b) =
                   (c1 * S f * S b + e2 * S d * S b) + (a1 * S d * S f + c2 * S f * S b)
        int1Left =
            rewrite sym $ multAssociative c2 (S f) (S b) in
            rewrite sym $ multAssociative c2 (S b) (S f) in
            rewrite sym $ multCommutative (S f) (S b) in
            rewrite plusCommutative
                ((a1 * S d) * S f + c2 * (S (b + f * S b)))
                ((c1 * S f) * S b + (e2 * S d) * S b) in Refl

        int1 : (c1 * S f * S b + e2 * S d * S b) + a1 * S d * S f + c2 * S f * S b =
               (c1 * S b * S f + a2 * S d * S f) + e1 * S d * S b + c2 * S f * S b
        int1 =
            rewrite sym $ plusAssociative
                (c1 * S f * S b + e2 * S d * S b)
                (a1 * S d * S f)
                (c2 * S f * S b)
            in rewrite sym $ plusAssociative
                (c1 * S b * S f + a2 * S d * S f)
                (e1 * S d * S b) (c2 * S f * S b) in rewrite sym $ int1Left in step2

        int2 : c1 * S f * S b + e2 * S d * S b + a1 * S d * S f =
               c1 * S b * S f + a2 * S d * S f + e1 * S d * S b
        int2 = plusRightCancel
            (c1 * S f * S b + e2 * S d * S b + a1 * S d * S f)
            (c1 * S b * S f + a2 * S d * S f + e1 * S d * S b)
            (c2 * S f * S b) int1

        int3 : c1 * S f * S b + (e2 * S d * S b + a1 * S d * S f) =
               c1 * S b * S f + (a2 * S d * S f + e1 * S d * S b)
        int3 = rewrite plusAssociative
                (c1 * S f * S b)
                (e2 * S d * S b)
                (a1 * S d * S f)
            in rewrite plusAssociative
                (c1 * S b * S f)
                (a2 * S d * S f)
                (e1 * S d * S b) in int2

        int4Left : c1 * S b * S f + (e2 * S d * S b + a1 * S d * S f) =
                   c1 * S f * S b + (e2 * S d * S b + a1 * S d * S f)
        int4Left =
            rewrite sym $ multAssociative c1 (S b) (S f)
            in rewrite multCommutative (S b) (S f)
            in rewrite multAssociative c1 (S f) (S b) in Refl

        int4 : c1 * S b * S f + (e2 * S d * S b + a1 * S d * S f) =
               c1 * S b * S f + (a2 * S d * S f + e1 * S d * S b)
        int4 = rewrite int4Left in int3

        int5 : (e2 * S d) * S b + (a1 * S d) * S f =
               (a2 * S d) * S f + (e1 * S d) * S b
        int5 = plusLeftCancel
            (c1 * S b * S f)
            (e2 * S d * S b + a1 * S d * S f)
            (a2 * S d * S f + e1 * S d * S b)
            int4

    step4 : S d * (a1 * S f + e2 * S b) = S d * (a2 * S f + e1 * S b)
    step4 =
        rewrite multDistributesOverPlusRight (S d) (a1 * S f) (e2 * S b)
        in rewrite multDistributesOverPlusRight (S d) (a2 * S f) (e1 * S b)
        in rewrite plusMiddleLaw (S d) a1 (S f)
        in rewrite plusMiddleLaw (S d) a2 (S f)
        in rewrite plusMiddleLaw (S d) e1 (S b)
        in rewrite plusMiddleLaw (S d) e2 (S b) in step3 where
            plusMiddleLaw : (x : Nat) -> (y : Nat) -> (z : Nat) -> x * (y * z) = y * x * z
            plusMiddleLaw x y z =
                rewrite multAssociative x y z
                in rewrite multCommutative x y
                in Refl

    transPrf : a1 * S f + e2 * S b = e1 * S b + a2 * S f
    transPrf = rewrite plusCommutative (e1 * S b) (a2 * S f)
        in multLeftCancel _ _ _ step4 where
            addensumIsZero : (x : Nat) -> (y : Nat) -> x + y = 0 -> x = 0
            addensumIsZero x Z prf = rewrite plusCommutative 0 x in prf

            addensumIsZero x (S k) prf = void $ SIsNotZ tmp where
                tmp : S k + x = 0
                tmp = rewrite plusCommutative (S k) x in prf

            multLeftCancel : (x, y, z : Nat)
                          -> S x * y = S x * z
                          -> y = z
            multLeftCancel x Z z prf = sym $ addensumIsZero _ _ (sym tmp) where
                tmp : 0 * x = z + (x * z)
                tmp = rewrite multCommutative 0 x in prf
            multLeftCancel x y Z prf = addensumIsZero _ _
                (rewrite multCommutative 0 x in prf)
            multLeftCancel x (S k) (S j) prf =
                let rec = multLeftCancel x k j in
                rewrite rec (plusLeftCancel _ _ _ int2) in Refl where
                    prf' : k + x * S k = j + x * S j
                    prf' = succInjective _ _ prf

                    int1 : k + (x + x * k) = j + (x + x * j)
                    int1 = rewrite sym $ multRightSuccPlus x k
                        in rewrite sym $ multRightSuccPlus x j in prf'

                    int2 : x + (k + x * k) = x + (j + x * j)
                    int2 = rewrite plusAssociative x k (x * k)
                        in rewrite plusAssociative x j (x * j)
                        in rewrite plusCommutative x k
                        in rewrite plusCommutative x j
                        in rewrite sym $ plusAssociative k x (x * k)
                        in rewrite sym $ plusAssociative j x (x * j) in int1

RatSetoid : Setoid
RatSetoid = let prf = EqProof RatEq ratReflx ratSym ratTrans
    in MkSetoid Rat RatEq prf
