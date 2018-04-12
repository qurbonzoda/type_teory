module Setoid

%default total
%access public export

Reflexive : {C : Type} -> (C -> C -> Type) -> Type
Reflexive {C} R = (x : C) -> R x x

Symmetric : {C : Type} -> (C -> C -> Type) -> Type
Symmetric {C} R = (x : C) -> (y : C)
               -> R x y -> R y x

Transitive : {C : Type} -> (C -> C -> Type) -> Type
Transitive {C} R = (x : C) -> (y : C) -> (z : C)
                -> R x y -> R y z -> R x z

data IsEquivalence : {C : Type}
                  -> (C -> C -> Type)
                  -> Type
                  where
    EqProof : {C : Type}
           -> (R : C -> C -> Type)
           -> Reflexive {C} R
           -> Symmetric {C} R
           -> Transitive {C} R
           -> IsEquivalence {C} R

record Setoid where
    constructor MkSetoid
    C : Type
    Equivalence : C -> C -> Type
    P : IsEquivalence Equivalence
