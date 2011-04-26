module L4Le where

open import L4NatCrib
open import L4AlgOrnCrib

LeD : Nat -> Desc (One * Nat)
LeD n = ornD (algOrn NatD (adda n))

Le : Nat -> Nat -> Set
Le x y = Data (LeD x) (_ , y)

leq : {y : Nat} -> Le y y
leq {y} = < base , refl >

les : {x y : Nat} -> Le x y -> Le x (su y)
les p = < step , _ , p , refl >

trans : forall {x y z} -> Le x y -> Le y z -> Le x z
trans p < base , refl > = p
trans p < step , _ , q , refl > = < step , _ , trans p q , refl >

