{-# OPTIONS --universe-polymorphism #-}

module L4NatCrib where

open import L4DescCrib  -- ok, I'm trying to keep it robust.

{- I need a two element type to tag base or step cases. -}

data Tag : Set where
  base step : Tag

{- Mixfix madness! I've written a combinator for dependent
   case analysis on Tag, so I can write readable descriptions. -}

base->_step->_ :  forall {a}{P : Tag -> Set a} ->
                  P base -> P step -> (c : Tag) -> P c
base->_step->_ pb ps base = pb
base->_step->_ pb ps step = ps

{- Now let's describe the natural numbers. -}

NatD : Desc One
NatD = sg Tag (
  base-> say <>
  step-> ask <> * say <> )

{- We've got the description, so let's get the type. -}

Nat : Set
Nat = Data NatD <>

{- We'd better rebuild the constructors. -}

ze : Nat
ze = < base , refl >

su :  Nat -> Nat
su x = < step , x , refl >

{- Now let's build addition as a fold. What's the algebra? -}

adda : Nat -> [ NatD ] (k Nat) :-> k Nat
adda y (base , refl)      = y
adda y (step , z , refl)  = su z

{- Stick it in, turn it on. -}

_+_ : Nat -> Nat -> Nat
x + y = fold {X = k Nat} (adda y) x
