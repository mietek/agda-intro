module L4List where

open import L4NatCrib public
open import L4OrnCrib

{- Let's see how to build lists from natural numbers by
   inserting a label in the step case. -}

ListO : Set -> Orn One _ NatD
ListO X = {!!}

{- Conor, before you go any further, you'll need to go
   back to L4Orn.agda -}







{-
{- Get the description by interpreting the ornament. -}

ListD : Set -> Desc One
ListD A = ornD (ListO A)

{- Define the List types. -}

List : Set -> Set
List X = Data (ListD X) <>

{- Check that you really get the constructors. -}

[l] : forall {A} -> List A
[l] = {!!}
_:l:_ : forall {A} -> A -> List A -> List A
a :l: x = {!!}

{- define append as a fold -}

_+l+_ : forall {A} -> List A -> List A -> List A
xs +l+ ys = fold {X = k (List _)} {!!} xs

{- Conor, the last example is after a lot of space lines, because you
   need to go and seal the deal in L4Orn.agda -}
-}

































{-
length : forall {A} -> List A -> Nat
length {A} = forget (ListO A)
-}

{- But that's not all, folks. We're free to invent ornaments, but we can
   also COMPUTE them! Let's truck on over to L4AlgOrn.agda -}