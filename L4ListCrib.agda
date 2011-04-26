module L4ListCrib where

open import L4NatCrib public
open import L4OrnCrib

{- Let's see how to build lists from natural numbers by
   inserting a label in the step case. -}

ListO : Set -> Orn One _ NatD
ListO X = sg Tag (
  base-> say (ok <>)
  step-> insert X \ _ -> ask (ok <>) * say (ok <>) )

{- Conor, before you go any further, you'll need to go
   back to L4Orn.agda -}

{- Get the description by interpreting the ornament. -}

ListD : Set -> Desc One
ListD A = ornD (ListO A)

{- Define the List types. -}

List : Set -> Set
List X = Data (ListD X) _

{- Check that you really get the constructors. -}

[l] : forall {A} -> List A
[l] = < base , refl >
_:l:_ : forall {A} -> A -> List A -> List A
a :l: x = < step , a , x , refl >

{- define append as a fold -}

_+l+_ : forall {A} -> List A -> List A -> List A
xs +l+ ys = fold {X = k (List _)}
  (spl (base-> (\ _ -> ys)
        step-> (spl \ x -> spl \ zs _ -> x :l: zs))) xs

{- Conor, the last example is after a lot of space lines, because you
   need to go and seal the deal in L4Orn.agda -}



































length : forall {A} -> List A -> Nat
length {A} = forget (ListO A)
