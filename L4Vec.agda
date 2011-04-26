module L4Vec where

open import L4ListCrib public
open import L4AlgOrnCrib

VecO : (X : Set) -> Orn (One * Nat) fst (ListD X)
VecO X = algOrn (ListD X) (ornAlg (ListO X))

VecD : (X : Set) -> Desc (One * Nat)
VecD X = ornD (VecO X)

Vec : Nat -> Set -> Set
Vec n X = Data (VecD X) (<> , n)

[] : forall {X} -> Vec ze X
[] = {!!}
_::_ : forall {X n} -> X -> Vec n X -> Vec (su n) X
x :: xs = {!!}

vecToList : forall {X n} -> Vec n X -> List X
vecToList {X} = forget (VecO X)

listToVec : forall {X}(xs : List X) -> Vec (length xs) X
listToVec {X} = remember (ornAlg (ListO X))

{- Conor, go back to L4AlgOrn.agda and do the big shocking theorem! -}
