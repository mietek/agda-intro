module Lec2 where

data Nat : Set where
  zero  :         Nat
  suc   : Nat ->  Nat

{-# BUILTIN NATURAL Nat #-}
{-# BUILTIN ZERO zero #-}
{-# BUILTIN SUC suc #-}

data Vec (X : Set) : Nat -> Set where
  <>   :                               Vec X zero
  _,_  : {n : Nat} -> X -> Vec X n ->  Vec X (suc n)

infixr 4 _,_

data Fin : Nat -> Set where
  zero  : {n : Nat} ->                 Fin (suc n)
  suc   : {n : Nat} -> (i : Fin n) ->  Fin (suc n)


fog : {n : Nat} -> Fin n -> Nat
fog zero     = zero
fog (suc i)  = suc (fog i)

vproj : {n : Nat}{X : Set} -> Vec X n -> Fin n -> X
vproj <> ()
vproj (x , xs) zero    = x
vproj (x , xs) (suc i) = vproj xs i

fin0s : Vec (Fin zero) zero
fin0s = <>

fin1s : Vec (Fin (suc zero)) (suc zero)
fin1s = zero , <>

fin2s : Vec (Fin (suc (suc zero))) (suc (suc zero))
fin2s = zero {n = suc zero} , suc {n = suc zero} (zero {n = zero}) , <>

