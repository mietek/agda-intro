module Lec1 where


data List (X : Set) : Set where
  <>    :                 List X
  _,_   : X -> List X ->  List X

infixr 4 _,_

{-
zap : {S T : Set} -> List (S -> T) -> List S -> List T
zap <> <> = <>
zap <> (y , y') = {!!}
zap (f , fs) <> = {!!}
zap (f , fs) (s , ss) = f s , zap fs ss
-}

data Nat : Set where
  zero  :         Nat
  suc   : (n : Nat) ->  Nat

length : {X : Set} -> List X -> Nat
length <>        = zero
length (x , xs)  = suc (length xs)


data Vec (X : Set) : Nat -> Set where
  <>    :                 Vec X zero
  _,_   : {n : Nat} -> X -> Vec X n ->  Vec X (suc n)

nid : Nat -> Nat
nid zero = zero
nid (suc n) = suc (nid n)

vap : forall {n S T} -> Vec (S -> T) n -> Vec S n -> Vec T n
vap <> <> = <>
vap (f , fs) (s , ss) = f s , vap fs ss

vec : forall {n X} -> X -> Vec X n
vec {zero} x = <>
vec {suc n} x = x , vec x

_+N_ : Nat -> Nat -> Nat
zero   +N y = y
suc x  +N y = suc (x +N y)

dbl : Nat -> Nat
dbl zero = zero
dbl (suc n) = suc (suc (dbl n))

swap : forall {n X} -> Vec X (dbl n) -> Vec X (dbl n)
swap {zero} <> = <>
swap {suc n}(x , (y , zs)) = y , (x , swap zs)

data _==_ {X : Set}(x : X) : X -> Set where
  refl : x == x

{-# BUILTIN EQUALITY _==_ #-}
{-# BUILTIN REFL refl #-}


sucLem : (x y : Nat) -> (x +N suc y) == suc (x +N y)
sucLem zero y = refl {- by agsy -}
sucLem (suc n) y rewrite sucLem n y = refl

{-
mutual 
  swap' : forall {X}(n : Nat) -> Vec X (n +N n) -> Vec X (n +N n)
  swap' (zero) <> = <>
  swap' (suc n)(x , ys) rewrite (sucLem n n) = swap'' n x ys

  swap'' : forall {X}(n : Nat) -> X -> 
           Vec X (suc (n +N n)) -> Vec X (suc (suc (n +N n)))
  swap'' n x (y , zs) = y , x , swap' n zs
-}
