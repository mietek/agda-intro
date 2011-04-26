module Lec5 where

open import VecFin
open import Lambda
open import View

data Zero : Set where -- no constructors!

data Poly : Set where
  I'          :                  Poly  -- the identity
  Zero' One'  :                  Poly  -- constants
  _+'_ _*'_   : (P Q : Poly) ->  Poly  -- choice and pairing

<_>P : Poly -> Set -> Set
< I'      >P  X  =  X
< Zero'   >P  X  =  Zero
< One'    >P  X  =  One
< P +' Q  >P  X  =  < P >P X + < Q >P X
< P *' Q  >P  X  =  < P >P X * < Q >P X

<_>p : (P : Poly) -> {X Y : Set} -> (X -> Y) -> < P >P X -> < P >P Y
<_>p I' f x = f x
<_>p Zero' f x = x
<_>p One' f x = x
<_>p (P +' Q) f (inl p) = inl (< P >p f p)
<_>p (P +' Q) f (inr q) = inr (< Q >p f q)
<_>p (P *' Q) f (p , q) = < P >p f p , < Q >p f q

-- exercise, functor laws

-- show < P >P can always be equipped idiomatic traverse

cp : Poly -> Poly -> Poly
cp I' R = R
cp Zero' _ = Zero'
cp One' _ = One'
cp (P +' Q) R = cp P R +' cp Q R
cp (P *' Q) R = cp P R *' cp Q R

-- ring a bell?
-- what to prove?

-- cp P I = P
-- cp associative

data _=1=_ {X : Set1}(x : X) : X -> Set1 where
  refl : x =1= x

-- should really go back and make the original polymorphic
-- will revisit soon

cpRespect : (P R : Poly)(X : Set) -> < cp P R >P X =1= < P >P (< R >P X)
cpRespect I' R X = refl
cpRespect Zero' R X = refl
cpRespect One' R X = refl
cpRespect (P +' Q) R X with < cp P R >P X | cpRespect P R X | < cp Q R >P X | cpRespect Q R X
cpRespect (P +' Q) R X | ._ | refl | ._ | refl = refl
cpRespect (P *' Q) R X with < cp P R >P X | cpRespect P R X | < cp Q R >P X | cpRespect Q R X
cpRespect (P *' Q) R X | ._ | refl | ._ | refl = refl

-- what happens for the morphisms?

D : Poly -> Poly
D I' = One'
D Zero' = Zero'
D One' = Zero'
D (P +' Q) = D P +' D Q
D (P *' Q) = (D P *' Q) +' (P *' D Q)


Div : Poly -> Poly
Div P = D P *' I'

_-P>_ : Poly -> Poly -> Set1
P -P> Q = {X : Set} -> < P >P X -> < Q >P X

up : (P : Poly) -> Div P -P> P
up I' (<> , x) = x
up Zero' (() , y)
up One' (() , x)
up (P +' Q) (inl p' , x) = inl (up P (p' , x))
up (P +' Q) (inr q' , x) = inr (up Q (q' , x))
up (P *' Q) (inl (p' , q) , x) = up P (p' , x) , q
up (P *' Q) (inr (p , q') , x) = p , up Q (q' , x)

down : (P : Poly) -> P -P> cp P (Div P)
down I' px = {!!}
down Zero' px = {!!}
down One' px = {!!}
down (P +' Q) px = {!!}
down (P *' Q) px = {!!}

discard : (P : Poly) -> Div P -P> I'
discard P (_ , x) = x

sideways : (P : Poly) -> Div P -P> cp (Div P) (Div P)
sideways P p'x = {!!}