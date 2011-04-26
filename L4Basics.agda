{-# OPTIONS --universe-polymorphism #-}

{- Agda (from darcs only?) has an experimental implementation of
   universe polymorphism, allowing us to reuse equipment at all levels
   of the predicative hierarchy. Today, we shall be operating on
   structures which contain Sets. -}

module L4Basics where

{- This is the incantation which makes uni-poly happen. -}

data Level : Set where
  zl : Level
  sl : Level -> Level

{-# BUILTIN LEVEL Level #-}
{-# BUILTIN LEVELZERO zl #-}
{-# BUILTIN LEVELSUC sl #-}


{- This is dependent composition. Look at the function before worrying
   about the type. The type is exactly the thing that's as dependent
   and polymorphic as possible. -}

_o_ : ∀ {a b c}
        {A : Set a} {B : A → Set b} {C : {x : A} → B x → Set c} →
      (∀ {x} (y : B x) → C y) → (g : (x : A) → B x) →
      ((x : A) → C (g x))
f o g = \ x → f (g x)
infixl 50 _o_

{- Identity is reassuringly normal -}

id : forall {a} {A : Set a} → A → A
id x = x

{- The K combinator is also as standard... -}

k : forall {a b} {A : Set a} {B : Set b} → A → B → A
k x = \ _ → x

{- ... but wait till you see S in lecture 5. -}

{- A handful of elementary datatypes. -}

data Zero : Set where
record One : Set where
  constructor <>

record Sg (S : Set)(T : S -> Set) : Set where
  constructor _,_
  field
    fst : S
    snd : T fst
open Sg public
infixr 40 _,_

{- This is "split" or "spread". It's handy for higher
   order programming. If I'm asked for a function from
   a tuple, this lets me take it apart. -}

spl : forall {a S T} -> {P : Sg S T -> Set a} ->
      ((s : S)(t : T s) -> P (s , t)) ->
      (st : Sg S T) -> P st
spl p (s , t) = p s t

_*_ : Set -> Set -> Set
S * T = Sg S \ _ -> T

{- Show a bit of splitting, eh? -}

{- Homogeneous equality, in traditional form. -}

data _==_ {X : Set}(x : X) : X -> Set where
  refl : x == x

{- Conor, if you've forgotten already, the next file is L4Desc.agda -}