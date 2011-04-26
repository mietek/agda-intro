module L4Desc where

open import L4Basics public

{- Descriptions of indexed datatypes. -}

data Desc (I : Set) : Set1 where
  say    : (j : I) -> Desc I
  sg     : (S : Set)(D : S -> Desc I) -> Desc I
  ask_*_ : (i : I) -> (D : Desc I) -> Desc I

_:->_ : {I : Set} -> (I -> Set) -> (I -> Set) -> Set
X :-> Y = {i : _} -> X i -> Y i
infix 40 _:->_

{- Each Desc I represents an endofunctor on I -> Set. Let's see that. -}

[_] : forall {I} -> Desc I -> (I -> Set) -> (I -> Set)
[_] (say j) X i = j == i
[_] (sg S D) X i = Sg S \ s -> [ D s ] X i
[_] (ask i * D) X i' = X i * [ D ] X i'

map : forall {I X Y}(D : Desc I) -> (X :-> Y) -> [ D ] X :-> [ D ] Y
map (say i)      f        q = q
map (sg S D)     f (s , xs) = s , map (D s) f xs
map (ask i * D)  f (x , xs) = f x , map D f xs


{- Now let's tie the knot. -}

data Data {I : Set}(D : Desc I)(i : I) : Set where
  <_> : [ D ] (Data D) i -> Data D i

{- It's an inductive type (initial algebra), so we get an iterator
   in the classic style (?). -}

{-
fold : forall {I X}{D : Desc I} -> ([ D ] X :-> X) -> Data D :-> X
fold {D = D} phi < ds > = phi (map D (fold phi) ds)
-}

{- Bugger. We can beat this into the termination checker by specializing
   map to map-with-fold. -}

mutual
  fold : forall {I X}{D : Desc I} -> ([ D ] X :-> X) -> Data D :-> X
  fold {D = D} phi < ds > = phi (mapFold D D phi ds)

  mapFold : forall {I X}(D' D : Desc I) -> ([ D' ] X :-> X) -> 
            [ D ] (Data D') :-> [ D ] X
  mapFold D' (say i)      phi        q = q
  mapFold D' (sg S D)     phi (s , xs) = s , mapFold D' (D s) phi xs
  mapFold D' (ask i * D)  phi (x , xs) = fold  phi x , mapFold D' D phi xs


{- Conor, don't do the next bit now. It's far too abstract. What you really
   needed five minutes ago was an example. Go to L4Nat.agda for a bit. -}

{- ----------------------------------------------------------------------- -}

{- Conor, you should have jumped here from L4AlgOrn.agda -}

{- But we shouldn't only have an iterator. Inductive datatypes should have
   induction principles. Let's calculate them. -}

{- Step 1. A predicate transformer. If I have a structure full of X's,
   how do I lift a property P of X's to the property of structures that
   says "P holds for all the X's in here". (Hint X is going to be Data D,
   and this is going to *state* the inductive hypotheses.) -}

All : {I : Set}(D : Desc I){X : I -> Set}(P : {i : I} -> X i -> Set)
      {i : I} -> [ D ] X i -> Set
All (say i) P x             = One                -- no x in here
All (sg S D) P (s , xs)     = All (D s) P xs      -- s ain't no x
All (ask i * D) P (x , xs)  = P x * All D P xs    -- business, at last!

everywhere : {I : Set}(D : Desc I){X : I -> Set}
             (P : {i : I} -> X i -> Set) ->
             ({i : I}(x : X i) -> P x) ->         -- if P holds for all x
             {i : I}(d : [ D ] X i) -> All D P d  -- then P holds everywhere
everywhere (say i)      P p xs       = _ 
everywhere (sg S D)     P p (s , xs) = everywhere (D s) P p xs
everywhere (ask i * D)  P p (x , xs) = p x , everywhere D P p xs

induction : {I : Set}(D : Desc I)(P : {i : I} -> Data D i -> Set) ->
            ({i : I}
             (d : [ D ] (Data D) i) ->     -- a bunch of kids
             All D P d ->                  -- their inductive hypotheses
             P < d >) ->                   -- conclude P for parent
            {i : I}(x : Data D i) -> P x
induction D P p < d > = p d (everywhere D P (induction D P p) d)


{- Same problem, same fix. -}
{-
mutual
  induction : {I : Set}(D : Desc I)(P : {i : I} -> Data D i -> Set) ->
              ({i : I}(d : [ D ] (Data D) i) -> All D P d -> P < d >) ->
              {i : I}(x : Data D i) -> P x
  induction D P p < d > = p d (everywhereInduction D D P p d)
  everywhereInduction :
    {I : Set}(D' D : Desc I)
    (P : {i : I} -> Data D' i -> Set) ->
    ({i : I}(d : [ D' ] (Data D') i) -> All D' P d -> P < d >) ->
    {i : I}(d : [ D ] (Data D') i) -> All D P d
  everywhereInduction D' (say i)      P p xs       = _ 
  everywhereInduction D' (sg S D)     P p (s , xs) =
    everywhereInduction D' (D s) P p xs
  everywhereInduction D' (ask i * D)  P p (x , xs) =
    induction D' P p x , everywhereInduction D' D P p xs
-}

{- Conor, now go back to L4AlgOrn.agda -}