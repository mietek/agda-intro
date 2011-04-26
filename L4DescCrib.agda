module L4DescCrib where

open import L4Basics public

data Desc (I : Set) : Set1 where
  say    : (i : I) -> Desc I
  sg     : (S : Set)(D : S -> Desc I) -> Desc I
  ask_*_ : (j : I) -> (D : Desc I) -> Desc I

_:->_ : {I : Set} -> (I -> Set) -> (I -> Set) -> Set
X :-> Y = {i : _} -> X i -> Y i
infix 40 _:->_

[_] : forall {I} -> Desc I -> (I -> Set) -> (I -> Set)
[ say i'     ] X i = i' == i
[ sg S D     ] X i = Sg S \ s -> [ D s ] X i
[ ask i' * D ] X i = X i' * [ D ] X i

map : forall {I X Y}(D : Desc I) -> (X :-> Y) -> [ D ] X :-> [ D ] Y
map (say i)      f        q = q
map (sg S D)     f (s , xs) = s , map (D s) f xs
map (ask i * D)  f (x , xs) = f x , map D f xs

data Data {I : Set}(D : Desc I)(i : I) : Set where
  <_> : [ D ] (Data D) i -> Data D i

{-
fold : forall {I X}{D : Desc I} -> ([ D ] X :-> X) -> Data D :-> X
fold {D = D} phi < ds > = phi (map D (fold phi) ds)
-}

mutual
  fold : forall {I X}{D : Desc I} -> ([ D ] X :-> X) -> Data D :-> X
  fold {D = D} phi < ds > = phi (mapFold D D phi ds)

  mapFold : forall {I X}(D' D : Desc I) -> ([ D' ] X :-> X) -> 
            [ D ] (Data D') :-> [ D ] X
  mapFold D' (say i)      phi        q = q
  mapFold D' (sg S D)     phi (s , xs) = s , mapFold D' (D s) phi xs
  mapFold D' (ask i * D)  phi (x , xs) = fold  phi x , mapFold D' D phi xs


All : {I : Set}(D : Desc I){R : I -> Set}(P : {i : I} -> R i -> Set)
      {i : I} -> [ D ] R i -> Set
All (say i) P x            = One 
All (sg S D) P (s , d)     = All (D s) P d
All (ask i * D) P (x , d)  = P x * All D P d

{-
everywhere : {I : Set}(D : Desc I){R : I -> Set}
             (P : {i : I} -> R i -> Set) ->
             ({i : I}(x : R i) -> P x) ->
             {i : I}(d : [ D ] R i) -> All D P d
everywhere (say i)      P p d       = _ 
everywhere (sg S D)     P p (s , d) = everywhere (D s) P p d
everywhere (ask i * D)  P p (x , d) = p x , everywhere D P p d

induction : {I : Set}(D : Desc I)(P : {i : I} -> Data D i -> Set) ->
            ({i : I}(d : [ D ] (Data D) i) -> All D P d -> P < d >) ->
            {i : I}(x : Data D i) -> P x
induction D P p < d > = p d (everywhere D P (induction D P p) d)
-}

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
  everywhereInduction D' (say i)      P p d       = _ 
  everywhereInduction D' (sg S D)     P p (s , d) =
    everywhereInduction D' (D s) P p d
  everywhereInduction D' (ask i * D)  P p (x , d) =
    induction D' P p x , everywhereInduction D' D P p d
