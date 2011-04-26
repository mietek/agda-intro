module Lec3 where
open import VecFin

data Tm (n : Nat) : Set where
  var   : (i : Fin n) ->         Tm n
  _$_   : (f a : Tm n) ->  Tm n
  lam   : (b : Tm (suc n)) ->    Tm n

infixl 6 _$_

sren : {m n : Nat} -> (Fin m -> Fin n) -> Tm m -> Tm n
sren s (var i) = var (s i)
sren s (f $ a) = sren s f $ sren s a
sren s (lam b) = lam (sren (weaken s) b)

ssub : {m n : Nat} -> (Fin m -> Tm n) -> Tm m -> Tm n
ssub s (var i) = s i
ssub s (f $ a) = ssub s f $ ssub s a
ssub {m}{n} s (lam b) = lam (ssub s' b) where
  s' : Fin (suc m) -> Tm (suc n)
  s' zero = var zero
  s' (suc i) = sren suc (s i)

infixr 4 _>>_
infixr 3 _!-_
infixr 3 _-!_

data Ty : Set where
  iota  :                Ty
  _>>_  : (S T : Ty) ->  Ty

[_]T : Ty -> Set
[ iota ]T = Nat
[ S >> T ]T = [ S ]T -> [ T ]T

data Context : Set where
  <>   : Context
  _,_  : (G : Context)(S : Ty) -> Context

[_]C : Context -> Set
[ <> ]C = One
[ G , S ]C = [ G ]C * [ S ]T

data _-!_ : Context -> Ty -> Set where
  zero  : forall {G T}                  -> G , T -! T
  suc   : forall {G S T}  (x : G -! T)  -> G , S -! T

[_]v : forall {G T} -> G -! T -> [ G ]C -> [ T ]T
[_]v zero = snd
[_]v (suc x) = \ gs -> [ x ]v (fst gs)

data _!-_ : Context -> Ty -> Set where

  var  : forall {G T}            (x : G -! T)
                          ->   ----------------
                                 G !- T

  -- $\lambda$-abstraction extends the context

  lam  : forall {G S T}          (b : G , S !- T)
                          ->   --------------------
                                 G !- S >> T

  -- application demands a type coincidence

  _$_  : forall {G S T}         (f : G !- S >> T)   (s : G !- S)
                          ->  ------------------------------------
                                G !- T


[_]t : forall {G T} -> G !- T -> [ G ]C -> [ T ]T
[ var x ]t = \ g -> [ x ]v g
[ lam b ]t = \ g s -> [ b ]t (g , s)
[ f $ s ]t = \ g -> [ f ]t g ([ s ]t g)

twice : forall {G T} -> G !- ((T >> T) >> (T >> T))
twice = lam (lam (var (suc zero) $ (var (suc zero) $ var zero)))