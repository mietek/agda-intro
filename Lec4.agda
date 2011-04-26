module Lec4 where
open import VecFin
open import Lambda

data _-Bounded?_ (u : Nat) : Nat -> Set where
  yes  : (i : Fin u) ->  u -Bounded? (fog i)
  no   : (x : Nat) ->    u -Bounded? (u +N x)

_-bounded?_ : (u n : Nat) -> u -Bounded? n
zero -bounded? n = no _
suc u -bounded? zero = yes zero
suc u -bounded? suc n with u -bounded? n
suc u -bounded? suc .(fog i) | yes i = yes (suc i)
suc u -bounded? suc .(u +N _) | no _  = no _


finl : (m : Nat){n : Nat} -> Fin m -> Fin (m +N n)
finl zero ()
finl (suc m) zero = zero
finl (suc m) (suc i) = suc (finl m i)

finr : (m : Nat){n : Nat} -> Fin n -> Fin (m +N n)
finr zero i = i
finr (suc m) i = suc (finr m i)

data FinSum (m n : Nat) : Fin (m +N n) -> Set where
  isFinl : (i : Fin m) -> FinSum m n (finl m i)
  isFinr : (j : Fin n) -> FinSum m n (finr m j)

finSum : (m : Nat){n : Nat}(k : Fin (m +N n)) -> FinSum m n k
finSum zero k = isFinr _
finSum (suc m) zero = isFinl _
finSum (suc m) (suc i) with finSum m i
finSum (suc m) (suc .(finl m i)) | isFinl i = isFinl (suc i)
finSum (suc m) (suc .(finr m j)) | isFinr j = isFinr j



Bin = Context Two

bone : Bin
bone = <>

bsuc : Bin -> Bin
bsuc <>        = <> , ff
bsuc (b , ff)  = b , tt
bsuc (b , tt)  = bsuc b , ff

peanoBin :  (P : Bin -> Set) ->
            (P bone) ->
            ((b : Bin) -> P b -> P (bsuc b)) ->
            (x : Bin) -> P x
peanoBin P pone psuc <> = pone
peanoBin P pone psuc (bs , tt) =
  peanoBin (\ bs -> P (bs , tt))
    (psuc _ (psuc _ pone)) (\ b p -> psuc _ (psuc _ p)) bs
peanoBin P pone psuc (bs , ff) =  peanoBin (\ bs -> P (bs , ff))
    (psuc _ pone) (\ b p -> psuc _ (psuc _ p)) bs

data PeanoBin : Bin -> Set where
  pone : PeanoBin bone
  psuc : forall {b} -> PeanoBin b -> PeanoBin (bsuc b)

pBsuc : (bs : Bin)(b : Two) -> PeanoBin bs -> PeanoBin (bs , b)
pBsuc .<> tt pone = psuc (psuc pone)
pBsuc .<> ff pone = psuc pone
pBsuc .(bsuc bs) tt (psuc {bs} p) = psuc (psuc (pBsuc bs tt p))
pBsuc .(bsuc bs) ff (psuc {bs} p) = psuc (psuc (pBsuc bs ff p))

pBin : (b : Bin) -> PeanoBin b
pBin <> = pone
pBin (bs , b) = pBsuc bs b (pBin bs)