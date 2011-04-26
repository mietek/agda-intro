module L4OrnCrib where

open import L4DescCrib public

{- The inverse image construction -}

data _^-1_ {I J : Set}(f : J -> I) : I -> Set where
  ok : (j : J) -> f ^-1 (f j)

{- ok j : f ^-1 i  iff  f j = i -}

{- The type of acetate overlays! -}

{- Here,   J is the type of fancy indices
           I is the type of plain indices
           f : J -> I  rubs out the fancy

   Remember, for Nat, I is One, so f is kind of predictable.
-}

data Orn {I}(J : Set)(f : J -> I) : Desc I -> Set1 where
  -- the first three mean "keep the existing format"
  -- but you still have to give a fancy j , good for each plain i
  say    : {i : I}(j : f ^-1 i) ->
           Orn J f (say i)
  sg     : (S : Set){D : S -> Desc I}(O : (s : S) -> Orn J f (D s)) ->
           Orn J f (sg S D)
  ask_*_ : {i : I}(j : f ^-1 i){D : Desc I}(O : Orn J f D) ->
           Orn J f (ask i * D)
  -- the last constructor says "insert a new field here, and depend on it"
  insert : (S : Set){D : Desc I}(O : S -> Orn J f D) ->
           Orn J f D

{- Conor, don't dare go any further without giving an example. Look at
   L4List.agda -}

{- We'd better make sure that ornamenting a plain description gives us
   a fancy description. That amounts to obeying the "insert" instructions. -}

ornD : forall {I J f}{D : Desc I} -> Orn J f D -> Desc J
ornD (say (ok j)) = say j
ornD (sg S O) = sg S \ s -> ornD (O s)
ornD (ask (ok j) * O) = ask j * ornD O
ornD (insert S O) = sg S \ s -> ornD (O s)

{- Conor, go to L4List.agda and check that we really get lists. -}

{- Read the rest of the file backwards. -}

{- Finally, all the worker function has to do is work through the
   ornament, deleting all the fields which got inserted. -}

ornAlgHelp : forall {I J f}{D : Desc I}{R : I -> Set} -> (O : Orn J f D) ->
              [ ornD O ] (R o f) :-> [ D ] R o f
ornAlgHelp (say (ok j)) refl = refl
ornAlgHelp (sg S O) (s , rs) = s , ornAlgHelp (O s) rs
ornAlgHelp (ask (ok j) * O) (r , rs) = r , ornAlgHelp O rs
ornAlgHelp (insert S O) (s , rs) = ornAlgHelp (O s) rs

{- So, the forgetful map is a fold, what's it's algebra?
   It's called the ORNAMENTAL ALGEBRA.
   It builds a plain node from a fancy node, then packs it with <_>. -}

ornAlg : forall {I J f}{D : Desc I}(O : Orn J f D) ->
           [ ornD O ] (Data D o f) :-> Data D o f
ornAlg D ds = < ornAlgHelp D ds >

{- We want to be sure that we can rub out the extra bits, to get plain
   data back from fancy data. We should be sure that f is respected. -}

forget : forall {I J f}{D : Desc I}(O : Orn J f D) ->
         (Data (ornD O)) :-> Data D o f
         -- forall {j} -> Data (ornD O) j -> Data D (f j)
forget O = fold (ornAlg O)
