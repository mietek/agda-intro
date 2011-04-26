module L4AlgOrn where

open import L4OrnCrib public

{- Every algebra induces an ALGEBRAIC ORNAMENT -}

{- Conor, is there a picture? -}

algOrn : forall {I J}(D : Desc I) -> ([ D ] J :-> J) -> Orn (Sg I J) fst D
algOrn D phi = {!!}


{- Conor, you had better do some examples. First check out L4Le.agda -}

{- Conor, you'll need to say something about induction (L4Desc.agda) before
   introducing this bit. -}

{-
remember : forall {I J}{D : Desc I}(phi : [ D ] J :-> J) ->
             {i : I} -> 
             (d : Data D i) ->                            -- plain data
             Data (ornD (algOrn D phi)) (i , fold phi d)  -- becomes fancy

remember {I}{J}{D} phi =
  induction D (\ {i} d ->  Data (ornD (algOrn D phi)) (i , fold phi d))
  \ d hs -> < help D phi d hs > where
    help : (E : Desc I)(psi : [ E ] J :-> J)
           {i : I}
           (e : [ E ] (Data D) i) ->
           All E (\ {i} d -> Data (ornD (algOrn D phi)) (i , fold phi d)) e ->
           [ ornD (algOrn E psi) ]
             (Data (ornD (algOrn D phi))) (i , psi (mapFold D E phi e))
    help (say i)      psi refl    hs       = refl
    help (sg S E)     psi (s , e) hs       = s , help (E s) (psi o _,_ s) e hs
    help (ask i * E)  psi (d , e) (h , hs) = let j = fold phi d in
      j , h , help E (psi o _,_ j) e hs
-}

{- We've seen another algebra... -}

{- Conor, it's time for Vec.agda. -}













{-


AOOAThm : {I : Set}(D : Desc I){J : I -> Set}(phi : [ D ] J :-> J) ->
          let Dphi = algOrn D phi in
          {ij : Sg I J}(x : Data (ornD Dphi) ij) ->
          fold phi (fold (ornAlg Dphi) x)
            == snd ij

AOOAThm {I} D {J} phi =
  induction oDphi
  (\ {ij} x ->  fold phi (fold (ornAlg Dphi) x) == snd ij)
  (help D phi) where
    Dphi = algOrn D phi
    oDphi = ornD Dphi
    help : (E : Desc I)(psi : [ E ] J :-> J)
           {ij : Sg I J}
           (e : [ ornD (algOrn E psi) ] (Data oDphi) ij) ->
           All (ornD (algOrn E psi))
             (\ {ij} x -> fold phi (fold (ornAlg Dphi) x) == snd ij)
             e -> psi
           (mapFold D E phi
            (ornAlgHelp (algOrn E psi)
            (mapFold oDphi (ornD (algOrn E psi))
             (ornAlg Dphi) e)))
             == snd ij
    help (say i) psi refl hs = refl
    help (sg S E) psi (s , e) hs = help (E s) (psi o _,_ s) e hs
    help (ask i * E) psi (j , x , e) (h , hs)
      with fold phi (fold (ornAlg (algOrn D phi)) x)
    help (ask i * E) psi (j , x , e) (refl , hs) | .j =
      help E (psi o _,_ j) e hs

-}

{- Conor, it's time for the finale! Go to L4Hutton.agda -}
