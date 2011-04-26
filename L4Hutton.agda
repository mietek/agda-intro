module L4Hutton where

open import L4VecCrib
open import L4AlgOrnCrib

{- Here's Hutton's Razor, described. -}

data HCon : Set where
  val : HCon
  add : HCon

HExp : Desc One
HExp = sg HCon args where
  args : HCon -> Desc One
  args val = sg Nat \ _ -> say <>
  args add = ask <> * ask <> * say <>

{- The evaluator is a fold. -}

hEval : Data HExp _ -> Nat
hEval = fold evAlg where
  evAlg : [ HExp ] (k Nat) :-> k Nat
  evAlg ( val , n , refl )     = n
  evAlg ( add , a , b , refl ) = a + b

{- Here is the Hutton stack code we had on Wednesday, described. -}

data HOp : Set where
  PUSH : HOp
  SEQ  : HOp
  ADD  : HOp

HCode : Desc (Nat * Nat)
HCode = sg HOp args where
  args : HOp -> Desc (Nat * Nat)
  args PUSH = sg Nat \ _ -> sg Nat \ i -> say (i , su i) 
  args SEQ  = sg Nat \ k -> sg Nat \ l -> sg Nat \ m ->
              ask (k , l) * ask (l , m) * say (k , m) 
  args ADD  = sg Nat \ i -> say (su (su i) , su i) 

{- The corresponding semantic objects are functions from input
   stacks to output stacks. -}

HSem : Nat * Nat -> Set
HSem ij = Vec (fst ij) Nat -> Vec (snd ij) Nat

{- Build the algebra which allows us to write the runtime as a fold. -}

HAlg : [ HCode ] HSem :-> HSem
HAlg codenode ns = {!!}

hrun : Data HCode :-> HSem
hrun = fold HAlg























{- Now...
   Invent fancy stack code, indexed by its meaning! -}

HCodeSem : Desc (Sg (Nat * Nat) HSem)  -- initial & final height, behaviour!
HCodeSem = ornD (algOrn HCode HAlg)

{- Write a compiler whose type guarantees the behaviour "push the value" -}

hCompileSem : (e : Data HExp _) ->
           {i : Nat} -> Data HCodeSem ((i , su i) , _::_ (hEval e))

hCompileSem = induction HExp
   (\e ->  {i : Nat} -> Data HCodeSem ((i , su i) , _::_ (hEval e)))
   help where
   help : (d : [ HExp ] (Data HExp) _) ->
          All HExp (\ e ->
           {i : Nat} -> Data HCodeSem ((i , su i) , _::_ (hEval e))) d ->
          {i : Nat} -> Data HCodeSem ((i , su i) , _::_ (hEval < d >))
   help exp = {!!}

















{-
{- The actual compiler produces plain code by rubbing out the semantic
   information. -}

hCompile : Data HExp _ -> {i : Nat} -> Data HCode (i , su i)
hCompile e = fold (ornAlg (algOrn HCode HAlg)) (hCompileSem e)

{- And it's correct for free. -}

hTheorem : (e : Data HExp _){i : Nat} ->
           hrun (hCompile e {i}) == _::_ (hEval e)
hTheorem e = AOOAThm HCode HAlg (hCompileSem e)
-}