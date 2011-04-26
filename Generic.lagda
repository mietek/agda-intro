%if False

\begin{code}

module Generic where
open import VecFin
open import Lambda
open import View

\end{code}

%endif

\chapter{Generic Programming}

A \emph{universe} is a collection of types, given as the image of a
function. A simple example is the universe
%format TT = "\F{TT}"
%format Zero = "\D{Zero}"
\begin{code}
data Zero : Set where -- no constructors!

TT : Two -> Set
TT tt  = One
TT ff  = Zero
\end{code}

|TT| gives you a universe of sets corresponding to \emph{decidable}
propositions.  You can use |TT| to attach decidable preconditions to
functions. The standard example is this
%format le = "\F{le}"
%format -N = "\F{ -_{N}}"
%format _-N_ = "\_\!" -N "\!\_"
%format exampleSubtraction = "\F{exampleSubtraction}"
%format exampleNonSubtraction = "\F{exampleNonSubtraction}"
\begin{code}
le : Nat -> Nat -> Two
le  zero     n        = tt
le  (suc m)  zero     = ff
le  (suc m)  (suc n)  = le m n

_-N_ : (m n : Nat){p : TT (le n m)} -> Nat
(m      -N zero)         = m
(zero   -N suc _)  {()}
(suc m  -N suc n)  {p}   = (m -N n) {p}

exampleSubtraction      :  Nat
exampleSubtraction      =  42 -N 37

{-exampleNonSubtraction   :  Nat
exampleNonSubtraction   =  37 -N 42-}
\end{code}


\subsection{Polynomials}

The basic building blocks of ordinary first-order datatypes are
\emph{polynomials}, describing how structures are built over elements
by choice and pairing.

\begin{code}
data Poly : Set where
  I           :                  Poly  -- the identity
  Zero' One'  :                  Poly  -- constants
  _+'_ _*'_   : (P Q : Poly) ->  Poly  -- choice and pairing
\end{code}

\begin{code}
<_>P : Poly -> Set -> Set
< I       >P  X  =  X
< Zero'   >P  X  =  Zero
< One'    >P  X  =  One
< P +' Q  >P  X  =  < P >P X + < Q >P X
< P *' Q  >P  X  =  < P >P X * < Q >P X
\end{code}

\begin{code}
<_>p : (P : Poly) -> {X Y : Set} -> (X -> Y) -> < P >P X -> < P >P Y
< P >p f x = ?
\end{code}