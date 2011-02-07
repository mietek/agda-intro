%if False

\begin{code}

module View where
open import VecFin

\end{code}

%endif

\chapter{Views}


%format -Bounded? = "\D{\!-Bounded?}"
%format _-Bounded?_ = "\_\!" -Bounded? "\!\_"
%format -bounded? = "\D{\!-bounded?}"
%format _-bounded?_ = "\_\!" -bounded? "\!\_"
%format yes = "\C{yes}"
%format no  = "\C{no}"
%format . = ".\!\!"
\begin{code}
data _-Bounded?_ (u : Nat) : Nat -> Set where
  yes  : (i : Fin u) ->  u -Bounded? (fog i)
  no   : (x : Nat) ->    u -Bounded? (u +N x)

_-bounded?_ : (u n : Nat) -> u -Bounded? n
zero     -bounded? n     = no n
(suc u)  -bounded? zero  = yes zero
(suc u)  -bounded? (suc n)          with  u -bounded? n
(suc u)  -bounded? (suc .(fog i))   |     yes i  = yes (suc i)
(suc u)  -bounded? (suc .(u +N x))  |     no x   = no x
\end{code}
