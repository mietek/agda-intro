%if False

\begin{code}

module View where
open import VecFin

\end{code}

%endif

\chapter{Views}

%format fog = "\F{fog}"
\nudge{If you resent writing |fog|, your instincts are sound!}
\begin{code}
fog : {n : Nat} -> Fin n -> Nat
fog zero     = zero
fog (suc i)  = suc (fog i)
\end{code}

%format -Bounded? = "\D{\!-Bounded?}"
%format _-Bounded?_ = "\_\!" -Bounded? "\!\_"
%format -bounded? = "\D{\!-bounded?}"
%format _-bounded?_ = "\_\!" -bounded? "\!\_"
%format yes = "\C{yes}"
%format no  = "\C{no}"
\begin{code}
data _-Bounded?_ (u : Nat) : Nat -> Set where
  yes  : (i : Fin u) ->  u -Bounded? (fog i)
  no   : (x : Nat) ->    u -Bounded? (u <+> x)

_-bounded?_ : (u n : Nat) -> u -Bounded? n
zero     -bounded? n     = no n
(suc u)  -bounded? zero  = yes zero
(suc u)  -bounded? (suc n)           with  u -bounded? n
(suc u)  -bounded? (suc .(fog i))    |     yes i  = yes (suc i)
(suc u)  -bounded? (suc .(u <+> x))  |     no x   = no x
\end{code}
