%if False

\begin{code}

module View where
open import VecFin

\end{code}

%endif

\chapter{Views}

Views~\citep{wadler:views} provide a way to give an alternative interface to an
existing type.

We can write a program which transforms our original data to its
alternative representation, but in the dependently typed setting, we
may and we should get a little more. Let's see how.

Given some `upper bound', a number |u|, we may check if any other number,
|n| is below it or not, for example, to check if |n| may be used to index a
vector of size |u|. However, a Boolean answer alone will not help, if our
indexing function |vproj| demands an element of |Fin u|. We could define a
function in |Nat -> Maybe (Fin u)| to compute |n|'s representation in |Fin u|
if it exists, but that simple type does not tell us what that representative
has to do with |n|. Alternatively, we can express what it means for |n| to
be \emph{bounds-checkable}: it must be detectably either representable in |Fin u|,
or |u + x| for some `excess' value |x|. Let's code up those possibilities.

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
\end{code}

If we had a value in |u -Bounded? n|, inspecting it would tell us which of
those two possibilities applies. Let us show that we can always construct
such a value. The base cases are straight forward, but something rather
unusual happens in the step.

\begin{code}
_-bounded?_ : (u n : Nat) -> u -Bounded? n
zero     -bounded? n     = no n
(suc u)  -bounded? zero  = yes zero
(suc u)  -bounded? (suc n)          with  u -bounded? n
(suc u)  -bounded? (suc .(fog i))   |     yes i  = yes (suc i)
(suc u)  -bounded? (suc .(u +N x))  |     no x   = no x
\end{code}

If we are to compare |suc u| with |suc n|, we surely need to know the
result of comparing |u| with |n|. The |with|
construct~\cite{conor.james:viewfromleft} allows us to grab the result
of that comparison and add a column for it to our pattern match. You
can see that the subsequent lines tabulate the possible outcomes of
the match, as well as showing patterns for the original
arguments. Moreover, something funny happens to those patterns: |n|
becomes instantiated with the non-constructor expressions corresponding to
the in- and out-of-bounds cases, marked with a dot. Operationally, there
is \emph{no need to check} that |n| takes the form indicated by the dotted
pattern: the operational check is a constructor case analysis on the result
of the recursive call, and the consequent analysis of |n| is forced by the
types of those constructors. We work hard to make values in precise types,
and we get repaid with information when we inspect those values!

The possibility that that inspecting one value might induce knowledge of
another is a phenomenon new with dependent types, and it necessitates some
thought about our programming notation, and also our selection of what programs
to write. When we write functions to inspect data, we should ask what the types
of those functions tell us about what the inspection will learn.