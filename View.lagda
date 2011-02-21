%if False

\begin{code}

module View where
open import VecFin
open import Lambda

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


\subsection{Finite Set Structure}

%format finl = "\F{finl}"
%format finr = "\F{finr}"

The natural numbers can be thought of as names for finite types. We
can equip these finite types with lots of useful structure.

Let's start with the \emph{coproduct} structure, corresponding to
addition. We can see |Fin (m +N n)| as the disjoint union of |Fin m|
(at the left, low end of the range) and |Fin n| (at the right, high end
of the range). Let us implement the injections. Firstly, |finl| embeds
|Fin m|, preserving numerical value. I am careful to make the value of
|m| visible, as you can't easily guess it from |m +N n|.

\begin{code}
finl : (m : Nat){n : Nat} -> Fin m -> Fin (m +N n)
finl zero ()
finl (suc m) zero = zero
finl (suc m) (suc i) = suc (finl m i)
\end{code}

Secondly, |finr| embeds |Fin n| by shifting its values up by |m|.

\begin{code}
finr : (m : Nat){n : Nat} -> Fin n -> Fin (m +N n)
finr zero i = i
finr (suc m) i = suc (finr m i)
\end{code}

Injections leave the job half done\nudge{Landin: if a job's worth doing,
it's worth half-doing.} We need to be able to tell them apart. We can
certainly split |Fin (m +N n)| as a disjoint union.
%format + = "\D{+}"
%format _+_ = "\_\!" + "\!\_"
%format inl = "\C{inl}"
%format inr = "\C{inr}"
\begin{code}
data _+_ (S T : Set) : Set where
  inl : S -> S + T
  inr : T -> S + T
\end{code}
%format finlr = "\F{finlr}"
\begin{code}
finlr : (m : Nat){n : Nat} -> Fin (m +N n) -> Fin m + Fin n
finlr zero     k                             = inr k
finlr (suc m)  zero                          = inl zero
finlr (suc m)  (suc k)  with  finlr m k 
...                     |     inl i          = inl (suc i)
...                     |     inr j          = inr j
\end{code}
However, that still leaves work undone. Here's another function of
the same type.
%format badlr = "\F{badlr}"
\begin{code}
badlr : (m : Nat){n : Nat} -> Fin (m +N n) -> Fin m + Fin n
badlr zero     {zero}   ()
badlr zero     {suc n}  _   = inr zero
badlr (suc m)           _   = inl zero
\end{code}
As you can see, it ignores its argument, except where necessary to
reject the input, and it returns the answer that's as far to the
left as possible under the circumstances.

The type of our testing function |finlr| makes no promise as to what
the test will tell us about the value being tested. We compute a value
in a disjoint union, but we \emph{learn} nothing about the values we
already possess. There's still time to change all that. We can show
that the |finl| and |finr| injections \emph{cover} |Fin (m +N n)| by
consrtucting a \emph{view}.
Firstly, let us state what it means to be in the image of |finl| or
|finr|.
%format FinSum = "\D{FinSum}"
%format finSum = "\F{finSum}"
%format isFinl = "\C{isFinl}"
%format isFinr = "\C{isFinr}"
\begin{code}
data FinSum (m n : Nat) : Fin (m +N n) -> Set where
  isFinl  : (i : Fin m) ->  FinSum m n (finl m i)
  isFinr  : (j : Fin n) ->  FinSum m n (finr m j)
\end{code}

Then let us show that every element is in one image or the other.
\begin{code}
finSum : (m : Nat){n : Nat}(k : Fin (m +N n)) -> FinSum m n k
finSum zero     k                                    = isFinr k
finSum (suc m)  zero                                 = isFinl zero
finSum (suc m)  (suc k)            with finSum m k
finSum (suc m)  (suc .(finl m i))  | isFinl i        = isFinl (suc i)
finSum (suc m)  (suc .(finr m j))  | isFinr j        = isFinr j
\end{code}
Note that the case analysis on the result of |finSum m k| exposes
which injection made |k|, directly in the patterns.

\subsection{|Fin|ish the Job}

\begin{exe}[Products]
Equip |Fin| with its product structure. Implement the constructor
%format fpair = "\F{fpair}"
\begin{spec}
fpair : (m n : Nat) -> Fin m -> Fin n -> Fin (m *N n)
\end{spec}
then show that it covers by constructing the appropriate view.
Use your view to implement the projections.
\end{exe}

\begin{exe}[Exponentials]
Implement the exponential function for |Nat|.
%format ^N = "\F{\hat{\,}^{N}}"
%format _^N_ = "\_\!" ^N "\!\_"
\begin{spec}
_^N_ : Nat -> Nat -> Nat
\end{spec}
Now implement the abstraction operator which codifies the
finitely many functions between |Fin m| and |Fin n|. (You know
how to tabulate a function; you know that a vector, like an
exponential, is an iterated product.)
%format flam = "\F{flam}"
\begin{spec}
flam : (m n : Nat) -> (Fin m -> Fin n) -> Fin (n ^N m)
\end{spec}
Show that |flam| covers, and thus implement application. You
will not be able to show that every function is given by applying
a code, for that is true only up to an extensional equality which
is not realised in Agda.
\end{exe}

\begin{exe}[Masochism] Implement dependent functions and pairs!
\end{exe}


\subsection{One Song to the Tune of Another (with James McKinna)}

Let's define positive binary numbers as snoc-lists of bits.
%format Bin = "\F{Bin}"
\begin{code}
Bin = Context Two
\end{code}

We can define a `one' and a `successor' operation for these numbers.
%format bone = "\F{bone}"
%format bsuc = "\F{bsuc}"
\begin{code}
bone : Bin
bone = <>

bsuc : Bin -> Bin
bsuc <>        = <> , ff
bsuc (b , ff)  = b , tt
bsuc (b , tt)  = bsuc b , ff
\end{code}

