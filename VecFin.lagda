%if False

\begin{code}

module VecFin where

\end{code}

%endif

\chapter{Vectors and Finite Sets}

It is necessary to cite \citet{hancock:amen} at some point.

%format Set = "\D{Set}"
%format Nat = "\D{Nat}"
%format zero = "\C{zero}"
%format suc = "\C{suc}"

\begin{code}

data Nat : Set where
  zero  : Nat
  suc   : Nat -> Nat

\end{code}
