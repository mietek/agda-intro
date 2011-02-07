%if False

\begin{code}

module VecFin where

\end{code}

%endif

\chapter{Vectors and Finite Sets}

%%It is necessary to cite \citet{hancock:amen} at some point.

%format Set = "\D{Set}"
%format List = "\D{List}"
%format <> = "\C{\langle\rangle}"
%format , = "\red{,}\,"
%format ucu = "\_" , "\!\_"
%% %format _,_ = "\_" , "\_"
%format Nat = "\D{Nat}"
%format zero = "\C{zero}"
%format suc = "\C{suc}"

\nudge{Agda has a very simple lexer and very few special characters.
To a first approximation, ()\{\}; stand alone and everything else must be delimited with whitespace. }
\begin{spec}

data List (X : Set) : Set where
  <>    :                 List X
  ucu   : X -> List X ->  List X

\end{spec}

%if False
\begin{code}

data List (X : Set) : Set where
  <>    :                 List X
  _,_   : X -> List X ->  List X

\end{code}
%endif

%format zap0 = "\F{zap}"
\begin{code}

zap0 : {S T : Set} -> List (S -> T) -> List S -> List T
zap0 <>        <>        = <>
zap0 (f , fs)  (s , ss)  = f s , zap0 fs ss
zap0 _         _         = <>  -- a dummy value, for cases we should not reach

\end{code}

That's the usual `garbage in? garbage out!' deal. Logically, we might
want to ensure the inverse: if we supply meaningful input, we want
meaningful output. But what is meaningful input? Lists the same
length!  Locally, we have a \emph{relative} notion of
meaningfulness. What is meaningful output?  We could say that if the
inputs were the same length, we expect output of that length. How
shall we express this property?

\nudge{The number of c's in |suc| is a long standing area of open
warfare.}
\nudge{Agda users tend to use lowercase-vs-uppercase to distinguish things in |Set|s from things which are or manipulate |Set|s.}
\begin{code}
data Nat : Set where
  zero  :         Nat
  suc   : Nat ->  Nat
\end{code}

%format length = "\F{length}"
\begin{code}
length : {X : Set} -> List X -> Nat
length <>        = zero
length (x , xs)  = suc (length xs)
\end{code}

Informally,\footnote{by which I mean, not to a computer}
we might state and prove something like
\[
  \forall |fs|, |ss|.\;
  |length fs| = |length ss| \Rightarrow |length (zap0 fs ss) = length fs|
\]
by structural induction~\citep{burstall:induction} on |fs|, say.
Of course, we could just as well have concluded that
|length (zap0 fs ss) = length ss|, and if we carry on |zap0|ping, we
shall accumulate a multitude of expressions known to denote the same
number.

What can we say about list concatenation? We may define addition.
%format +N = "\mathbin{\F{+_N}}"
%format _+N_ = "\_\!" +N "\!\_"
\nudge{How many ways to define |+N|?}
\begin{code}
_+N_ : Nat -> Nat -> Nat
zero   +N y = y
suc x  +N y = suc (x +N y)
\end{code}
We may define concatenation.
%format +L+ = "\mathbin{\F{+_L\!+}}"
%format _+L+_ = "\_\!" +L+ "\!\_"
\begin{code}
_+L+_ : {X : Set} -> List X -> List X -> List X
<>        +L+ ys =  ys
(x , xs)  +L+ ys =  x , (xs +L+ ys)
\end{code}
It takes a proof by induction (and a convenient definition of |+N|)
to note that
\[
  |length (xs +L+ ys)| = |length xs +N length ys|
\]


Matters get worse if we try to work with matrices as lists of lists (a
matrix is a column of rows, say).  How do we express rectangularity?
Can we define a function to compute the dimensions of a matrix? Do we
want to?  What happens in degenerate cases? Given \(m\), \(n\), we
might at least say that the outer list has length \(m\) and that all
the inner lists have length \(n\). Talking about matrices gets easier
if we imagine that the dimensions are \emph{prescribed}---to be checked,
not measured.


\subsection{Peano Exercises}

\begin{exe}[Go Forth and Multiply!]
Given addition, implement multiplication.
%format *N = "\mathbin{\F{\times_N}}"
%format _*N_ = "\_\!" *N "\!\_"
\begin{spec}
_*N_ : Nat -> Nat -> Nat
\end{spec}
\end{exe}

\begin{exe}[Subtract with Dummy]
Implement subtraction, with a nasty old dummy return when you take
a big number from a small one.
%format -N = "\mathbin{\F{\-_N}}"
%format _-N_ = "\_\!" -N "\!\_"
\begin{spec}
_-N_ : Nat -> Nat -> Nat
\end{spec}
\end{exe}

\begin{exe}[Divide with a Duplicate]
Implement division. Agda won't let you do repeated subtraction
directly (not structurally decreasing), but you can do something
sensible (modulo the dummy) like this:
%format /N = "\mathbin{\F{\div_N}}"
%format _/N_ = "\_\!" /N "\!\_"
%format help = "\F{help}"
\begin{spec}
_/N_ : Nat -> Nat -> Nat
x /N d = help x d where
   help : Nat -> Nat -> Nat
   help x e = -- |{!!}|
\end{spec}
You can recursively peel |suc|s from |e| one at a time, with the
original |d| still in scope.
\end{exe}


\section{Vectors}

Here are lists, indexed by numbers which happen to measure their
length: these are known in the trade as \emph{vectors}.

\nudge{Agda allows overloading of constructors, as its approach to
typechecking is of a bidirectional character}
%format Vec = "\D{Vec}"
\begin{code}
data Vec (X : Set) : Nat -> Set where
  <>   :                               Vec X zero
  _,_  : {n : Nat} -> X -> Vec X n ->  Vec X (suc n)
\end{code}

%format vap = "\F{vap}"
\nudge{Might want to say something about head and tail, and about how
coverage checking works anyway.}
\nudge{Not greatly enamoured of |S T : Set| notation, but there it is.}
\begin{code}
vap : {n : Nat}{S T : Set} -> Vec (S -> T) n -> Vec S n -> Vec T n
vap <>        <>        = <>
vap (f , fs)  (s , ss)  = f s , vap fs ss
\end{code}

%format vec = "\F{vec}"
\nudge{|vec| is an example of a function with an indexing argument that is
usually inferrable, but never irrelevant.}
\begin{code}
vec : {n : Nat}{X : Set} -> X -> Vec X n
vec {zero}   x = <>
vec {suc n}  x = x , vec x
\end{code}

%format +V+ = "\mathbin{\F{+_V\!+}}"
%format _+V+_ = "\_\!" +V+ "\!\_"
\nudge{By now, you may have noticed the proliferation of listy types.}
\begin{code}
_+V+_ : {m n : Nat}{X : Set} -> Vec X m -> Vec X n -> Vec X (m +N n)
<>        +V+ ys = ys
(x , xs)  +V+ ys = x , (xs +V+ ys)
\end{code}

\nudge{Here's a stinker. Of course, you can rejig |+N| to be tail
recursive and make |+V+| a stinker.}
%format vrevapp = "\F{vrevapp}"
\begin{spec}
vrevapp : {m n : Nat}{X : Set} -> Vec X m -> Vec X n -> Vec X (m +N n)
vrevapp <>        ys = ys
vrevapp (x , xs)  ys = --|{! vrevapp xs (x , ys) !}|
\end{spec}

\nudge{Which other things work badly? Filter?}

%format vtraverse = "\F{vtraverse}"
\nudge{I wanted to make |_/_| left-associative, but no such luck.}
\begin{code}
vtraverse :  {F : Set -> Set} ->
             ({X : Set} -> X -> F X) ->
             ({S T : Set} -> F (S -> T) -> F S -> F T) ->
             {n : Nat}{X Y : Set} ->
             (X -> F Y) -> Vec X n -> F (Vec Y n)
vtraverse pure _/_ f <>        =  pure <>
vtraverse pure _/_ f (x , xs)  =  (pure _,_ / f x) / vtraverse pure _/_ f xs
\end{code}

%format ic = "\T{I}"
%format kc = "\T{K}"
\nudge{When would be a good time to talk about universe polymorphism?}
\begin{code}
ic : {X : Set} -> X -> X
ic x = x

kc : {X Y : Set} -> X -> Y -> X
kc x y = x
\end{code}

%format vsum = "\F{vsum}"
\nudge{Why is |Y| undetermined?}
\begin{code}
vsum : {n : Nat} -> Vec Nat n -> Nat
vsum = vtraverse (kc zero) _+N_ {Y = Nat} ic
\end{code}


\subsection{Matrix Exercises}

Let us define an |m| by |n| matrix to be a vector of |m| rows, each length |n|.
%format Matrix = "\F{Matrix}"
\begin{code}
Matrix : Nat -> Nat -> Set -> Set
Matrix m n X = Vec (Vec X n) m
\end{code}

\begin{exe}[Matrices are Applicative]
Show that |Matrix m n| can be equipped with operations analogous to
|vec| and |vap|.
%format vvec = "\F{vvec}"
%format vvap = "\F{vvap}"
\begin{spec}
vvec :   {m n : Nat}{X : Set} -> X -> Matrix m n X
vvap :   {m n : Nat}{S T : Set} ->
         Matrix m n (S -> T) -> Matrix m n S -> Matrix m n T
\end{spec}
which, respectively, copy a given element into each position, and apply functions to
arguments in corresponding positions. 
\end{exe}

\begin{exe}[Matrix Addition]
Use the applicative interface for |Matrix| to define their elementwise addition.
%format +M = "\mathbin{\F{+_M}}"
%format _+M_ = "\_\!" +M "\!\_"
\begin{spec}
_+M_ : {m n : Nat} -> Matrix m n Nat -> Matrix m n Nat -> Matrix m n Nat
\end{spec}
\end{exe}

\begin{exe}[Matrix Transposition]
Use |vtraverse| to give a one-line definition of matrix transposition.
%format transpose = "\F{transpose}"
\begin{spec}
transpose : {m n : Nat}{X : Set} -> Matrix m n X -> Matrix n m X
\end{spec}
\end{exe}

%format idMatrix = "\F{idMatrix}"
\begin{exe}[Identity Matrix]
Define a function
\begin{spec}
idMatrix : {n : Nat} -> Matrix n n Nat
\end{spec}
\end{exe}

\begin{exe}[Matrix Multiplication]
Define matrix multiplication. There are lots of ways to do this.
Some involve defining scalar product, first.
%format *M = "\mathbin{\F{\times_M}}"
%format _*M_ = "\_\!" *M "\!\_"
\begin{spec}
_*M_ :  {l m n : Nat} -> Matrix l m Nat -> Matrix m n Nat -> Matrix l n Nat
\end{spec}
\end{exe}




\subsection{Unit and Sigma types}

%format One = "\D{1\!\!1}"
%format Sg = "\D{\Upsigma}"
%format * = "\mathbin{\F{\times}}"
%format _*_ = "\_\!" * "\!\_"
%format fst = "\F{fst}"
%format snd = "\F{snd}"

%format constructor = "\mathkw{constructor}"
\nudge{Why do this with records?}
\begin{code}
record One : Set where
  constructor <>
open One public
\end{code}

\nudge{The |field| keyword declares fields, we can also add `manifest' fields.}
\begin{code}
record Sg (S : Set)(T : S -> Set) : Set where
  constructor _,_
  field
    fst  : S
    snd  : T fst
open Sg public

_*_ : Set -> Set -> Set
S * T = Sg S \ _ -> T
\end{code}
\subsection{Apocrypha}
%format VecR = "\F{VecR}"
\nudge{You would not invent dependent pattern matching if vectors were your
only example.}
\begin{code}
VecR : Set -> Nat -> Set
VecR X zero      = One
VecR X (suc n)   = X * VecR X n
\end{code}
%format vconcR = "\F{vconcR}"
\nudge{The definition is logically the same, why are the programs noisier?}
\begin{code}
vconcR :  {m n : Nat}{X : Set} ->
          VecR X m -> VecR X n -> VecR X (m +N n)
vconcR {zero}   <>        ys = ys
vconcR {suc m}  (x , xs)  ys = x , vconcR {m} xs ys
\end{code}

%format == = "\D{=\!\!=}"
%format _==_ = "\_\!" == "\!\_"

\begin{code}
data _==_ {X : Set}(x : X) : X -> Set where
  <> : x == x
\end{code}

%if False
\begin{code}
{-# BUILTIN EQUALITY _==_ #-}
{-# BUILTIN REFL <> #-}
\end{code}
%endif

%format len = "\F{len}"
\begin{code}
len : {X : Set} -> List X -> Nat
len <>        = zero
len (x , xs)  = suc (len xs)
\end{code}

%format VecP = "\F{VecP}"
%format vnil = "\F{vnil}"
%format vcons = "\F{vcons}"
%format vapP = "\F{vapP}"
\nudge{Agda's |\| scopes rightward as far as possible, reducing bracketing. Even newer
  fancy binding sugar might make this prettier still.}
\begin{code}
VecP : Set -> Nat -> Set
VecP X n = Sg (List X) \ xs -> len xs == n
\end{code}

\begin{code}
vnil : {X : Set} -> VecP X zero
vnil = <> , <>
\end{code}

\nudge{It's already getting bad here, but we can match |p| against |<>| and complete.}
\begin{spec}
vcons : {X : Set}{n : Nat} -> X -> VecP X n -> VecP X (suc n)
vcons x (xs , p) = (x , xs) ,  -- |{! !}|
\end{spec}

%format XX = "?"
\nudge{But this really is toxic.}
\begin{spec}
vapP :  {n : Nat}{S T : Set} ->
        VecP (S -> T) n -> VecP S n -> VecP T n
vapP (<> , <>)        (<> , <>)       = <> , <>
vapP ((f , fs) , <>)  ((s , ss) , p)  = (f s , vap (fs , XX) (ss , XX)) , XX
\end{spec}





\section{Finite Sets}

If we know the size of a vector, can we hope to project from it safely?
Here's a family of \emph{finite sets}, good to use as indices into vectors.

%format Fin = "\D{Fin}"
\begin{code}
data Fin : Nat -> Set where
  zero  : {n : Nat} ->                 Fin (suc n)
  suc   : {n : Nat} -> (i : Fin n) ->  Fin (suc n)
\end{code}

Finite sets are sets of bounded numbers. One thing we may readily do is
forget the bound.\nudge{Do you resent writing this function? You should.}
%format fog = "\F{fog}"
\begin{code}
fog : {n : Nat} -> Fin n -> Nat
fog zero     = zero
fog (suc i)  = suc (fog i)
\end{code}

Now let's show how to give a total projection from a vector of known size.
%format vproj = "\F{vproj}"
\nudge{Here's our first Aunt Fanny. We could also swap the arguments around.}
\begin{code}
vproj : {n : Nat}{X : Set} -> Vec X n -> Fin n -> X
vproj <>        ()
vproj (x , xs)  zero     = x
vproj (x , xs)  (suc i)  = vproj xs i
\end{code}
\nudge{It's always possible to give enough Aunt Fannies to satisfy the coverage
checker.}

Suppose we want to project at an index not known to be suitably bounded.
How might we check the bound? We shall return to that thought, later.


\subsection{Renamings}

We'll shortly use |Fin| to type bounded sets of de Bruijn indices.
Functions from one finite set to another will act as `renamings'.

Extending the context with a new assumption is sometimes known as `weakening': making more
assumptions weakens an argument.
Suppose we have a function from |Fin m| to |Fin n|, renaming variables, as it were.
How should weakening act on this function? Can we extend the function to
the sets one larger, mapping the `new' source zero to the `new' target zero?
This operation shows how to push a renaming under a binder.
%format weaken = "\F{weaken}"
\nudge{Categorists, what should we prove about |weaken|?}
\begin{code}
weaken : {m n : Nat} -> (Fin m -> Fin n) -> Fin (suc m) -> Fin (suc n)
weaken f zero     = zero
weaken f (suc i)  = suc (f i)
\end{code}

One operation we'll need corresponds to inserting a new variable somewhere in
the context. This operation is known as `thinning'. Let's define the order-preserving
injection from |Fin n| to |Fin (suc n)| which misses a given element
%format thin = "\F{thin}"
\begin{code}
thin : {n : Nat} -> Fin (suc n) -> Fin n -> Fin (suc n)
thin           zero      = suc
thin {zero}    (suc ())
thin {suc n}   (suc i)   = weaken (thin i)
\end{code}




\subsection{Finite Set Exercises}

\begin{exe}[Tabulation] Invert |vproj|. Given a function from a |Fin| set, show
how to construct the vector which tabulates it.
%format vtab = "\F{vtab}"
\begin{spec}
vtab : {n : Nat}{X : Set} -> (Fin n -> X) -> Vec X n
\end{spec}
\end{exe}

\begin{exe}[Plan a Vector] Show how to construct the `plan' of a
vector---a vector whose elements each give their own position, counting up from
|zero|.
%format vplan = "\F{vplan}"
\begin{spec}
vplan : {n : Nat} -> Vec (Fin n) n
\end{spec}
\end{exe}

\begin{exe}[Max a |Fin|] Every nonempty finite set has a smallest
element |zero| and a largest element which has as many |suc|s as
allowed. Construct the latter
%format max = "\F{max}"
\begin{spec}
max : {n : Nat} -> Fin (suc n)
\end{spec}
\end{exe}

\begin{exe}[Embed, Preserving |fog|] Give the embedding from one finite
set to the next which preserves the numerical value given by |fog|.
%format emb = "\F{emb}"
\begin{spec}
emb : {n : Nat} -> Fin n -> Fin (suc n)
\end{spec}
\end{exe}

%format thick = "\F{thick}"
%format Maybe = "\D{Maybe}"
%format yes = "\C{yes}"
%format no = "\C{no}"
\begin{exe}[Thickening] Construct |thick i| the partial inverse of |thin i|. You'll
need
\begin{code}
data Maybe (X : Set) : Set where
  yes  : X ->  Maybe X
  no   :       Maybe X
\end{code}
Which operations on |Maybe| will help? Discover and define them as you implement:
\begin{spec}
thick : {n : Nat} -> Fin (suc n) -> Fin (suc n) -> Maybe (Fin n)
\end{spec}
Note that |thick| acts as an inequality test.
\end{exe}

\begin{exe}[Order-Preserving Injections]
%format OPI = "\D{OPI}"
Define an inductive family \[|OPI : Nat -> Nat -> Set|\] such that |OPI m n| gives a unique
first-order representation to exactly the order-preserving injections from |Fin m| to
|Fin n|, and give
the functional interpretation of your data. Show that |OPI| is closed under identity and
composition.
\end{exe}