%if False

\begin{code}

module Lambda where
open import VecFin

\end{code}

%endif

\chapter{Lambda Calculus\\ with de Bruijn Indices}

I'm revisiting chapter 7 of my thesis here.

%format forall = "\D{\forall}"
%format Tm = "\D{Tm}"
%format var = "\C{var}"
%format $ = "\C{\$}"
%format _$_ = "\_\!" $ "\!\_"
%format lam = "\C{lam}"


Here are the $\lambda$-terms with |n| available de Bruijn indices~\citep{deBruijn:dummies}.

\begin{code}
data Tm (n : Nat) : Set where
  var   : Fin n ->         Tm n
  _$_   : Tm n -> Tm n ->  Tm n
  lam   : Tm (suc n) ->    Tm n

infixl 6 _$_
\end{code}

Which operations work?

Substitute for |zero|?\nudge{How many different kinds of trouble
are we in?}
%format sub0 = "\F{sub0}"
%format yuk = "?"
\begin{spec}
sub0 : {n : Nat} -> Tm n -> Tm (suc n) -> Tm n
sub0 s (var zero)     = s
sub0 s (var (suc i))  = var i
sub0 s (f $ a)        = sub0 s f $ sub0 s a
sub0 s (lam b)        = lam (sub0 yuk b)
\end{spec}

Simultaneous substitution? \nudge{Notoriously not structurally recursive.}
%format ssub = "\F{ssub}"
%format sig = "\V{\sigma}"
%format sig' = "\V{\sigma'}"
\begin{spec}
ssub : {m n : Nat} -> (Fin m -> Tm n) -> Tm m -> Tm n
ssub sig (var i) = sig i
ssub sig (f $ a) = ssub sig f $ ssub sig a
ssub {m}{n} sig (lam b) = lam (ssub sig' b) where
  sig' : Fin (suc m) -> Tm (suc n)
  sig' zero     = var zero
  sig' (suc i)  = ssub (\ i -> var (suc i)) (sig i)
\end{spec}

At this point, Thorsten Altenkirch and Bernhard Reus~\citep{DBLP:conf/csl/AltenkirchR99}
reached for the hammer of wellordering, but there's a cheaper way to
get out of the jam.


\section{Simultaneous Renaming and Substitution}

You can define simultaneous renaming really easily.

%format wkr = "\F{wkr}"
%format ren = "\F{ren}"
%format rho = "\V{\rho}"
\begin{code}
wkr : {m n : Nat} -> (Fin m -> Fin n) -> Fin (suc m) -> Fin (suc n)
wkr rho zero     = zero
wkr rho (suc i)  = suc (rho i)

ren : {m n : Nat} -> (Fin m -> Fin n) -> Tm m -> Tm n
ren rho (var i) = var (rho i)
ren rho (f $ a) = ren rho f $ ren rho a
ren rho (lam b) = lam (ren (wkr rho) b)
\end{code}

And you can define substitution, given renaming.
%format wks = "\F{wks}"
%format sub = "\F{sub}"
\begin{code}
wks : {m n : Nat} -> (Fin m -> Tm n) -> Fin (suc m) -> Tm (suc n)
wks sig zero     = var zero
wks sig (suc i)  = ren suc (sig i)

sub : {m n : Nat} -> (Fin m -> Tm n) -> Tm m -> Tm n
sub sig (var i) = sig i
sub sig (f $ a) = sub sig f $ sub sig a
sub sig (lam b) = lam (sub (wks sig) b)
\end{code}

How repetitive! Let's abstract out the pattern.

%format Kit = "\D{Kit}"
%format mkKit = "\C{mkKit}"
%format mkv = "\F{mkv}"
%format mkt = "\F{mkt}"
%format wki = "\F{wki}"
\begin{code}
record Kit (I : Nat -> Set) : Set where
  constructor mkKit
  field
    mkv  : {n : Nat} -> Fin n -> I n
    mkt  : {n : Nat} -> I n -> Tm n
    wki  : {n : Nat} -> I n -> I (suc n)
open Kit public
\end{code}

%format tau = "\V{\tau}"
%format wk = "\F{wk}"
%format act = "\F{act}"
\begin{code}
wk :  {I : Nat -> Set} -> Kit I -> {m n : Nat} ->
      (Fin m -> I n) -> Fin (suc m) -> I (suc n)
wk k tau zero     = mkv k zero
wk k tau (suc i)  = wki k (tau i)

act : {I : Nat -> Set} -> Kit I -> {m n : Nat} ->
      (Fin m -> I n) -> Tm m -> Tm n
act k tau (var i)  = mkt k (tau i)
act k tau (f $ a)  = act k tau f $ act k tau a
act k tau (lam b)  = lam (act k (wk k tau) b)
\end{code}


\subsection{Exercises}

\begin{exe}[Renaming Kit]
Define the renamimg kit.
%format renk = "\F{renk}"
\begin{spec}
renk : Kit Fin
\end{spec}
\end{exe}

\begin{exe}[Substitution Kit]
Define the substitution kit.
%format subk = "\F{subk}"
\begin{spec}
subk : Kit Tm
\end{spec}
\end{exe}

\begin{exe}[Substitute |zero|]
\begin{spec}
sub0 : {n : Nat} -> Tm n -> Tm (suc n) -> Tm n
\end{spec}
\end{exe}

\begin{exe}[Reduce One]
Define a function to contract the leftmost redex in a $\lambda$-term, if there is one.
%format leftRed = "\F{leftRed}"
\begin{spec}
leftRed : {n : Nat} -> Tm n -> Maybe (Tm n)
\end{spec}
\end{exe}

\begin{exe}[Complete Development]
Show how to compute the complete development of a $\lambda$-term, contracting all its
visible redexes in parallel (but not the redexes which thus arise).
%format develop = "\F{develop}"
\begin{spec}
develop : {n : Nat} -> Tm n -> Tm n
\end{spec}
\end{exe}

\begin{exe}[Gasoline Alley]
Write an iterator, computing the |n|-fold self-composition of an endofunction, effectively
interpreting each |Nat| as its corresponding Church numeral.
%format iterate = "\F{iterate}"
\begin{spec}
iterate : Nat -> {X : Set} -> (X -> X) -> X -> X
\end{spec}
You can use |iterate| and |develop| to run $\lambda$-terms for as many steps as you like,
as long as you are modest in your likes.
\end{exe}

\begin{exe}[Another Substitution Recipe]
It occurred to me at time of writing that one might cook substitution differently.
Using abacus-style addition
%format +a = "\mathbin{\F{+_a}}"
%format _+a_ = "\_\!" +a "\!\_"
\begin{code}
_+a_ : Nat -> Nat -> Nat
zero   +a n  = n
suc m  +a n  = m +a suc n
\end{code}
let
%format Sub = "\F{Sub}"
\begin{code}
Sub : Nat -> Nat -> Set
Sub m n = (w : Nat) -> Fin (w +a m) -> Tm (w +a n)
\end{code}
be the type of substitions which can be weakened.
Define
%format subw = "\F{subw}"
\begin{spec}
subw : {m n : Nat} -> Sub m n -> Tm m -> Tm n
\end{spec}
Now show how to turn a renaming into a |Sub|.
%format renSub = "\F{renSub}"
\begin{spec}
renSub : {m n : Nat} -> (Fin m -> Fin n) -> Sub m n
\end{spec}
Finally, show how to turn a simultaneous substitution into a |Sub|.
%format subSub = "\F{subSub}"
\begin{spec}
subSub : {m n : Nat} -> (Fin m -> Tm n) -> Sub m n
\end{spec}
\end{exe}


%if False
What to prove?

\begin{spec}
record GoodKit {I : Nat -> Set}(k : Kit I) : Set where
  constructor mkGoodKit
  field
    acti    : {m n : Nat} -> (Fin m -> I n) -> I m -> I n
    activ   : {m n : Nat}(f : Fin m -> I n) -> (i : Fin m) -> acti f (mkv k i) == f i
    actit   : {m n : Nat}(f : Fin m -> I n) -> (i : I m) -> act k f (mkt k i) == mkt k (acti f i)
    actiw   : {m n : Nat}(f : Fin m -> I n) -> (t : I m) -> acti (wk k f) (wki k t) == wki k (acti f t)
    mktmkv  : {n : Nat}(i : Fin n) -> mkt k (mkv k i) == var i
    wkisuc  : {n : Nat}(i : Fin n) -> wki k (mkv k i) == mkv k (suc i)
open GoodKit public
\end{spec}

\begin{spec}
wkId : {I : Nat -> Set}{k : Kit I}(gk : GoodKit k)
       {n : Nat}(i : Fin (suc n)) -> wk k (mkv k) i == mkv k i
wkId gk zero     = <>
wkId gk (suc i)  = wkisuc gk i

wkComp : {I : Nat -> Set}(k : Kit I)(gk : GoodKit k) ->
         {l m n : Nat}(f : Fin m -> I n)(g : Fin l -> I m)
         (i : Fin (suc l)) -> acti gk (wk k f) (wk k g i) == wk k (\ j -> acti gk f (g j)) i
wkComp k gk f g zero     = activ gk (wk k f) zero
wkComp k gk f g (suc i)  = actiw gk f (g i)

actId : {I : Nat -> Set}(k : Kit I)(gk : GoodKit k) ->
        {n : Nat}(t : Tm n) -> act k (mkv k) t == t
actId k gk (var i)  = mktmkv gk i
actId k gk (f $ a)  rewrite actId k gk f | actId k gk a = <>
actId k gk (lam b)  = yuk
\end{spec}

\begin{spec}
_^=_ : {S T : Set} -> (S -> T) -> (S -> T) -> Set
f ^= g = (s : _) -> f s == g s

wkExt : {I : Nat -> Set}(k : Kit I)
        {m n : Nat}(f g : Fin m -> I n)(q : f ^= g)
        (i : Fin (suc m)) -> wk k f i == wk k g i
wkExt k f g q zero     = <>
wkExt k f g q (suc i)  rewrite q i = <>

wkId : {I : Nat -> Set}{k : Kit I}(gk : GoodKit k)
       {n : Nat}(i : Fin (suc n)) -> wk k (mkv k) i == mkv k i
wkId gk zero     = <>
wkId gk (suc i)  = wkisuc gk i

wkComp : {I : Nat -> Set}{k : Kit I}(gk : GoodKit k) ->
         {l m n : Nat}(f : Fin m -> I n)(g : Fin l -> I m)
         (i : Fin (suc l)) -> acti gk (wk k f) (wk k g i) == wk k (\ i -> acti gk f (g i)) i
wkComp {I}{k}  gk f g zero     = activ gk (wk k f) zero
wkComp         gk f g (suc i)  = actiw gk f (g i)

actExt :  {I : Nat -> Set}(k : Kit I)
          {m n : Nat}(f g : Fin m -> I n)(q : f ^= g)
          (t : Tm m) -> act k f t == act k g t
actExt k f g q (var i) rewrite q i = <>
actExt k f g q (h $ a) rewrite actExt k f g q h | actExt k f g q a = <>
actExt k f g q (lam b) rewrite actExt k (wk k f) (wk k g) (wkExt k f g q) b = <>

actId : {I : Nat -> Set}{k : Kit I}(gk : GoodKit k) ->
        {n : Nat}
        (t : Tm n) -> act k (mkv k) t == t
actId         gk (var i)  = mktmkv gk i
actId         gk (f $ a)  rewrite actId gk f | actId gk a = <>
actId {I}{k}  gk (lam b)  rewrite actExt k (wk k (mkv k)) (mkv k) (wkId gk) b
                          | actId gk b = <>

actComp : {I : Nat -> Set}{k : Kit I}(gk : GoodKit k) ->
         {l m n : Nat}(f : Fin m -> I n)(g : Fin l -> I m)
         (t : Tm l) -> act k f (act k g t) == act k (\ i -> acti gk f (g i)) t
actComp         gk f g (var i)  = actit gk f (g i)
actComp         gk f g (h $ a)  rewrite actComp gk f g h | actComp gk f g a = <>
actComp {I}{k}  gk f g (lam b)
  rewrite actComp gk (wk k f) (wk k g) b
  | actExt k  (\ i -> acti gk (wk k f) (wk k g i))
              (wk k (\ i -> acti gk f (g i))) (wkComp gk f g) b
  = <>

\end{spec}

\begin{spec}
renK : Kit Fin
renK = mkKit ic var suc

renk : {m n : Nat} ->
      (Fin m -> Fin n) -> Tm m -> Tm n
renk = act renK

renGK : GoodKit renK
renGK = record 
  {  acti    = ic
  ;  activ   = \ f i -> <>
  ;  actit   = \ f i -> <>
  ;  actiw   = \ f t -> <>
  ;  mktmkv  = \ i -> <>
  ;  wkisuc  = \ i -> <>
  }

subK : Kit Tm
subK = mkKit var ic (renk suc)

subk : {m n : Nat} ->
      (Fin m -> Tm n) -> Tm m -> Tm n
subk = act subK

subGK : GoodKit subK
subGK = record 
  {  acti    = subk
  ;  activ   = \ f i -> <>
  ;  actit   = \ f i -> <>
  ;  actiw   = XX
  ;  mktmkv  = \ i -> <>
  ;  wkisuc  = \ i -> <>
  }


\end{spec}
%endif


\subsection{How to Hide de Bruijn Indices}

%format embed = "\F{embed}"

\begin{code}

max : {n : Nat} -> Fin (suc n)
max {zero}   = zero
max {suc n}  = suc (max {n})

embed : {n : Nat} -> Fin n -> Fin (suc n)
embed zero     = zero
embed (suc n)  = suc (embed n)

\end{code}

%format shifty = "\F{shifty}"
%format lambda = "\F{lambda}"
%format myTest = "\F{myTest}"

\begin{code}

shifty : (m : Nat){n : Nat} -> Fin (suc (m +N n))
shifty zero     = max
shifty (suc m)  = embed (shifty m)

lambda :  {m : Nat} ->
          (({n : Nat} -> Tm (suc (m +N n))) -> Tm (suc m)) ->
          Tm m
lambda {m} f = lam (f \{n} -> var (shifty m {n}))

myTest : Tm zero
myTest = lambda \ f -> lambda \ x -> f $ (f $ x)

\end{code}


\subsection{Simply Typed Lambda Calculus}

Altenkirch and Reus carry on to develop simultaneous type-preserving
substitution for the \emph{simply-typed} \(\lambda\)-calculus. Let's see how.

%format Ty = "\D{Ty}"
%format iota = "\C{\upiota}"
%format >> = "\C{\vartriangleright}"
%format _>>_ = "\_\!" >> "\!\_"
%format Context = "\D{Context}"
%format !- = "\D{\vdash}"
%format _!-_ = "\_\!" !- "\!\_"
%format -! = "\D{\dashv}"
%format _-!_ = "\_\!" -! "\!\_"
\begin{code}
infixr 4 _>>_
infixr 3 _!-_
infixr 3 _-!_
\end{code}

\begin{code}
data Ty : Set where
  iota  :                Ty
  _>>_  : (S T : Ty) ->  Ty
\end{code}

I'll have a bunch of variations, so it will help if I make context
a general type of snoc-list.

\begin{code}
data Context (X : Set) : Set where
  <>   : Context X
  _,_  : (G : Context X)(S : X) -> Context X
\end{code}

Variables become typed references into the context.

\begin{code}
data _-!_ {X : Set} : Context X -> X -> Set where
  zero  : forall {G T}                  -> G , T -! T
  suc   : forall {G S T}  (x : G -! T)  -> G , S -! T
\end{code}

Types reflect the typing rules (which are syntax-directed).
I exploit comment syntax to write a suggestive line of dashes
in the relevant places. I have not managed to persuade
\texttt{lhs2TeX} to achieve that.

\begin{code}
data _!-_ : Context Ty -> Ty -> Set where

  var  : forall {G T}            (x : G -! T)
                          ->   ----------------
                                 G !- T

  -- $\lambda$-abstraction extends the context

  lam  : forall {G S T}          (b : G , S !- T)
                          ->   --------------------
                                 G !- S >> T

  -- application demands a type coincidence

  _$_  : forall {G S T}         (f : G !- S >> T)   (s : G !- S)
                          ->  ------------------------------------
                                G !- T
\end{code}

%format < = "\F{\llbracket}"
%format >T = "\F{\rrbracket_T}"
%format <_>T = < "\_" >T
%format >C = "\F{\rrbracket_C}"
%format <_>C = < "\_" >C
%format >v = "\F{\rrbracket_v}"
%format <_>v = < "\_" >v
%format >t = "\F{\rrbracket_t}"
%format <_>t = < "\_" >t
%format eval = "\F{eval}"
%format example = "\F{example}"
%format Gam = "\V{\Gamma}"
%format Del = "\V{\Delta}"

Implementing an evaluator is an exercise in denotational semantics.
First, explain what types mean: functions are\ldots functions!

\begin{code}
<_>T : Ty -> Set
< iota >T    = Nat
< S >> T >T  = < S >T -> < T >T
\end{code}

Interpret contexts as types of environments.

\begin{code}
<_>C : Context Ty -> Set
< <> >C        = One
< Gam , S >C   = < Gam >C * < S >T
\end{code}

Interpret variables as projections from environments.

\begin{code}
<_>v : forall {Gam T} -> Gam -! T -> < Gam >C -> < T >T
< zero >v    (_ , t)  = t
< suc i >v   (g , _)  = < i >v g
\end{code}

Interpret terms, plumbing the environment.

\begin{code}
<_>t : forall {Gam T} -> Gam !- T -> < Gam >C -> < T >T
< var x >t  = < x >v
< lam b >t  = \ g s -> < b >t (g , s)
< f $ s >t  = \ g -> < f >t g (< s >t g)

eval : forall {T} -> <> !- T -> < T >T
eval t = < t >t <>
\end{code}

Here's an example term. You may notice that Agda cannot fully infer
its type, but it is still willing to run it.

\begin{spec}
example : <> !- _
example = (lam (var zero)) $ lam (var zero)
\end{spec}

\subsection{Exercises}

\begin{exe}[Simultaneous Substitution]
Using a technique of your choice and implementing auxiliary functions
as needed, show how to adapt our implementation of scope-safe substitution
to type-safe substitution. Define

%format tsub = "\F{tsub}"

\begin{spec}
tsub : forall {Gam Del}  -> (forall {T} -> Gam -! T -> Del !- T)
                         -> (forall {T} -> Gam !- T -> Del !- T)
\end{spec}
\end{exe}

Based on Paul Blain Levy's \emph{call-by-push-value} calculus, here's
a variation on the simply typed $\lambda$-calculus for you to play with
and extend.

%format VTy = "\D{VTy}"
%format CTy = "\D{CTy}"
%format UNK = "\C{UNK}"
%format ONE = "\C{ONE}"
%format TWO = "\C{TWO}"
%format EFF = "\C{EFF}"
%format <! = "\C{\lfloor}"
%format !> = "\C{\rfloor}"
%format <!_!> = <! "\!\_\!" !>
%format Two = "\D{2\!\!2}"
%format tt = "\C{tt}"
%format ff = "\C{ff}"

Types are separated into \emph{value} types for `being' and \emph{computation}
types for `doing'. I've supplied some primitive value types.
\begin{code}
mutual
  data VTy : Set where             -- value types for ways of being
    UNK      : CTy -> VTy          -- a suspended computation is a value
    ONE TWO  : VTy                 -- primitive value types
  data CTy : Set where             -- computation types for ways of doing
    EFF   : VTy -> CTy             -- making a value by doing effects
    _>>_  : VTy -> CTy -> CTy      -- abstract a computation

data Two : Set where tt ff : Two
\end{code}
You may wish to add more value types.

%format Eff = "\D{Eff}"
%format ret = "\C{ret}"
%format >>= = "\mathbin{\F{>\!\!>\!\!=}}"
%format _>>=_ = "\_\!" >>= "\!\_"
%format toss = "\C{toss}"

To give semantics to these types, we'll need a type of
command-response trees.  They make a monad. Here I've added a
command |toss|, whose `ML type' would be |One -> Two|, but it's
really tossing a coin.
\begin{code}
data Eff (X : Set) : Set where
  ret   : X ->                      Eff X
  toss  : One -> (Two -> Eff X) ->  Eff X
\end{code}

The |ret| constructor puts values at the leaves of the tree.
Meanwhile, the `bind', |>>=| acts like tree-grafting, pasting
new command-response strategies onto the leaves of old.

\begin{exe}[Bind for |toss|ing Trees]
Define |>>=| to graft strategy trees together.
\begin{spec}
_>>=_ : forall {S T} -> Eff S -> (S -> Eff T) -> Eff T
ret x     >>= f = f x
toss u k  >>= f = toss u \ b -> k b >>= f
\end{spec}
\end{exe}

You may wish to modify the signature of operations available,
but the general structure of |Eff X| trees will remain the same,
with nodes carry commands and edges branching over possible responses.

%format >VT = "\F{\rrbracket_{VT}}"
%format <_>VT = < "\_" >VT
%format >CT = "\F{\rrbracket_{CT}}"
%format <_>CT = < "\_" >CT
%format Args = "\F{Args}"
%format Return = "\F{Return}"
To give you a better clue of what's going on, let me define the
semantics of these types. Values are, er, values in the given type.
By contrast, computations are Kleisli arrows---operations which produce
|Eff|-strategies to compute a |Return| value, given a tuple of |Args|.
\begin{code}
mutual
  <_>VT : VTy -> Set
  < UNK C >VT  = < C >CT
  < ONE >VT    = One
  < TWO >VT    = Two

  <_>CT : CTy -> Set
  < C >CT = Args C -> Eff (Return C)

  Args : CTy -> Set
  Args (EFF V)   = One
  Args (V >> C)  = < V >VT * Args C

  Return : CTy -> Set
  Return (EFF V)   = < V >VT
  Return (V >> C)  = Return C
\end{code}
We have separated being and doing. There are two categories at work
\begin{itemize}
\item |<_>CT| gives the subcategory of |Set| containing just those named by
elements of |CTy|, with morphisms given by
%format ->C = "\mathbin{\F{\rightarrow_{C}}}"
%format _->C_ = "\_\!" ->C "\!\_"
%format ->V = "\mathbin{\F{\rightarrow_{V}}}"
%format _->V_ = "\_\!" ->V "\!\_"
\begin{code}
_->C_ : CTy -> CTy -> Set
C ->C C' = < C >CT -> < C' >CT
\end{code}
and the usual functional identity and composition;
\item we have
the subcategory of |Eff|'s Kleisli category induced by |<_>VT|, with objects
named by elements of |VTy| and morphisms being
\begin{code}
_->V_ : VTy -> VTy -> Set
V ->V V' = < V >VT -> Eff < V' >VT
\end{code}
with |ret| as the identity and |>>=| inducing a composition
%format oV = "\mathbin{\F{\circ_{V}}}"
%format _oV_ = "\_\!" oV "\!\_"
\begin{spec}
_oV_ : {R S T : Set} -> (S -> Eff T) -> (R -> Eff S) -> R -> Eff T
f oV g = \ r -> g r >>= f
\end{spec}
You may wish to check that this composition is associative and absorbs
identity on either side.
\end{itemize}
 
\begin{exe}[Functorial |EFF| and |UNK|]
Show that the |EFF| and |UNK| constructors, which turn value
types into computation types and vice versa, extend to functors.

%format EFF$ = "\F{EFF}^{\T{\$}}"
%format UNK$ = "\F{UNK}^{\T{\$}}"
\begin{spec}
EFF$ : {V V' : VTy} -> (V ->V V') -> (EFF V ->C EFF V')

UNK$ : {C C' : CTy} -> (C ->C C') -> (UNK C ->V UNK C')
\end{spec}
Feel free to prove that identity and composition are suitably respected.
\end{exe}

\begin{exe}[Up the Adjunction]
Now show
\[
  |C ->C EFF V| \quad\cong\quad |UNK C ->V V|
\]
%format c2v = "\F{c2v}"
%format v2c = "\F{v2c}"
\begin{spec}
c2v : forall {C V} -> (C ->C EFF V) -> (UNK C ->V V)

v2c : forall {C V} -> (UNK C ->V V) -> (C ->C EFF V)
\end{spec}
in such a way that the two are mutually inverse.
\end{exe}
We've split our monad into an adjunction, connecting distinct notions of
value and computation.

Now, let's have some language.

%format Value = "\D{Value}"
%format Compt = "\D{Compt}"
%format if = "\C{if}"
%format bind = "\C{bind}"
\begin{code}
mutual
  data Value (Gam : Context VTy)  : VTy -> Set where
    var    :  forall {V}  -> Gam -! V ->     Value Gam V
    <>     :                                 Value Gam ONE
    tt ff  :                                 Value Gam TWO
    <!_!>  :  forall {C}  -> Compt Gam C ->  Value Gam (UNK C)
  data Compt (Gam : Context VTy)  : CTy -> Set where
    toss   :                                                         Compt Gam (EFF TWO)
    lam    :  forall {V C}  -> Compt (Gam , V) C ->                  Compt Gam (V >> C)
    _$_    :  forall {V C}  -> Compt Gam (V >> C) -> Value Gam V ->  Compt Gam C
    ret    :  forall {V}    -> Value Gam V ->                        Compt Gam (EFF V)
    bind   :  forall {V C}  -> Compt Gam (EFF V) -> Compt (Gam , V) C ->
                                                                     Compt Gam C
    if     :  forall {C}    -> Value Gam TWO -> Compt Gam C -> Compt Gam C ->
                                                                     Compt Gam C
\end{code}

Here are contexts, interpreted as environment types, with variables
represented as value projections.
%format >CV = "\F{\rrbracket_{CV}}"
%format <_>CV = < "\_" >CV
%format >vv = "\F{\rrbracket_{vv}}"
%format <_>vv = < "\_" >vv
\begin{code}
<_>CV : Context VTy -> Set
< <> >CV        = One
< Gam , V >CV   = < Gam >CV * < V >VT

<_>vv : forall {Gam V} -> Gam -! V -> < Gam >CV -> < V >VT
< zero >vv    (_ , t)  = t
< suc i >vv   (g , _)  = < i >vv g
\end{code}

Now your turn.
%format >vt = "\F{\rrbracket_{vt}}"
%format <_>vt = < "\_" >vt
%format >ct = "\F{\rrbracket_{ct}}"
%format <_>ct = < "\_" >ct
\begin{exe}[Interpreter]
Define mutually recursive interpreters for values and computations.
You should interpret |toss| via the |toss| constructor of |Eff|.
\begin{spec}
mutual
  <_>vt : forall {Gam V} -> Value Gam V ->  < Gam >CV ->  < V >VT
  <_>ct : forall {Gam C} -> Compt Gam C ->  < Gam >CV ->  < C >CT
\end{spec}
\end{exe}

\begin{exe}[Natural Numbers]
Extend the language with a |VTy| of natural numbers, adding |zero| and |suc|
constructors to |Value| and an effectful primitive recursor to |Compt|.
\end{exe}

%format get = "\C{get}"
%format put = "\C{put}"
\begin{exe}[Input/Output]
Extend |Eff|, and your extended language with |get| and |put| operators,
respectively reading and writing natural numbers.
\end{exe}

\begin{exe}[State] Implement an interpreter for |Eff| strategies,
treating the |get| and |put| operations as reading and writing a
|Nat|-valued state. Feel free to make |toss| work any way you like.
\end{exe}

