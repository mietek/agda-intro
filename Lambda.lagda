%if False

\begin{code}

module Lambda where
open import VecFin

\end{code}

%endif

\chapter{Lambda Calculus\\ with de Bruijn Indices}

I'm revisiting chapter 7 of my thesis here.

%format Tm = "\D{Tm}"
%format var = "\C{var}"
%format $ = "\C{\$}"
%format _$_ = "\_\!" $ "\!\_"
%format lam = "\C{lam}"

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


%if False
What to prove?

\begin{code}
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
\end{code}

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

\begin{code}
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

\end{code}

\begin{code}
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
  ;  actiw   = {!!}
  ;  mktmkv  = \ i -> <>
  ;  wkisuc  = \ i -> <>
  }


\end{code}
%endif