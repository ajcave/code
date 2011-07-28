 \documentclass{article}

 % The following packages are needed because unicode
 % is translated (using the next set of packages) to
 % latex commands. You may need more packages if you
 % use more unicode characters:

 \usepackage{amssymb}
 \usepackage{bbm}
 \usepackage[greek,english]{babel}
 \usepackage{MnSymbol}
 \usepackage{txfonts}
 % This handles the translation of unicode to latex:

 \usepackage{ucs}
 \usepackage[utf8x]{inputenc}
 \usepackage{autofe}

 % Some characters that are not automatically defined
 % (you figure out by the latex compilation errors you get),
 % and you need to define:

 \DeclareUnicodeCharacter{8988}{\ensuremath{\ulcorner}}
 \DeclareUnicodeCharacter{8989}{\ensuremath{\urcorner}}
 \DeclareUnicodeCharacter{8803}{\ensuremath{\overline{\equiv}}}
 \DeclareUnicodeCharacter{9657}{\ensuremath{\smalltriangleright}}
 \DeclareUnicodeCharacter{411}{\ensuremath{\lambdaslash}}
 \DeclareUnicodeCharacter{9656}{\ensuremath{\blacktriangleright}} 
 % Add more as you need them (shouldn’t happen often).

 % Using “\newenvironment” to redefine verbatim to
 % be called “code” doesn’t always work properly. 
 % You can more reliably use:

 \usepackage{fancyvrb}

 \DefineVerbatimEnvironment
   {code}{Verbatim}
   {} % Add fancy options here if you like.

 \begin{document}

\begin{code} 
module ltyping where

data nat : Set where 
 z : nat
 s : (n : nat) -> nat

data var : nat -> Set where
 z : ∀ {n} -> var (s n)
 s : ∀ {n} -> (x : var n) -> var (s n)

data sort : Set where
 ⋆ : sort
 □ : sort

data tm (n : nat) : Set where
 ▹ : (x : var n) -> tm n
 ƛ : (U : tm n) -> (M : tm (s n)) -> tm n
 _·_ : (M : tm n) -> (N : tm n) -> tm n
 ∀· : (U : tm n) -> (T : tm (s n)) -> tm n
 ▸ : (S : sort) -> tm n

-- A variable for variable substitution is a mapping from variables
-- "in n" to variables "in m". This includes all combinations of
-- exchange, weakening, and contraction
vsubst : (n m : nat) -> Set
vsubst n m = var n -> var m

vext : ∀ {n m} -> vsubst n m -> vsubst (s n) (s m)
vext vs  z = z
vext vs (s x) = s (vs x)

vsub : ∀ {n m} -> vsubst n m -> tm n -> tm m
vsub vs (▹ x) = ▹ (vs x)
vsub vs (ƛ U M) = ƛ (vsub vs U) (vsub (vext vs) M)
vsub vs (M · N) = (vsub vs M) · (vsub vs N)
vsub vs (∀· U T) = ∀· (vsub vs U) (vsub (vext vs) T)
vsub vs (▸ S) = ▸ S

-- A substitution from the domain with n variables to the domain with
-- m variables is a mapping from variables "from n" to terms in m variables
subst : (n m : nat) -> Set
subst n m = var n -> tm m

ext : ∀ {n m} -> subst n m -> tm m -> subst (s n) m
ext vs t z = t
ext vs t (s x) = vs x

sub : ∀ {n m} -> subst n m -> tm n -> tm m
sub vs (▹ x) = vs x
sub vs (ƛ U M) = ƛ (sub vs U) (sub (ext (λ x -> vsub s (vs x)) (▹ z)) M)
sub vs (M · N) = (sub vs M) · (sub vs N)
sub vs (∀· U T) = ∀· (sub vs U) (sub (ext (λ x -> vsub s (vs x)) (▹ z)) T)
sub vs (▸ S) = ▸ S

id : ∀ {n} -> subst n n
id x = ▹ x

-- Single substitution as a special case of simultaneous
single : ∀ {n} -> tm (s n) -> tm n -> tm n
single M N = sub (ext id N) M

wkn : ∀ {n} -> tm n -> tm (s n)
wkn t = vsub s t

{- Typing -}
data axiom : sort -> sort -> Set where
 ⋆∶□ : axiom ⋆ □

data rule : sort -> sort -> sort -> Set where
 ⋆ : rule ⋆ ⋆ ⋆

data ctx : (n : nat) -> Set where
 ⊡ : ctx z
 _,_ : ∀ {n} (Γ : ctx n) -> (T : tm n) -> ctx (s n)

data vof : ∀ {n} (Γ : ctx n) -> var n -> tm n -> Set where
 z : ∀ {n} {Γ : ctx n} {T} -> vof (Γ , T) z (wkn T)
 s : ∀ {n} {Γ : ctx n} {T S x} -> vof Γ x T -> vof (Γ , S) (s x) (wkn T)

_,* : nat -> nat
Γ ,* = s Γ
data _⊢_≡β_ : (Γ : nat) -> (M N : tm Γ) -> Set where
 ▹ : ∀ {Γ x}
   -> Γ     ⊢ (▹ x) ≡β (▹ x)
 ƛ : ∀ {Γ U1 U2 M1 M2}
   -> Γ     ⊢ U1 ≡β U2 
   -> Γ ,*  ⊢ M1 ≡β M2 -- Equal in the extended context
   -> Γ     ⊢ (ƛ U1 M1) ≡β (ƛ U2 M2)
 -- etc

-- Forget all the types from a context
〚_〛 : ∀ {n} -> ctx n -> nat
〚_〛 {n} Γ = n

data of {n : nat} (Γ : ctx n) : (M : tm n) -> (T : tm n) -> Set where
 ▹ : ∀ {x T} (X : vof Γ x T) -> of Γ (▹ x) T
 ax : ∀ {S1 S2} -> axiom S1 S2 -> of Γ (▸ S1) (▸ S2)
 ƛ : ∀ {U T M S1 S2 S3}
     -> rule S1 S2 S3
     -> of Γ U (▸ S1)
     -> of (Γ , U) T (▸ S2)
     -> of (Γ , U) T M
     -> of Γ (ƛ U M) (∀· U T) 
 Π : ∀ {U T S1 S2 S3}
     -> rule S1 S2 S3
     -> of Γ U (▸ S1)
     -> of (Γ , U) T (▸ S2)
     -> of Γ (∀· U T) (▸ S3)
 _·_ : ∀ {M N U T}
     -> of Γ M (∀· U T)
     -> of Γ N U
     -> of Γ (M · N) (single T N)
 ≡-conv : ∀ {M T U S}
     -> of Γ M U
     -> of Γ T (▸ S)
     -> 〚 Γ 〛 ⊢ U ≡β T -- Forget all the types when we go to the ≡β judgement
     -> of Γ M T

\end{code}

\end{document}

