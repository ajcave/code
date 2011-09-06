module indexing where

record unit : Set where
 constructor tt

data ctx (I : Set) : Set where
 ⊡ : ctx I 
 _,_ : (Γ : ctx I) (T : I) -> ctx I

data var {I} : (Γ : ctx I) (T : I) -> Set where 
 z : ∀ {Γ T} -> var (Γ , T) T
 s : ∀ {Γ T S} (x : var Γ S) -> var (Γ , T) S

data tm (Γ : ctx unit) : Set where
 ▹ : var Γ tt -> tm Γ
 _·_ : (m : tm Γ) -> (n : tm Γ) -> tm Γ
 ƛ : (m : tm (Γ , tt)) -> tm Γ

data tp : Set where
 i : tp
 _⇒_ : (T S : tp) -> tp


data Tm (Γ : ctx tp) : tp -> Set where
 ▹ : ∀ {T} (x : var Γ T) -> Tm Γ T
 _·_ : ∀ {T S} (M : Tm Γ (T ⇒ S)) (N : Tm Γ T) -> Tm Γ S
 ƛ : ∀ {T S} (M : Tm (Γ , T) S) -> Tm Γ (T ⇒ S)

<<_>> : ctx tp -> ctx unit
<< ⊡ >> = ⊡
<< Γ , T >> = << Γ >> , tt

<_> : ∀ {Γ T} -> var Γ T -> var << Γ >> tt
< z > = z
< s x > = s < x >

〚_〛 : ∀ {Γ T} -> Tm Γ T -> tm << Γ >>
〚 ▹ x 〛 = ▹ < x >
〚 M · N 〛 = 〚 M 〛 · 〚 N 〛
〚 ƛ M 〛 = ƛ 〚 M 〛

data subst {I : Set} (A : I -> Set) : ctx I -> Set where
 ⊡ : subst A ⊡
 _,_ : ∀ {Γ T} (σ : subst A Γ) (x : A T) -> subst A (Γ , T)

vsub : ∀ {I} -> ctx I -> ctx I -> Set
vsub Γ Δ = subst (var Δ) Γ
tsub : ctx unit -> ctx unit -> Set
tsub Γ Δ = subst (λ _ -> tm Δ) Γ
Tsub : ctx tp -> ctx tp -> Set
Tsub Γ Δ = subst (Tm Δ) Γ

record foo {I J : Set} (A : ctx I -> ctx J -> Set) (B : ctx J -> J -> Set) : Set where
 field
  f : I -> J
  ext : ∀ {Γ Δ T} -> A Γ Δ -> A (Γ , T) (Δ , f T)
  lookup : ∀ {Γ Δ T} -> A Γ Δ -> (x : var Γ T) -> B Δ (f T)

traverse-tm : ∀ (A : ctx unit -> ctx unit -> Set) (B : ctx unit -> Set) (f : foo A (λ Δ T -> B Δ)) (app : ∀ {Δ} -> B Δ -> B Δ -> B Δ)
 (lam : ∀ {Δ} -> B (Δ , tt) -> B Δ) {Γ Δ} (θ : A Γ Δ) (t : tm Γ) -> B Δ
traverse-tm A B f app lam θ (▹ y) = foo.lookup f θ y
traverse-tm A B f app lam θ (m · n) = app (traverse-tm A B f app lam θ m) (traverse-tm A B f app lam θ m)
traverse-tm A B f app lam θ (ƛ m) = lam (traverse-tm A B f app lam (foo.ext f θ) m)

Lookup : ∀ {I} {A Γ} {T : I} (θ : subst A Γ) (x : var Γ T) -> A T
Lookup ⊡ ()
Lookup (θ , x) z = x
Lookup (θ , x) (s x') = Lookup θ x'