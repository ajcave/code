module mltt-main where
open import mltt

φsubst : ∀ {n m} {A A' : tm n} (p : Φ A) (e : A ≡ A') {M} {w : vsubst n m} -> φ p w M -> φ (subst Φ e p) w M
φsubst p refl t = t

data dctx : ctx Unitz -> Set where
 ⊡ : dctx ⊡
 _,_ : ∀ {n} -> (Γ : dctx n) -> tm n -> dctx (n , *)

data _∋_∶_ : ∀ {n} -> dctx n -> var n * -> tm n -> Set where
 top : ∀ {n} {Γ : dctx n} {A} -> (Γ , A) ∋ top ∶ ([ wkn-vsub ]r A)
 pop : ∀ {n} {Γ : dctx n} {x} {A B} -> Γ ∋ x ∶ B -> (Γ , A) ∋ (pop x) ∶ ([ wkn-vsub ]r B)

mutual
 data wfctx : ∀ {n} -> dctx n -> Set where
  ⊡ : wfctx ⊡
  _,_ : ∀ {n} {Γ : dctx n} -> wfctx Γ -> ∀ {A} -> Γ ⊢ A type -> wfctx (Γ , A)

 data _⊢_type {n} (Γ : dctx n) : tm n -> Set where
  set : Γ ⊢ set type
  Π : ∀ {A B} -> Γ ⊢ A type -> (Γ , A) ⊢ B type -> Γ ⊢ (Π A B) type
  emb : ∀ {A} -> Γ ⊢ A ∶ set -> Γ ⊢ A type

 data _⊢_∶_ {n} (Γ : dctx n) : tm n -> tm n -> Set where
  bool : Γ ⊢ bool ∶ set
  tt : Γ ⊢ tt ∶ bool
  ff : Γ ⊢ ff ∶ bool
  ▹ : ∀ {A x} -> Γ ⊢ A type -> Γ ∋ x ∶ A -> Γ ⊢ (▹ x) ∶ A
  Π : ∀ {A B} -> Γ ⊢ A ∶ set -> (Γ , A) ⊢ B ∶ set -> Γ ⊢ (Π A B) ∶ set
  ƛ : ∀ {A B M} -> Γ ⊢ A type -> (Γ , A) ⊢ M ∶ B -> Γ ⊢ (ƛ M) ∶ (Π A B)
  _·_ : ∀ {A B M N} -> Γ ⊢ M ∶ (Π A B) -> Γ ⊢ N ∶ A -> Γ ⊢ (M · N) ∶ ([ N /x] B)
  if : ∀ {C M N1 N2} -> (Γ , bool) ⊢ C type -> Γ ⊢ M ∶ bool -> Γ ⊢ N1 ∶ ([ tt /x] C) -> Γ ⊢ N2 ∶ ([ ff /x] C) -> Γ ⊢ (if M N1 N2) ∶ ([ M /x] C)
  conv : ∀ {A B} {M} -> Γ ⊢ A type -> B ≈ A -> Γ ⊢ M ∶ B -> Γ ⊢ M ∶ A

data Φs : ∀ {n m} -> dctx n -> tsubst n m -> Set where
 ⊡ : ∀ {m} -> Φs {m = m} ⊡ tt
 _,_ : ∀ {n m} {Γ} {σ : tsubst n m} {A} {a} -> Φs Γ σ -> Φ ([ σ ]t A) -> Φs (Γ , A) (σ , a)

data φs : ∀ {n m} -> (Γ : dctx n) -> (σ : tsubst n m) -> Φs Γ σ -> Set where
 ⊡ : ∀ {m} -> φs {m = m} ⊡ tt ⊡
 _,[_]_ : ∀ {n m} {Γ} {σ : tsubst n m} {ps} {A} {a} -> φs Γ σ ps -> ∀ p -> φ p id-vsub a -> φs (Γ , A) (σ , a) (ps , p)

Φswkn : ∀ {n m k} {Γ : dctx n} {σ : tsubst n m} (w : vsubst m k) -> Φs Γ σ -> Φs Γ ([ w ]rs σ)
Φswkn w ⊡ = ⊡
Φswkn {Γ = Γ , A} w (y , y') = (Φswkn w y) , subst Φ (ren-sub-comp A) (Φwkn w y')

φswkn : ∀ {n m k} {Γ : dctx n} {σ : tsubst n m} (w : vsubst m k) {ps : Φs Γ σ} -> φs Γ σ ps -> φs Γ ([ w ]rs σ) (Φswkn w ps)
φswkn w ⊡ = ⊡
φswkn {Γ = Γ , A} w (y ,[ p ] y') = (φswkn w y) ,[ subst Φ (ren-sub-comp A) (Φwkn w p) ] φsubst (Φwkn w p) (ren-sub-comp A) {!!}

_⊨_type : ∀ {n} (Γ : dctx n) -> tm n -> Set
Γ ⊨ A type = ∀ {m} {σ : tsubst _ m} {ps : Φs Γ σ} -> φs Γ σ ps -> Φ ([ σ ]t A)

{-_⊨_set : ∀ {n} (Γ : dctx n) -> tm n -> Set
Γ ⊨ A set = ∀ {m} {σ : tsubst _ m} {ps : Φs Γ σ} -> φs Γ σ ps -> Ψ ([ σ ]t A)

Π'' : ∀ {n} {Γ} (A : tm n) B -> Γ ⊨ A set -> (Γ , A) ⊨ B set -> Γ ⊨ (Π A B) set
Π'' A B t1 t2 = λ x → Π (t1 x) (λ a x₁ → subst Ψ (subeq2 B) (t2 (x ,[ {!!} ] x₁))) -}

sub-ren-lem : ∀ {n m k} (σ : tsubst n m) (v : vsubst m k) (a : tm k) B
 -> [ [ v ]rs σ , a ]t B ≡ [ a /x] ([ vsub-ext v ]r ([ tsub-ext σ ]t B))
sub-ren-lem σ v a B = trans (trans
   (subeq2 B)
   (cong (λ α → [ a /x] ([ α ]t B)) (sym ren-sub-ext-comp)))
   (cong [ a /x] (sym (ren-sub-comp B)))

Π' : ∀ {n} {Γ} (A : tm n) B -> Γ ⊨ A type -> (Γ , A) ⊨ B type -> Γ ⊨ (Π A B) type
Π' A B t1 t2 {σ = σ} x = Π (t1 x) f
 where f : ∀ {m'} (v : vsubst _ m') a (x₁ : φ (t1 x) v a) -> Φ ([ a /x] ([ vsub-ext v ]r ([ tsub-ext σ ]t B)))
       f v a x₁ with t2 (φswkn v x ,[ subst Φ (ren-sub-comp A) (Φwkn v (t1 x)) ] φsubst (Φwkn v (t1 x)) (ren-sub-comp A) (φfunct'id v (t1 x) x₁))
       ... | q' = subst Φ (sub-ren-lem σ v a B) q'

_⊨_∶'_[_] : ∀ {n} (Γ : dctx n) (M : tm n) A -> Γ ⊨ A type -> Set
Γ ⊨ M ∶' A [ d ] = ∀ {m} {σ : tsubst _ m} {ps : Φs Γ σ} (qs : φs Γ σ ps) -> φ (d qs) id-vsub ([ σ ]t M)

_⊨_∶_ : ∀ {n} (Γ : dctx n) (M : tm n) A -> Set
Γ ⊨ M ∶ A = ∀ {m} {σ : tsubst _ m} {ps : Φs Γ σ} (qs : φs Γ σ ps) (p : Φ ([ σ ]t A)) -> φ p id-vsub ([ σ ]t M)

κ : ∀ {A B : Set} -> B -> A -> B
κ b = λ _ -> b

mutual
 Πinv1' : ∀ {n} (A : tm n) B -> Φ (Π A B) -> Φ A
 Πinv1' A B (Π p x) = p
 Πinv1' A B (neut ())
 Πinv1' A B (closed (Π1 x) p) = closed x (Πinv1' _ B p)
 Πinv1' A B (closed (Π2 x) p) = Πinv1' A _ p

 Πinv2' : ∀ {n} (A : tm n) B -> (p : Φ (Π A B)) -> ∀ {a} -> φ (Πinv1' A B p) id-vsub a -> Φ ([ a /x] B)
 Πinv2' A B (Π p y) {a} q = subst (λ α → Φ ([ a /x] α)) (reneq4 {M = B}) (y id-vsub a q)
 Πinv2' A B (neut ()) q
 Πinv2' A B (closed (Π1 y) y') q = Πinv2' _ B y' q
 Πinv2' A B (closed (Π2 y) y') q = closed (sub⟶*' _ y) (Πinv2' A _ y' q)

Πinv2 : ∀ {n} {Γ : dctx n} A B -> Γ ⊨ (Π A B) type -> (Γ , A) ⊨ B type
Πinv2 A B t (x1 ,[ p ] x2) = subst Φ (sym (subeq2 B)) (Πinv2' _ _ (t x1) (lemma3-3c' p (Πinv1' _ _ (t x1))  x2))

⊨subst : ∀ {n} {Γ : dctx n} A B -> (Γ , A) ⊨ B type -> (p : Γ ⊨ A type) -> ∀ {N} -> Γ ⊨ N ∶ A -> Γ ⊨ ([ N /x] B) type
⊨subst A B t p n x = subst Φ (subeq1 B) (t (x ,[ p x ] n x (p x)))

φeqdep' : ∀ {n} {B B' M N : tm n} (p : Φ B) (q : Φ B') -> B ≡ B' -> M ⟶ N -> φ p id-vsub N -> φ q id-vsub M
φeqdep' p q refl s t = lemma3-3c' p q (φ-closed p (trans1 s refl) t)

φeq : ∀ {n} {B B' M N : tm n} (p : Φ B) (q : Φ B') -> B' ⟶* B -> M ⟶* N -> φ p id-vsub N -> φ q id-vsub M
φeq p q s1 s t = _×_.proj₁ (lemma3-3' p q id-vsub (common refl s1)) (φ-closed p s t)

φeq' : ∀ {n} {B B' M N : tm n} (p : Φ B) (q : Φ B') -> B ≈ B' -> M ⟶* N -> φ p id-vsub N -> φ q id-vsub M
φeq' p q s1 s t = _×_.proj₁ (lemma3-3' p q id-vsub s1) (φ-closed p s t)

ƛ' : ∀ {n} {Γ} (A : tm n) B M (d1 : Γ ⊨ A type) (d2 : (Γ , A) ⊨ B type) ->  (Γ , A) ⊨ M ∶ B -> Γ ⊨ (ƛ M) ∶' (Π A B) [ Π' A B d1 d2 ]
ƛ' A B M d1 d2 t {σ = σ} qs with t ({!!} ,[ {!!} ] {!!}) {!!}
... | q1 = {!!} , {!!}
 {-{!!} , (λ b q ->
   let z = (d2 (qs ,[ d1 qs ] q))
   in φeqdep' z (subst Φ (subeq2 B) z) (subeq2 B) β (subst (φ z) (subeq2 M) (t (qs ,[ d1 qs ] q) z))) -}