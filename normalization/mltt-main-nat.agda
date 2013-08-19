module mltt-main-nat where
open import mltt-nat

φsubst : ∀ {n m} {A A' : tm n} (p : Φ A) (e : A ≡ A') {M} {w : vsubst n m} -> φ p w M -> φ (subst Φ e p) w M
φsubst p refl t = t

φsubst' : ∀ {n m} {A A' : tm n} (p : Φ A) (e : A ≡ A') {M} {w : vsubst n m} -> φ (subst Φ e p) w M -> φ p w M
φsubst' p refl t = t

φeqdep' : ∀ {n} {B B' M N : tm n} (p : Φ B) (q : Φ B') -> B ≡ B' -> M ⟶ N -> φ p id-vsub N -> φ q id-vsub M
φeqdep' p q refl s t = lemma3-3c' p q (φ-closed p (trans1 s refl) t)

φeqdep2 : ∀ {n} {B B' M N : tm n} (p : Φ B) (q : Φ B') -> B ≡ B' -> M ≡ N -> φ p id-vsub N -> φ q id-vsub M
φeqdep2 p q refl refl t = lemma3-3c' p q t

φeqdep3 : ∀ {n} {B B' B'' M N : tm n} (p : Φ B) (e1 : B ≡ B') (e2 : B ≡ B'')
 -> M ⟶ N -> φ (subst Φ e1 p) id-vsub N -> φ (subst Φ e2 p) id-vsub M
φeqdep3 p refl refl s t = φ-closed p (trans1 s refl) t

φstep : ∀ {n} {B M N : tm n} (p : Φ B) -> M ⟶ N -> φ p id-vsub N -> φ p id-vsub M
φstep p s t = φ-closed p (trans1 s refl) t

φcong : ∀ {n} {B M N : tm n} (p : Φ B) -> M ≡ N -> φ p id-vsub N -> φ p id-vsub M
φcong p refl t = t

φeq : ∀ {n} {B B' M N : tm n} (p : Φ B) (q : Φ B') -> B' ⟶* B -> M ⟶* N -> φ p id-vsub N -> φ q id-vsub M
φeq p q s1 s t = _×_.proj₁ (lemma3-3' p q id-vsub (common refl s1)) (φ-closed p s t)

φeq' : ∀ {n} {B B' M N : tm n} (p : Φ B) (q : Φ B') -> B ≈ B' -> M ⟶* N -> φ p id-vsub N -> φ q id-vsub M
φeq' p q s1 s t = _×_.proj₁ (lemma3-3' p q id-vsub s1) (φ-closed p s t)

φwkn : ∀ {n m k} {A : tm n} {w : vsubst n m} (v : vsubst m k) (p : Φ A) {M} -> φ p w M -> φ p (v ∘v w) ([ v ]r M)
φwkn v bool (t1 , (t2 , t3)) = ([ v ]r t1) , ((ren⟶* v t2) , rename-norm-bool t3)
φwkn {w = w} v (Π {A} {B} p y) (norm q r , t2) = norm (ren⟶* v q) (rename-norm r) , λ v' b q ->
                 φeqdep2
                 (y ((v' ∘v v) ∘v w) b (subst (λ α → φ p α b) (ren-assoc w) q))
                 (y (v' ∘v (v ∘v w)) b q)
                 (cong (λ α → [ b /x] ([ vsub-ext α ]r B)) (sym (ren-assoc w)))
                 (cong₂ _·_ (ren-comp _) refl)
                 (t2 (v' ∘v v) b (subst (λ α → φ p α b) (ren-assoc w) q))
φwkn v (neut y) (t1 , (t2 , t3)) = ([ v ]r t1) , ((ren⟶* v t2) , (rename-neut t3))
φwkn v (closed y y') t = φwkn v y' t
φwkn v set t = Ψwkn v t
φwkn v nat (t1 , (t2 , t3)) = ([ v ]r t1) , ((ren⟶* v t2) , rename-norm-nat t3)

φwkn' : ∀ {m k} {A : tm m}  (v : vsubst m k) (p : Φ A) {M} -> φ p id-vsub M -> φ (Φwkn v p) id-vsub ([ v ]r M)
φwkn' v p {M} t = φfunct'id v p (subst (λ α → φ p α ([ v ]r M)) (sym id-v-right) (φwkn v p t))

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
  nat : Γ ⊢ nat ∶ set
  tt : Γ ⊢ tt ∶ bool
  ff : Γ ⊢ ff ∶ bool
  zero : Γ ⊢ zero ∶ nat
  suc : ∀ {M} -> Γ ⊢ M ∶ nat -> Γ ⊢ (suc M) ∶ nat
  rec : ∀ {C N M P} -> (Γ , nat) ⊢ C type -> Γ ⊢ N ∶ nat -> Γ ⊢ M ∶ ([ zero /x] C)
                    -> ((Γ , nat) , C) ⊢ P ∶ ([ suc (▹ (pop top)) /x] ([ wkn-vsub ∘v wkn-vsub ]r C))
                    -> Γ ⊢ (rec N M P) ∶ ([ N /x] C)
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
φswkn {Γ = Γ , A} w (y ,[ p ] y') = (φswkn w y) ,[ subst Φ (ren-sub-comp A) (Φwkn w p) ] φsubst (Φwkn w p) (ren-sub-comp A) (φwkn' w p y')

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
Π' A B t1 t2 {σ = σ} x = Π (t1 x) (λ v a x₁ ->
    subst Φ (sub-ren-lem σ v a B)
     (t2 (φswkn v x ,[ subst Φ (ren-sub-comp A) (Φwkn v (t1 x)) ]
           φsubst (Φwkn v (t1 x)) (ren-sub-comp A) (φfunct'id v (t1 x) x₁))))

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


mutual
 reflect : ∀ {n} {A M : tm n} -> (p : Ψ A) -> neutral M -> ψ p id-vsub M
 reflect bool r = _ , (refl , neut r)
 reflect (Π p y) r = (norm refl (neut r)) , f
  where f : ∀ {k} (v : vsubst _ k) b q -> _
        f v b q with reify (Ψwkn v p) (ψfunct'id v p (subst (λ α → ψ p α b) (sym id-v-right) q))
        f v b q | norm y' y0 = ψ-closed (y (v ∘v id-vsub) b q) (app2* y') (reflect (y (v ∘v id-vsub) b q) ((rename-neut r) · y0))
 reflect (neut y) r = _ , (refl , r)
 reflect (closed y y') r = reflect y' r
 reflect nat r = , (refl , neut r)

 reify : ∀ {n} {A M : tm n} -> (p : Ψ A) -> ψ p id-vsub M -> normalizable M
 reify bool (t1 , (t2 , t3)) = norm t2 (normal-bool-normal t3)
 reify (Π p y) (h , _) = h
 reify (neut y) (t1 , (t2 , r)) = norm t2 (neut r)
 reify (closed y y') r = reify y' r
 reify nat (t1 , (t2 , t3)) = norm t2 (normal-nat-normal t3)

reifyt : ∀ {n} {A : tm n} -> Ψ A -> normalizable A
reifyt bool = norm refl bool
reifyt nat = norm refl nat
reifyt (Π t x) with reifyt t | reifyt (x wkn-vsub (▹ top) (ψfunctid wkn-vsub t (reflect (Ψwkn wkn-vsub t) (▹ top))))
reifyt (Π {A} {B} t x) | norm y y' | norm y0 y1 = norm (Π* y (⟶*cong2 subeq7 refl y0)) (Π y' y1)
reifyt (neut x) = norm refl (neut x)
reifyt (closed x t) with reifyt t
reifyt (closed x₂ t) | norm x x₁ = norm (trans1 x₂ x) x₁

mutual
 reflect' : ∀ {n} {A M : tm n} -> (p : Φ A) -> neutral M -> φ p id-vsub M
 reflect' bool r = _ , (refl , neut r)
 reflect' (Π p y) r = (norm refl (neut r)) , f
  where f : ∀ {k} (v : vsubst _ k) b q -> _
        f v b q with reify' (Φwkn v p) (φfunct'id v p (subst (λ α → φ p α b) (sym id-v-right) q))
        f v b q | norm y' y0 = φ-closed (y (v ∘v id-vsub) b q) (app2* y') (reflect' (y (v ∘v id-vsub) b q) ((rename-neut r) · y0))
 reflect' (neut y) r = _ , (refl , r)
 reflect' (closed y y') r = reflect' y' r
 reflect' set r = neut r
 reflect' nat r = , (refl , neut r)

 reify' : ∀ {n} {A M : tm n} -> (p : Φ A) -> φ p id-vsub M -> normalizable M
 reify' bool (t1 , (t2 , t3)) = norm t2 (normal-bool-normal t3)
 reify' (Π p y) (h , _) = h
 reify' (neut y) (t1 , (t2 , r)) = norm t2 (neut r)
 reify' (closed y y') r = reify' y' r
 reify' set r = reifyt r
 reify' nat (t1 , (t2 , t3)) = norm t2 (normal-nat-normal t3)

ƛ' : ∀ {n} {Γ} (A : tm n) B M (d1 : Γ ⊨ A type) (d2 : (Γ , A) ⊨ B type) ->  (Γ , A) ⊨ M ∶ B -> Γ ⊨ (ƛ M) ∶' (Π A B) [ Π' A B d1 d2 ]
ƛ' A B M d1 d2 t {σ = σ} qs =
 nor
 ,
 λ v b q ->
 let z = (φswkn _ qs ,[ subst Φ (ren-sub-comp A) (Φwkn _ (d1 qs)) ] φsubst (Φwkn _ (d1 qs)) (ren-sub-comp A) (φfunct'id _ (d1 qs) q))
 in φsubst (d2 z) (sub-ren-lem σ (v ∘v id-vsub) b B)
    (φstep (d2 z) β
    (φcong (d2 z)
    (trans (sym (sub-ren-lem σ v b M)) (cong (λ α → [ [ α ]rs σ , b ]t M) id-v-right))
    (t z (d2 z))))
 where nor : normalizable ([ σ ]t (ƛ M))
       nor with (φswkn wkn-vsub qs ,[ subst Φ (ren-sub-comp A) (Φwkn _ (d1 qs)) ] φsubst (Φwkn _ (d1 qs)) (ren-sub-comp A) (reflect' (Φwkn _ (d1 qs)) (▹ top)))
       ... | z  with reify' (d2 z) (t z (d2 z))
       nor | z | norm y y' = norm (ƛ* y) (ƛ y')

mem : ∀ {n} {Γ} {A : tm n} x -> Γ ∋ x ∶ A -> Γ ⊨ (▹ x) ∶ A
mem .top (top {_} {_} {A}) (qs ,[ p ] x) p₁ = φeqdep p p₁ (subeq3 A) x
mem .(pop x) (pop {n} {Γ} {x} {A} {B} d) (qs ,[ p ] x₁) p₁ = φeqdep (subst Φ (sym (subeq3 B)) p₁) p₁ (subeq3 B) (mem x d qs (subst Φ (sym (subeq3 B)) p₁))

⊨conv : ∀ {n} {Γ} {A B : tm n} M (p : Γ ⊨ B type) (q : Γ ⊨ A type) -> B ≈ A -> Γ ⊨ M ∶ B -> Γ ⊨ M ∶' A [ q ]
⊨conv M p q s t qs = φeq' (p qs) (q qs) ([]-cong s) refl (t qs (p qs))

if1* : ∀ {n} {M N1 N1' N2 : tm n} -> N1 ⟶* N1' -> (if M N1 N2) ⟶* (if M N1' N2)
if1* refl = refl
if1* (trans1 x t) = trans1 (ifc1 x) (if1* t)

if2* : ∀ {n} {M N1 N2 N2' : tm n} -> N2 ⟶* N2' -> (if M N1 N2) ⟶* (if M N1 N2')
if2* refl = refl
if2* (trans1 x t) = trans1 (ifc2 x) (if2* t)

if3* : ∀ {n} {M M' N1 N1' N2 N2' : tm n} -> M ⟶* M' -> N1 ⟶* N1' -> N2 ⟶* N2' -> (if M N1 N2) ⟶* (if M' N1' N2')
if3* s1 s2 s3 = ⟶*-trans (if* s1) (⟶*-trans (if1* s2) (if2* s3))

-- TODO: Try doing this in "premonoidal category" style
if' : ∀ {n} {Γ} (C : tm (n , *)) M N1 N2 (d : (Γ , bool) ⊨ C type) -> (t : Γ ⊨ M ∶ bool) -> Γ ⊨ N1 ∶ ([ tt /x] C) -> Γ ⊨ N2 ∶ ([ ff /x] C) -> Γ ⊨ (if M N1 N2) ∶' ([ M /x] C) [ ⊨subst bool C d (κ bool) t ]
if' C M N1 N2 d t t1 t2 qs with t qs bool
if' C M N1 N2 d t t1 t2 qs | .tt , (q1 , tt) = φeq (subst Φ (subeq1 C) (d (qs ,[ bool ] (, refl , tt)))) (subst Φ (subeq1 C) (d (qs ,[ bool ] (, q1 , tt))))
    (⟶*cong2 (subeq1 C) (subeq1 C) (sub⟶*2 q1 C)) (⟶*-trans (if* q1) (trans1 if1 refl)) (t1 qs (subst Φ (subeq1 C) (d (qs ,[ bool ] (, refl , tt)))))
if' C M N1 N2 d t t1 t2 qs | .ff , (q1 , ff) = φeq (subst Φ (subeq1 C) (d (qs ,[ bool ] (, refl , ff)))) (subst Φ (subeq1 C) (d (qs ,[ bool ] (, q1 , ff))))
    (⟶*cong2 (subeq1 C) (subeq1 C) (sub⟶*2 q1 C)) (⟶*-trans (if* q1) (trans1 if2 refl)) (t2 qs (subst Φ (subeq1 C) (d (qs ,[ bool ] (, refl , ff)))))
if' C M N1 N2 d t t1 t2 qs | M' , (q1 , neut x) with
              subst Φ (subeq1 C {N = tt}) (d (qs ,[ bool ] (, refl , tt)))
... | z1 with subst Φ (subeq1 C {N = ff}) (d (qs ,[ bool ] (, refl , ff)))
... | z2 with reify' z1 (t1 qs z1) | reify' z2 (t2 qs z2)
... | norm y y' | norm y2 y2' = φ-closed (subst Φ (subeq1 C) (d _)) (if3* q1 y y2) (reflect' (subst Φ (subeq1 C) (d _)) (if x y' y2'))

mutual
 prop1 : ∀ {n} {A : tm n} -> Ψ A -> Φ A
 prop1 bool = bool
 prop1 (Π t x) = Π (prop1 t) (λ v a x₁ → prop1 (x v a (prop3' t x₁))) 
 prop1 (neut x) = neut x
 prop1 (closed x t) = closed x (prop1 t)
 prop1 nat = nat

 prop3 : ∀ {n m} {v : vsubst n m} {M A} (p : Ψ A) -> ψ p v M -> φ (prop1 p) v M
 prop3 bool r = r
 prop3 {v = w} (Π t x) (r1 , r2) = r1 , (λ v b q → prop3 (x (v ∘v w) b (prop3' t q)) (r2 v b (prop3' t q)))
 prop3 (neut x) r = r
 prop3 (closed x t) r = prop3 t r
 prop3 nat r = r
 
 prop3' : ∀ {n m} {v : vsubst n m} {M A} (p : Ψ A) -> φ (prop1 p) v M -> ψ p v M
 prop3' nat r = r
 prop3' bool r = r
 prop3' {v = w} (Π t x) (r1 , r2) = r1 , (λ v b q → prop3' (x (v ∘v w) b q) (f v b q))
  where f : ∀ {k} (v : vsubst _ k) b q -> _
        f v b q = lemma3-3c' (prop1 (x (v ∘v w) b (prop3' t (prop3 t q)))) (prop1 (x (v ∘v w) b q)) (r2 v b (prop3 t q))
 prop3' (neut x) r = r
 prop3' (closed x t) r = prop3' t r


Π'' : ∀ {n} {Γ} (A : tm n) B -> Γ ⊨ A ∶ set -> (Γ , A) ⊨ B ∶ set -> Γ ⊨ (Π A B) ∶' set [ κ set ]
Π'' A B t1 t2 {σ = σ} x = Π (t1 x set) (λ w a x' → subst Ψ (sub-ren-lem σ w a B)
 (t2 ((φswkn w x) ,[ (subst Φ (ren-sub-comp A) (Φwkn w (prop1 (t1 x set)))) ]
       φsubst (Φwkn w (prop1 (t1 x set))) (ren-sub-comp A) (φfunct'id w (prop1 (t1 x set)) (prop3 (t1 x set) x')))
     set))

app' : ∀ {n} {Γ} (A : tm n) B M N (d1 : Γ ⊨ A type) (d2 : (Γ , A) ⊨ B type) -> Γ ⊨ M ∶ (Π A B) -> (t : Γ ⊨ N ∶ A) -> Γ ⊨ (M · N) ∶' ([ N /x] B) [ ⊨subst A B d2 d1 t ]
app' A B M N d1 d2 t1 t2 {σ = σ} qs with (t2 qs (d1 qs)) | t1 qs (Π' A B d1 d2 qs)
app' A B M N d1 d2 t1 t2 {σ = σ} qs | q0 | q1 , q2 with q2 id-vsub ([ σ ]t N) (subst (λ α → φ (d1 qs) α ([ σ ]t N)) id-v-right q0)
... | z2 = φeqdep2
             (subst Φ (sub-ren-lem _ _ _ B) (d2 _))
             (subst Φ (subeq1 B) (d2 _))
             (trans
                 (sym (sub-ren-lem _ _ _ B))
                 (trans (cong (λ α → [ α , [ σ ]t N ]t B)
                 (trans (cong (λ α → [ α ]rs σ) (sym id-v-right)) reneq4'))
                 (subeq1 B)))
             (cong₂ _·_ (sym reneq4) refl)
             z2

suc' : ∀ {n} {Γ : dctx n} M -> Γ ⊨ M ∶ nat -> Γ ⊨ (suc M) ∶' nat [ κ nat ]
suc' M d qs with d qs nat
suc' M d qs | t1 , (t2 , t3) = (suc t1) , (suc* t2 , (suc t3))



rec' : ∀ {n} {Γ : dctx n} C M P
 -> (d : (Γ , nat) ⊨ C type)  -> Γ ⊨ M ∶ ([ zero /x] C)
 -> ((Γ , nat) , C) ⊨ P ∶ ([ suc (▹ (pop top)) /x] ([ wkn-vsub ∘v wkn-vsub ]r C))
 -> ∀ {m} (N : tm m) {σ : tsubst _ m} {ps : Φs Γ σ} (qs : φs Γ σ ps) -> (p : normal-nat N) -> φ (subst Φ (subeq2 C {N = N}) (d (qs ,[ nat ] (, (refl , p))))) id-vsub (rec N ([ σ ]t M) ([ tsub-ext (tsub-ext σ) ]t P))
rec' C M P d dm dp .zero qs zero with dm qs (subst Φ (subeq1 C) (d (qs ,[ nat ] (, refl , zero))))
... | z0 = φeqdep3 (d _) (subeq1 C) (subeq2 C) recβz z0
rec' C M P d dm dp .(suc n₁) qs (suc {n₁} p) with φsubst' (d _) (subeq2 C) (rec' C M P d dm dp n₁ qs p)
... | z0 with dp ((qs ,[ nat ] (, refl , p)) ,[ (d (qs ,[ nat ] (, refl , p))) ] z0) {!!}
... | z = φstep (subst Φ (subeq2 C) (d _)) recβsuc {!!}
rec' C M P d dm dp N {σ = σ} qs (neut x) with dm qs (subst Φ (subeq1 C) (d (qs ,[ nat ] (, refl , zero))))
... | z with reify' (subst Φ (subeq1 C) (d _)) z
... | z0 with dp (((φswkn (wkn-vsub ∘v wkn-vsub) qs) ,[ nat ] (, refl , neut (▹ (pop top)))) ,[ d ((φswkn _ qs) ,[ nat ] (, refl , neut (▹ (pop top)))) ] reflect' (d _) (▹ top)) (subst Φ {!!} (d ((φswkn (wkn-vsub ∘v wkn-vsub) qs) ,[ nat ] (, refl , suc (neut (▹ (pop top)))))))
... | z1 with reify' {M = [ tsub-ext (tsub-ext σ) ]t P} (subst Φ {!!} (d ((φswkn (wkn-vsub ∘v wkn-vsub) qs) ,[ nat ] (, refl , suc (neut (▹ (pop top))))))) z1
rec' C M P d dm dp N qs (neut x) | z | norm y1 y2 | z1 | norm x₁ x₂ = φ-closed (subst Φ (subeq2 C) (d _)) (rec* refl y1 x₁) (reflect' (subst Φ (subeq2 C) (d _)) (rec x y2 x₂))

rec'' : ∀ {n} {Γ} C (N : tm n) M P
 -> (dc : (Γ , nat) ⊨ C type) -> (dn : Γ ⊨ N ∶ nat) -> Γ ⊨ M ∶ ([ zero /x] C)
 -> ((Γ , nat) , C) ⊨ P ∶ ([ suc (▹ (pop top)) /x] ([ wkn-vsub ∘v wkn-vsub ]r C))
 -> Γ ⊨ (rec N M P) ∶' ([ N /x] C) [ ⊨subst nat C dc (κ nat) dn ]
rec'' C N M P dc dn dm dp {σ = σ} qs with dn qs nat
... | (t1 , (t2 , t3)) with rec' C M P dc dm dp t1 qs t3
... | z = φeq (subst Φ (subeq2 C) (dc _)) (subst Φ (subeq1 C) (dc _)) (⟶*cong2 (subeq1 C) (subeq2 C) (sub⟶*2 t2 C)) (rec1* t2) z

mutual
 lem1 : ∀ {n A} (Γ : dctx n) -> Γ ⊢ A type -> Γ ⊨ A type
 lem1 Γ set = κ set
 lem1 Γ (Π {A} {B} y y') = Π' A B (lem1 Γ y) (lem1 _ y')
 lem1 Γ (emb y) = λ x → prop1 (lem3 Γ y x set)
 
 lem2 : ∀ {n M A} (Γ : dctx n)  -> Γ ⊢ M ∶ A -> Γ ⊨ A type
 lem2 Γ bool = κ set
 lem2 Γ tt = κ bool
 lem2 Γ ff = κ bool
 lem2 Γ (▹ y y') = lem1 Γ y
 lem2 Γ (Π y y') = κ set
 lem2 Γ (ƛ {A} {B} y y') = Π' A B (lem1 Γ y) (lem2 (Γ , A) y')
 lem2 Γ (_·_ {A} {B} y y') = ⊨subst A B (Πinv2 A B (lem2 Γ y)) (lem2 Γ y') (lem3 Γ y')
 lem2 Γ (if {C} x t t₁ t₂) = ⊨subst bool C (lem1 (Γ , bool) x) (κ bool) (lem3 Γ t)
 lem2 Γ (conv y y' y0) = lem1 Γ y
 lem2 Γ nat = κ set
 lem2 Γ zero = κ nat
 lem2 Γ (suc n) = κ nat
 lem2 Γ (rec {C} c n m p) = ⊨subst nat C (lem1 _ c) (κ nat) (lem3 Γ n)

 lem3 : ∀ {n M A} (Γ : dctx n) (d : Γ ⊢ M ∶ A) -> Γ ⊨ M ∶ A
 lem3 Γ t qs p = lemma3-3c' (lem2 Γ t qs) p (lem3' Γ t qs)

 lem3' : ∀ {n M A} (Γ : dctx n) (d : Γ ⊢ M ∶ A) -> Γ ⊨ M ∶' A [ lem2 Γ d ]
 lem3' Γ bool = κ bool
 lem3' Γ tt = λ qs → tt , (refl , tt)
 lem3' Γ ff = λ qs → ff , (refl , ff)
 lem3' Γ (▹ y y') = λ qs → mem _ y' qs (lem1 Γ y qs)
 lem3' Γ (Π {A} {B} y y') = Π'' A B (lem3 Γ y) (lem3 (Γ , A) y')
 lem3' Γ (ƛ {A} {B} {M} y y') = ƛ' A B M (lem1 Γ y) (lem2 (Γ , A) y') (lem3 (Γ , A) y')
 lem3' Γ (_·_ {A} {B} {M} {N} t t₁) = app' A B M N (lem2 Γ t₁) (Πinv2 A B (lem2 Γ t)) (lem3 Γ t) (lem3 Γ t₁)
 lem3' Γ (if {C} {M} {N1} {N2} x t t₁ t₂) = if' C M N1 N2 (lem1 (Γ , bool) x) (lem3 Γ t) (lem3 Γ t₁) (lem3 Γ t₂)
 lem3' Γ (conv {A} {B} {M} y y' y0) = ⊨conv M (lem2 Γ y0) (lem1 Γ y) y' (lem3 Γ y0) 
 lem3' Γ nat = κ nat
 lem3' Γ zero = λ qs → zero , (refl , zero)
 lem3' Γ (suc {N} n) = suc' N (lem3 Γ n)
 lem3' Γ (rec {C} {N} {M} {P} c n m p) = rec'' C N M P (lem1 _ c) (lem3 _ n) (lem3 _ m) (lem3 _ p)

mutual
 idΦ : ∀ {n} {Γ : dctx n} -> wfctx Γ -> Φs Γ id-tsub
 idΦ ⊡ = ⊡
 idΦ (_,_ d {A} x) = Φswkn wkn-vsub (idΦ d) , subst Φ (ren-sub-comp A) (Φwkn wkn-vsub (lem1 _ x (idφ d))) 

 idφ : ∀ {n} {Γ : dctx n} (d : wfctx Γ) -> φs _ id-tsub (idΦ d)
 idφ ⊡ = ⊡
 idφ (_,_ d {A} x) = φswkn wkn-vsub (idφ d) ,[ subst Φ (ren-sub-comp A) (Φwkn wkn-vsub (lem1 _ x (idφ d))) ]
  φsubst (Φwkn wkn-vsub (lem1 _ x (idφ d))) (ren-sub-comp A) (reflect' (Φwkn wkn-vsub (lem1 _ x (idφ d))) (▹ top)) 

yay : ∀ {n M A} {Γ : dctx n} -> wfctx Γ -> Γ ⊢ M ∶ A -> normalizable M
yay d0 d = subst normalizable subeq4 (reify' (lem2 _ d (idφ d0)) (lem3' _ d (idφ d0)))