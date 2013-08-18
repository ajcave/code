module mltt-main where
open import mltt

φsubst : ∀ {n m} {A A' : tm n} (p : Φ A) (e : A ≡ A') {M} {w : vsubst n m} -> φ p w M -> φ (subst Φ e p) w M
φsubst p refl t = t

φeqdep' : ∀ {n} {B B' M N : tm n} (p : Φ B) (q : Φ B') -> B ≡ B' -> M ⟶ N -> φ p id-vsub N -> φ q id-vsub M
φeqdep' p q refl s t = lemma3-3c' p q (φ-closed p (trans1 s refl) t)

φeqdep2 : ∀ {n} {B B' M N : tm n} (p : Φ B) (q : Φ B') -> B ≡ B' -> M ≡ N -> φ p id-vsub N -> φ q id-vsub M
φeqdep2 p q refl refl t = lemma3-3c' p q t

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


mutual
 reflect : ∀ {n} {A M : tm n} -> (p : Ψ A) -> neutral M -> ψ p id-vsub M
 reflect bool r = _ , (refl , neut r)
 reflect (Π p y) r = (norm refl (neut r)) , f
  where f : ∀ {k} (v : vsubst _ k) b q -> _
        f v b q with reify (Ψwkn v p) (ψfunct'id v p (subst (λ α → ψ p α b) (sym id-v-right) q))
        f v b q | norm y' y0 = ψ-closed (y (v ∘v id-vsub) b q) (app2* y') (reflect (y (v ∘v id-vsub) b q) ((rename-neut r) · y0))
 reflect (neut y) r = _ , (refl , r)
 reflect (closed y y') r = reflect y' r

 reify : ∀ {n} {A M : tm n} -> (p : Ψ A) -> ψ p id-vsub M -> normalizable M
 reify bool (t1 , (t2 , t3)) = norm t2 (normal-bool-normal t3)
 reify (Π p y) (h , _) = h
 reify (neut y) (t1 , (t2 , r)) = norm t2 (neut r)
 reify (closed y y') r = reify y' r

reifyt : ∀ {n} {A : tm n} -> Ψ A -> normalizable A
reifyt bool = norm refl bool
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

 reify' : ∀ {n} {A M : tm n} -> (p : Φ A) -> φ p id-vsub M -> normalizable M
 reify' bool (t1 , (t2 , t3)) = norm t2 (normal-bool-normal t3)
 reify' (Π p y) (h , _) = h
 reify' (neut y) (t1 , (t2 , r)) = norm t2 (neut r)
 reify' (closed y y') r = reify' y' r
 reify' set r = reifyt r

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

mutual
 lem1 : ∀ {n A} (Γ : dctx n) -> Γ ⊢ A type -> Γ ⊨ A type
 lem1 Γ t = {!!}
 
 lem2 : ∀ {n M A} (Γ : dctx n)  -> Γ ⊢ M ∶ A -> Γ ⊨ A type
 lem2 Γ bool = {!!}
 lem2 Γ tt = {!!}
 lem2 Γ ff = {!!}
 lem2 Γ (▹ y y') = {!!}
 lem2 Γ (Π y y') = {!!}
 lem2 Γ (ƛ y y') = {!!}
 lem2 Γ (y · y') = {!!}
 lem2 Γ (if y y' y0 y1) = {!!}
 lem2 Γ (conv y y' y0) = {!!}

 lem3 : ∀ {n M A} (Γ : dctx n) (d : Γ ⊢ M ∶ A) -> Γ ⊨ M ∶ A
 lem3 Γ t qs p = lemma3-3c' (lem2 Γ t qs) p (lem3' Γ t qs)

 lem3' : ∀ {n M A} (Γ : dctx n) (d : Γ ⊢ M ∶ A) -> Γ ⊨ M ∶' A [ lem2 Γ d ]
 lem3' Γ d t = {!!}

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