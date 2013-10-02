module fancy-STLCSub where
{- Based on Conor McBride's Lambda calculus in 160 lines -}
open import Level
open import Relation.Binary.PropositionalEquality
open import Data.Product

id : {T : Set} -> T -> T
id x = x
_o_ : ∀ {R S T : Set} -> (S -> T) -> (R -> S) -> R -> T
(f o g) x = f (g x)
infixr 2 _o_

data Ty : Set where
  nat : Ty
  _>_ : (S T : Ty) -> Ty
infixr 5 _>_

data Cx : Set where
  [] : Cx
  _,_ : (G : Cx)(S : Ty) -> Cx
infixl 4 _,_

data _<:_ (T : Ty) : Cx -> Set where
  top : ∀ {G} -> T <: (G , T)
  pop : ∀ {G S} -> T <: G -> T <: (G , S)

data _!-_ (G : Cx) : Ty -> Set where
  c : G !- nat
  va : ∀ {T} -> T <: G -> G !- T
  _$_ : ∀ {S T} -> G !- S > T -> G !- S -> G !- T
  la : ∀ {S T} -> G , S !- T -> G !- S > T

infixl 3 _!-_ _<:_
infixl 5 _$_

_++_ : Cx -> Cx -> Cx
G ++ [] = G
G ++ (D , S) = (G ++ D) , S

_===_ : ∀ {G D}(f g : ∀ {T} -> G !- T -> D !- T) -> Set
_===_ f g = ∀ {T}(t : _ !- T) -> f t ≡ g t

record Kit (Im : Cx -> Ty -> Set) : Set where
  Arr : Cx -> Cx -> Set
  Arr G D = ∀ {T} -> T <: G -> Im D T
  AEQ : ∀ {G D}(f g : Arr G D) -> Set
  AEQ f g = ∀ {T}(i : T <: _) -> f i ≡ g i
  field
    vaim : ∀ {G T} -> T <: G -> Im G T
    imtm : ∀ {G T} -> Im G T -> G !- T
    wkim : ∀ {S G T} -> Im G T -> Im (G , S) T
    vaSplit : ∀ {G T}(i : T <: G) -> imtm (vaim i) ≡ va i
    wkVaim : ∀ {G S T}(i : T <: G) -> wkim {S} (vaim i) ≡ vaim (pop i)
  wkf : ∀ {S G D} -> (Arr G D) -> Arr (G , S) (D , S)
  wkf f top      = vaim top
  wkf f (pop i)  = wkim (f i)
  apf : ∀ {G D} -> Arr G D -> ∀ {T} -> G !- T -> D !- T
  apf f c = c
  apf f (va i) = imtm (f i)
  apf f (m $ n) = apf f m $ apf f n
  apf f (la m) = la (apf (wkf f) m)
  shift : ∀ {G D} H -> Arr G D -> Arr (G ++ H) (D ++ H)
  shift []      f = f
  shift (H , S) f = wkf (shift H f)
  wkfE : ∀ {G D S}{f g : Arr G D} -> AEQ f g -> AEQ (wkf {S} f) (wkf g)
  wkfE q top                  = refl
  wkfE q (pop i)              = cong wkim (q i)
  apfE : ∀ {G D}{f g : Arr G D} -> AEQ f g -> apf f === apf g
  apfE q c                                     = refl
  apfE q (va i)                                = cong imtm (q i)
  apfE q (m $ n)  rewrite apfE q m | apfE q n  = refl
  apfE q (la m)   rewrite apfE (wkfE q) m      = refl
  wkfId : ∀ {G S} -> AEQ (wkf {S} (vaim {G})) (vaim {G , S})
  wkfId top = refl
  wkfId (pop i) = wkVaim i
open Kit

apfId : ∀ {Im} (K : Kit Im) {G} -> apf K (vaim K {G}) === id
apfId K c = refl
apfId K (va i) = vaSplit K i
apfId K (m $ n) rewrite apfId K m | apfId K n = refl
apfId K (la n) = cong la (trans (apfE K (wkfId K) n) (apfId K n))

Ren : Kit (\ G T -> T <: G)
Ren = record {vaim = \ i -> i; imtm = va; wkim = pop;
              vaSplit = \ _ -> refl; wkVaim = \ _ -> refl}
ren : ∀ {G D} -> Arr Ren G D -> ∀ {T} -> G !- T -> D !- T
ren = apf Ren

wkfRen : ∀ {Im}(K : Kit Im){G D H}(f : Arr K D H)(r : Arr Ren G D){S} ->
           AEQ K (wkf K {S} (f o r)) (wkf K f o wkf Ren r)
wkfRen K f r top = refl
wkfRen K f r (pop i) = refl
apfRen : ∀ {Im}(K : Kit Im){G D H}(f : Arr K D H)(r : Arr Ren G D) ->
           apf K (f o r) === (apf K f o ren r)
apfRen K f r c = refl
apfRen K f r (va i) = refl
apfRen K f r (m $ n) rewrite apfRen K f r m | apfRen K f r n = refl
apfRen K f r (la m) = cong la (trans
  (apfE K (wkfRen K f r) m) (apfRen K (wkf K f) (wkf Ren r) m))

Sub : Kit _!-_
Sub = record {vaim = va; imtm = \ t -> t; wkim = ren pop;
              vaSplit = \ _ -> refl; wkVaim = \ _ -> refl}
sub : ∀ {G D} -> Arr Sub G D -> ∀ {T} -> G !- T -> D !- T
sub = apf Sub

_,,_ : ∀ {S G D} -> Arr Sub G D -> D !- S -> Arr Sub (G , S) D
_,,_ σ t top = t
_,,_ σ t (pop x) = σ x

eq, : ∀ {S G D} (σ1 σ2 : Arr Sub (G , S) D) -> (AEQ Sub (σ1 o pop) (σ2 o pop)) -> σ1 top ≡ σ2 top -> AEQ Sub σ1 σ2
eq, σ1 σ2 p1 p2 top = p2
eq, σ1 σ2 p1 p2 (pop i) = p1 i

renPopLem : ∀ {G D}(f : Arr Ren G D){S} ->
   (ren pop o ren f) === (ren (wkf Ren {S} f) o ren pop)
renPopLem f t = trans ((sym (apfRen Ren _ _ t))) (apfRen Ren _ _ t)

thinLem : ∀ {G D} H (f : Arr Sub G D) {S T} (i : T <: (G ++ H))->
      (shift Sub H (wkf Sub {S} f) o shift Ren H pop) i ≡
      (ren (shift Ren H pop) o shift Sub H f) i
thinLem []      f i       = refl
thinLem (H , R) f top     = refl
thinLem (H , R) f (pop i) = trans (cong (ren pop) (thinLem H f i)) (renPopLem (shift Ren H pop) (shift Sub H f i))

shiftLem : ∀ {G D} H {S} (f : Arr Sub G D) ->
             (sub (shift Sub H (wkf Sub {S} f)) o ren (shift Ren H pop))
             === (ren (shift Ren H pop) o sub (shift Sub H f))
shiftLem H f c = refl
shiftLem H f (va i) = thinLem H f i
shiftLem H {S} f (m $ n) rewrite shiftLem H {S} f m | shiftLem H {S} f n = refl
shiftLem H f (la m) = cong la (shiftLem (H , _) f m)

wkfSub : ∀ {G D H S}(s : Arr Sub D H)(f : Arr Sub G D) ->
         AEQ Sub (sub (wkf Sub {S} s) o wkf Sub f) (wkf Sub (sub s o f))
wkfSub s f top = refl
wkfSub s f (pop i) = shiftLem [] s (f i)

apfSub : ∀ {G D H}(s : Arr Sub D H)(f : Arr Sub G D) ->
         (sub s o sub f) === sub (sub s o f)
apfSub s f c = refl
apfSub s f (va i) = refl
apfSub s f (m $ n) rewrite apfSub s f m | apfSub s f n = refl
apfSub s f (la m) = cong la
  (trans (apfSub (wkf Sub s) (wkf Sub f) m) (apfE Sub (wkfSub s f) m))

lemma : ∀ {Γ Δ T S} -> (σ : Arr Sub Γ Δ) -> ∀ (N : Δ !- T) (M : (Γ , T) !- S) -> sub (σ ,, N) M ≡ sub (va ,, N) (sub (wkf Sub σ) M)
lemma σ N M = trans (apfE Sub (eq, (σ ,, N) (sub (va ,, N) o wkf Sub σ) (λ i → trans (sym (apfId Sub (σ i))) (apfRen Sub (va ,, N) pop (σ i))) refl) M) (sym (apfSub _ _ M))

data _→*_ : ∀ {T} -> [] !- T -> [] !- T -> Set where
 ap1 : ∀ {T S} {M1 M2 : [] !- (T > S)} {N1 : _ !- T} -> M1 →* M2  -> (M1 $ N1) →* (M2 $ N1)
 β : ∀ {T S} (M : ([] , T) !- S) (N : [] !- T) -> ((la M) $ N) →* (sub (va ,, N) M)
 →*-refl : ∀ {T} {M : [] !- T} -> M →* M
 →*-trans : ∀ {T} {M N P : _ !- T} -> M →* N -> N →* P -> M →* P

data isNormal : ∀ {T} (t : [] !- T) -> Set where
 la : ∀ {T S} (t : (_ , T) !- S) -> isNormal (la t)
 c : isNormal c

halts : ∀ {T} (t : [] !- T) -> Set
halts {T} t = ∃ (λ (n : _ !- T) → (t →* n) × isNormal n)

reduce : ∀ T -> [] !- T -> Set
reduce nat t = halts t
reduce (T > S) t = halts t × (∀ (x : _ !- T) -> reduce T x -> reduce S (t $ x))

reduce-closed : ∀ {T} {t t' : _ !- T} -> (t →* t') -> reduce T t' -> reduce T t
reduce-closed {nat} p (N , (q1 , q2)) = N , ((→*-trans p q1) , q2)
reduce-closed {T > S} p ((N , (q1 , q2)) , f) = (N , (→*-trans p q1 , q2)) , (λ x rx → reduce-closed (ap1 p) (f x rx))

reduce-ext : ∀ {Γ} {σ : Arr Sub Γ []} (θ : ∀ {U} (x : U <: Γ) -> reduce U (σ x)) {T} {t : _ !- T} (w : reduce T t) ->
 ∀ {U} (x : U <: (Γ , T)) -> reduce U ((σ ,, t) x)
reduce-ext θ w top = w
reduce-ext θ w (pop y) = θ y

thm : ∀ {Γ T} (σ : Arr Sub Γ []) (θ : ∀ {U} (x : U <: Γ) -> reduce U (σ x)) (t : Γ !- T) -> reduce T (sub σ t)
thm σ θ c = c , (→*-refl , c)
thm σ θ (va y) = θ y
thm σ θ (M $ N) = proj₂ (thm σ θ M) (sub σ N) (thm σ θ N)
thm σ θ (la {T} {S} M) = (_ , (→*-refl , (la _))) , (λ N redN → reduce-closed {S} (β _ _) (subst (reduce _) (lemma σ N M) (thm (σ ,, N) (reduce-ext θ redN) M)))

reify : ∀ {T} (t : [] !- T) -> reduce T t -> halts t
reify {nat} t p = p
reify {T > S} t (h , _) = h

done : ∀ {T} (t : [] !- T) -> halts t
done {T} t = reify _ (subst (reduce T) (apfId Sub t) (thm va (λ ()) t))