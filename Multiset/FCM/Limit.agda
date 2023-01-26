{-# OPTIONS --safe #-}

module Multiset.FCM.Limit where

open import Multiset.Prelude
open import Multiset.Util using (!_ ; isInjective)

open import Multiset.FCM.Base as M
open import Multiset.FCM.Properties as M
open import Multiset.FCM.Logic as M using (_∈_)

open import Multiset.Limit.Chain
open import Multiset.Limit.TerminalChain as TerminalChain
  hiding (cut ; pres ; diag)

open import Multiset.Omniscience using (LLPO)

open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Function using (_∘_)
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.HLevels

open import Cubical.Data.Unit as Unit using (Unit ; tt)
open import Cubical.Data.Empty as Empty
open import Cubical.Data.Sigma as Sigma using (_×_; Σ≡Prop)
open import Cubical.Data.Sum as Sum using (_⊎_ ; inl ; inr)
open import Cubical.Data.Nat hiding (_^_; isEven; isOdd)
open import Cubical.Data.Nat.Order renaming (_≤_ to _≤N_; _≟_ to _≟N_) hiding (eq) 
open import Cubical.Data.Bool as Bool
  using (Bool ; if_then_else_ ; true ; false ; _and_ ; not; dichotomyBool; isSetBool; _≟_;
         false≢true; true≢false)

open import Cubical.Relation.Nullary

open import Cubical.HITs.PropositionalTruncation as PT
  using
    ( ∥_∥₁
    ; ∣_∣₁
    ; squash₁
    )

open import Cubical.HITs.SetQuotients as SQ

open import Multiset.Equivalences.FCM-PList
open import Multiset.Ordering.Order
open import Cubical.Data.List hiding (map)
open import Cubical.Relation.Binary

open Limit using (elements ; is-lim)

instance
  FunctorM : Functor {ℓ-zero} M
  FunctorM .Functor.map = map
  FunctorM .Functor.map-id = mapId
  FunctorM .Functor.map-comp = mapComp

!^ : ∀ n → M ^ (suc n) → M ^ n
!^ n = M map-!^ n

shiftedLimitPath : ∀ {shlim₁ shlim₂} → (∀ n → shlim₁ .elements n ≡ shlim₂ .elements n) → shlim₁ ≡ shlim₂
shiftedLimitPath = isSet→LimitPathExt (shift (ch M)) (λ k → isSetM)

pres : M (Lim M) → ShLim M
pres = TerminalChain.pres M

infixr 6 _⊎₁_
_⊎₁_ : ∀ {ℓ ℓ'} → (A : Type ℓ) → (B : Type ℓ') → Type (ℓ-max ℓ ℓ')
A ⊎₁ B = ∥ A ⊎ B ∥₁

cut : (n : ℕ) → Lim M → M ^ n
cut = TerminalChain.cut M

module _ {ℓ} {X : Type ℓ} where
  ⟅_,_⟆ : X → X → M X
  ⟅ x , y ⟆ = η x ⊕ η y

  ⟅_,_⟆≡⟅_,_⟆ : (x y z w : X) → Type _
  ⟅ x , y ⟆≡⟅ z , w ⟆ = ∥ ((x ≡ z) × (y ≡ w)) ⊎ ((x ≡ w) × (y ≡ z)) ∥₁

  ⟅,⟆-comm : ∀ x y → ⟅ x , y ⟆ ≡ ⟅ y , x ⟆
  ⟅,⟆-comm x y = comm (η x) (η y)

diag : (ℕ → Lim M) → (n : ℕ) → M ^ n
diag = TerminalChain.diag M

Complete : Type _
Complete = {x y₁ y₂ : Lim M}
  → (ys : ℕ → Lim M)
  → (p : ∀ n → (ys n ≡ y₁) ⊎ (ys n ≡ y₂))
  → (q : ∀ n → cut n x ≡ diag ys n)
  → (x ≡ y₁) ⊎₁ (x ≡ y₂)

isPropComplete : isProp Complete
isPropComplete =
  isPropImplicitΠ2 λ _ _ → isPropImplicitΠ λ _ → isPropΠ3 λ _ _ _ → PT.isPropPropTrunc

diag-ysᶜ-islim-alternating : ∀ {n} {a b : Lim M}
  → (x : Lim M)
  → (ys : ℕ → Lim M)
  → (∀ n → cut n x ≡ diag ys n)
  → (ys n ≡ a)
  → (ys (suc n) ≡ b)
  → !^ n (cut (suc n) a) ≡ cut n b
diag-ysᶜ-islim-alternating {n = n} {a} {b} x ys q ysₙ≡a ysₙ₊₁≡b =
  !^ n (cut (suc n) a)   ≡⟨ a .is-lim n ⟩
  cut n a                ≡⟨ cong (cut n) (sym ysₙ≡a) ⟩
  diag ys n              ≡⟨ sym (q n) ⟩
  cut n x                ≡⟨ sym (x .is-lim n) ⟩
  !^ n (cut (suc n) x)   ≡⟨ cong (!^ n) (q (suc n)) ⟩
  !^ n (diag ys (suc n)) ≡⟨ cong (!^ n ∘ cut (suc n)) ysₙ₊₁≡b ⟩
  !^ n (cut (suc n) b)   ≡⟨ b .is-lim n ⟩
  cut n b ∎

pres-inj⇒complete : isInjective pres → Complete
pres-inj⇒complete inj {x} {y₁} {y₂} ys p q = goal where

  ysᶜ : ℕ → Lim M
  ysᶜ n = Sum.elim (λ ysₙ≡y₁ → y₂) (λ ysₙ≡y₂ → y₁) (p n)

  p∧pᶜ : ∀ n → ⟅ ys n , ysᶜ n ⟆ ≡ ⟅ y₁ , y₂ ⟆
  p∧pᶜ n with p n
  ... | inl ysₙ≡y₁ = cong ⟅_, y₂ ⟆ ysₙ≡y₁
  ... | inr ysₙ≡y₂ = cong ⟅_, y₁ ⟆ ysₙ≡y₂ ∙ ⟅,⟆-comm y₂ y₁

  diag-ysᶜ-islim : ∀ n → !^ n (diag ysᶜ (suc n)) ≡ diag ysᶜ n
  diag-ysᶜ-islim n with (p (suc n)) | (p n)
  ... | inl ysₙ₊₁≡y₁ | inl ysₙ≡y₁ = y₂ .is-lim n
  ... | inl ysₙ₊₁≡y₁ | inr ysₙ≡y₂ = diag-ysᶜ-islim-alternating x ys q ysₙ≡y₂ ysₙ₊₁≡y₁
  ... | inr ysₙ₊₁≡y₂ | inl ysₙ≡y₁ = diag-ysᶜ-islim-alternating x ys q ysₙ≡y₁ ysₙ₊₁≡y₂
  ... | inr ysₙ₊₁≡y₂ | inr ysₙ≡y₂ = y₁ .is-lim n

  xᶜ : Lim M
  xᶜ .elements = diag ysᶜ
  xᶜ .is-lim = diag-ysᶜ-islim

  qᶜ : ∀ n → cut n xᶜ ≡ diag ysᶜ n
  qᶜ n with p n
  ... | inl _ = refl
  ... | inr _ = refl

  pres-diags-pair-path : pres ⟅ x , xᶜ ⟆ ≡ pres ⟅ y₁ , y₂ ⟆
  pres-diags-pair-path = shiftedLimitPath λ n →
    map (cut n) ⟅ x , xᶜ ⟆ ≡⟨⟩
    ⟅ cut n x , cut n xᶜ ⟆ ≡⟨ cong₂ ⟅_,_⟆ (q n) (qᶜ n) ⟩
    ⟅ diag ys n , diag ysᶜ n ⟆ ≡⟨⟩
    map (cut n) ⟅ ys n , ysᶜ n ⟆ ≡⟨ cong (map (cut n)) (p∧pᶜ n) ⟩
    map (cut n) ⟅ y₁   , y₂    ⟆ ∎

  diags-pair-path : ⟅ x , xᶜ ⟆ ≡ ⟅ y₁ , y₂ ⟆
  diags-pair-path = inj ⟅ x , xᶜ ⟆ ⟅ y₁ , y₂ ⟆ pres-diags-pair-path

  goal : ∥ (x ≡ y₁) ⊎ (x ≡ y₂) ∥₁
  goal = PT.rec PT.isPropPropTrunc (Sum.elim (PT.map inl) (PT.map inr)) x∈⟅y₁,y₂⟆ where
    x∈⟅x,xᶜ⟆ : x ∈ ⟅ x , xᶜ ⟆
    x∈⟅x,xᶜ⟆ = ∣ inl ∣ refl {x = x} ∣₁ ∣₁

    x∈⟅y₁,y₂⟆ : x ∈ ⟅ y₁ , y₂ ⟆
    x∈⟅y₁,y₂⟆ = subst (x ∈_) diags-pair-path x∈⟅x,xᶜ⟆

-- From completeness to LLPO

-- The sequence corresponding to the infinite tree in which each node
-- has exactly one subtree.
long : ∀ n → M ^ n
long zero = tt*
long (suc n) = η (long n)

long-isLim : isLimit (ch M) long
long-isLim zero = refl
long-isLim (suc n) = cong η (long-isLim n)

long-ch : Lim M
long-ch = lim long long-isLim

-- Given a sequence a : ℕ → Bool, we a variant (long? a) of long,
-- which is equal to long if the sequence a contains only value false,
-- but its height stop growing if there is n : ℕ such that (a n) is
-- the first true in a.
long? : (a : ℕ → Bool) → ∀ n → M ^ n
long? a zero = tt*
long? a (suc n) =
  if a 0 then ε else η (long? (a ∘ suc) n)

long?-isLim : (a : ℕ → Bool) → isLimit (ch M) (long? a)
long?-isLim a zero = refl
long?-isLim a (suc n) with a 0
... | false = cong η (long?-isLim (a ∘ suc) n)
... | true = refl

long?-ch : (a : ℕ → Bool) → Lim M
long?-ch a = lim (long? a) (long?-isLim a)

-- connections between long and (long? a)
long?-isLim' : (a : ℕ → Bool) (aP : isProp (Σ[ n ∈ ℕ ] a n ≡ true))
  → ∀ n → a (suc n) ≡ true → !^ n (long? a (suc n)) ≡ long n
long?-isLim' a aP zero eq = refl
long?-isLim' a aP (suc n) eq with dichotomyBool (a 0)
... | inl p = Empty.rec (znots (cong fst (aP (_ , p) (_ , eq)))) 
... | inr p = 
  cong (λ z → map (!^ n) (if z then ε else η (if a 1 then ε else η (long? (λ x → a (suc (suc x))) n)))) p
  ∙ cong η (long?-isLim' (a ∘ suc) (λ { (x , q) (y , r) → Σ≡Prop (λ _ → isSetBool _ _) (injSuc (cong fst (aP (_ , q) (_ , r)))) }) n eq)

¬cons≡nil' : ∀ {A : Type} {x : A} xs {ys} → ¬ (xs ++ x List.∷ ys ≡ [])
¬cons≡nil' [] = ¬cons≡nil
¬cons≡nil' (x List.∷ xs) = ¬cons≡nil

singletonP : {X : Type} {x y : X} {xs ys : List X}
  → Perm xs ys
  → xs ≡ x List.∷ [] → ys ≡ y List.∷ []
  → x ≡ y
singletonP stop eqx eqy = cons-inj₁ (sym eqx ∙ eqy)
singletonP (perm {xs = []} p) eqx eqy = Empty.rec (¬cons≡nil (cons-inj₂ eqx))
singletonP (perm {xs = x List.∷ xs} p) eqx eqy = Empty.rec (¬cons≡nil' xs (cons-inj₂ eqx))

isEquivRel∥Perm∥₁ : {X : Type}
  → BinaryRelation.isEquivRel (λ (xs ys : List X) → ∥ Perm xs ys ∥₁)
isEquivRel∥Perm∥₁ =
  BinaryRelation.equivRel
    (λ xs → ∣ stop ∣₁)
    (λ xs ys → PT.map invP)
    λ xs ys zs → PT.rec2 PT.isPropPropTrunc (λ p q → ∣ transP p q ∣₁)

inj-η-set : {X : Type} (setX : isSet X) {x y : X}
  → η x ≡ η y → x ≡ y
inj-η-set setX eq =
  PT.rec (setX _ _)
         (λ p → singletonP p refl refl)
         (effective (λ _ _ → PT.isPropPropTrunc)
                    isEquivRel∥Perm∥₁
                    _ _
                    (cong (truncRelIso .Iso.fun ∘ MToPList) eq))

long?≠long : (a : ℕ → Bool) (aP : isProp (Σ[ n ∈ ℕ ] a n ≡ true))
  → ∀ n → long? a (suc n) ≡ long (suc n) → a n ≡ false
long?≠long a aP zero eq with a 0
... | false = refl
... | true = Empty.rec (η≢ε (sym eq)) 
long?≠long a aP (suc n) eq with a 0
... | false = long?≠long (a ∘ suc) (λ { (x , q) (y , r) → Σ≡Prop (λ _ → isSetBool _ _) (injSuc (cong fst (aP (_ , q) (_ , r)))) }) n (inj-η-set isSetM eq) 
... | true = Empty.rec (η≢ε (sym eq))

-- given a sequence (a : ℕ → Bool) and two values x,y : A, the
-- sequence (seq-ch a x y true) is defined as follows: it returns y if
-- there exists an even number (k ≤ n) such that (a k = true) and
-- (a j = false) for all j < k; in all other cases seq-ch a x y true n
-- returns x.
seq-ch : {A : Type} (a : ℕ → Bool) (x y : A) → Bool → ℕ → A
seq-ch a x y b zero = if a 0 and b then y else x
seq-ch a x y b (suc n) = if a 0 and b then y else seq-ch (a ∘ suc) x y (not b) n

-- lemmata about the behaviour of seq-ch
seq-ch-lem1 : {A : Type} (a : ℕ → Bool) (x y : A) (b : Bool) (n : ℕ)
  → (∀ k → k ≤N n → a k ≡ false) → seq-ch a x y b n ≡ x
seq-ch-lem1 a x y b zero p with p 0 zero-≤
... | r with a 0 | b
... | false | false = refl
... | false | true = refl
... | true | false = refl
... | true | true = Empty.rec (true≢false r)
seq-ch-lem1 a x y b (suc n) p with p 0 zero-≤
... | r with a 0 | b
... | false | false = seq-ch-lem1 (a ∘ suc) x y true n λ k le → p (suc k) (suc-≤-suc le)
... | false | true = seq-ch-lem1 (a ∘ suc) x y false n λ k le → p (suc k) (suc-≤-suc le)
... | true | false = seq-ch-lem1 (a ∘ suc) x y true n λ k le → p (suc k) (suc-≤-suc le)
... | true | true = Empty.rec (true≢false r)

isEven? : Bool → ℕ → Type
isEven? false n = isOddT n
isEven? true n = isEvenT n

seq-ch-lem2 : {A : Type} (a : ℕ → Bool) (x y : A) (b : Bool) (n : ℕ)
  → ∀ k → k ≤N n → a k ≡ true → isEven? b k → seq-ch a x y b n ≡ y
seq-ch-lem2 a x y b zero zero le eq ev with a 0
... | false = Empty.rec (false≢true eq)
seq-ch-lem2 a x y true zero zero le eq ev | true = refl
seq-ch-lem2 a x y b (suc n) zero le eq ev with a 0
... | false = Empty.rec (false≢true eq)
seq-ch-lem2 a x y true (suc n) zero le eq ev | true = refl
seq-ch-lem2 a x y b zero (suc k) le eq ev = Empty.rec (¬-<-zero le)
seq-ch-lem2 a x y b (suc n) (suc k) le eq ev with a 0
seq-ch-lem2 a x y false (suc n) (suc k) le eq ev | false = seq-ch-lem2 (a ∘ suc) x y true n k (pred-≤-pred le) eq ev
seq-ch-lem2 a x y true (suc n) (suc k) le eq ev | false = seq-ch-lem2 (a ∘ suc) x y false n k (pred-≤-pred le) eq ev
seq-ch-lem2 a x y false (suc n) (suc k) le eq ev | true = seq-ch-lem2 (a ∘ suc) x y true n k (pred-≤-pred le) eq ev
seq-ch-lem2 a x y true (suc n) (suc k) le eq ev | true = refl

seq-ch-lem3 : {A : Type} (a : ℕ → Bool) (aP : isProp (Σ[ n ∈ ℕ ] a n ≡ true))
  → (x y : A) (b : Bool) (n : ℕ)
  → ∀ k → k ≤N n → a k ≡ true → isEven? b k → seq-ch a x y (not b) n ≡ x
seq-ch-lem3 a aP x y true zero zero le eq ev with a 0
... | false = Empty.rec (false≢true eq)
... | true = refl
seq-ch-lem3 a aP x y true (suc n) zero le eq ev with dichotomyBool (a 0)
... | inr q = Empty.rec (false≢true (sym q ∙ eq)) 
... | inl q =
  cong (λ z → if z and false then y else seq-ch (a ∘ suc) x y true n) q
  ∙ seq-ch-lem1 (a ∘ suc) x y true n
      (λ k le' → Sum.rec (λ p → Empty.rec (snotz (cong fst (aP (_ , p) (_ , eq))) )) (λ p → p) (dichotomyBool (a (suc k)))) 
seq-ch-lem3 a aP x y b zero (suc k) le eq ev = Empty.rec (¬-<-zero le)
seq-ch-lem3 a aP x y false (suc n) (suc k) le eq ev with dichotomyBool (a 0)
... | inr p =
  cong (λ z → if z and true then y else seq-ch (a ∘ suc) x y false n) p
  ∙ seq-ch-lem3 (a ∘ suc) (λ { (x , q) (y , r) → Σ≡Prop (λ _ → isSetBool _ _) (injSuc (cong fst (aP (_ , q) (_ , r)))) }) x y true n k (pred-≤-pred le) eq ev
... | inl p = Empty.rec (snotz (cong fst (aP (_ , eq) (_  , p))))
seq-ch-lem3 a aP x y true (suc n) (suc k) le eq ev with dichotomyBool (a 0)
... | inr p = 
  cong (λ z → if z and false then y else seq-ch (a ∘ suc) x y true n) p
  ∙ seq-ch-lem3 (a ∘ suc) ((λ { (x , q) (y , r) → Σ≡Prop (λ _ → isSetBool _ _) (injSuc (cong fst (aP (_ , q) (_ , r)))) })) x y false n k (pred-≤-pred le) eq ev
... | inl p = Empty.rec (snotz (cong fst (aP (_ , eq) (_  , p))))

≤-suc-cases : ∀ k n → k ≤N suc n
  → (k ≤N n) ⊎ (k ≡ suc n)
≤-suc-cases zero n le = inl zero-≤
≤-suc-cases (suc k) zero le = inr (cong suc (≤0→≡0 (pred-≤-pred le)))
≤-suc-cases (suc k) (suc n) le with ≤-suc-cases k n (pred-≤-pred le)
... | inl p = inl (suc-≤-suc p)
... | inr p = inr (cong suc p)

true-before? : (a : ℕ → Bool) (n : ℕ)
  → Dec (Σ[ k ∈ ℕ ] (k ≤N n) × (a k ≡ true))
true-before? a zero with a zero ≟ true
... | yes p = yes (0 , ≤-refl , p)
... | no ¬p = no (λ { (k , k≤ , eq) →
  ¬p (cong a (sym (≤0→≡0 k≤)) ∙ eq) })
true-before? a (suc n) with true-before? a n
... | yes (k , k≤ , eq) = yes (k , ≤-suc k≤ , eq)
... | no ¬ih with a (suc n) ≟ true
... | yes p = yes (suc n , ≤-refl , p)
... | no ¬p = no (λ { (k , k≤ , eq) → Sum.rec (λ r → ¬ih (_ , r , eq)) (λ r → ¬p (cong a (sym r) ∙ eq)) (≤-suc-cases k n k≤) }) 

decEven : ∀ n → isEvenT n ⊎ isOddT n
decEven zero = inl tt
decEven (suc n) = Sum.rec inr inl (decEven n)

diag-seq-ch :  (a : ℕ → Bool) (aP : isProp (Σ[ n ∈ ℕ ] a n ≡ true)) (n : ℕ) →
  !^ n (seq-ch a long-ch (long?-ch a) true (suc n) .elements (suc n)) ≡
    seq-ch a long-ch (long?-ch a) true n .elements n 
diag-seq-ch a aP n with true-before? a n
... | yes (k , le , eq) with decEven k
... | inl p =
  cong (λ z → !^ n (z .elements (suc n))) (seq-ch-lem2 a long-ch (long?-ch a) true (suc n) k (≤-suc le) eq p)
  ∙ long?-isLim a n
  ∙ cong (λ z → z .elements n) (sym (seq-ch-lem2 a long-ch (long?-ch a) true n k le eq p))
... | inr p = 
  cong (λ z → !^ n (z .elements (suc n))) (seq-ch-lem3 a aP long-ch (long?-ch a) false (suc n) k (≤-suc le) eq p)
  ∙ long-isLim n
  ∙ cong (λ z → z .elements n) (sym (seq-ch-lem3 a aP long-ch (long?-ch a) false n k le eq p))
diag-seq-ch a aP n | no ¬p with dichotomyBool (a (suc n))
... | inr q =
  cong (λ z → !^ n (z .elements (suc n))) (seq-ch-lem1 a long-ch (long?-ch a) true (suc n)
    (λ k le → Sum.rec (λ r → Empty.rec (Sum.rec (λ p → ¬p (k , p , r)) (λ p → false≢true (sym q ∙ cong a (sym p) ∙ r)) (≤-suc-cases _ _ le)))
                    (λ r → r)
                    (dichotomyBool (a k))))
  ∙ long-isLim n
  ∙ cong (λ z → z .elements n) (sym (seq-ch-lem1 a long-ch (long?-ch a) true n
      λ k le → Sum.rec (λ r → Empty.rec (¬p (k , le , r))) (λ r → r) (dichotomyBool (a k))))
... | inl q  with decEven (suc n)
... | inl ev = 
  cong (λ z → !^ n (z .elements (suc n))) (seq-ch-lem2 a long-ch (long?-ch a) true (suc n) (suc n) ≤-refl q ev)
  ∙ long?-isLim' a aP n q
  ∙ cong (λ z → z .elements n) (sym (seq-ch-lem1 a long-ch (long?-ch a) true n
      λ k le → Sum.rec (λ r → Empty.rec (¬p (k , le , r))) (λ r → r) (dichotomyBool (a k))))
... | inr odd =
  cong (λ z → !^ n (z .elements (suc n))) (seq-ch-lem3 a aP long-ch (long?-ch a) false (suc n) (suc n) ≤-refl q odd)
  ∙ long-isLim n
  ∙ cong (λ z → z .elements n) (sym (seq-ch-lem1 a long-ch (long?-ch a) true n
      λ k le → Sum.rec (λ r → Empty.rec (¬p (k , le , r))) (λ r → r) (dichotomyBool (a k))))

seq-ch-cases : {A : Type} (a : ℕ → Bool)
  → (x y : A) (b : Bool) (n : ℕ)
  → (seq-ch a x y b n ≡ x) ⊎ (seq-ch a x y b n ≡ y)
seq-ch-cases a x y false zero with a 0
... | false = inl refl
... | true = inl refl
seq-ch-cases a x y true zero with a 0
... | false = inl refl
... | true = inr refl
seq-ch-cases a x y false (suc n) with a 0
... | false = seq-ch-cases (a ∘ suc) x y true n
... | true = seq-ch-cases (a ∘ suc) x y true n
seq-ch-cases a x y true (suc n) with a 0
... | false = seq-ch-cases (a ∘ suc) x y false n
... | true = inr refl

complete⇒llpo : Complete → LLPO
complete⇒llpo complete a aP =
  PT.map (Sum.rec (λ eq → inl λ n ev → Sum.rec (λ p → Empty.rec (case1 eq n ev p))
                                                 (λ p → p)
                                                 (dichotomyBool (a n)))
                  (λ eq → inr λ n odd → Sum.rec (λ p → Empty.rec (case2 eq n odd p))
                                                 (λ p → p)
                                                 (dichotomyBool (a n))))
         (complete {x = x} z lem1 lem2)
  where
    y1 : Lim M
    y1 = long-ch
 
    y2 : Lim M
    y2 = long?-ch a

    z : ℕ → Lim M
    z = seq-ch a y1 y2 true

    x : Lim M
    x = lim (λ n → cut n (z n)) (diag-seq-ch a aP)

    lem1 : ∀ n → (z n ≡ y1) ⊎ (z n ≡ y2)
    lem1 = seq-ch-cases a y1 y2 true

    lem2 : ∀ n → cut n (z n) ≡ cut n x
    lem2 n = refl

    case1 : x ≡ y1 → ∀ n → isEvenT n → a n ≡ true → ⊥
    case1 eqx n ev eq = false≢true (sym (long?≠long a aP n bad) ∙ eq) 
      where
        bad : long? a (suc n) ≡ long (suc n)
        bad =
          sym (funExt⁻ (cong elements (seq-ch-lem2 a long-ch (long?-ch a) true (suc n) n (≤-suc ≤-refl) eq ev)) (suc n))
          ∙ funExt⁻ (cong elements eqx) (suc n)

    case2 : x ≡ y2 → ∀ n → isOddT n → a n ≡ true → ⊥
    case2 eqx n ev eq = false≢true (sym (long?≠long a aP n (sym bad)) ∙ eq) 
      where
        bad : long (suc n) ≡ long? a (suc n)
        bad =
          sym (funExt⁻ (cong elements (seq-ch-lem3 a aP long-ch (long?-ch a) false (suc n) n (≤-suc ≤-refl) eq ev)) (suc n))
          ∙ funExt⁻ (cong elements eqx) (suc n)





pres-inj⇒llpo : isInjective pres → LLPO
pres-inj⇒llpo = complete⇒llpo ∘ pres-inj⇒complete
