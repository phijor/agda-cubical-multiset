{-# OPTIONS --safe #-}

module Multiset.Inductive.Limit where

open import Multiset.Prelude
open import Multiset.Util using (!_ ; isInjective ; isSurjective)

open import Multiset.Inductive.Base as M
open import Multiset.Inductive.Properties as M
open import Multiset.Inductive.Logic as M using (_∈_)

open import Multiset.Chains
open import Multiset.Chains.FunctorChain

open import Multiset.Omniscience using (LLPO)

open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Function using (_∘_)
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.HLevels

open import Cubical.Data.Unit as Unit using (Unit ; tt)
open import Cubical.Data.Empty as Empty
open import Cubical.Data.Sigma as Sigma
open import Cubical.Data.Sum as Sum using (_⊎_ ; inl ; inr)
open import Cubical.Data.Nat.Base hiding (_^_)
open import Cubical.Data.Bool.Base as Bool
  using (Bool ; if_then_else_ ; true ; false ; _and_ ; not)

open import Cubical.Relation.Nullary

open import Cubical.HITs.PropositionalTruncation as PT
  using
    ( ∥_∥₁
    ; ∣_∣₁
    )

instance
  FunctorM : Functor M
  FunctorM .Functor.map = map
  FunctorM .Functor.map-id = mapId
  FunctorM .Functor.map-comp = mapComp

open Limit.ChainLimit

!^ : ∀ n → M ^ (suc n) → M ^ n
!^ n = M map-!^ n

isSetShLimM : isSet (ShLim M)
isSetShLimM = Limit.isOfHLevelChainLimit _ 2 (λ n → isSetM)

isSetUnorderedTree : ∀ {n} → isSet (M ^ n)
isSetUnorderedTree {zero} = Unit.isSetUnit
isSetUnorderedTree {suc n} = isSetM

limitPath : ∀ {lim₁ lim₂} → (∀ n → lim₁ .elements n ≡ lim₂ .elements n) → lim₁ ≡ lim₂
limitPath = Limit.isSet→ChainLimitPathExt (ch M) (λ k → isSetUnorderedTree {k})

shiftedLimitPath : ∀ {shlim₁ shlim₂} → (∀ n → shlim₁ .elements n ≡ shlim₂ .elements n) → shlim₁ ≡ shlim₂
shiftedLimitPath = Limit.isSet→ChainLimitPathExt (shift (ch M)) (λ k → isSetM)

module _ {ℓ ℓ′ : Level} {A : Type ℓ} {B : A → Type ℓ′} where
  zipDep : M ((x : A) → B x) → (x : A) → M (B x)
  zipDep = M.rec (isSetΠ λ x → isSetM) ε* η* _⊕*_ unit* assoc* comm* where
    ε* : ∀ x → M (B x)
    ε* = λ _ → ε

    η* : ∀ f x → M (B x)
    η* f x = η (f x)

    _⊕*_ : ∀ f g x → M (B x)
    _⊕*_ f g x = f x ⊕ g x

    unit* : ∀ f → ε* ⊕* f ≡ f
    unit* f = funExt $ unit ∘ f

    assoc* : ∀ f g h
      → (f ⊕* (g ⊕* h)) ≡ ((f ⊕* g) ⊕* h)
    assoc* f g h = funExt λ x → assoc (f x) (g x) (h x)

    comm* : ∀ f g
      → f ⊕* g ≡ g ⊕* f
    comm* f g = funExt λ x → comm (f x) (g x)

module _ where
  open Limit
  open ChainLimit

  cut : (n : ℕ) → Lim M → M ^ n
  cut n l = l .elements n

  zip₁ : M (Lim M) → ∀ n → M (M ^ n)
  zip₁ xs = zipDep (map elements xs)

  zip₁-islim : (xs : M (Lim M)) → isShLim M (zip₁ xs)
  zip₁-islim = ind {P = λ xs → isShLim M (zip₁ xs)}
    (λ xs → isPropΠ λ n → isSetM (!^ (suc n) (zip₁ xs (suc n))) (zip₁ xs n))
    empty* singl* λ {xs} {ys} → (union* xs ys) where

    empty* : ∀ n → ε ≡ ε
    empty* _ = refl

    singl* : (x : Lim M) → ∀ n → map (!^ n) (zip₁ (η x) (suc n)) ≡ zip₁ (η x) n
    singl* x n = cong η (x .isChainLimit n)

    union*
      : ∀ (xs ys : M (Lim M))
      → isShLim M (zip₁ xs)
      → isShLim M (zip₁ ys)
      → isShLim M (zip₁ (xs ⊕ ys))
    union* _ _ indH-xs indH-ys n = cong₂ _⊕_ (indH-xs n) (indH-ys n)

zip : M (Lim M) → ShLim M
zip xs .Limit.ChainLimit.elements = zip₁ xs
zip xs .Limit.ChainLimit.isChainLimit = zip₁-islim xs

infixr 6 _⊎₁_
_⊎₁_ : ∀ {ℓ ℓ'} → (A : Type ℓ) → (B : Type ℓ') → Type (ℓ-max ℓ ℓ')
A ⊎₁ B = ∥ A ⊎ B ∥₁

module _ {ℓ} {X : Type ℓ} where
  ⟅_,_⟆ : X → X → M X
  ⟅ x , y ⟆ = η x ⊕ η y

  ⟅_,_⟆≡⟅_,_⟆ : (x y z w : X) → Type _
  ⟅ x , y ⟆≡⟅ z , w ⟆ = ∥ ((x ≡ z) × (y ≡ w)) ⊎ ((x ≡ w) × (y ≡ z)) ∥₁

  ⟅,⟆-comm : ∀ x y → ⟅ x , y ⟆ ≡ ⟅ y , x ⟆
  ⟅,⟆-comm x y = comm (η x) (η y)

diag : (ℕ → Lim M) → (n : ℕ) → M ^ n
diag z n = cut n (z n)

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
  !^ n (cut (suc n) a)   ≡⟨ a .isChainLimit n ⟩
  cut n a                ≡⟨ cong (cut n) (sym ysₙ≡a) ⟩
  diag ys n              ≡⟨ sym (q n) ⟩
  cut n x                ≡⟨ sym (x .isChainLimit n) ⟩
  !^ n (cut (suc n) x)   ≡⟨ cong (!^ n) (q (suc n)) ⟩
  !^ n (diag ys (suc n)) ≡⟨ cong (!^ n ∘ cut (suc n)) ysₙ₊₁≡b ⟩
  !^ n (cut (suc n) b)   ≡⟨ b .isChainLimit n ⟩
  cut n b ∎

zip-inj⇒complete : isInjective zip → Complete
zip-inj⇒complete inj {x} {y₁} {y₂} ys p q = goal where

  ysᶜ : ℕ → Lim M
  ysᶜ n = Sum.elim (λ ysₙ≡y₁ → y₂) (λ ysₙ≡y₂ → y₁) (p n)

  p∧pᶜ : ∀ n → ⟅ ys n , ysᶜ n ⟆ ≡ ⟅ y₁ , y₂ ⟆
  p∧pᶜ n with p n
  ... | inl ysₙ≡y₁ = cong ⟅_, y₂ ⟆ ysₙ≡y₁
  ... | inr ysₙ≡y₂ = cong ⟅_, y₁ ⟆ ysₙ≡y₂ ∙ ⟅,⟆-comm y₂ y₁

  diag-ysᶜ-islim : ∀ n → !^ n (diag ysᶜ (suc n)) ≡ diag ysᶜ n
  diag-ysᶜ-islim n with (p (suc n)) | (p n)
  ... | inl ysₙ₊₁≡y₁ | inl ysₙ≡y₁ = y₂ .isChainLimit n
  ... | inl ysₙ₊₁≡y₁ | inr ysₙ≡y₂ = diag-ysᶜ-islim-alternating x ys q ysₙ≡y₂ ysₙ₊₁≡y₁
  ... | inr ysₙ₊₁≡y₂ | inl ysₙ≡y₁ = diag-ysᶜ-islim-alternating x ys q ysₙ≡y₁ ysₙ₊₁≡y₂
  ... | inr ysₙ₊₁≡y₂ | inr ysₙ≡y₂ = y₁ .isChainLimit n

  xᶜ : Lim M
  xᶜ .elements = diag ysᶜ
  xᶜ .isChainLimit = diag-ysᶜ-islim

  qᶜ : ∀ n → cut n xᶜ ≡ diag ysᶜ n
  qᶜ n with p n
  ... | inl _ = refl
  ... | inr _ = refl

  zip-diags-pair-path : zip ⟅ x , xᶜ ⟆ ≡ zip ⟅ y₁ , y₂ ⟆
  zip-diags-pair-path = shiftedLimitPath λ n →
    zip₁ ⟅ x , xᶜ ⟆ n ≡⟨⟩
    ⟅ cut n x , cut n xᶜ ⟆ ≡⟨ cong₂ ⟅_,_⟆ (q n) (qᶜ n) ⟩
    ⟅ diag ys n , diag ysᶜ n ⟆ ≡⟨⟩
    zip₁ ⟅ ys n , ysᶜ n ⟆ n ≡⟨ cong (λ z → zip₁ z n) (p∧pᶜ n) ⟩
    zip₁ ⟅ y₁   , y₂    ⟆ n ∎

  diags-pair-path : ⟅ x , xᶜ ⟆ ≡ ⟅ y₁ , y₂ ⟆
  diags-pair-path = inj ⟅ x , xᶜ ⟆ ⟅ y₁ , y₂ ⟆ zip-diags-pair-path

  goal : ∥ (x ≡ y₁) ⊎ (x ≡ y₂) ∥₁
  goal = PT.rec PT.isPropPropTrunc (Sum.elim (PT.map inl) (PT.map inr)) x∈⟅y₁,y₂⟆ where
    x∈⟅x,xᶜ⟆ : x ∈ ⟅ x , xᶜ ⟆
    x∈⟅x,xᶜ⟆ = ∣ inl ∣ refl {x = x} ∣₁ ∣₁

    x∈⟅y₁,y₂⟆ : x ∈ ⟅ y₁ , y₂ ⟆
    x∈⟅y₁,y₂⟆ = subst (x ∈_) diags-pair-path x∈⟅x,xᶜ⟆

{-
long : (n : ℕ) → M ^ n
long zero = tt
long (suc n) = η (long n)

long-istree : ∀ n → !^ n (long (suc n)) ≡ long n
long-istree zero = refl {x = tt}
long-istree (suc n) = cong η (long-istree n)

long-tree : Lim M
long-tree .elements = long
long-tree .isChainLimit = long-istree

long? : (a : ℕ → Bool) → (n : ℕ) → M ^ n
long? a zero = tt
long? a (suc n) =
  if (a 0)
    then ε
    else η (long? (a ∘ suc) n)

long?-istree : ∀ a n → !^ n (long? a (suc n)) ≡ long? a n
long?-istree a zero = refl {x = tt}
long?-istree a (suc n) with a 0
... | true = refl {x = ε}
... | false = cong η (long?-istree (a ∘ suc) n)

long?-tree : (a : ℕ → Bool) → Lim M
long?-tree a .elements = long? a
long?-tree a .isChainLimit = long?-istree a

sequence′ : (a : ℕ → Bool) (x y : Lim M) → (even? : Bool) → ℕ → Lim M
sequence′ a x y even? with (a 0) and even?
... | true = λ n → y
... | false = λ { 0 → x ; (suc n) → sequence′ (a ∘ suc) x y (not even?) n }

sequence′-either : (a : ℕ → Bool) (x y : Lim M) (even? : Bool)
  → ∀ n → (sequence′ a x y even? n ≡ x) ⊎ (sequence′ a x y even? n ≡ y)
sequence′-either a x y even? with (a 0 and even?)
... | true = λ n → inr (refl {x = y})
... | false =
  λ { zero → inl (refl {x = x})
    ; (suc n) → sequence′-either (a ∘ suc) x y (not even?) n
    }

module _ (a : ℕ → Bool) (x y : Lim M) where
  sequence′-diag : Bool → (n : ℕ) → M ^ n
  sequence′-diag even? = diag (sequence′ a x y even?)

  sequence′-diag-islim : (even? : Bool) → ∀ n → !^ n (sequence′-diag (not even?) (suc n)) ≡ sequence′-diag even? n
  sequence′-diag-islim even? with a 0 and even?
  ... | false = {! !}
  ... | true = {! !}

sequence : (a : ℕ → Bool) (x y : Lim M) → ℕ → Lim M
sequence a x y = sequence′ a x y true

sequence-either : (a : ℕ → Bool) (x y : Lim M)
  → ∀ n → (sequence a x y n ≡ x) ⊎ (sequence a x y n ≡ y)
sequence-either a x y = sequence′-either a x y true

sequence-odd : (a : ℕ → Bool) (x y : Lim M)
  → ∀ n → isOddT n → sequence a x y n ≡ x
sequence-odd a x y with a 0
... | true = {! !}
... | false = {! !}

zip-complete⇒LLPO : Complete → LLPO
zip-complete⇒LLPO complete a true? = PT.map (Sum.map-⊎ case₁ {! !})
  (complete {x = longs-diag} {y₁ = long-tree} {y₂ = long?-tree a} longs (sequence-either a _ _) λ n → refl {x = diag longs n})
  where

  longs : ℕ → Lim M
  longs = sequence a long-tree (long?-tree a)

  longs-diag : Lim M
  longs-diag .elements = diag longs
  longs-diag .isChainLimit n =
    (!^ n) (diag longs (suc n)) ≡⟨ {! !} ⟩
    diag longs n ∎

  case₁ : longs-diag ≡ long-tree → ∀ n → isEvenT n → a n ≡ false
  case₁ p n with a 0
  ... | false = {! !}
  ... | true = {! cong (cut n) p!}
-}
