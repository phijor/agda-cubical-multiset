{-# OPTIONS --safe #-}

module Multiset.Limit.Chain where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Structure
open import Cubical.Foundations.Function
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.HLevels
open import Cubical.Data.Nat.Base as ℕ
  using (ℕ ; zero ; suc)
open import Cubical.Data.Sigma
open import Cubical.Reflection.RecordEquiv

open Iso

private
  variable
    ℓ ℓA : Level
    A : Type ℓA

-- A Chain is a sequence of types Ob₀, Ob₁, ... connected
-- by functions Ob₀ ←π₀─ Ob₁ ←π₁─ Ob₂ ← ...
record Chain (ℓ : Level) : Type (ℓ-suc ℓ) where
  constructor chain
  field
    Ob : (n : ℕ) → Type ℓ
    π : ∀ n → Ob (suc n) → Ob n

shift : Chain ℓ → Chain ℓ
shift (chain Ob π) = chain (Ob ∘ suc) (π ∘ suc)

module _ (C : Chain ℓ) where
  open Chain

  isLimit : (x : (n : ℕ) → C .Ob n) → Type ℓ
  isLimit x = ∀ n → (C .π n) (x (suc n)) ≡ x n

  record Limit : Type ℓ where
    constructor lim
    open Chain
    field
      elements : (n : ℕ) → C .Ob n
      is-lim : isLimit elements

  unquoteDecl LimitIsoΣ = declareRecordIsoΣ LimitIsoΣ (quote Limit)

  open Limit

  isOfHLevelLimit : ∀ n
    → (∀ k → isOfHLevel n (C .Ob k))
    → isOfHLevel n Limit
  isOfHLevelLimit n hlev = isOfHLevelRetractFromIso n
    LimitIsoΣ
    (isOfHLevelΣ n
      (isOfHLevelΠ n hlev)
      (λ el → isOfHLevelΠ n λ k → isOfHLevelPath n (hlev k) _ _)
    )

  isSetLimit : (∀ k → isSet (C .Ob k)) → isSet Limit
  isSetLimit = isOfHLevelLimit 2

  LimitPathP : {l₀ l₁ : Limit}
    → (Σ[ elements≡ ∈ ((l₀ .elements) ≡ (l₁ .elements)) ] PathP (λ i → isLimit (elements≡ i)) (l₀ .is-lim) (l₁ .is-lim))
    → l₀ ≡ l₁
  LimitPathP (elements≡ , is-lim≡) = λ i → lim (elements≡ i) (is-lim≡ i)

  LimitPathPExt : {l₀ l₁ : Limit}
    → (elements≡ : ∀ n → l₀ .elements n ≡ l₁ .elements n)
    → (is-lim≡ : ∀ n → PathP (λ i → C .π n (elements≡ (suc n) i) ≡ elements≡ n i) (l₀ .is-lim n) (l₁ .is-lim n))
    → l₀ ≡ l₁
  LimitPathPExt elements≡ is-lim≡ = λ i → lim (λ n → elements≡ n i) (λ n → is-lim≡ n i)

  isSet→LimitPathExt : (setCh : ∀ k → isSet (C .Ob k))
    → {l₀ l₁ : Limit}
    → (∀ n → l₀ .elements n ≡ l₁ .elements n)
    → l₀ ≡ l₁
  isSet→LimitPathExt setCh elements≡ = LimitPathPExt elements≡ set-coh where
    set-coh : ∀ n → Square _ _ _ _
    set-coh n = isSet→isSet' (setCh n) _ _ _ (elements≡ n)

  record Cone (A : Type ℓA) : Type (ℓ-max ℓ ℓA) where
    constructor cone
    field
      leg : (n : ℕ) → A → C .Ob n
      commutes : (n : ℕ) → (C .π n) ∘ (leg (suc n)) ≡ leg n

  toCone : (f : A → Limit) → Cone A
  toCone {A = A} f = cone
    (λ n a → (f a) .elements n)
    (λ n → funExt (aux n)) where

    aux : ∀ n a → (C .π n (f a .elements (suc n))) ≡ f a .elements n
    aux n a = (f a) .is-lim n

  ofCone : Cone A → A → Limit
  ofCone (cone leg commutes) a = lim (λ n → leg n a) λ n → funExt⁻ (commutes n) a

universalPropertyIso : {C : Chain ℓ} → Iso (A → Limit C) (Cone C A)
universalPropertyIso .fun = toCone _
universalPropertyIso .inv = ofCone _
universalPropertyIso .rightInv _ = refl
universalPropertyIso .leftInv _ = refl

universalProperty : {C : Chain ℓ} → (A → Limit C) ≃ Cone C A
universalProperty = isoToEquiv universalPropertyIso
