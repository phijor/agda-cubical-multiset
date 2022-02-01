module Multiset.Chains where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Structure
open import Cubical.Foundations.Function
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Isomorphism
open import Cubical.Data.Nat.Base
open import Cubical.Reflection.RecordEquiv

private
  variable
    ℓ ℓA : Level
    A : Type ℓA

record Chain (ℓ : Level) : Type (ℓ-suc ℓ) where
  constructor chain
  field
    Ob : (n : ℕ) → Type ℓ
    π : ∀ n → Ob (suc n) → Ob n

module Limit (C : Chain ℓ) where
  open Chain

  IsChainLimit : (x : (n : ℕ) → C .Ob n) → Type ℓ
  IsChainLimit x = ∀ n → (C .π n) (x (suc n)) ≡ x n

  record ChainLimit : Type ℓ where
    constructor lim
    open Chain
    field
      proj : (n : ℕ) → C .Ob n
      isChainLimit : IsChainLimit proj

  record Cone (A : Type ℓA) : Type (ℓ-max ℓ ℓA) where
    constructor cone
    field
      leg : (n : ℕ) → A → C .Ob n
      commutes : (n : ℕ) → (C .π n) ∘ (leg (suc n)) ≡ leg n

  toCone : (f : A → ChainLimit)
    → Cone A
  toCone {A = A} f = cone
    (λ n a → (f a) .proj n)
    (λ n → funExt (aux n)) where
    open ChainLimit

    aux : ∀ n a → (C .π n (f a .proj (suc n))) ≡ f a .proj n
    aux n a = (f a) .isChainLimit n

  ofCone : Cone A → A → ChainLimit
  ofCone (cone leg commutes) a = lim (λ n → leg n a) λ n → funExt⁻ (commutes n) a

  universalProperty : (A → ChainLimit) ≃ Cone A
  universalProperty = isoToEquiv (iso toCone ofCone (λ c → refl) λ f → refl)

record Cochain (ℓ : Level) : Type (ℓ-suc ℓ) where
  field
    Ob : (n : ℕ) → Type ℓ
    ι : ∀ n → Ob n → Ob (suc n)

module Colimit (C : Cochain ℓ) where
  open Cochain

  IsCochainLimit : (x : (n : ℕ) → C .Ob n) → Type ℓ
  IsCochainLimit x = (n : ℕ) → x (suc n) ≡ C .ι n (x n)

  record CochainLimit : Type ℓ where
    constructor colim
    open Cochain
    field
      inj : (n : ℕ) → C .Ob n
      isCochainLimit : IsCochainLimit inj

  unquoteDecl CochainLimitIsoΣ = declareRecordIsoΣ CochainLimitIsoΣ (quote CochainLimit)

  universalProperty : CochainLimit ≃ C .Ob 0
  universalProperty = isoToEquiv
    (iso
      (λ L → L .inj 0)
      (λ x → colim (iter' x) (iterIsLim x))
      (λ _ → refl)
      (λ L → {!   !})
    ) where
    open CochainLimit

    iter' : (x : C .Ob 0) (n : ℕ) → C .Ob n
    iter' x 0 = x
    iter' x (suc n) = C .ι n (iter' x n)

    iterIsLim : ∀ x → IsCochainLimit (iter' x)
    iterIsLim x = λ n → refl
