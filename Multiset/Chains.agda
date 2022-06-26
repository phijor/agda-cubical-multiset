module Multiset.Chains where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Structure
open import Cubical.Foundations.Function
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Isomorphism
open import Cubical.Data.Nat.Base as ℕ
  using (ℕ ; zero ; suc)
open import Cubical.Data.Sigma
open import Cubical.Reflection.RecordEquiv

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

-- TODO: Can we define a shifted chain?

-- A limit of a Chain C = (Ob, π) is a sequence of elements
-- x₀ : Ob₀, x₁ : Ob₁, ... together with a proof that that
-- it is preserved under the maps πₙ of the chain, i.e.
--
--  ∀ n : ℕ.    πₙ(xₙ₊₁) ≡ xₙ
module Limit (C : Chain ℓ) where
  open Chain

  IsChainLimit : (x : (n : ℕ) → C .Ob n) → Type ℓ
  IsChainLimit x = ∀ n → (C .π n) (x (suc n)) ≡ x n

  record ChainLimit : Type ℓ where
    constructor lim
    open Chain
    field
      elements : (n : ℕ) → C .Ob n
      isChainLimit : IsChainLimit elements

  unquoteDecl ChainLimitIsoΣ = declareRecordIsoΣ ChainLimitIsoΣ (quote ChainLimit)

  open ChainLimit

  ChainLimitPathP : {l₀ l₁ : ChainLimit}
    → (Σ[ elements≡ ∈ ((l₀ .elements) ≡ (l₁ .elements)) ] PathP (λ i → IsChainLimit (elements≡ i)) (l₀ .isChainLimit) (l₁ .isChainLimit))
    → l₀ ≡ l₁
  ChainLimitPathP (elements≡ , isChainLimit≡) = λ i → lim (elements≡ i) (isChainLimit≡ i)

  ChainLimitPathPExt : {l₀ l₁ : ChainLimit}
    → (elements≡ : ∀ n → l₀ .elements n ≡ l₁ .elements n)
    → (isChainLimit≡ : ∀ n → PathP (λ i → C .π n (elements≡ (suc n) i) ≡ elements≡ n i) (l₀ .isChainLimit n) (l₁ .isChainLimit n))
    → l₀ ≡ l₁
  ChainLimitPathPExt elements≡ isChainLimit≡ = λ i → lim (λ n → elements≡ n i) (λ n → isChainLimit≡ n i)

  record Cone (A : Type ℓA) : Type (ℓ-max ℓ ℓA) where
    constructor cone
    field
      leg : (n : ℕ) → A → C .Ob n
      commutes : (n : ℕ) → (C .π n) ∘ (leg (suc n)) ≡ leg n

  toCone : (f : A → ChainLimit)
    → Cone A
  toCone {A = A} f = cone
    (λ n a → (f a) .elements n)
    (λ n → funExt (aux n)) where

    aux : ∀ n a → (C .π n (f a .elements (suc n))) ≡ f a .elements n
    aux n a = (f a) .isChainLimit n

  ofCone : Cone A → A → ChainLimit
  ofCone (cone leg commutes) a = lim (λ n → leg n a) λ n → funExt⁻ (commutes n) a

  universalProperty : (A → ChainLimit) ≃ Cone A
  universalProperty = isoToEquiv (iso toCone ofCone (λ c → refl) λ f → refl)

module FunctorChain
  (F : Type ℓ → Type ℓ) (map : {X Y : Type ℓ} → (X → Y) → (F X → F Y))
  (X₀ : Type ℓ) (init : F X₀ → X₀) where
  open Chain

  iterObj : (n : ℕ) → Type ℓ
  iterObj zero = X₀
  iterObj (suc n) = F (iterObj n)

  iterInit : (n : ℕ) → iterObj (suc n) → iterObj n
  iterInit zero = init
  iterInit (suc n) = map (iterInit n)

  iterated : Chain ℓ
  iterated .Ob n = iterObj n
  iterated .π n = iterInit n

  open Limit iterated
    using ()
    renaming
      ( ChainLimit to IteratedLimit
      ; ChainLimitPathP to IteratedLimitPathP
      ; ChainLimitPathPExt to IteratedLimitPathPExt
      )
    public

  shifted : Chain ℓ
  shifted .Ob n = F (iterated .Ob n)
  shifted .π n = map (iterated .π n)

  open Limit shifted
    using ()
    renaming
      ( ChainLimit to ShiftedLimit
      ; ChainLimitPathP to ShiftedLimitPathP
      ; ChainLimitPathPExt to ShiftedLimitPathPExt
      )
    public

  open ShiftedLimit
    renaming
      ( elements to shiftedElements
      ; isChainLimit to isShiftedChainLimit
      )
    public

  module _ (shiftLim : ShiftedLimit) where
    open Limit using (ChainLimit)
    open ChainLimit

    shifted→iterated : IteratedLimit
    shifted→iterated .elements = λ n → iterated .π n (shiftLim .elements n)
    shifted→iterated .isChainLimit = λ n → cong (iterInit n) (shiftLim .isChainLimit n)

  module _ (iterLim : IteratedLimit) where
    open Limit using (ChainLimit)
    open ChainLimit

    iterated→shifted : ShiftedLimit
    iterated→shifted .elements = λ n → iterLim .elements (suc n)
    iterated→shifted .isChainLimit = λ n → iterLim .isChainLimit (suc n)

  module _ where
    open Iso
    open Limit
    open ChainLimit

    open import Multiset.Util.Square using (kiteFiller)

    shifted≅iterated : Iso IteratedLimit ShiftedLimit
    shifted≅iterated .fun = iterated→shifted
    shifted≅iterated .inv = shifted→iterated
    shifted≅iterated .rightInv (lim _ isLim) =
      ShiftedLimitPathPExt (isLim) (λ n → kiteFiller)
    shifted≅iterated .leftInv (lim _ isLim) =
      IteratedLimitPathPExt isLim (λ n → kiteFiller)

    shifted≃iterated : IteratedLimit ≃ ShiftedLimit
    shifted≃iterated = isoToEquiv shifted≅iterated

  isLimitPreserving : Type ℓ
  isLimitPreserving = F IteratedLimit ≃ ShiftedLimit


record Cochain (ℓ : Level) : Type (ℓ-suc ℓ) where
  field
    Ob : (n : ℕ) → Type ℓ
    ι : ∀ n → Ob n → Ob (suc n)

module Colimit (C : Cochain ℓ) where
  open import Cubical.Foundations.HLevels
  open Cochain

  IsCochainLimit : (x : (n : ℕ) → C .Ob n) → Type ℓ
  IsCochainLimit x = (n : ℕ) → x (suc n) ≡ C .ι n (x n)

  -- Fun fact: the hLevel of IsCochainLimit does *not* depend on (C .Ob 0)
  isCochainLimitIsOfHLevel : (l : HLevel) → (∀ n → isOfHLevel (suc l) (C .Ob (suc n))) → (x : (n : ℕ) → C .Ob n) → isOfHLevel l (IsCochainLimit x)
  isCochainLimitIsOfHLevel l lC x = isOfHLevelΠ l λ n → isOfHLevelPath' l (lC n) (x (suc n)) (C .ι n (x n))

  isCochainLimitIsOfHLevelDep : (l : HLevel) → (∀ n → isOfHLevel (suc l) (C .Ob (suc n))) → isOfHLevelDep l IsCochainLimit
  isCochainLimitIsOfHLevelDep l lC = isOfHLevel→isOfHLevelDep l (isCochainLimitIsOfHLevel l lC)

  isCochainLimitIsProp = isCochainLimitIsOfHLevel 0
  isCochainLimitIsPropDep = isCochainLimitIsOfHLevelDep 0

  record CochainLimit : Type ℓ where
    constructor lim
    open Cochain
    field
      elements : (n : ℕ) → C .Ob n
      isCochainLimit : IsCochainLimit elements

  unquoteDecl CochainLimitIsoΣ = declareRecordIsoΣ CochainLimitIsoΣ (quote CochainLimit)

  open CochainLimit

  CochainLimitPathP : {l₀ l₁ : CochainLimit}
    → (Σ[ elements≡ ∈ ((l₀ .elements) ≡ (l₁ .elements)) ] PathP (λ i → IsCochainLimit (elements≡ i)) (l₀ .isCochainLimit) (l₁ .isCochainLimit))
    → l₀ ≡ l₁
  CochainLimitPathP = cong (CochainLimitIsoΣ .Iso.inv) ∘ ΣPathP

  universalProperty : CochainLimit ≃ C .Ob 0
  universalProperty = up-equiv where
    open import Multiset.Util

    iter' : (x : C .Ob 0) (n : ℕ) → C .Ob n
    iter' x 0 = x
    iter' x (suc n) = C .ι n (iter' x n)

    isLimIter : ∀ x → IsCochainLimit (iter' x)
    isLimIter x = λ n → refl

    aux : (l : CochainLimit) → ∀ n → iter' (l .elements 0) n ≡ l .elements n
    aux l zero = refl
    aux l (suc n) = cong (C .ι n) (aux l n) ∙ sym (l .isCochainLimit n)

    module _ (z : CochainLimit) (n : ℕ) where
      -- Idea: aux z (suc n) ≡ cong (C .ι n) (aux l n) ∙ sym (l .isCochainLimit n) by definition.
      -- Build the canonical filler.
      aux-filler : Square
        (cong (C .ι n) (aux z n))
        (aux z (suc n))
        (refl {x = C .ι n (iter' (z .elements 0) n)})
        (sym (isCochainLimit z n))
      aux-filler = compPath-filler _ _

      -- The above filler is almost what we want.
      -- We simply need to rotate the sides of the square.
      up-square : Square
        {- top -} refl
        {- bot -} (isCochainLimit z n)
        {- lft -} (aux z (suc n))
        {- rgt -} (cong (C .ι n) (aux z n))
      up-square = λ i j → aux-filler (~ j) i

    up-equiv = isoToEquiv
      (iso
        (λ z → z .elements 0)
        (λ x → lim (iter' x) (isLimIter x))
        (λ _ → refl)
        (λ z → CochainLimitPathP
          ( funExt (aux z)
          , funExt (λ n → up-square z n)
          )
        )
      )
