{-# OPTIONS --safe #-}

module Multiset.Limit.Cochain where

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


record Cochain (ℓ : Level) : Type (ℓ-suc ℓ) where
  field
    Ob : (n : ℕ) → Type ℓ
    ι : ∀ n → Ob n → Ob (suc n)

  -- Given some (x₀ : Ob 0), we can trace it through the chain.
  cotrace : (x₀ : Ob 0) → (n : ℕ) → Ob n
  cotrace x₀ 0 = x₀
  cotrace x₀ (suc n) = ι n (cotrace x₀ n)

module Colimit (C : Cochain ℓ) where
  open import Cubical.Foundations.HLevels
  open Cochain

  -- XXX: What if we truncate this definition
  -- so that it becomes a proposition?  This would
  -- certainly make our live easier in everything
  -- that depends on it.
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

    -- The initial term of this limit, in Ob₀.
    init : C .Ob 0
    init = elements 0

    -- Following the transition function ι : Obₙ → Obₙ₊₁,
    -- we obtain a term in Obₙ for any (n : ℕ).
    -- Note that (follow n) and (elements n) are *not*
    -- definitionally the same, only up to some path
    -- obtained by function extensionality from (isCochainLimit).
    follow : (n : ℕ) → C .Ob n
    follow = cotrace C init

  unquoteDecl CochainLimitIsoΣ = declareRecordIsoΣ CochainLimitIsoΣ (quote CochainLimit)

  open CochainLimit

  CochainLimitPathP : {l₀ l₁ : CochainLimit}
    → (Σ[ elements≡ ∈ ((l₀ .elements) ≡ (l₁ .elements)) ] PathP (λ i → IsCochainLimit (elements≡ i)) (l₀ .isCochainLimit) (l₁ .isCochainLimit))
    → l₀ ≡ l₁
  CochainLimitPathP = cong (CochainLimitIsoΣ .Iso.inv) ∘ ΣPathP

  -- Given any term in the first object of a cochain,
  -- its cotrace defines a limit.
  module _ (x₀ : C .Ob 0) where
    cotraceIsCochainLimit : IsCochainLimit (cotrace C x₀)
    cotraceIsCochainLimit = λ n → refl {x = C .ι n (cotrace C x₀ n)}

    cotraceLimit : CochainLimit
    cotraceLimit .elements = cotrace C x₀
    cotraceLimit .isCochainLimit = cotraceIsCochainLimit

  -- We show that (cf. `cotracePath` below) there exists
  -- an identification between any colimit and the colimit
  -- induced by following its initial element through the
  -- chain.
  module Cotrace (colim : CochainLimit) where
    -- At the nᵗʰ point in the chain, there is an identification
    -- between the cotrace of initial element and the nᵗʰ term of
    -- the colimit.
    elemPathExt : ∀ n → follow colim n ≡ colim .elements n
    elemPathExt 0 = refl
    elemPathExt (suc n) = cong (C .ι n) (elemPathExt n) ∙ sym (colim .isCochainLimit n)

    -- The tricky part of this proof is to show that there is an identification
    -- between the properties of "being a colimit" (`isCochainLimit`).
    -- This stems from the fact that IsCochainLimit is in general not a proposition.
    -- It would be, if Ob₀ was a set, but that's not the situation we're in.
    --
    -- The strategy then becomes to construct a square that depends on the definition
    -- of elemPathExt.
    module _ (n : ℕ) where
      private
        -- These are the paths in the second clause of elemPathExt:
        --  elemPathExt (suc n) ≔ p ∙ sym q
        p : C .ι n (follow colim n) ≡ C .ι n (colim .elements n)
        p = (cong (C .ι n) (elemPathExt n))

        q : colim .elements (suc n) ≡ C .ι n (colim .elements n)
        q = colim .isCochainLimit n

        _ : follow colim (suc n) ≡ follow colim (suc n)
        _ = refl

      --  This is the filler that we're after:
      --                                 refl
      --    (follow colim (suc n)) ================= (follow colim (suc n))
      --              |   ∙—→                                  |
      --            p |   ↓                                    |
      --              |                                        |
      --  (C .ι n (colim .elements n))                         | p
      --              |                                        |
      --          q⁻¹ |                                        |
      --              |                                        |
      --   (colim .elements (suc n)) ----------- (C .ι n (colim .elements n))
      --                                  q
      isCochainSquareExt : Square refl q (p ∙ (sym q)) p
      isCochainSquareExt = λ i j → filler (~ j) i where

        -- Luckily, the above square is a rotated version of one of the
        -- path composition coherences:
        filler : Square p (p ∙ sym q) refl (sym q)
        filler = compPath-filler p (sym q)

    elemPath : follow colim ≡ colim .elements
    elemPath = funExt elemPathExt

    isCochainSquare : PathP (λ i → IsCochainLimit (elemPath i))
      (cotraceIsCochainLimit (init colim))
      (colim .isCochainLimit)
    isCochainSquare = funExt isCochainSquareExt

    -- Using function extensionality in both components, we finally obtain
    -- the desired identification:
    cotracePath : cotraceLimit (init colim) ≡ colim
    cotracePath = CochainLimitPathP (elemPath , isCochainSquare)

  open Cotrace
    using (cotracePath)
    renaming
      ( elemPathExt to cotraceElemPathExt
      ; elemPath to cotraceElemPath
      )
    public

  universalPropertyIso : Iso CochainLimit (C .Ob 0)
  universalPropertyIso = def where
    def : Iso _ _
    def .Iso.fun = CochainLimit.init
    def .Iso.inv = cotraceLimit
    def .Iso.rightInv = λ _ → refl
    def .Iso.leftInv = cotracePath

  universalProperty : CochainLimit ≃ C .Ob 0
  universalProperty = isoToEquiv universalPropertyIso
