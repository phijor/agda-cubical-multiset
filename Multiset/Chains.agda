module Multiset.Chains where

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

  isOfHLevelChainLimit : ∀ n
    → (∀ k → isOfHLevel n (C .Ob k))
    → isOfHLevel n ChainLimit
  isOfHLevelChainLimit n hlev = isOfHLevelRetractFromIso n 
    ChainLimitIsoΣ
    (isOfHLevelΣ n
      (isOfHLevelΠ n hlev)
      (λ el → isOfHLevelΠ n λ k → isOfHLevelPath n (hlev k) _ _)
    )

  ChainLimitPathP : {l₀ l₁ : ChainLimit}
    → (Σ[ elements≡ ∈ ((l₀ .elements) ≡ (l₁ .elements)) ] PathP (λ i → IsChainLimit (elements≡ i)) (l₀ .isChainLimit) (l₁ .isChainLimit))
    → l₀ ≡ l₁
  ChainLimitPathP (elements≡ , isChainLimit≡) = λ i → lim (elements≡ i) (isChainLimit≡ i)

  ChainLimitPathPExt : {l₀ l₁ : ChainLimit}
    → (elements≡ : ∀ n → l₀ .elements n ≡ l₁ .elements n)
    → (isChainLimit≡ : ∀ n → PathP (λ i → C .π n (elements≡ (suc n) i) ≡ elements≡ n i) (l₀ .isChainLimit n) (l₁ .isChainLimit n))
    → l₀ ≡ l₁
  ChainLimitPathPExt elements≡ isChainLimit≡ = λ i → lim (λ n → elements≡ n i) (λ n → isChainLimit≡ n i)

  isSet→ChainLimitPathExt : (setCh : ∀ k → isSet (C .Ob k))
    → {l₀ l₁ : ChainLimit}
    → (∀ n → l₀ .elements n ≡ l₁ .elements n)
    → l₀ ≡ l₁
  isSet→ChainLimitPathExt setCh elements≡ = ChainLimitPathPExt elements≡ set-coh where
    set-coh : ∀ n → Square _ _ _ _
    set-coh n = isSet→isSet' (setCh n) _ _ _ (elements≡ n)

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

  universalPropertyIso : Iso (A → ChainLimit) (Cone A)
  universalPropertyIso .fun = toCone
  universalPropertyIso .inv = ofCone
  universalPropertyIso .rightInv _ = refl
  universalPropertyIso .leftInv _ = refl

  universalProperty : (A → ChainLimit) ≃ Cone A
  universalProperty = isoToEquiv universalPropertyIso

mapLimit : {C D : Chain ℓ}
  → (f : (n : ℕ) → (C .Chain.Ob n) → (D .Chain.Ob n))
  → Limit.ChainLimit C
  → Limit.ChainLimit D
mapLimit f (Limit.lim elements isChainLimit) = Limit.lim
  (λ n → f n (elements n))
  λ n → {! cong f!}

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
