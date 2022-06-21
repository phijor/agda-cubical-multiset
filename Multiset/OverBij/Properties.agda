module Multiset.OverBij.Properties where

open import Multiset.OverBij.Base as OverBij
open import Multiset.Bij as Bij
open import Multiset.Chains
  using
    ( Chain
    ; module Limit
    )

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Function using (_∘_)

open import Cubical.Functions.FunExtEquiv using (funExtDep ; funExtDep⁻)

open import Cubical.Data.Sigma as Σ
  using (ΣPathP)
open import Cubical.Data.Nat as ℕ
  using (ℕ ; zero ; suc)
open import Cubical.Data.Unit as Unit
  using
    ( Unit
    ; tt
    )

private
  variable
    ℓ : Level

  ℓ₀ = ℓ-zero

  iter : ℕ → (Type ℓ → Type ℓ) → (Type ℓ → Type ℓ)
  iter {ℓ} zero F X = X
  iter {ℓ} (suc n) F X = F (iter n F X) -- iter n F (F X)

  !_ : (A : Type ℓ) → A → Unit
  ! A = λ a → tt

  iter-map : ∀ {F : Type ℓ → Type ℓ} {X Y : Type ℓ}
    → (n : ℕ)
    → (map : ∀ {X Y : Type ℓ} → (X → Y) → (F X → F Y))
    → ((X → Y) → (iter n F X → iter n F Y))
  iter-map zero map f = f
  iter-map {F = F} (suc n) map f = map (iter-map n map f) -- iter-map {X = F _} {Y = F _} n map (map f)

FMGpd^ : ℕ → (Type ℓ → Type ℓ)
FMGpd^ {ℓ = ℓ} n = iter n FMGpd
-- FMGpd^ zero X = X
-- FMGpd^ (suc n) X = FMGpd^ n (FMGpd X)

FMGpdMap^ : ∀ {X Y : Type ℓ} (n : ℕ) → (X → Y) → (FMGpd^ n X → FMGpd^ n Y)
FMGpdMap^ n = iter-map n (OverBij.map)
-- FMGpdMap^ zero f = f
-- FMGpdMap^ (suc n) f = (FMGpdMap^ n (OverBij.map f))

-- isGroupoidFMGpd^ : ∀ {X : Type ℓ} {n : ℕ} → isGroupoid X → isGroupoid (FMGpd^ n X)
-- isGroupoidFMGpd^ {n = zero} gpdX = gpdX
-- isGroupoidFMGpd^ {X = X} {n = suc n} gpdX = isGroupoidFMGpd^ {X = FMGpd X} {n = n} (isGroupoidFMGpd gpdX)

open Chain

!-FMGpd : (n : ℕ) → FMGpd (FMGpd^ n Unit) → FMGpd^ n Unit
!-FMGpd zero = ! FMGpd Unit
!-FMGpd (suc n) = map (!-FMGpd n) -- FMGpdMap^ n (! (FMGpd Unit))

!-Chain : Chain ℓ₀
!-Chain .Ob n = FMGpd^ n Unit
!-Chain .π n = !-FMGpd n

open module !-Limit = Limit !-Chain
  renaming
    ( IsChainLimit to !-IsChainLimit
    ; ChainLimit to !-ChainLimit
    ; Cone to !-Cone
    )

open !-ChainLimit
open !-Cone

-- ωTree : Type ℓ₀
-- ωTree = Σ[ t ∈ ((n : ℕ) → FMGpd^ n Unit) ] (∀ n → !-FMGpd n (t (suc n)) ≡ t n)

-- ωCone : !-Cone ωTree
-- ωCone = Limit.cone (λ n t → t .fst n) (λ n → funExt (λ t → t .snd n))

-- _→ωCone : {V : Type ℓ} → (c : !-Cone V) → V → ωTree
-- c →ωCone = λ v → (λ n → c .leg n v) , (λ n → funExt⁻ (c .commutes n) v)

-- !-lim : ωTree → !-ChainLimit
-- !-lim (t , p) .elements = t
-- !-lim (t , p) .isChainLimit = p

shifted!-Chain : Chain ℓ₀
shifted!-Chain .Ob n = FMGpd (!-Chain .Ob n)
shifted!-Chain .π n = map (!-Chain .π n)

open module shifted!-Limit = Limit shifted!-Chain
  renaming
    ( IsChainLimit to shifted!-IsChainLimit
    ; ChainLimit   to shifted!-ChainLimit
    ; Cone         to shifted!-Cone
    )

open Iso

open Limit
open ChainLimit

shifted!Lim→!Lim : shifted!-ChainLimit → !-ChainLimit
(shifted!Lim→!Lim (lim el isLim)) .elements = λ n → !-FMGpd n (el n)
(shifted!Lim→!Lim (lim el isLim)) .isChainLimit = λ n → cong (!-FMGpd n) (isLim n)

!Lim→shifted!Lim : !-ChainLimit → shifted!-ChainLimit
!Lim→shifted!Lim (lim el isLim) .elements = λ n → el (suc n)
!Lim→shifted!Lim (lim el isLim) .isChainLimit = λ n → isLim (suc n)

-- These are connections
--
-- * -- p -- *
-- |         |
-- p         q
-- |         |
-- * -- q -- *
someSq : (n : ℕ) → ((lim el isLim) : !-ChainLimit)
  → Square
    (cong (!-FMGpd n) (isLim (suc n)))
    (isLim n)
    (cong (!-FMGpd n) (isLim (suc n)))
    (isLim n)
someSq n (lim el isLim) = {!   !}

anotherSq : (n : ℕ) → ((lim el isLim) : shifted!-ChainLimit)
  → Square
    (cong (map (!-FMGpd n)) (isLim (suc n))) -- (cong (!-FMGpd n) (isLim (suc n)))
    (isLim n) -- (isLim n)
    (cong (map (!-FMGpd n)) (isLim (suc n))) -- (cong (!-FMGpd n) (isLim (suc n)))
    (isLim n)
anotherSq = {!   !}

shifted!-ChainLimit≅!-ChainLimit : Iso shifted!-ChainLimit !-ChainLimit
fun shifted!-ChainLimit≅!-ChainLimit = shifted!Lim→!Lim
inv shifted!-ChainLimit≅!-ChainLimit = !Lim→shifted!Lim
rightInv shifted!-ChainLimit≅!-ChainLimit = λ { l@(lim el isLim) → !-Limit.ChainLimitPathP (funExt isLim , funExt (λ n → someSq n l)) }
leftInv shifted!-ChainLimit≅!-ChainLimit = λ { l@(lim el isLim) → shifted!-Limit.ChainLimitPathP ((funExt isLim) , funExt (λ n → anotherSq n l)) }

α : FMGpd (!-ChainLimit) → shifted!-ChainLimit
elements (α x) = λ n → map (λ l → l .elements n) x
isChainLimit (α (b , v)) = λ n → ΣPathP (refl , (funExt (λ xs → v xs .isChainLimit n)))

module _ (lim : shifted!-ChainLimit) where
  b : ℕ → Bij
  b n = lim .elements n .fst

  v : ∀ n → ⟨Bij→FinSet⟩ (b n) → FMGpd^ n Unit
  v n = lim .elements n .snd

  bEq : ∀ n → b (suc n) ≡ b n
  bEq n = cong fst (lim .isChainLimit n)

  vEq : ∀ n
    → PathP (λ i → ⟨Bij→FinSet⟩ (bEq n i) → FMGpd^ n Unit)
      (!-FMGpd n ∘ v (suc n)) (v n)
  vEq n = cong snd (lim .isChainLimit n)

  vEqExt : ∀ n x y
    → PathP (λ i → ⟨Bij→FinSet⟩ (bEq n i)) x y
    → !-FMGpd n (v (suc n) x) ≡ v n y
  vEqExt n x y = funExtDep⁻ (vEq n)

  bContr : ∀ n → b n ≡ b 0
  bContr zero = refl
  bContr (suc n) = bEq n ∙ bContr n

  -- TODO: maybe there is a vContrExt derived from vEqExt
  --  vContrExt : ∀ n x y → PathP (λ i → ⟨Bij→FinSet⟩ (bContr n i)) x y → v n ≡ !-FMGpd n (lim .elements n)
  -- What happens if we try to prove that by induction on n? Does that help?

  vContr : ∀ n
    → PathP (λ i → ⟨Bij→FinSet⟩ (bContr n i) → FMGpd^ n Unit)
      (v n) λ _ → !-FMGpd n (lim .elements n)
  vContr zero = refl
  vContr (suc n) =
    compPathP' {B = λ (x : Bij) → ⟨Bij→FinSet⟩ x → FMGpd^ (suc n) Unit}
      {y' = {!   !}} -- TODO: find the midpoint of this path comp
      {p = bEq n} {q = bContr n}
      {! vEq n  !} {! (vContr n)  !}

-- Lemma: el n .fst ≡ el m .fst for any m, n
lemma₁ : ∀ n → (l : shifted!-ChainLimit) → l .elements 0 .fst ≡ l .elements n .fst
lemma₁ zero l = refl
lemma₁ (suc n) l = lemma₁ n l ∙ sym (cong fst (l .isChainLimit n))
  -- l .elements 0 .fst ≡⟨ lemma₁ n l ⟩
  -- l .elements n .fst ≡⟨ sym (cong fst (l .isChainLimit n)) ⟩
  -- l .elements (suc n) .fst ∎

α⁻¹ : shifted!-ChainLimit → FMGpd (!-ChainLimit)
α⁻¹ (lim el isLim) =
  ( (el 0 .fst)
  , λ xs → !-Limit.lim
    (λ n → !-Chain .π n (el n))
    (λ n → cong (!-FMGpd n) (isLim n))
  )

lemma₂ : ∀ n (l : shifted!-ChainLimit)
  → PathP (λ i → ⟨Bij→FinSet⟩ (lemma₁ n l i) → !-Chain .Ob n)
      (λ x → snd (α⁻¹ l) x .elements n)
      (snd (l .elements n))
lemma₂ zero l = refl
lemma₂ (suc n) l = funExtDep (λ p → ΣPathP ((cong fst (l .isChainLimit n) ∙ {! lemma₂ n l  !}) , {!   !}))

α-section : ∀ (x : shifted!-ChainLimit) → α (α⁻¹ x) ≡ x
α-section l@(lim el isLim) = shifted!-Limit.ChainLimitPathP
  ( (funExt (λ n → ΣPathP
    ( lemma₁ n l
    , {! cong fst (isLim n)  !}
      -- funExtDep λ {x₀} {x₁} p →
      -- !-FMGpd n (el n) ≡⟨ {! cong snd (isLim n)  !} ⟩
      -- snd (el n) x₁ ∎
    )))
  , {!   !}
  )

-- TODO: α is an equivalence
