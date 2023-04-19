{-# OPTIONS --safe #-}

module Multiset.Limit.TerminalChain where

open import Multiset.Prelude
open import Multiset.Util using (!_)
open import Multiset.Util.Square using (kiteFiller)
open import Multiset.Limit.Chain
open import Multiset.Functor public

open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Function
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism
open import Cubical.Data.Nat.Base hiding (_^_)

module _ {ℓ} (F : Type ℓ → Type ℓ) {{ FunctorF : Functor F }} where
  open Chain
  open Limit
    using (elements ; is-lim)

  open Functor FunctorF using (map ; map-id ; map-comp)

  _^_ : ℕ → Type ℓ
  _^_ zero = Unit*
  _^_ (suc n) = F (_^_ n)

  infixl 7 _^_

  private
    F^_ = _^_

  _map-!^_ : ∀ n → F^ suc n → F^ n
  _map-!^_ zero = λ _ → tt*
  _map-!^_ (suc n) = map (_map-!^_ n)

  private
    !^ : ∀ n → F^ suc n → F^ n
    !^ = _map-!^_

  ch : Chain ℓ
  ch .Ob = _^_
  ch .π = _map-!^_

  sh = shift ch

  Lim = Limit ch
  ShLim = Limit sh

  isOfHLevelLim = isOfHLevelLimit ch

  isLim : (el : (n : ℕ) → F^ n) → Type ℓ
  isLim = isLimit ch

  isShLim : (el : (n : ℕ) → F^ suc n) → Type ℓ
  isShLim = isLimit sh

  LimPathPExt = LimitPathPExt ch
  ShLimPathPExt = LimitPathPExt (shift ch)

  isSet→LimPath : (∀ k → isSet (F^ k)) → ∀ {lim₁ lim₂} → (∀ n → lim₁ .elements n ≡ lim₂ .elements n) → lim₁ ≡ lim₂
  isSet→LimPath setF = isSet→LimitPathExt ch setF

  isSet→ShLimPath : (∀ k → isSet (F^ suc k)) → ∀ {shlim₁ shlim₂} → (∀ n → shlim₁ .elements n ≡ shlim₂ .elements n) → shlim₁ ≡ shlim₂
  isSet→ShLimPath setF = isSet→LimitPathExt (shift ch) setF

  isShLim→isLim : ∀ {el : (n : ℕ) → F^ suc n} → isShLim el → isLim (λ n → !^ n (el n))
  isShLim→isLim {el} is-shlim n = cong (!^ n) (is-shlim n)

  isLim→isShLim : ∀ {el : (n : ℕ) → F^ n} → isLim el → isShLim (el ∘ suc)
  isLim→isShLim islim n = islim (suc n)

  ShLim→Lim : ShLim → Lim
  ShLim→Lim sh .elements n = !^ n (sh .elements n)
  ShLim→Lim sh .is-lim = isShLim→isLim (sh .is-lim)

  Lim→ShLim : Lim → ShLim
  Lim→ShLim l .elements = l .elements ∘ suc
  Lim→ShLim l .is-lim = isLim→isShLim (l .is-lim)

  open Iso

  ShiftedLimitIso : Iso ShLim Lim
  ShiftedLimitIso .fun = ShLim→Lim
  ShiftedLimitIso .inv = Lim→ShLim
  ShiftedLimitIso .rightInv (lim _ is-lim) = LimPathPExt is-lim λ n → kiteFiller
  ShiftedLimitIso .leftInv (lim _ is-shlim) = ShLimPathPExt is-shlim λ n → kiteFiller

  ShLim≃Lim : ShLim ≃ Lim
  ShLim≃Lim = isoToEquiv ShiftedLimitIso

  cut : (n : ℕ) → Lim → F^ n
  cut n l = l .elements n

  cut-is-lim : ∀ n → (!^ n) ∘ cut (suc n) ≡ cut n
  cut-is-lim n = funExt λ l → l .is-lim n

  pres : F Lim → ShLim
  pres x .elements n = map (cut n) x
  pres x .is-lim n =
    map (!^ n) (map (cut (suc n)) x) ≡⟨ sym (map-comp (!^ n) (cut (suc n)) x) ⟩
    map (!^ n ∘ cut (suc n)) x       ≡⟨ cong (λ f → map f x) (cut-is-lim n) ⟩∎
    map (cut n) x ∎

  diag : (ℕ → Lim) → (n : ℕ) → F^ n
  diag ys n = cut n (ys n)

  diag-islim-alternating :
      (x : Lim)
    → (ys : ℕ → Lim)
    → (∀ n → cut n x ≡ diag ys n)
    → ∀ n → !^ n (cut (suc n) (ys n)) ≡ cut n (ys (suc n))
  diag-islim-alternating x ys q n =
    !^ n (cut (suc n) (ys n)) ≡⟨ ys n .is-lim n ⟩
    diag ys n                 ≡⟨ sym (q n) ⟩
    cut n x                   ≡⟨ sym (x .is-lim n) ⟩
    !^ n (cut (suc n) x)      ≡⟨ cong (!^ n) (q (suc n)) ⟩
    !^ n (diag ys (suc n))    ≡⟨ ys (suc n) .is-lim n ⟩
    cut n (ys (suc n)) ∎

isLimitPreserving : ∀ {ℓ} (F : Type ℓ → Type ℓ) → {{ Functor F }} → Type ℓ
isLimitPreserving F = isEquiv (pres F)

module Fixpoint {ℓ} {F : Type ℓ → Type ℓ} {{FunctorF : Functor F}} (is-lim-pres : isLimitPreserving F) where
  open Functor FunctorF

  pres⁻ : ShLim F → F (Lim F)
  pres⁻ = invIsEq is-lim-pres

  fix : F (Lim F) ≃ Lim F
  fix = (pres F , is-lim-pres) ∙ₑ ShLim≃Lim F

  fix⁺ : F (Lim F) → Lim F
  fix⁺ = equivFun fix

  fix⁺≡ShLim→Lim∘pres : fix⁺ ≡ ShLim→Lim F ∘ pres F
  fix⁺≡ShLim→Lim∘pres = refl

  fix⁻ : Lim F → F (Lim F)
  fix⁻ = invEq fix

  fix⁻≡pres⁻∘Lim→ShLim : fix⁻ ≡ pres⁻ ∘ Lim→ShLim F
  fix⁻≡pres⁻∘Lim→ShLim = refl

  fix⁺-step' : ∀ n x → map (cut F n) x ≡ cut F (suc n) (fix⁺ x)
  fix⁺-step' n x =
    map (cut _ n) x ≡⟨ cong-map (funExt⁻ (sym $ cut-is-lim F n)) x ⟩
    map (F map-!^ n ∘ (cut F (suc n))) x ≡⟨ map-comp _ _ x ⟩
    map (F map-!^ n) (map (cut F (suc n)) x) ≡⟨⟩
    map (F map-!^ n) (pres F x .Limit.elements (suc n)) ≡⟨⟩
    (F map-!^ (suc n)) (pres F x .Limit.elements (suc n)) ≡⟨⟩
    cut F (suc n) (ShLim→Lim F (pres F x)) ≡⟨⟩
    cut F (suc n) (fix⁺ x) ∎

  fix⁺-step : ∀ n x → map (cut F n) x ≡ cut F (suc n) (fix⁺ x)
  fix⁺-step n x = cong-map (funExt⁻ (sym $ cut-is-lim F n)) x ∙ map-comp _ _ x

  -- private
  --   fix⁺-step-coh : ∀ n {x} → isProp (F ^ suc n) → fix⁺-step' n x ≡ fix⁺-step n x
  --   fix⁺-step-coh n {x} setF = {! setF _ _!}

  fix⁻-step : ∀ n x → map (cut F n) (fix⁻ x) ≡ cut F (suc n) x
  fix⁻-step n x =
    map (cut F n) (fix⁻ x)        ≡⟨ fix⁺-step n (fix⁻ x) ⟩
    cut F (suc n) (fix⁺ $ fix⁻ x) ≡⟨ cong (cut F (suc n)) (secEq fix x) ⟩∎
    cut F (suc n) x ∎

  fix⁺-step-ext : ∀ n → map (cut F n) ≡ cut F (suc n) ∘ fix⁺
  fix⁺-step-ext = funExt ∘ fix⁺-step

  fix⁻-step-ext : ∀ n → map (cut F n) ∘ fix⁻ ≡ cut F (suc n)
  fix⁻-step-ext = funExt ∘ fix⁻-step

open Fixpoint public
  using (fix ; fix⁺)
