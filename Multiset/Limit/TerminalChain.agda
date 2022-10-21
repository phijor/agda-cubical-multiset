{-# OPTIONS --safe #-}

module Multiset.Limit.TerminalChain where

open import Multiset.Prelude
open import Multiset.Util using (!_)
open import Multiset.Util.Square using (kiteFiller)
open import Multiset.Limit.Chain

open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Function
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism
open import Cubical.Data.Nat.Base hiding (_^_)

record Functor (F : Type → Type) : Type₁ where
  field
    map : ∀ {X Y : Type} → (X → Y) → (F X → F Y)
    map-id : ∀ {X} x → map (idfun X) x ≡ x
    map-comp : ∀ {X Y Z}
      → (g : Y → Z)
      → (f : X → Y)
      → ∀ x → map (g ∘ f) x ≡ map g (map f x)

module _ (F : Type → Type) {{ FunctorF : Functor F }} where
  open Chain
  open Limit
    using (elements ; is-lim)

  open Functor FunctorF using (map ; map-id ; map-comp)

  _^_ : ℕ → Type
  _^_ zero = Unit
  _^_ (suc n) = F (_^_ n)

  infixl 7 _^_

  private
    F^_ = _^_

  _map-!^_ : ∀ n → F^ suc n → F^ n
  _map-!^_ zero = !_
  _map-!^_ (suc n) = map (_map-!^_ n)

  private
    !^ : ∀ n → F^ suc n → F^ n
    !^ = _map-!^_

  ch : Chain ℓ-zero
  ch .Ob = _^_
  ch .π = _map-!^_

  sh = shift ch

  Lim = Limit ch
  ShLim = Limit sh

  isLim : (el : (n : ℕ) → F^ n) → Type
  isLim = isLimit ch

  isShLim : (el : (n : ℕ) → F^ suc n) → Type
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

isLimitPreserving' : (F : Type → Type) → {{ Functor F }} → Type
isLimitPreserving' F = isEquiv (pres F)

isLimitPreserving : (F : Type → Type) → {{ Functor F }} → Type
isLimitPreserving F = F (Lim F) ≃ ShLim F

fix : ∀ {F}
  → {{FunctorF : Functor F}}
  → isLimitPreserving F
  → F (Lim F) ≃ Lim F
fix {F = F} pres = pres ∙ₑ ShLim≃Lim F
