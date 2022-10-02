module Multiset.Chains.FunctorChain where

open import Multiset.Prelude
open import Multiset.Util using (!_)
open import Multiset.Util.Square using (kiteFiller)
open import Multiset.Chains

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
  open Limit.ChainLimit
    using (elements ; isChainLimit)

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

  Lim = Limit.ChainLimit ch
  ShLim = Limit.ChainLimit sh

  isLim : (el : (n : ℕ) → F^ n) → Type
  isLim = Limit.IsChainLimit ch

  isShLim : (el : (n : ℕ) → F^ suc n) → Type
  isShLim = Limit.IsChainLimit sh

  LimPathPExt = Limit.ChainLimitPathPExt ch
  ShLimPathPExt = Limit.ChainLimitPathPExt (shift ch)


  ShLim→Lim : ShLim → Lim
  ShLim→Lim sh .elements n = ch .π n (sh .elements n)
  ShLim→Lim sh .isChainLimit n = cong (ch .π n) (sh .isChainLimit n)

  Lim→ShLim : Lim → ShLim
  Lim→ShLim lim .elements = lim .elements ∘ suc
  Lim→ShLim lim .isChainLimit = lim .isChainLimit ∘ suc

  open Iso

  ShiftedLimitIso : Iso ShLim Lim
  ShiftedLimitIso .fun = ShLim→Lim
  ShiftedLimitIso .inv = Lim→ShLim
  ShiftedLimitIso .rightInv lim = LimPathPExt (lim .isChainLimit) λ n → kiteFiller
  ShiftedLimitIso .leftInv sh = ShLimPathPExt (sh .isChainLimit) λ n → kiteFiller

  ShLim≃Lim : ShLim ≃ Lim
  ShLim≃Lim = isoToEquiv ShiftedLimitIso

  isWidePullback : (x : F^ 1) → (el : (n : ℕ) → F^ suc n) → Type
  isWidePullback x el = ∀ n → map !_ (el n) ≡ x

  isOfHLevelHasTrace : ∀ {x₀} {el} {n}
    → isOfHLevel (suc n) (F^ 1)
    → isOfHLevel n (isWidePullback x₀ el)
  isOfHLevelHasTrace {x₀} {el} {n = n} lvl = isOfHLevelΠ n λ k → isOfHLevelPath' n lvl (map !_ (el k)) x₀

  isShLim→isWidePullback : (shlim : ShLim) → isWidePullback (shlim .elements 0) (shlim .elements)
  isShLim→isWidePullback shlim zero = map-id (shlim .elements 0)
  isShLim→isWidePullback shlim@(Limit.lim el islim) (suc n) =
    map (!_)             (el (suc n))  ≡⟨⟩
    map (!_ ∘ !^ n)      (el (suc n))  ≡⟨ #1 ⟩
    map (!_) (map (!^ n) (el (suc n))) ≡⟨ #2 ⟩
    map (!_) (el n)                    ≡⟨ #3 ⟩
    shlim .elements 0 ∎ where

    #1 = map-comp !_ (!^ n) (el (suc n))
    #2 = cong (map !_) (islim n)
    #3 = isShLim→isWidePullback shlim n


isLimitPreserving : (F : Type → Type) → {{ Functor F }} → Type
isLimitPreserving F = F (Lim F) ≃ ShLim F

fix : ∀ {F}
  → {{FunctorF : Functor F}}
  → isLimitPreserving F
  → F (Lim F) ≃ Lim F
fix {F = F} pres = pres ∙ₑ ShLim≃Lim F
