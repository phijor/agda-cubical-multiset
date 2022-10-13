{-# OPTIONS --safe #-}

module Multiset.Util.Trace where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Isomorphism
  renaming (Iso to _≅_)
open import Cubical.Foundations.Function
  using (const)
open import Cubical.Foundations.Path
  using (flipSquare)

open import Cubical.Data.Nat
open import Cubical.Data.Sigma
  renaming
    ( fst to step
    ; snd to connect
    ) public


private
  variable
    ℓ : Level
    A : Type ℓ

Trace : Type ℓ → Type ℓ
Trace A = Σ[ as ∈ (ℕ → A) ] (∀ n → as n ≡ as (suc n))

constTrace : A → Trace A
constTrace a = const a , const refl

module _ (trace : Trace A) where
  as = trace .step
  is-link = trace .connect

  to0 : ∀ n → as 0 ≡ as n
  to0 0 = refl
  to0 (suc n) = to0 n ∙ is-link n

  constTraceConnectSquare : ∀ n → PathP (λ i → to0 n i ≡ (to0 n ∙ is-link n) i) refl (is-link n)
  constTraceConnectSquare n = flipSquare filler where
    filler : PathP (λ j → as 0 ≡ is-link n j) (to0 n) (to0 n ∙ is-link n)
    filler = compPath-filler (to0 n) (is-link n)

  constTracePath : constTrace (as 0) ≡ (as , is-link)
  constTracePath = ΣPathP (funExt to0 , funExt constTraceConnectSquare)

start : Trace A → A
start trace = trace .step 0

open _≅_
TraceIso : Trace A ≅ A
TraceIso .fun = start
TraceIso .inv = constTrace
TraceIso .leftInv = constTracePath
TraceIso .rightInv a = refl
