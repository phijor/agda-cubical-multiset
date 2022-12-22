{-# OPTIONS --safe #-}

module Multiset.Coalgebra where

open import Multiset.Prelude
open import Multiset.Functor

open import Cubical.Foundations.Function using (idfun ; _∘_)
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism

private
  variable
    ℓ : Level

module _ {ℓ} (F : Type ℓ → Type ℓ) {{FunctorF : Functor F}} where
  open Functor FunctorF
    renaming (map to F[_])

  isCoalgebraMorphism : ∀ {A B} → (α : A → F A) → (β : B → F B) → (f : A → B) → Type _
  isCoalgebraMorphism α β f = β ∘ f ≡ F[ f ] ∘ α

  isSet→isPropIsCoalgebraMorphism : ∀ {A B}
    → (α : A → F A) → (β : B → F B) → (f : A → B)
    → isSet (F B) → isProp (isCoalgebraMorphism α β f)
  isSet→isPropIsCoalgebraMorphism {A} {B} α β f setF = setA→FB (β ∘ f) (F[ f ] ∘ α) where
    setA→FB : isSet (A → F B)
    setA→FB = isSet→ setF

  CoalgebraMorphism : ∀ {A B} → (α : A → F A) → (β : B → F B) → Type _
  CoalgebraMorphism α β = Σ[ f ∈ (_ → _) ] isCoalgebraMorphism α β f

  isTerminal : ∀ {νF} (out : νF → F νF) → Type _
  isTerminal out = ∀ {B} → (β : B → F B) → isContr (CoalgebraMorphism β out)

  module _ {νF} {out : νF → F νF} (is-terminal : isTerminal out) where
    ana : ∀ {B} → (β : B → F B) → CoalgebraMorphism β out
    ana β = is-terminal β .fst

    anaEq : ∀ {B} {β : B → F B} → (f : CoalgebraMorphism β out) → ana β ≡ f
    anaEq {β = β} f = is-terminal β .snd f
