{-# OPTIONS --safe --hidden-argument-puns #-}

module Multiset.Util.SetQuotients where

open import Multiset.Prelude

open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Equiv.Properties
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Function using (_∘_)
open import Cubical.Foundations.Structure
open import Cubical.Foundations.Function
open import Cubical.Functions.Embedding
open import Cubical.Functions.Surjection

open import Cubical.Data.Sigma
open import Cubical.HITs.SetQuotients as SQ using (_/_ ; [_] ; eq/)
open import Cubical.HITs.SetTruncation as ST using ()
open import Cubical.HITs.PropositionalTruncation as PT using (∥_∥₁)
open import Cubical.HITs.PropositionalTruncation.Monad using (_>>=_ ; return)

private
  variable
    ℓ ℓ' ℓ'' : Level
    A B C : Type ℓ
    R S : A → A → Type ℓ

open Iso

map : (f : A → B) (pres : ∀ {a a'} → R a a' → S (f a) (f a')) → A / R → B / S
map f pres = SQ.rec SQ.squash/ ([_] ∘ f) λ a a' p → eq/ _ _ (pres p)

module _
  (isoA : Iso A B)
  (presS : ∀ {a a'} → R a a' → S (isoA .fun a) (isoA .fun a'))
  (presR : ∀ {b b'} → S b b' → R (isoA .inv b) (isoA .inv b'))
  where
  relBiimpl→QuotIso : Iso (A / R) (B / S)
  relBiimpl→QuotIso .fun = map (isoA .fun) presS
  relBiimpl→QuotIso .inv = map (isoA .inv) presR
  relBiimpl→QuotIso .rightInv = SQ.elimProp (λ _ → _/_.squash/ _ _) λ a → cong [_] (isoA .rightInv a)
  relBiimpl→QuotIso .leftInv = SQ.elimProp (λ _ → _/_.squash/ _ _) λ b → cong [_] (isoA .leftInv b)

module Coimage (is-set-A : isSet A) (is-set-B : isSet B) (f : A → B) where
  _∼_ : A → A → Type _
  _∼_ x y = (f x ≡ f y)

  isProp-∼ : (x y : A) → isProp (x ∼ y)
  isProp-∼ x y = is-set-B (f x) (f y)

  Coimage : Type _
  Coimage = A / _∼_

  coim : A → Coimage
  coim = [_]

  cores : Coimage → B
  cores = SQ.rec is-set-B f (λ a b r → r)

  coim-β : f ≡ cores ∘ coim
  coim-β = refl

  cores-fiber-map : ∀ b → fiber f b → fiber cores b
  cores-fiber-map b (a , p) = coim a , p

  cores-inj : (c d : Coimage) → cores c ≡ cores d → c ≡ d
  cores-inj = SQ.elimProp2 (λ c d → isProp→ (SQ.squash/ c d)) SQ.eq/

  isEmbedding-cores : isEmbedding cores
  isEmbedding-cores = injEmbedding is-set-B (cores-inj _ _)

  module isSurjection (is-surj-f : isSurjection f) where
    isSurjection-cores : isSurjection cores
    isSurjection-cores b = PT.map (cores-fiber-map b) (is-surj-f b)

    isEquiv-cores : isEquiv cores
    isEquiv-cores = isEmbedding×isSurjection→isEquiv (isEmbedding-cores , isSurjection-cores)

    coresEquiv : Coimage ≃ B
    coresEquiv .fst = cores
    coresEquiv .snd = isEquiv-cores

    coim-β⁻¹ : coim ≡ invEq coresEquiv ∘ f
    coim-β⁻¹ = funExt λ a → invEq (equivAdjointEquiv coresEquiv) (sym (coim-β ≡$ a))

  cores⁻¹ : isSurjection f → B → Coimage
  cores⁻¹ is-surj-f b = PT.rec→Set SQ.squash/ cores* 2-const-cores* (is-surj-f b) where
    coresΣ : fiber f b → fiber cores b
    coresΣ (a , p) = [ a ] , p

    cores* : fiber f b → Coimage
    cores* (a , _) = [ a ]

    2-const-cores* : 2-Constant cores*
    2-const-cores* (a , p) (a′ , p′) = SQ.eq/ a a′ (p ∙ sym p′)

  coim-surj : isSurjection coim
  coim-surj = SQ.elimProp (λ _ → PT.isPropPropTrunc) coim-surj* where
    coim-surj* : (a : A) → ∥ fiber coim (coim a) ∥₁
    coim-surj* a = PT.∣ a , refl ∣₁

private
  hasSectionPostCompEquiv : (f : A → B) → (e : B ≃ C)
    → hasSection (equivFun e ∘ f)
    → hasSection f
  hasSectionPostCompEquiv {A} {B} {C} f e*@(e , _) (g , sec) = f⁻¹ , f⁻¹-sec where
    f⁻¹ : B → A
    f⁻¹ = g ∘ e

    f⁻¹-sec : section f f⁻¹
    f⁻¹-sec b = invEq (congEquiv e*) lemma where
      lemma : e (f (g (e b))) ≡ e b
      lemma = sec (e b)

hasSection-[]→AxiomOfChoice : (ℓ : Level)
  → ((A : hSet ℓ) (R : ⟨ A ⟩ → ⟨ A ⟩ → Type ℓ) → ∃[ rep ∈ (⟨ A ⟩ / R → ⟨ A ⟩) ] section [_] rep)
  → ((A B : hSet ℓ) (f : ⟨ A ⟩ → ⟨ B ⟩) → isSurjection f → ∃[ g ∈ (⟨ B ⟩ → ⟨ A ⟩) ] section f g)
hasSection-[]→AxiomOfChoice ℓ [-]-section A B f is-surj-f = PT.map goal ([-]-section A _∼_)
  where
    open Coimage (str A) (str B) f

    coim-equiv : Coimage ≃ ⟨ B ⟩
    coim-equiv = isSurjection.coresEquiv is-surj-f

    module _ ([-]-section : hasSection {B = Coimage} [_]) where
      lemma : hasSection (invEq coim-equiv ∘ f)
      lemma = subst {x = [_]} {y = invEq coim-equiv ∘ f} hasSection (isSurjection.coim-β⁻¹ is-surj-f) [-]-section

      goal : hasSection f
      goal = hasSectionPostCompEquiv f (invEquiv coim-equiv) lemma
