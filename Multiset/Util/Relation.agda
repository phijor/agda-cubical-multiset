{-# OPTIONS --safe #-}

module Multiset.Util.Relation where

open import Multiset.Prelude

open import Cubical.Foundations.Function using (idfun ; _∘_)
open import Cubical.Foundations.Isomorphism
open import Cubical.Data.Unit.Base using (Unit* ; tt*)
open import Cubical.Data.Unit.Properties using (isPropUnit* ; isOfHLevelUnit*)
open import Cubical.Relation.Binary.Base using (Rel ; module BinaryRelation)

Tot : ∀ {ℓ} → (A : Type ℓ) → (ℓR : Level) → Rel A A ℓR
Tot A _ = λ _ _ → Unit*

module _ {ℓ} {A : Type ℓ} {ℓR} where
  open BinaryRelation (Tot A ℓR)
  isPropTot : ∀ a b → isProp (Tot A ℓR a b)
  isPropTot a b = isPropUnit*

  isReflTot : isRefl
  isReflTot _ = tt*

  isSymTot : isSym
  isSymTot _ _ tt* = tt*

  isTransTot : isTrans
  isTransTot _ _ _ tt* tt* = tt*

private
  variable
    ℓA ℓB ℓC ℓR ℓS ℓT : Level
    A : Type ℓA
    B : Type ℓB
    C : Type ℓC

module _ (R : Rel A A ℓR) (S : Rel B B ℓS) where
  PreservesRel : (f : A → B) → Type _
  PreservesRel f = ∀ {a a'} → R a a' → S (f a) (f a')

  ReflectsRel : (f : A → B) → Type _
  ReflectsRel f = ∀ {a a'} → S (f a) (f a') → R a a'

ReflectsRelComp : ∀ (R : Rel A A ℓR) (S : Rel B B ℓS) (T : Rel C C ℓT) {f : A → B} {g : B → C} → ReflectsRel R S f → ReflectsRel S T g → ReflectsRel R T (g ∘ f)
ReflectsRelComp _ _ _ f-reflects g-reflects = f-reflects ∘ g-reflects


module _ (R : Rel A A ℓR) (S : Rel B B ℓS) where
  ReflectsRel→SectionPreservesRel : (f : A → B) (g : B → A) → (section f g) → ReflectsRel R S f → PreservesRel S R g
  ReflectsRel→SectionPreservesRel f g sect f-preserves {b} {b'} bSb' = f-preserves (subst (λ (· : B → B) → S (· b) (· b')) sect-ext bSb') where
    sect-ext : idfun B ≡ f ∘ g
    sect-ext = funExt (sym ∘ sect)

  -- fix⁻-pres-bisim : ∀ {s t : Tree} → Bisim s t → Relator Bisim (fix⁻ s) (fix⁻ t)
  PreservesRel→SectionReflectsRel : (f : A → B) (g : B → A) → section f g → PreservesRel R S f → ReflectsRel S R g
  PreservesRel→SectionReflectsRel f g sect preserves {b} {b'} bSb' = reflects where
    step₁ : S (f (g b)) (f (g b'))
    step₁ = preserves bSb'

    reflects : S b b'
    reflects = subst (λ (· : B → B) → S (· b) (· b')) (funExt sect) step₁

  -- PreservesRel→FooPreservesRel : (f : A → B) (g : B → A) → section f g → PreservesRel R S f → PreservesRel S R g
  -- PreservesRel→FooPreservesRel f g sect preserves {b} {b'} bSb' = {! preserves!} where

module _ {ℓA ℓB ℓR ℓS} {A : Type ℓA} {B : Type ℓB}
  (R : Rel A A ℓR) (S : Rel B B ℓS)
  (propR : ∀ {a a'} → isProp (R a a'))
  (propS : ∀ {b b'} → isProp (S b b'))
  (e : Iso A B)
  where
  open Iso

  Rel-pres-reflects-Iso :
      (∀ a a' → Iso (R a a') (S (e .fun a) (e .fun a')))
    → (∀ b b' → Iso (S b b') (R (e .inv b) (e .inv b')))
  Rel-pres-reflects-Iso p b b' .fun bSb' = p (e .inv b) (e .inv b') .inv (subst (λ · → S (· b) (· b')) (sym (funExt (e .rightInv))) bSb')
  Rel-pres-reflects-Iso p b b' .inv aRa' = subst (λ (· : B → B) → S (· b) (· b')) (funExt (e .rightInv)) (p _ _ .fun aRa')
  Rel-pres-reflects-Iso p b b' .rightInv _ = propR _ _
  Rel-pres-reflects-Iso p b b' .leftInv _ = propS _ _

