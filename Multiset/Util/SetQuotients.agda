{-# OPTIONS --safe #-}

module Multiset.Util.SetQuotients where

open import Multiset.Prelude

open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Function using (_∘_)

open import Cubical.HITs.SetQuotients as SQ using (_/_ ; [_] ; eq/)

private
  variable
    ℓ ℓ' ℓ'' : Level
    A B : Type ℓ
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

