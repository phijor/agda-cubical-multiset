{-# OPTIONS --safe #-}

module Multiset.Relation.Category where

open import Multiset.Prelude
open import Multiset.Relation.Base

open import Cubical.Categories.Category
open import Cubical.Categories.Functor

module _ ℓ ℓR where
  private
    ℓ-ob = ℓ-suc (ℓ-max ℓ ℓR)
    ℓ-hom = ℓ-max ℓ ℓR

  RelationCategory : Category ℓ-ob ℓ-hom
  RelationCategory .Category.ob = Relation ℓ ℓR
  RelationCategory .Category.Hom[_,_] = Rel[_⇒_]
  RelationCategory .Category.id = idRel⇒
  RelationCategory .Category._⋆_ = _⋆Rel⇒_
  RelationCategory .Category.⋆IdL = ⋆Rel⇒IdL
  RelationCategory .Category.⋆IdR = ⋆Rel⇒IdR
  RelationCategory .Category.⋆Assoc = ⋆Rel⇒Assoc
  RelationCategory .Category.isSetHom = isSetRel⇒ _ _

  RelationEndo : Type _
  RelationEndo = Functor RelationCategory RelationCategory
