{-# OPTIONS --safe #-}

module Multiset.Setoid.Category where

open import Multiset.Prelude
open import Multiset.Setoid.Base as Setoid

open import Cubical.Foundations.Function using (_∘_)
open import Cubical.HITs.SetQuotients as SQ using (_/_)
open import Cubical.Categories.Category
open import Cubical.Categories.Functor
open import Cubical.Relation.Binary using (module BinaryRelation)

module _ ℓ ℓR where
  private
    ℓ-ob = ℓ-suc (ℓ-max ℓ ℓR)
    ℓ-hom = ℓ-max ℓ ℓR

  SetoidCategory : Category ℓ-ob ℓ-hom
  SetoidCategory .Category.ob = Setoid ℓ ℓR
  SetoidCategory .Category.Hom[_,_] = SetoidHom
  SetoidCategory .Category.id = SetoidIdHom
  SetoidCategory .Category._⋆_ = Setoid._⋆_
  SetoidCategory .Category.⋆IdL = Setoid.⋆IdL
  SetoidCategory .Category.⋆IdR = Setoid.⋆IdR
  SetoidCategory .Category.⋆Assoc = Setoid.⋆Assoc
  SetoidCategory .Category.isSetHom = Setoid.isSetSetoidHom
