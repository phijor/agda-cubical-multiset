module Multiset.GroupAction.Instances where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Data.Unit renaming (Unit to UnitType)
open import Cubical.Algebra.Group.Base
open import Cubical.Algebra.Group.Instances.Unit
open import Cubical.Foundations.Isomorphism renaming (Iso to _≅_)

open import Multiset.GroupAction.Base

module Trivial {ℓG : Level} (G : Group ℓG) {ℓS : Level} (S : Type ℓS) where

  TrivialActionStr : GroupActionStr G S
  TrivialActionStr = groupactionstr (λ _ s → s) (isgroupaction (λ _ → refl) (λ _ _ _ → refl))

  TrivialAction : GroupAction G ℓS
  TrivialAction = (S ,  TrivialActionStr)

UnitActionStr : {ℓS : Level} (S : Type ℓS) → GroupActionStr Unit S
UnitActionStr S = TrivialUnit.TrivialActionStr
  where
    module TrivialUnit = Trivial Unit S

UnitAction : {ℓS : Level} (S : Type ℓS) → GroupAction Unit ℓS
UnitAction S = S , (UnitActionStr S)

module Symmetric {ℓS : Level} (S : Type ℓS) (≅-isSet : isSet (S ≅ S)) where

  open import Multiset.Group.Symmetric

  open module Symmetric = Sym S ≅-isSet
  
  SymmetricAction : GroupAction Sym ℓS
  SymmetricAction = S , (groupactionstr (λ f s → f .fun s) (isgroupaction (λ s → refl) λ f g s → refl))
    where
      open _≅_
