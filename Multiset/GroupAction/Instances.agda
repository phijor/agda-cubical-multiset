module Multiset.GroupAction.Instances where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Data.Unit renaming (Unit to UnitType)
open import Cubical.Algebra.Group.Base
open import Cubical.Algebra.Group.Instances.Unit
open import Cubical.Foundations.Isomorphism renaming (Iso to _≅_)

open import Multiset.GroupAction.Base

module Trivial {ℓG : Level} (G : Group ℓG) {ℓS : Level} (S : Type ℓS) where

  TrivialAction : GroupAction G ℓS
  TrivialAction =
    ( S
    , groupactionstr (λ _ s → s) (isgroupaction (λ _ → refl) (λ _ _ _ → refl)) 
    )

module Symmetric {ℓS : Level} (S : Type ℓS) (≅-isSet : isSet (S ≅ S)) where

  open import Cubical.Algebra.Monoid.Base
  open import Cubical.Algebra.Semigroup.Base
  open import Cubical.Algebra.Group.Properties

  circIso : (S ≅ S) → (S ≅ S) → (S ≅ S)
  circIso f g = compIso g f

  Sym : Group ℓS
  Sym = (S ≅ S) , groupstr idIso circIso invIso sym-isgroup
    where
      sym-issemigroup : IsSemigroup circIso
      sym-issemigroup = issemigroup ≅-isSet λ f g h → {!   !}

      sym-ismonoid : IsMonoid idIso circIso
      sym-ismonoid = ismonoid sym-issemigroup {!   !}

      sym-isgroup : IsGroup idIso circIso invIso
      sym-isgroup = isgroup sym-ismonoid {!   !}
  
  SymmetricAction : GroupAction Sym ℓS
  SymmetricAction = S , (groupactionstr (λ f s → f .fun s) (isgroupaction (λ s → refl) λ f g s → refl))
    where
      open _≅_
