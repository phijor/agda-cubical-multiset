module Multiset.GroupAction.Instances where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Structure
open import Cubical.Foundations.HLevels using (hSet)
open import Cubical.Data.Nat using (ℕ)
open import Cubical.Data.Fin using (Fin)
open import Cubical.Algebra.Group.Base
open import Cubical.Algebra.Group.Instances.Unit
open import Cubical.Algebra.SymmetricGroup

open import Multiset.GroupAction.Base

--- The trivial action of a group G on an arbitrary Type S.
--- Each element of G acts by the identity.
module Trivial {ℓG : Level} (G : Group ℓG) {ℓS : Level} (S : Type ℓS) where

  TrivialActionStr : GroupActionStr G S
  TrivialActionStr = groupactionstr (λ _ s → s) (isgroupaction (λ _ → refl) (λ _ _ _ → refl))

  TrivialAction : GroupAction G ℓS
  TrivialAction = (S ,  TrivialActionStr)

--- The unit action:
---
--- The 1-element group (Unit) acts by identity on each element of S.
--- contravariant.
module Unit {ℓS : Level} (S : Type ℓS) where
  
  UnitActionStr : GroupActionStr Unit S
  UnitActionStr = TrivialUnit.TrivialActionStr
    where
      module TrivialUnit = Trivial Unit S

  UnitAction : GroupAction Unit ℓS
  UnitAction = S , UnitActionStr

--- The symmetric action:
--- 
--- The symmetric group of self-equivalences of a *set* S (i.e. S ≃ S)
--- acts by inverse function application:
---
---   _ ▸ _ : S ≃ S × S → S
---   σ ▸ s ↦ σ⁻¹(s)
---
--- Note that the inverse is necessary since composition of equivalences
--- is defined covariantly (diagramatically), but function application is
module Symmetric {ℓS : Level} (S : hSet ℓS) where
  open import Cubical.Foundations.Equiv
  
  SymmetricGroup : Group _
  SymmetricGroup = Symmetric-Group (⟨ S ⟩) (str S)

  -- SymmetricActionStr : GroupActionStr (SymmetricGroup )

  SymmetricAction : GroupAction SymmetricGroup ℓS
  SymmetricAction = ⟨ S ⟩ , groupactionstr (λ σ s → equivFun (invEquiv σ) s) (isgroupaction (λ s → refl) (λ g h s → refl))


--- The symmetric action on a finite set.
--- This is a specialization of the symmetric action of a general type.
module Sym (n : ℕ) where
  open import Cubical.Data.Fin using (isSetFin)
  open import Cubical.Foundations.Structure

  SymAction : GroupAction (Sym n) ℓ-zero
  SymAction = Symmetric.SymmetricAction (Fin n , isSetFin)

  SymActionStr : GroupActionStr (Sym n) (Fin n)
  SymActionStr = str SymAction


--- Actions on finite sets, specialized to `PermutationAction`s.
module FinPermutation (n : ℕ) where

  UnitPermAction : PermutationAction n _
  UnitPermAction = Unit , Unit.UnitActionStr (Fin n)

  SymPermAction : PermutationAction n _
  SymPermAction = (Sym n) , Sym.SymActionStr n
