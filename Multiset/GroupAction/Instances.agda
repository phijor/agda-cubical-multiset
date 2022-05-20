module Multiset.GroupAction.Instances where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Structure
open import Cubical.Foundations.HLevels using (hSet)
open import Cubical.Foundations.Equiv using (equivFun ; invEquiv)
open import Cubical.Data.Nat.Base using (ℕ)
open import Cubical.Data.Fin.Base using (Fin)
open import Cubical.Data.Fin.Properties using (isSetFin)
open import Cubical.Algebra.Group.Base
open import Cubical.Algebra.Group.Instances.Unit
open import Cubical.Algebra.SymmetricGroup

open import Multiset.GroupAction.Base

private
  variable
    ℓS ℓG : Level

--- The trivial action of a group G on an arbitrary Type S.
--- Each element of G acts by the identity.
module _ (G : Group ℓG) (S : hSet ℓS) where

  TrivialActionStr : GroupActionStr G ⟨ S ⟩
  TrivialActionStr = groupactionstr (λ _ s → s) (isgroupaction (str S) (λ _ → refl) (λ _ _ _ → refl))

  TrivialAction : GroupAction G ℓS
  TrivialAction = (⟨ S ⟩ ,  TrivialActionStr)

--- The unit action:
---
--- The 1-element group (Unit) acts by identity on each element of S.
module _ (S : hSet ℓS) where

  UnitActionStr : GroupActionStr Unit ⟨ S ⟩
  UnitActionStr = TrivialActionStr Unit S

  UnitAction : GroupAction Unit ℓS
  UnitAction = ⟨ S ⟩ , UnitActionStr

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
--- contravariant.
module _ (S : hSet ℓS) where

  SymmetricGroup : Group ℓS
  SymmetricGroup = Symmetric-Group (⟨ S ⟩) (str S)

  -- SymmetricActionStr : GroupActionStr (SymmetricGroup )

  SymmetricAction : GroupAction SymmetricGroup ℓS
  SymmetricAction = ⟨ S ⟩ , groupactionstr (λ σ s → equivFun (invEquiv σ) s) (isgroupaction (str S) (λ s → refl) (λ g h s → refl))


--- The symmetric action on a finite set.
--- This is a specialization of the symmetric action of a general type.
module _ (n : ℕ) where

  SymAction : GroupAction (Sym n) ℓ-zero
  SymAction = SymmetricAction (Fin n , isSetFin)

  SymActionStr : GroupActionStr (Sym n) (Fin n)
  SymActionStr = str SymAction


--- Actions on finite sets, specialized to `PermutationAction`s.
module _ (n : ℕ) where
  -- TODO: This is insanely slow to typecheck.  Figure out why.

  UnitPermAction : PermutationAction n ℓ-zero
  UnitPermAction = Unit , UnitActionStr (Fin n , isSetFin)

  SymPermAction : PermutationAction n ℓ-zero
  SymPermAction = (Sym n) , SymActionStr n
