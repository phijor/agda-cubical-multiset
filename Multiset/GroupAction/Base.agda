module Multiset.GroupAction.Base where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Structure
open import Cubical.Data.Nat.Base hiding (_·_)
open import Cubical.Data.Fin.Base
open import Cubical.Algebra.Group.Base
open import Cubical.Reflection.RecordEquiv

private
  variable
    ℓG ℓS : Level

record IsGroupAction
  (G : Group ℓG)
  {S : Type ℓS} (_▸_ : ⟨ G ⟩ → S → S) : Type (ℓ-max ℓG ℓS) where

  constructor isgroupaction

  open GroupStr (str G) using (_·_; 1g)

  field
    act-1g : ∀ s → 1g ▸ s ≡ s
    act-distmul : ∀ g h (s : S) → g ▸ (h ▸ s) ≡ (g · h) ▸ s

unquoteDecl IsGroupActionIsoΣ = declareRecordIsoΣ IsGroupActionIsoΣ (quote IsGroupAction)

record GroupActionStr (G : Group ℓG) (S : Type ℓS) : Type (ℓ-max ℓG ℓS) where

  constructor groupactionstr

  field
    _▸_ : ⟨ G ⟩ → S → S
    isGroupAction : IsGroupAction G _▸_

  infixr 9 _▸_

  open IsGroupAction isGroupAction public

GroupAction : (G : Group ℓG) → ∀ ℓS → Type (ℓ-max ℓG (ℓ-suc ℓS))
GroupAction G ℓS = TypeWithStr ℓS (GroupActionStr G)

GroupActionOn : (S : Type ℓS) → ∀ ℓG → Type (ℓ-max ℓS (ℓ-suc ℓG))
GroupActionOn S ℓG = Σ[ G ∈ Group ℓG ] GroupActionStr G S

groupActionOnToAction : {S : Type ℓS} → (P : GroupActionOn S ℓG) → GroupAction (P .fst) ℓS
groupActionOnToAction {S = S} P = S , P .snd

PermutationAction : (n : ℕ) → ∀ ℓG → Type (ℓ-suc ℓG)
PermutationAction n = GroupActionOn (Fin n)

permutationActionToAction : {n : ℕ} → (P : PermutationAction n ℓG) → GroupAction (P .fst) ℓ-zero
permutationActionToAction {n = n} = groupActionOnToAction

module _ {G : Group ℓG} {ℓT : Level} (S : GroupAction G ℓS) (T : GroupAction G ℓT) where
  private
    open module S = GroupActionStr (str S)
    open module T = GroupActionStr (str T)

  isEquivariant : (f : ⟨ S ⟩ → ⟨ T ⟩) → Type (ℓ-max ℓG (ℓ-max ℓS ℓT))
  isEquivariant f = ∀ g s → f (g S.▸ s) ≡ g T.▸ (f s)

  EquivariantMap : Type (ℓ-max ℓG (ℓ-max ℓS ℓT))
  EquivariantMap = Σ[ f ∈ (⟨ S ⟩ → ⟨ T ⟩) ] isEquivariant f

-- Notes:
-- Type of all permutations of a type: T ≃ T
-- Type of all permutations of `k` elements: Sym (Fin k) := (Fin k) ≃ (Fin k)
-- To get only proper subgroups of Sym (Fin k), consider *faithful* group actions
