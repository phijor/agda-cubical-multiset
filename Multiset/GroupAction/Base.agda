module Multiset.GroupAction.Base where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Structure
open import Cubical.Data.Nat hiding (_·_)
open import Cubical.Data.Nat.Order using (¬-<-zero; ≤-refl)
open import Cubical.Data.Nat.Properties using (+-suc)
open import Cubical.Data.Prod
open import Cubical.Data.Fin
open import Cubical.Data.Bool.Base renaming (Bool to BoolType; _⊕_ to xor)
open import Cubical.Data.Empty renaming (rec to ex-falso)
open import Cubical.Algebra.Group
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

PermutationAction : (k : ℕ) → ∀ ℓG → Type (ℓ-suc ℓG)
PermutationAction k ℓG = TypeWithStr ℓG (λ G → Σ[ Gs ∈ GroupStr G ] GroupActionStr (G , Gs) (Fin k))

-- Notes:
-- Type of all permutations of a type: T ≃ T
-- Type of all permutations of `k` elements: Sym (Fin k) := (Fin k) ≃ (Fin k)
-- To get only proper subgroups of Sym (Fin k), consider *faithful* group actions
