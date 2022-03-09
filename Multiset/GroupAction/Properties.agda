module Multiset.GroupAction.Properties where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Structure
open import Cubical.Data.Nat.Base hiding (_·_)
open import Cubical.Algebra.Group.Base

open import Multiset.GroupAction.Base

private
  variable
    ℓG ℓS : Level

module GroupActionTheory (G : Group ℓG) (S : GroupAction G ℓS) where

  private
    open module S = GroupActionStr (str S)
    open module G = GroupStr (str G)

  act-invl : ∀ g s → inv g ▸ g ▸ s ≡ s
  act-invl g s =
    ( inv g ▸ g ▸ s ≡⟨ act-distmul _ _ _ ⟩
      (inv g · g) ▸ s ≡⟨ cong (_▸ s) (G.invl _) ⟩
      1g ▸ s ≡⟨ act-1g _ ⟩
      s ∎
    )

  act-invr : ∀ g s → g ▸ inv g ▸ s ≡ s
  act-invr g s =
    ( g ▸ inv g ▸ s ≡⟨ act-distmul _ _ _ ⟩
      (g · inv g) ▸ s ≡⟨ cong (_▸ s) (G.invr _) ⟩
      1g ▸ s ≡⟨ act-1g _ ⟩
      s ∎
    )

  act-at : (g : ⟨ G ⟩) → ⟨ S ⟩ → ⟨ S ⟩
  act-at g = g ▸_

  actionAtIsIso : (g : ⟨ G ⟩) → isIso (g ▸_)
  actionAtIsIso g =
    ( ((inv g) ▸_)
    -- section
    , (act-invr g)
    -- retract
    , (act-invl g)
    )

  --- A group action is faithful if the homormorphism G → Sym(S)
  --- given by (λ g → g ▸_) has trivial kernel.
  isFaithful' : Type (ℓ-max ℓG ℓS)
  isFaithful' = (g : ⟨ G ⟩) → (act-at g) ≡ (λ s → s) → g ≡ 1g

  isFaithful : Type (ℓ-max ℓG ℓS)
  isFaithful = (g h : ⟨ G ⟩) → (act-at g) ≡ (act-at h) → g ≡ h

  isFree : Type (ℓ-max ℓG ℓS)
  isFree = (g h : ⟨ G ⟩) → (s : ⟨ S ⟩) → g ▸ s ≡ h ▸ s → g ≡ h
