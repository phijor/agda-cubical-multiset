module Multiset.GroupAction.Orbit where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Structure
open import Cubical.Algebra.Group.Base
open import Cubical.HITs.TypeQuotients.Base renaming (_/ₜ_ to _/_)

open import Multiset.GroupAction.Base
open import Multiset.GroupAction.Properties

private
  variable
    ℓG ℓS : Level
    
module _ (G : Group ℓG) (S : GroupAction G ℓS) where

  private
    open import Cubical.Relation.Binary.Base

    open module S = GroupActionStr (str S)
    open module G = GroupStr (str G)
    open module GAT = GroupActionTheory G S

  _∼_ : (s t : ⟨ S ⟩) → Type (ℓ-max ℓG ℓS)
  s ∼ t = Σ[ g ∈ ⟨ G ⟩ ] g ▸ s ≡ t

  isTransitive : Type (ℓ-max ℓG ℓS)
  isTransitive = (s t : ⟨ S ⟩) → s ∼ t

  open module ∼-Rel = BinaryRelation _∼_

  ∼-refl : isRefl
  ∼-refl s = 1g , S.act-1g s

  ∼-sym : isSym
  ∼-sym s t (g , g▸s≡t) =
    ( inv g
    , ( inv g ▸ t ≡⟨ cong (inv g ▸_) (sym g▸s≡t) ⟩
        inv g ▸ g ▸ s ≡⟨ act-invl _ _ ⟩
        s ∎
      )
    )

  ∼-trans : isTrans
  ∼-trans s t u (g , g▸s≡t) (h , h▸t≡u) =
    ( (h · g)
    , (
        (h · g) ▸ s ≡⟨ sym (act-distmul _ _ _) ⟩
        h ▸ g ▸ s ≡⟨ cong (h ▸_) g▸s≡t ⟩
        h ▸ t ≡⟨ h▸t≡u ⟩
        u ∎
      )
    )

  ∼-isEquivRel : isEquivRel
  ∼-isEquivRel = BinaryRelation.equivRel ∼-refl ∼-sym ∼-trans

  Orbit : Type (ℓ-max ℓG ℓS)
  Orbit = ⟨ S ⟩ / _∼_

  orbit : ⟨ S ⟩ → Orbit
  orbit s = [ s ]

map : {ℓS ℓT : Level} {G : Group ℓG} {S : GroupAction G ℓS} {T : GroupAction G ℓT}
  (f : EquivariantMap S T) → Orbit G S → Orbit G T
map f [ s ] = [ f .fst s ]
map {S = S} {T = T} (f , isEquivariant-f) (eq/ s₀ s₁ (g , g▸s₀≡s₁) i) = well-defined i
  where
    open module T = GroupActionStr (str T)
    open module S = GroupActionStr (str S)

    well-defined : [ f s₀ ] ≡ [ f s₁ ]
    well-defined = eq/ _ _
      ( g
      , ( g T.▸ (f s₀)
        ≡⟨ sym (isEquivariant-f g s₀) ⟩
          (f (g S.▸ s₀))
        ≡⟨ cong f g▸s₀≡s₁ ⟩ f s₁ ∎
        )
      )
