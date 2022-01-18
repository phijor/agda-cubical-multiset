module Multiset.GroupAction.Induced where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Structure
open import Cubical.Data.Empty renaming (rec to ex-falso)
open import Cubical.Algebra.Group

open import Multiset.GroupAction.Base

private
  variable
    ℓG ℓS : Level

module Opposite (G : Group ℓG) where

  private
    open module G = GroupStr (str G)

  _·'_ : ⟨ G ⟩ → ⟨ G ⟩ → ⟨ G ⟩
  g ·' h = h · g

  ·'-assoc : (g h k : ⟨ G ⟩) → g ·' (h ·' k) ≡ (g ·' h) ·' k
  ·'-assoc g h k = sym (G.assoc k h g)
  
  open import Cubical.Algebra.Monoid.Base
  open import Cubical.Algebra.Semigroup.Base
  open import Cubical.Algebra.Group.Properties

  OppositeGroup : Group ℓG
  OppositeGroup = ⟨ G ⟩ , (groupstr 1g _·'_ G.inv op-isgroup)
    where
      op-issemigroup : IsSemigroup _·'_
      op-issemigroup = issemigroup G.is-set ·'-assoc

      op-ismonoid : IsMonoid 1g _·'_
      op-ismonoid = ismonoid op-issemigroup λ g → (G.lid g) , (G.rid g)

      op-isgroup : IsGroup 1g _·'_ G.inv
      op-isgroup = isgroup op-ismonoid (λ g → (G.invl g) , (G.invr g))


module Induced {G : Group ℓG} (S : GroupAction G ℓS) where

  private
    open module S = GroupActionStr (str S)
    open module G = GroupStr (str G)
    open module OppositeG = Opposite G renaming (OppositeGroup to Gᵒᵖ)
    open module GT = GroupTheory G

  Induced : {ℓX : Level} (X : Type ℓX) → GroupAction Gᵒᵖ (ℓ-max ℓS ℓX)
  Induced {ℓX} X =
    ( (⟨ S ⟩ → X)
    , groupactionstr
      (λ g f s → f (g ▸ s))
      (isgroupaction
        (λ f → funExt (λ s → cong f (S.act-1g s)))
        λ g h f → funExt (λ s → cong f (S.act-distmul h g s))
      )
    )

  act-inv-1g : ∀ s → inv 1g ▸ s ≡ s
  act-inv-1g s =
    ( inv 1g ▸ s ≡⟨ cong (_▸ s) inv1g ⟩
      1g ▸ s     ≡⟨ act-1g s ⟩
      s ∎
    )

  act-inv-distmul : ∀ g h s → inv h ▸ (inv g ▸ s) ≡ inv (g · h) ▸ s
  act-inv-distmul g h s =
    ( inv h ▸ (inv g ▸ s) ≡⟨ act-distmul _ _ _ ⟩
      (inv h · inv g) ▸ s  ≡⟨ cong (_▸ s) (sym (invDistr _ _)) ⟩
      inv (g · h) ▸ s ∎
    )

  InducedInv : {ℓX : Level} (X : Type ℓX) → GroupAction G (ℓ-max ℓS ℓX)
  InducedInv X =
    ( (⟨ S ⟩ → X)
    , ( groupactionstr
        (λ g f s → f (inv g ▸ s))
        (isgroupaction
          (λ f → funExt (λ s → cong f (act-inv-1g s)))
          λ g h f → funExt (λ s →  cong f (act-inv-distmul g h s))
        )
      )
    )
