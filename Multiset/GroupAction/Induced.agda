module Multiset.GroupAction.Induced where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Structure
open import Cubical.Foundations.Function
open import Cubical.Algebra.Group.Base
open import Cubical.Algebra.Group.Properties
open import Cubical.HITs.TypeQuotients.Base

open import Multiset.GroupAction.Base
open import Multiset.GroupAction.Orbit

private
  variable
    ℓG ℓS : Level

module _ (G : Group ℓG) where

  private
    open module G = GroupStr (str G)

  _·'_ : ⟨ G ⟩ → ⟨ G ⟩ → ⟨ G ⟩
  g ·' h = h · g

  ·'-assoc : (g h k : ⟨ G ⟩) → g ·' (h ·' k) ≡ (g ·' h) ·' k
  ·'-assoc g h k = sym (G.assoc k h g)

  open import Cubical.Algebra.Monoid.Base
  open import Cubical.Algebra.Semigroup.Base

  OppositeGroup : Group ℓG
  OppositeGroup = ⟨ G ⟩ , (groupstr 1g _·'_ G.inv op-isgroup)
    where
      op-issemigroup : IsSemigroup _·'_
      op-issemigroup = issemigroup G.is-set ·'-assoc

      op-ismonoid : IsMonoid 1g _·'_
      op-ismonoid = ismonoid op-issemigroup λ g → (G.lid g) , (G.rid g)

      op-isgroup : IsGroup 1g _·'_ G.inv
      op-isgroup = isgroup op-ismonoid (λ g → (G.invl g) , (G.invr g))


module _ {G : Group ℓG} (S : GroupAction G ℓS) {ℓX : Level} (X : Type ℓX) where

  private
    open module S = GroupActionStr (str S)
    open module G = GroupStr (str G)
    open module GT = GroupTheory G

    Gᵒᵖ = OppositeGroup G

  InducedOp : GroupAction Gᵒᵖ (ℓ-max ℓS ℓX)
  InducedOp =
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
    ( {- inv 1g ▸ s -} cong (_▸ s) inv1g
    ∙ {- 1g ▸ s -} act-1g s
      {- s -}
    )

  act-inv-distmul : ∀ g h s → inv h ▸ (inv g ▸ s) ≡ inv (g · h) ▸ s
  act-inv-distmul g h s =
    ( {- inv h ▸ (inv g ▸ s) -} act-distmul _ _ _
    ∙ {- (inv h · inv g) ▸ s -} cong (_▸ s) (sym (invDistr _ _))
      {- inv (g · h) ▸ s -}
    )

  Induced : GroupAction G (ℓ-max ℓS ℓX)
  Induced =
    ( (⟨ S ⟩ → X)
    , ( groupactionstr
        (λ g f s → f (inv g ▸ s))
        (isgroupaction
          (λ f → funExt (λ s → cong f (act-inv-1g s)))
          λ g h f → funExt (λ s →  cong f (act-inv-distmul g h s))
        )
      )
    )

module OrbitMap {G : Group ℓG} (S : GroupAction G ℓS)
  {ℓX ℓY : Level} {X : Type ℓX} {Y : Type ℓY}
  where
  open Orbit (Induced S Y)

  -- postComp : {v w : ⟨ S ⟩ → X} (v∼w : v ∼ w) (f : )

  well-defined : (f : X → Y) (v w : ⟨ S ⟩ → X)
    → (v∼w : [ Induced S X ∣ v ∼ w ])
    → orbitof (f ∘ v) ≡ orbitof (f ∘ w)
  well-defined f v w (g , g▸v≡w) = eq/ _ _
    ( g , cong (f ∘_) (g▸v≡w)
      -- TODO: to use proofs that are written in equational
      -- reasoning style, one has to get rid of the extra
      -- refl introduced by ∎.  Use the groupoid laws for ≡
      -- to get rid of it (Foundations.GroupoidLaws).
      -- 1. (g ▸Y (f ∘ v) ≡⟨ (λ i s → f (g▸v≡w i s)) ⟩ f ∘ w ∎)
      -- 2. funExt
      --   (λ s →
      --     ( (g ▸Y (f ∘ v)) s
      --       ≡⟨ refl ⟩
      --     f (v (inv g S.▸ s))
      --       ≡⟨ cong f (funExt⁻ g▸v≡w s) ⟩
      --     f (w s)
      --       ∎
      --     )
      --   )
    )

  descend : (f : X → Y) → (Induced S X) /∼ → (Induced S Y) /∼
  descend f = Orbit.elim (Induced S X) (λ v → [ f ∘ v ]) (well-defined f)

module _ {G : Group ℓG} (S : GroupAction G ℓS) {ℓX : Level} (X : Type ℓX) where
  open OrbitMap S
  open Orbit (Induced S X)

  descend-id : descend (idfun X) ≡ idfun ((Induced S X) /∼)
  descend-id = funExt aux
    where
      aux : ∀ v → descend (idfun X) v ≡ v
      aux = elim (λ s → refl) λ s t s∼t i → refl

module _ {G : Group ℓG} (S : GroupAction G ℓS) {ℓX ℓY ℓZ : Level}
  {X : Type ℓX} {Y : Type ℓY} {Z : Type ℓZ}
  where

  open module OrbitMapS = OrbitMap S

  descend-comp : (f : X → Y) (g : Y → Z)
    → descend (g ∘ f) ≡ descend g ∘ descend f
  descend-comp f g = funExt aux
    where
      aux : ∀ v → descend (g ∘ f) v ≡ descend g (descend f v)
      aux = Orbit.elim (Induced S X)
        (λ _ → refl)
        (λ s t s∼t i j → well-defined (g ∘ f) s t s∼t i)
