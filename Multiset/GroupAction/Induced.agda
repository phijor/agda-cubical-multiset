module Multiset.GroupAction.Induced where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Structure
open import Cubical.Foundations.Function
open import Cubical.Foundations.HLevels
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


module _ {G : Group ℓG} (S : GroupAction G ℓS) {ℓX : Level} (X : hSet ℓX) where

  private
    open module S = GroupActionStr (str S)
    open module G = GroupStr (str G)
    open module GT = GroupTheory G

    Gᵒᵖ = OppositeGroup G

    isSetS→X : isSet (⟨ S ⟩ → ⟨ X ⟩)
    isSetS→X = isSetΠ (λ _ → str X)

  InducedOp : GroupAction Gᵒᵖ (ℓ-max ℓS ℓX)
  InducedOp =
    ( (⟨ S ⟩ → ⟨ X ⟩)
    , groupactionstr
      (λ g f s → f (g ▸ s))
      (isgroupaction
        isSetS→X
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
    ( (⟨ S ⟩ → ⟨ X ⟩)
    , ( groupactionstr
        (λ g f s → f (inv g ▸ s))
        (isgroupaction
          isSetS→X
          (λ f → funExt (λ s → cong f (act-inv-1g s)))
          λ g h f → funExt (λ s →  cong f (act-inv-distmul g h s))
        )
      )
    )

module OrbitMap {G : Group ℓG} (S : GroupAction G ℓS)
  {ℓX ℓY : Level} {X : Type ℓX} {Y : Type ℓY}
  (isSetX : isSet X) (isSetY : isSet Y)
  where
  open Orbit (Induced S (Y , isSetY))

  private
    S→X = Induced S (X , isSetX)
    S→Y = Induced S (Y , isSetY)

  -- postComp : {v w : ⟨ S ⟩ → X} (v∼w : v ∼ w) (f : )

  well-defined : (f : X → Y) (v w : ⟨ S ⟩ → X)
    → (v∼w : v ∼[ S→X ] w)
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

  descend : (f : X → Y) → S→X /∼ → S→Y /∼
  descend f = Orbit.elim S→X (λ v → [ f ∘ v ]) (well-defined f)

module _ {G : Group ℓG} (S : GroupAction G ℓS) {ℓX : Level} (X : hSet ℓX) where
  open OrbitMap S (str X) (str X)

  private
    S→X = Induced S X

  open Orbit S→X

  descend-id : descend (idfun ⟨ X ⟩) ≡ idfun (S→X /∼)
  descend-id = funExt aux
    where
      aux : ∀ v → descend (idfun ⟨ X ⟩) v ≡ v
      aux = elim (λ s → refl) λ s t s∼t i → refl

module _ {G : Group ℓG} (S : GroupAction G ℓS) {ℓX ℓY ℓZ : Level}
  {X : Type ℓX} {Y : Type ℓY} {Z : Type ℓZ}
  (isSetX : isSet X)
  (isSetY : isSet Y)
  (isSetZ : isSet Z)
  where

  open module OrbitMapS = OrbitMap S

  descend-comp : (f : X → Y) (g : Y → Z)
    → descend isSetX isSetZ (g ∘ f) ≡ descend isSetY isSetZ g ∘ descend isSetX isSetY f
  descend-comp f g = funExt
    ( Orbit.elim (Induced S (X , isSetX))
      (λ _ → refl)
      (λ s t s∼t i j → well-defined isSetX isSetZ (g ∘ f) s t s∼t i)
    )
