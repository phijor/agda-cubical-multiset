module Multiset.GroupAction.Orbit where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Structure
open import Cubical.Foundations.HLevels
open import Cubical.Data.Sigma
open import Cubical.Algebra.Group.Base
open import Cubical.HITs.TypeQuotients.Base renaming (_/ₜ_ to _/_)
open import Cubical.HITs.TypeQuotients.Properties renaming
  ( elim to elimTyQuot
  ; rec to recTyQuot
  ; elimProp to elimPropTyQuot
  )

open import Multiset.GroupAction.Base
open import Multiset.GroupAction.Properties

private
  variable
    ℓG ℓS : Level

isReachable : {G : Group ℓG} (S : GroupAction G ℓS) (s t : ⟨ S ⟩) → Type (ℓ-max ℓG ℓS)
isReachable {G = G} S s t = Σ[ g ∈ ⟨ G ⟩ ] g ▸ s ≡ t where
  open GroupActionStr (str S)

∼-syntax : {G : Group ℓG} (S : GroupAction G ℓS) (s t : ⟨ S ⟩) → Type (ℓ-max ℓG ℓS)
∼-syntax = isReachable

syntax ∼-syntax S s t = s ∼[ S ] t

isFree→isPropIsReachable : {G : Group ℓG} (S : GroupAction G ℓS) → GroupActionTheory.isFree G S → (s t : ⟨ S ⟩) → isProp (s ∼[ S ] t)
isFree→isPropIsReachable {G = G} S freeness s t (g , g▸s≡t) (h , h▸s≡t) = Σ≡Prop (λ g → is-set-carrier _ t) (freeness _ _ s g▸s≡h▸s) where
  open GroupActionStr (str S)

  g▸s≡h▸s : g ▸ s ≡ h ▸ s
  g▸s≡h▸s = g▸s≡t ∙ (sym h▸s≡t)

module Orbit {G : Group ℓG} (S : GroupAction G ℓS) where

  private
    open import Cubical.Relation.Binary.Base

    open module S = GroupActionStr (str S)
    open module G = GroupStr (str G)
    open module GAT = GroupActionTheory G S

  _∼_ : (s t : ⟨ S ⟩) → Type (ℓ-max ℓG ℓS)
  s ∼ t = isReachable S s t

  isTransitive : Type (ℓ-max ℓG ℓS)
  isTransitive = (s t : ⟨ S ⟩) → s ∼ t

  open module ∼-Rel = BinaryRelation _∼_

  ∼-refl : isRefl
  ∼-refl s = 1g , S.act-1g s

  Path→∼ : {s t : ⟨ S ⟩} → s ≡ t → s ∼ t
  Path→∼ {s = s} s≡t = 1g , (S.act-1g s ∙ s≡t)

  ∼-sym : isSym
  ∼-sym s t (g , g▸s≡t) =
    ( inv g
    , ( {- inv g ▸ t -} cong (inv g ▸_) (sym g▸s≡t)
      ∙ {- inv g ▸ g ▸ s -} act-invl _ _
        {- s -}
      )
    )

  ∼-trans : isTrans
  ∼-trans s t u (g , g▸s≡t) (h , h▸t≡u) =
    ( (h · g)
    , ( {- (h · g) ▸ s -} sym (act-distmul _ _ _)
      ∙ {- h ▸ g ▸ s -}  cong (h ▸_) g▸s≡t
      ∙ {- h ▸ t -}       h▸t≡u
        {- u -}
      )
    )

  ∼-isEquivRel : isEquivRel
  ∼-isEquivRel = BinaryRelation.equivRel ∼-refl ∼-sym ∼-trans

  OrbitType : Type (ℓ-max ℓG ℓS)
  OrbitType = ⟨ S ⟩ / _∼_

  orbitof : ⟨ S ⟩ → OrbitType
  orbitof s = [ s ]

  [_]∼ = orbitof

  Path→OrbitPath : {s t : ⟨ S ⟩} → s ≡ t → [ s ]∼ ≡ [ t ]∼
  Path→OrbitPath s≡t = eq/ _ _ (Path→∼ s≡t)

  elim : {ℓ : Level} {B : OrbitType → Type ℓ}
    → (f : (s : ⟨ S ⟩) → B (orbitof s))
    → (∀ (s t : ⟨ S ⟩) → (s∼t : s ∼ t) → PathP (λ i → B (eq/ s t s∼t i)) (f s) (f t))
    → (o : OrbitType) → B o
  elim = elimTyQuot

  rec : {ℓ : Level} {X : Type ℓ}
    → (f : ⟨ S ⟩ → X)
    → (∀ (s t : ⟨ S ⟩) → (s∼t : s ∼ t) → f s ≡ f t)
    → OrbitType → X
  rec = recTyQuot

  elimProp : {ℓ : Level} {B : OrbitType → Type ℓ}
    → (∀ s → isProp (B s))
    → (f : (s : ⟨ S ⟩) → B (orbitof s))
    → (o : OrbitType) → B o
  elimProp = elimPropTyQuot

module _ {G : Group ℓG} (S : GroupAction G ℓS) where
  open Orbit S

  _/∼ : Type (ℓ-max ℓG ℓS)
  _/∼ = OrbitType

map : {ℓS ℓT : Level} {G : Group ℓG} {S : GroupAction G ℓS} {T : GroupAction G ℓT}
  (f : EquivariantMap S T) → S /∼ → T /∼
map {S = S} {T = T} (f , isEquivariant-f) = elim (λ s → [ f s ]) well-defined where
  open module OrbitS = Orbit S

  well-defined : ∀ s₀ s₁ → s₀ ∼ s₁ → [ f s₀ ] ≡ [ f s₁ ]
  well-defined s₀ s₁ (g , g▸s₀≡s₁) = eq/ _ _
    ( g
    -- The below proof shows that
    -- g ▸ (f s₀) ≡ f (g ▸ s₀) ≡ f s₁
    , sym (isEquivariant-f g s₀) ∙ cong f g▸s₀≡s₁
    )
