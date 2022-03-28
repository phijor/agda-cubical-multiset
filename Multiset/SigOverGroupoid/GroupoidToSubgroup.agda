module Multiset.SigOverGroupoid.GroupoidToSubgroup where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Univalence
open import Cubical.Foundations.Equiv
  renaming (compEquiv to infixr 9 _∘≃_)
open import Cubical.Foundations.Function
  using (_∘_)
import Cubical.Foundations.GroupoidLaws as GpdLaws

open import Cubical.Data.Nat
open import Cubical.Data.Fin

open import Cubical.HITs.SetTruncation
  renaming
    ( map to map-∥_∥₂
    ; rec to ∥-∥₂-rec
    ; elim to ∥-∥₂-elim
    )
open import Cubical.HITs.PropositionalTruncation
  using
    (isPropPropTrunc)

open import Cubical.Algebra.Group
open import Cubical.Algebra.SymmetricGroup

open import Multiset.Util using (pathToEquivComp)
open import Multiset.SigOverGroupoid.Base

private
  variable
    ℓ ℓPos ℓOp : Level

  -- TODO: Subgroups don't play well with universe levels.
  -- Mostly because group-homs go between types of the same level.
  -- Restrict to shapes that live in level 0 for now.
  ℓSh : Level
  ℓSh = ℓ-zero

toSubGpSig : GroupoidSignature ℓSh ℓOp → SubgroupSignature ℓSh
toSubGpSig Sig = subgroupsig Op isSetSetTrunc arity G where
  open GroupoidSignature Sig

  -- The set of operations of the signature is obtained
  -- by set-truncating the type of shapes.
  Op : Type ℓSh
  Op = ∥ Shape ∥₂

  -- Set truncation preserves exactly the points of the
  -- type of shapes, so define the arity of a shape to
  -- be its size (i.e. the number of positions it contains).
  arity : Op → ℕ
  arity = ∥-∥₂-rec isSetℕ sz

  -- Here comes the definition of the family of subgroups,
  -- encoding the symmetries of the groupoid of shapes.
  module _ (sh : Shape) where abstract
    -- The group of automorphisms of a shape is its set of
    -- self-identifications.
    AutSh : Group ℓSh
    AutSh = Aut sh (isGpdShape sh sh)

    -- Every self-identification (a path sh ≡ sh) maps to a permutation
    -- of its size-type.
    -- (Well not quite, it maps into the set of self-identification of
    -- the latter.  See the full story below).
    ϕ : sh ≡ sh → (Fin (sz sh) ≡ Fin (sz sh))
    ϕ = (cong (Fin ∘ sz))

    -- Since ϕ is just transport of paths using congruence, it preserves
    -- path composition (i.e. the group operation in AutSh).
    ϕ-pres∙ : ∀ p₁ p₂ → ϕ (p₁ ∙ p₂) ≡ (ϕ p₁) ∙ (ϕ p₂)
    ϕ-pres∙ = GpdLaws.cong-∙ (Fin ∘ sz)

    -- Postcomposition of ϕ with the lift of paths to equivalences forms
    -- a group homomorphism: from the group of self-identifications of a
    -- path to the set of permutations of its size-type.
    shapePathToPermutation : GroupHom AutSh (Sym (sz sh))
    shapePathToPermutation = pathToEquiv ∘ ϕ , makeIsGroupHom pathToEquiv∘ϕ-pres∙ where
      -- Lifting self-identifications preserves composition; this time composition of equivalences.
      pathToEquiv∘ϕ-pres∙ : ∀ p₁ p₂ → pathToEquiv (ϕ (p₁ ∙ p₂)) ≡ (pathToEquiv (ϕ p₁)) ∘≃ (pathToEquiv (ϕ p₂))
      pathToEquiv∘ϕ-pres∙ p₁ p₂ = cong pathToEquiv (ϕ-pres∙ p₁ p₂) ∙ pathToEquivComp (ϕ p₁) (ϕ p₂)

  -- The image of this lift defines a subgroups of permutations.
  G' : (sh : Shape) → Subgroup (Sym (sz sh))
  G' sh = imSubgroup (shapePathToPermutation sh)


  G : (op : Op) → Subgroup (Sym (arity op))
  G = ∥-∥₂-elim {B = Subgroup ∘ Sym ∘ arity} (λ sh → isSetSubgroup (Sym (arity sh))) G'
