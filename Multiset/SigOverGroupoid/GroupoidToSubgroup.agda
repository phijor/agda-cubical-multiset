module Multiset.SigOverGroupoid.GroupoidToSubgroup where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Univalence
open import Cubical.Foundations.Equiv
  renaming (compEquiv to infixr 9 _∙≃_)
open import Cubical.Foundations.Equiv.Properties
  using
    ( isEquivCong
    ; conjugatePathEquiv
    )
open import Cubical.Foundations.Function
  using (_∘_)
open import Cubical.Foundations.HLevels
  using
    ( isOfHLevel≃
    ; isOfHLevel≡
    )
open import Cubical.Foundations.Structure
import Cubical.Foundations.GroupoidLaws as GpdLaws

open import Cubical.Functions.Embedding

open import Cubical.Data.Nat
open import Cubical.Data.SumFin

open import Cubical.HITs.SetTruncation
  renaming
    ( map to map-∥_∥₂
    ; rec to ∥-∥₂-rec
    ; elim to ∥-∥₂-elim
    )
import Cubical.HITs.PropositionalTruncation as Prop

open import Cubical.Algebra.Group

open import Multiset.Util using (pathToEquivComp; conjugate)
open import Multiset.SigOverGroupoid.Base

private
  variable
    ℓ ℓPos ℓSh : Level

  -- TODO: Subgroups don't play well with universe levels.
  -- Mostly because group-homs go between types of the same level.
  -- Restrict to shapes that live in level 0 for now.
  -- TODO: not necessary anymore.
  -- ℓSh : Level
  -- ℓSh = ℓ-zero

toSubGpSig : GroupoidSignature ℓSh ℓPos → SubgroupSignature _ _
toSubGpSig {ℓSh = ℓSh} {ℓPos = ℓPos} Sig = subgroupsig Op isSetSetTrunc arity {!   !} where
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
  module _ (sh : Shape) where
    -- The group of automorphisms of a shape is its set of
    -- self-identifications.
    AutSh : Group ℓSh
    AutSh = Aut sh (isGpdShape sh sh)

    private
      n : ℕ
      n = sz sh

    -- Every self-identification (a path sh ≡ sh) maps to a permutation
    -- of its size-type.
    -- (Well not quite, it maps into the set of self-identification of
    -- the latter.  See the full story below).
    ϕ : sh ≡ sh → (Fin (sz sh) ≡ Fin (sz sh))
    ϕ = (cong (Fin ∘ sz))

    -- TODO: WTF!?
    ϕ-const-refl : (p : sh ≡ sh) → refl ≡ ϕ p
    ϕ-const-refl p = λ i → cong Fin (sz-const i) where
      sz-const : refl ≡ cong sz p
      sz-const = isSetℕ (sz sh) (sz sh) refl (cong sz p)


    ϕ′ : ⟨ Pos sh ⟩ ≃ ⟨ Pos sh ⟩ → Fin (sz sh) ≃ Fin (sz sh)
    ϕ′ = conjugate (isOfHLevel≃ 2 isSetFin isSetFin) ∣α∣ where
      ∣α∣ : Prop.∥ ⟨ Pos sh ⟩ ≃ Fin (sz sh) ∥
      ∣α∣ = str (Pos sh) .snd

    ψ : (⟨ Pos sh ⟩ ≡ ⟨ Pos sh ⟩) → (Lift {j = ℓPos} (Fin n) ≡ Lift (Fin n))
    ψ π = Prop.rec→Set (isOfHLevel≡ 2 isSetLiftFin isSetLiftFin) conj conj-const ∣p∣ where
      ∣α∣ : Prop.∥ ⟨ Pos sh ⟩ ≃ Fin n ∥
      ∣α∣ = str (Pos sh) .snd

      ∣p∣ : Prop.∥ ⟨ Pos sh ⟩ ≡ Lift (Fin n) ∥
      ∣p∣ = Prop.map (λ α → ua (α ∙≃ LiftEquiv)) ∣α∣

      conj : ⟨ Pos sh ⟩ ≡ Lift (Fin n) → (Lift {j = ℓPos} (Fin n) ≡ Lift (Fin n))
      conj p = (sym p) ∙∙ π ∙∙ p

      conj-const : ∀ p q → conj p ≡ conj q
      conj-const p q = {!   !}


    -- Since ϕ is just transport of paths using congruence, it preserves
    -- path composition (i.e. the group operation in AutSh).
    ϕ-pres∙ : ∀ p₁ p₂ → ϕ (p₁ ∙ p₂) ≡ (ϕ p₁) ∙ (ϕ p₂)
    ϕ-pres∙ = GpdLaws.cong-∙ (Fin ∘ sz)

    -- Postcomposition of ϕ with the lift of paths to equivalences forms
    -- a group homomorphism: from the group of self-identifications of a
    -- path to the set of permutations of its size-type.

    ϕ-isGroupHom : IsGroupHom (str AutSh) ϕ (str (Perm (sz sh)))
    ϕ-isGroupHom = makeIsGroupHom ϕ-pres∙ where
      -- Lifting self-identifications preserves composition; this time composition of equivalences.
      pathToEquiv∘ϕ-pres∙ : ∀ p₁ p₂ → pathToEquiv (ϕ (p₁ ∙ p₂)) ≡ (pathToEquiv (ϕ p₁)) ∙≃ (pathToEquiv (ϕ p₂))
      pathToEquiv∘ϕ-pres∙ p₁ p₂ = cong pathToEquiv (ϕ-pres∙ p₁ p₂) ∙ pathToEquivComp (ϕ p₁) (ϕ p₂)

    shapePathToPermutation : GroupHom AutSh (Perm (sz sh))
    shapePathToPermutation = ϕ , ϕ-isGroupHom

    ϕ-inj : ∀ {p q} → ϕ p ≡ ϕ q → p ≡ q
    ϕ-inj {p} {q} eq = {! eq  !}

    ϕ-isEmbedding : isEmbedding ϕ
    ϕ-isEmbedding = injEmbedding (isGpdShape sh sh) isSetAutFin ϕ-inj

  -- The image of this lift defines a subgroups of permutations.
  G' : (sh : Shape) → PermutationGroup ℓSh (sz sh)
  G' sh = permutationgrp (AutSh sh) (ϕ sh) (ispermutation (ϕ-isGroupHom sh) (ϕ-isEmbedding sh))
    -- imSubgroup {G = AutSh sh} ( {! shapePathToPermutation sh  !} , {!  isMono !})


  G : (op : Op) → PermutationGroup ℓSh (arity op)
  G = ∥-∥₂-elim (λ _ → isSetPermutationGroup) G'
