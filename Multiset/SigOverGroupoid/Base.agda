module Multiset.SigOverGroupoid.Base where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
  using
    ( fiber
    ; _≃_
    ; idEquiv
    ; equivFun
    ; invEquiv
    )
open import Cubical.Foundations.Equiv.Fiberwise
  using
    ( fundamentalTheoremOfId
    )
open import Cubical.Foundations.HLevels
  using
    ( isOfHLevel≡
    ; isOfHLevel≃
    ; isOfHLevelLift
    ; isOfHLevelRetractFromIso
    ; isOfHLevelRespectEquiv
    ; isSetΣ
    ; isPropΠ
    )
open import Cubical.Foundations.Function using (_∘_)
open import Cubical.Foundations.Isomorphism
  using
    ( Iso
    ; iso
    ; isoToPath
    ; isoToEquiv
    )
open import Cubical.Foundations.Structure
open import Cubical.Foundations.Univalence using (pathToEquiv)

open import Cubical.Reflection.RecordEquiv

open import Cubical.Data.Nat.Base using (ℕ)
open import Cubical.Data.Sigma
open import Cubical.Data.SumFin
  using
    ( Fin
    ; isSetFin
    )

open import Cubical.Functions.Embedding
  using
    ( isEmbedding
    ; isPropIsEmbedding
    ; hasPropFibers
    ; isEmbedding→hasPropFibers
    )

open import Cubical.Algebra.Group
  using
    ( Group
    ; Group₀
    ; makeGroup
    ; Subgroup
    ; Subgroup→Group
    ; isMono
    ; IsGroupHom
    ; isPropIsGroupHom
    ; isPropIsGroup
    )
  renaming
    ( GroupHom to Group[_,_]
    )
open import Cubical.Algebra.SymmetricGroup
  using (Symmetric-Group)
  -- hiding (Sym)

open import Cubical.Data.FinSet
  using
    ( FinSet
    ; card
    )

private
  ℓ-one : Level
  ℓ-one = ℓ-suc ℓ-zero

  Group₁ = Group ℓ-one

module _ {ℓ : Level} {X : Type ℓ} (x : X) (isSetPath : isSet (x ≡ x)) where
  import Cubical.Foundations.GroupoidLaws as GpdLaws

  Aut : Group ℓ
  Aut = makeGroup {G = x ≡ x}
        refl
        _∙_
        sym
        isSetPath
        GpdLaws.assoc
        (sym ∘ GpdLaws.rUnit) (sym ∘ GpdLaws.lUnit)
        GpdLaws.rCancel GpdLaws.lCancel

isSetLiftFin : ∀ {ℓ} {n} → isSet (Lift {j = ℓ} (Fin n))
isSetLiftFin = isOfHLevelLift 2 isSetFin

isSetAutFin : ∀ {n} → isSet (Fin n ≡ Fin n)
isSetAutFin = isOfHLevel≡ 2 isSetFin isSetFin

Perm : (n : ℕ) → Group₁
Perm n = Aut (Fin n) isSetAutFin

--- This is like Sym from Cubical.Algebra.SymmetricGroup,
--- except that it's carrier is the Fin of Cubical.Data.SumFin.
Sym : (n : ℕ) → Group₀
Sym n = Symmetric-Group (Fin n) isSetFin

record isPermutation {ℓ : Level} {n : ℕ} (G : Group ℓ) (f : ⟨ G ⟩ → Fin n ≡ Fin n) : Type (ℓ-max (ℓ-suc ℓ-zero) ℓ) where
  constructor ispermutation
  field
    isGrpHom : IsGroupHom (str G) f (str (Perm n))
    isEmb : isEmbedding f

record PermutationGroup (ℓ : Level) (n : ℕ) : Type (ℓ-suc ℓ) where
  constructor permutationgrp
  field
    SubGroup : Group ℓ
    inclusion : ⟨ SubGroup ⟩ → Fin n ≡ Fin n

    isPerm : isPermutation SubGroup inclusion

  open isPermutation isPerm public

unquoteDecl PermutationGroupIsoΣ = declareRecordIsoΣ PermutationGroupIsoΣ (quote PermutationGroup)

module _ {ℓ : Level} {n : ℕ} where
  open PermutationGroup

  isPropIsPermutation : (G : Group ℓ) (f : ⟨ G ⟩ → Fin n ≡ Fin n) → isProp (isPermutation G f)
  isPropIsPermutation G f = λ p q i → ispermutation (isPropIsGroupHom G _ (p .isGrpHom) (q .isGrpHom) i) (isPropIsEmbedding (p .isEmb) (q .isEmb) i) where
    open isPermutation

  hasPropFibersInclusion : (G : PermutationGroup ℓ n) → hasPropFibers (G .inclusion)
  hasPropFibersInclusion G = isEmbedding→hasPropFibers (G .isEmb)

  PermutationGroupEq : (G H : PermutationGroup ℓ n) → Type _
  PermutationGroupEq G H = (∀ π → fiber (inclusion G) π ≃ fiber (inclusion H) π)

  isPropPermutationGroupEq : ∀ G H → isProp (PermutationGroupEq G H)
  isPropPermutationGroupEq G H = isPropΠ (λ π → isOfHLevel≃ 1 (hasPropFibersInclusion G π) (hasPropFibersInclusion H π))

  PermutationGroupId' : ∀ (G H : PermutationGroup ℓ n)
    → (G ≡ H) ≃ (∀ π → fiber (inclusion G) π ≃ fiber (inclusion H) π)
  PermutationGroupId' G H = isoToEquiv (iso toFiberEquiv ofFiberEquiv {!   !} {!   !}) where
    toFiberEquiv : (G ≡ H) → PermutationGroupEq G H
    toFiberEquiv G≡H = λ π → pathToEquiv (cong (λ G → fiber (inclusion G) π) G≡H)

    ofFiberEquiv : ∀ {G H} → PermutationGroupEq G H → (G ≡ H)
    ofFiberEquiv {G} {H} EqGH = cong (PermutationGroupIsoΣ .inv) (ΣPathP (ΣPathP ({!   !}) , {!   !})) where
      open Iso

      G→H : ⟨ G .SubGroup ⟩ → ⟨ H .SubGroup ⟩
      G→H g = {!   !}

      SubGroupEq : ⟨ G .SubGroup ⟩ ≡ ⟨ H .SubGroup ⟩
      SubGroupEq = isoToPath (iso {!   !} {!   !} {!   !} {!   !})

  PermutationGroupId : ∀ (G H : PermutationGroup ℓ n)
    → (G ≡ H) ≃ (∀ π → fiber (inclusion G) π ≃ fiber (inclusion H) π)
  PermutationGroupId = fundamentalTheoremOfId PermutationGroupEq toRefl isContrEq where
    toRefl : (G : PermutationGroup ℓ n) → PermutationGroupEq G G
    toRefl = λ _ _ → idEquiv _

    isContrEq : ∀ G → isContr (Σ[ H ∈ PermutationGroup ℓ n ] PermutationGroupEq G H)
    isContrEq G = (G , (toRefl G)) , contraction where
      contraction : (p : Σ[ H ∈ PermutationGroup ℓ n ] PermutationGroupEq G H) → (G , (toRefl G)) ≡ p
      contraction (H , EqHG) = ΣPathP ({!   !} , {!   !})


  PermutationGroup≡ : ∀ {G H : PermutationGroup ℓ n}
    → (∀ (π : Fin n ≡ Fin n) → fiber (inclusion G) π ≃ fiber (inclusion H) π)
    → G ≡ H
  PermutationGroup≡ {G} {H} = equivFun (invEquiv (PermutationGroupId G H))

  isSetPermutationGroup : isSet (PermutationGroup ℓ n)
  isSetPermutationGroup = λ G H → isOfHLevelRespectEquiv 1 (invEquiv (PermutationGroupId G H)) (isPropPermutationGroupEq G H)


record GroupoidSignature (ℓSh ℓPos : Level) : Type (ℓ-suc (ℓ-max ℓSh ℓPos)) where
  constructor groupoidsig
  field
    Shape : Type ℓSh
    isGpdShape : isGroupoid Shape
    Pos : Shape → FinSet ℓPos

  sz : Shape → ℕ
  sz = card ∘ Pos

record SubgroupSignature (ℓOp : Level) (ℓSymm : Level) : Type (ℓ-suc (ℓ-max (ℓ-suc ℓSymm) ℓOp)) where
  constructor subgroupsig
  field
    Op : Type ℓOp
    isSetOp : isSet Op
    arity : Op → ℕ
    Symm : ∀ op → PermutationGroup ℓSymm (arity op)

  SymmGrp : (op : Op) → Group ℓSymm
  SymmGrp op = (Symm op) .SubGroup where
    open PermutationGroup
