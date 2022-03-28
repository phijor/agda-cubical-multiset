module Multiset.SigOverGroupoid.Base where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels using (isOfHLevel≡)
open import Cubical.Foundations.Function using (_∘_)

open import Cubical.Data.Nat.Base using (ℕ)
open import Cubical.Data.SumFin
  using
    ( Fin
    ; isSetFin
    )

open import Cubical.Algebra.Group
  using
    ( Group
    ; Group₀
    ; makeGroup
    ; Subgroup
    ; Subgroup→Group
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

Perm : (n : ℕ) → Group₁
Perm n = Aut (Fin n) (isOfHLevel≡ 2 (isSetFin) (isSetFin))

--- This is like Sym from Cubical.Algebra.SymmetricGroup,
--- except that it's carrier is the Fin of Cubical.Data.SumFin.
Sym : (n : ℕ) → Group₀
Sym n = Symmetric-Group (Fin n) isSetFin

record GroupoidSignature (ℓSh ℓPos : Level) : Type (ℓ-suc (ℓ-max ℓSh ℓPos)) where
  constructor groupoidsig
  field
    Shape : Type ℓSh
    isGpdShape : isGroupoid Shape
    Pos : Shape → FinSet ℓPos

  sz : Shape → ℕ
  sz = card ∘ Pos

record SubgroupSignature (ℓOp : Level) : Type (ℓ-suc ℓOp) where
  constructor subgroupsig
  field
    Op : Type ℓOp
    isSetOp : isSet Op
    arity : Op → ℕ
    Symm : ∀ op → Subgroup (Sym (arity op))

  SymmGrp : (op : Op) → Group₀
  SymmGrp op = Subgroup→Group (Sym (arity op)) (Symm op)
