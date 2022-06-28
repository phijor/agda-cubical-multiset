module Multiset.OverBij.Base where

open import Multiset.Bij as Bij

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Structure
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Function using (_∘_)

open import Cubical.Data.Sigma as Σ
open import Cubical.Data.Nat as ℕ
  using (ℕ)

open import Cubical.Reflection.RecordEquiv

open import Cubical.Data.SumFin as Fin
  using (Fin ; fzero ; fsuc)

private
  variable
    ℓ : Level
    X Y : Type ℓ

abstract
  open import Cubical.Foundations.Equiv

  Idx : Bij → Type ℓ-zero
  Idx = λ x → ⟨ Bij→FinSet x ⟩

  unIdx : {n : ℕ} → Idx (obj n) → Fin n
  unIdx idx = idx

Vect : Type ℓ → Bij → Type ℓ
Vect X k = Idx k → X

isOfHLevelVect : ∀ {k} (n : ℕ) → isOfHLevel n X → isOfHLevel n (Vect X k)
isOfHLevelVect n hLevel = isOfHLevelΠ n (λ idx → hLevel)

record Bag (X : Type ℓ) : Type ℓ where
  constructor ⟅_⟆
  field
    {card} : Bij
    members : Vect X card

⟅⟆-syntax : {X : Type ℓ} (k : Bij) → (Idx k → X) → Bag X
⟅⟆-syntax k members = ⟅ members ⟆

⟅⟆-implicit-syntax : {X : Type ℓ} {k : Bij} → (Idx k → X) → Bag X
⟅⟆-implicit-syntax members = ⟅ members ⟆

⟅⟆-obj-syntax : {X : Type ℓ} (n : ℕ) (members : Fin n → X) → Bag X
⟅⟆-obj-syntax n members = ⟅ (λ (idx : Idx (obj n)) → members (unIdx idx)) ⟆

syntax ⟅⟆-syntax k (λ idx → x) = ⟅ x ∣ idx ∈ k ⟆
syntax ⟅⟆-implicit-syntax (λ idx → x) = ⟅ idx ↦ x ⟆
syntax ⟅⟆-obj-syntax n (λ k → x) = ⟅ x ∣ k ≤ n ⟆

unquoteDecl BagIsoΣ = declareRecordIsoΣ BagIsoΣ (quote Bag)

BagPathP : ∀ {m n : Bij}
  → (p : m ≡ n)
  → {v : Vect X m}
  → {w : Vect X n}
  → (q : PathP (λ i → Vect X (p i)) v w)
  → ⟅ v ⟆ ≡ ⟅ w ⟆
BagPathP _ q i = ⟅ q i ⟆

BagPathPExt : ∀ {m n : Bij}
  → (p : m ≡ n)
  → {v : Vect X m}
  → {w : Vect X n}
  → ({idx₀ : Idx m} {idx₁ : Idx n} (q : PathP (λ i → Idx (p i)) idx₀ idx₁) → v idx₀ ≡ w idx₁)
  → ⟅ v ⟆ ≡ ⟅ w ⟆
BagPathPExt p q = BagPathP p (funExtDep q)


BagPath : ∀ {m : Bij} {v w : Vect X m}
  → v ≡ w
  → ⟅ v ⟆ ≡ ⟅ w ⟆
BagPath = cong ⟅_⟆

BagPathExt : ∀ {m : Bij} {v w : Vect X m}
  → (∀ (k : Idx m) → v k ≡ w k)
  → ⟅ v ⟆ ≡ ⟅ w ⟆
BagPathExt ext = BagPath (funExt ext)

isGroupoidBag : isGroupoid X → isGroupoid (Bag X)
isGroupoidBag gpdX = isOfHLevelRetractFromIso 3 BagIsoΣ (isGroupoidΣ isGroupoidBij λ _ → isOfHLevelVect 3 gpdX)

map : (f : X → Y) → (Bag X → Bag Y)
map f ⟅ members ⟆ = ⟅ f ∘ members ⟆

map∘map : ∀ {Z : Type ℓ} → (f : X → Y) (g : Y → Z)
  → (xs : Bag X)
  → map g (map f xs) ≡ map (g ∘ f) xs
map∘map f g xs = refl


module Example where
  open import Cubical.Foundations.Equiv
  open import Cubical.Foundations.Isomorphism

  -- Bag comprehension:
  ex : Bag ℕ
  ex = ⟅ 42 ∣ idx ≤ 3 ⟆

  -- Sometimes, the cardinality of a bag
  -- can be inferred from context:
  exImplicitPath : ex ≡ ⟅ idx ↦ 42 ⟆
  exImplicitPath = BagPathExt (λ idx → refl)
