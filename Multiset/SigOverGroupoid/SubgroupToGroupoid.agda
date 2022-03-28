module Multiset.SigOverGroupoid.SubgroupToGroupoid where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Univalence using (ua)
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Structure

open import Cubical.Data.Fin
open import Cubical.Data.Nat
open import Cubical.Data.Sigma

open import Cubical.HITs.TypeQuotients
  renaming
    (rec to /ₜ-rec)
open import Cubical.HITs.GroupoidTruncation
  renaming
    (rec to ∥-∥₃-rec)

open import Cubical.Data.FinSet

-- open import Multiset.GroupoidAction
open import Multiset.SigOverGroupoid.Base

private
  variable
    ℓ ℓPos ℓOp : Level

  ℓSh : Level
  ℓSh = ℓ-zero

isFinSet→isSet : {X : Type ℓ} → isFinSet X → isSet X
isFinSet→isSet {X = X} = ∥-∥₀-rec isPropIsSet FinEquiv→isSetX where

  FinEquiv→isSetX : Σ[ n ∈ ℕ ] (X ≃ Fin n) → isSet X
  FinEquiv→isSetX (n , α) = isOfHLevelRespectEquiv 2 (invEquiv α) isSetFin

FinSet→hSet : FinSet {ℓ} → hSet ℓ
FinSet→hSet (X , isFinSetX) = X , (isFinSet→isSet isFinSetX)

isGroupoidFinSet : isGroupoid (FinSet {ℓ})
isGroupoidFinSet {ℓ = ℓ} = isGroupoidRetract from to (λ _ → refl) isGroupoidFinSet' where

  FinSet' : Type (ℓ-suc ℓ)
  FinSet' = Σ[ X ∈ (hSet ℓ) ] ∃[ n ∈ ℕ ] ⟨ X ⟩ ≃ Fin n

  isGroupoidFinSet' : isGroupoid FinSet'
  isGroupoidFinSet' = isOfHLevelΣ 3 (isOfHLevelTypeOfHLevel 2) (λ X → isProp→isOfHLevelSuc 2 isPropPropTrunc)

  to : FinSet' → FinSet {ℓ}
  to (X , isFinX) = ⟨ X ⟩ , isFinX

  from : FinSet {ℓ} → FinSet'
  from (X , isFinSetX) = (X , isFinSet→isSet isFinSetX) , isFinSetX




FinSetPath : {X Y : FinSet {ℓ}} → ⟨ X ⟩ ≡ ⟨ Y ⟩ → X ≡ Y
FinSetPath = Σ≡Prop (λ _ → isProp-isFinSet)

toGpdSig : SubgroupSignature ℓOp → GroupoidSignature ℓOp ℓ-zero
toGpdSig {ℓOp = ℓOp} Sig = groupoidsig Fattened isGroupoidFattened Pos where
  open SubgroupSignature Sig

  data Loops : Op → Op → Type ℓOp where
    extra : ∀ op → (g : ⟨ SymmGrp op ⟩) → Loops op op

  Fattened : Type ℓOp
  Fattened = ∥ Op /ₜ Loops ∥₃

  isGroupoidFattened : isGroupoid Fattened
  isGroupoidFattened = isGroupoidGroupoidTrunc

  pos : Op → FinSet
  pos op = Fin (arity op) , isFinSetFin

  permutation : ∀ {op} → (g : ⟨ SymmGrp op ⟩) → (Fin (arity op) ≡ Fin (arity op))
  permutation (π , _) = ua π

  loopLift : ∀ op₁ op₂ → Loops op₁ op₂ → pos op₁ ≡ pos op₂
  loopLift op .op (extra .op g) = FinSetPath (permutation g)

  Pos : Fattened → FinSet
  Pos = ∥-∥₃-rec isGroupoidFinSet (/ₜ-rec pos loopLift)
