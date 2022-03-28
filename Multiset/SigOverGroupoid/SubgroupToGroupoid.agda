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

isGroupoidFinSet : isGroupoid (FinSet {ℓ})
isGroupoidFinSet {ℓ = ℓ} = isOfHLevelRespectEquiv 3 equiv isGroupoidFinSet' where
  open import Cubical.HITs.PropositionalTruncation
    renaming (rec to ∥-∥-rec)

  isFinSet→isSet : {X : Type ℓ} → isFinSet X → isSet X
  isFinSet→isSet {X = X} isFinSetX = ∥-∥-rec isPropIsSet FinEquiv→isSetX isFinSetX where

    FinEquiv→isSetX : Σ[ n ∈ ℕ ] (X ≃ Fin n) → isSet X
    FinEquiv→isSetX (n , α) = isOfHLevelRespectEquiv 2 (invEquiv α) isSetFin

    isFinSetΣX : isFinSetΣ X
    isFinSetΣX = transport isFinSet≡isFinSetΣ isFinSetX

  FinSet' : Type (ℓ-suc ℓ)
  FinSet' = Σ[ X ∈ (hSet ℓ) ] ∃[ n ∈ ℕ ] ⟨ X ⟩ ≃ Fin n

  isGroupoidFinSet' : isGroupoid FinSet'
  isGroupoidFinSet' = isOfHLevelΣ 3 (isOfHLevelTypeOfHLevel 2) (λ X → isProp→isOfHLevelSuc 2 isPropPropTrunc)

  equiv : FinSet' ≃ FinSet {ℓ}
  equiv = isoToEquiv (iso to from sect retr) where

    to : FinSet' → FinSet {ℓ}
    to (X , isFinX) = ⟨ X ⟩ , ∥-∥-rec isProp-isFinSet (λ (n , α) → ∣ n , α ∣) isFinX

    from : FinSet {ℓ} → FinSet'
    from (X , isFinSetX) = (X , isFinSet→isSet isFinSetX) , ∥-∥-rec isPropPropTrunc (λ (n , α) → ∣ n , α ∣) isFinSetX

    sect : section to from
    sect _ = Σ≡Prop (λ _ → isProp-isFinSet) refl

    retr : retract to from
    retr X = Σ≡Prop (λ _ → isPropPropTrunc) (Σ≡Prop (λ _ → isPropIsSet) refl)

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
