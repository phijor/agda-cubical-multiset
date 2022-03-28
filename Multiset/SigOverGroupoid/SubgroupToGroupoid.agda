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
open import Cubical.HITs.PropositionalTruncation
  renaming
    ( rec to ∥-∥₀-rec
    ; map to ∥-∥₀-map
    )

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

FinSet≡ : {X Y : FinSet {ℓ}} → ⟨ X ⟩ ≡ ⟨ Y ⟩ → X ≡ Y
FinSet≡ = Σ≡Prop (λ _ → isProp-isFinSet)

module Fatten {ℓ ℓ' : Level} (X : Type ℓ) (E : X → Type ℓ') where

  data Fattened : Type (ℓ-max ℓ ℓ') where
    ⌜_⌝ : (pt : X) → Fattened
    loop : ∀ {pt} → (e : E pt) → ⌜ pt ⌝  ≡ ⌜ pt ⌝
    groupoidTrunc : isGroupoid Fattened

  rec : {B : Type ℓOp} → isGroupoid B
    → (f : X → B)
    → (pres-loop : ∀ {pt} (e : E pt) → f pt ≡ f pt)
    → (Fattened → B)
  rec _      f pres-loop ⌜ pt ⌝ = f pt
  rec _      f pres-loop (loop e i) = pres-loop e i
  rec isGpdB f pres-loop (groupoidTrunc F₁ F₂ p₁ p₂ sq₁ sq₂ i₁ i₂ i₃) =
    isGpdB _ _ _ _
      (λ i j → rec isGpdB f pres-loop (sq₁ i j))
      (λ i j → rec isGpdB f pres-loop (sq₂ i j))
      i₁ i₂ i₃

  isGroupoidFattened : isGroupoid Fattened
  isGroupoidFattened = groupoidTrunc

toGpdSig : SubgroupSignature ℓOp → GroupoidSignature ℓOp ℓ-zero
toGpdSig {ℓOp = ℓOp} Sig = groupoidsig Fattened isGroupoidFattened Pos where
  open SubgroupSignature Sig

  pos : Op → FinSet {ℓ = ℓ-zero}
  pos op = Fin (arity op) , isFinSetFin

  permutation : ∀ {op} → (g : ⟨ SymmGrp op ⟩) → pos op ≡ pos op
  permutation {op} (π , _) = FinSet≡ (ua π)

  open Fatten Op (λ op → ⟨ SymmGrp op ⟩)

  Pos : Fattened → FinSet
  Pos = rec isGroupoidFinSet pos permutation
