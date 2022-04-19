module Multiset.SigOverGroupoid.SubgroupToGroupoid where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Univalence using (ua)
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Structure

open import Cubical.Data.SumFin.Base
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
    ℓ ℓOp ℓSymm : Level

FinSet→hSet : FinSet ℓ → hSet ℓ
FinSet→hSet (X , isFinSetX) = X , (isFinSet→isSet isFinSetX)

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
  rec {B = B} isGpdB f pres-loop (groupoidTrunc F₁ F₂ p₁ p₂ sq₁ sq₂ i j k) = cube i j k where

      rec-f : Fattened → B
      rec-f = rec isGpdB f pres-loop

      cube : Cube _ _ _ _ refl refl
      cube = isGpdB
        (rec-f F₁)
        (rec-f F₂)
        (cong rec-f p₁)
        (cong rec-f p₂)
        (cong (cong rec-f) sq₁)
        (cong (cong rec-f) sq₂)

  isGroupoidFattened : isGroupoid Fattened
  isGroupoidFattened = groupoidTrunc

toGpdSig : SubgroupSignature ℓOp ℓSymm
  → GroupoidSignature
    {- ℓSh = -} (ℓ-max ℓOp ℓSymm)
    {- ℓPos = -} ℓ-zero
toGpdSig {ℓOp = ℓOp} {ℓSymm = ℓSymm} Sig = groupoidsig Fattened isGroupoidFattened Pos where
  open SubgroupSignature Sig

  pos : Op → FinSet ℓ-zero
  pos op = Fin (arity op) , isFinSetFin

  permutation : ∀ {op} → (g : ⟨ SymmGrp op ⟩) → pos op ≡ pos op
  permutation {op} g = Σ≡Prop (λ _ → isPropIsFinSet) (ϕ g) where
    open PermutationGroup

    ϕ = (Symm op) .embedding .fst

  open Fatten Op (λ op → ⟨ SymmGrp op ⟩)

  Pos : Fattened → FinSet ℓ-zero
  Pos = rec isGroupoidFinSet pos permutation
