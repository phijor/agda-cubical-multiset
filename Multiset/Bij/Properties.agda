module Multiset.Bij.Properties where

open import Multiset.Bij.Base as Bij

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Univalence
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Path
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Function

open import Cubical.Data.Sigma
open import Cubical.Data.FinSet
open import Cubical.Data.SumFin as Fin
open import Cubical.Data.Nat as ℕ
  using
    ( ℕ
    )

open import Cubical.Functions.Embedding
open import Cubical.Functions.Surjection

open import Cubical.HITs.PropositionalTruncation as PT
  using ()
  renaming
    ( ∣_∣₁ to ∣_∣
    ; ∥_∥₁ to ∥_∥
    )

FinSet₀ : Type₁
FinSet₀ = FinSet ℓ-zero

Bij→FinSet : Bij → FinSet₀
Bij→FinSet = rec isGroupoidFinSet obj* hom* id-coh* comp-coh* where
  obj* : ℕ → FinSet₀
  obj* n = (Fin n) , isFinSetFin

  path* : ∀ {m n} → Fin m ≡ Fin n → obj* m ≡ obj* n
  path* = Σ≡Prop (λ A → isPropIsFinSet {A = A})

  isPropIsFinSetPath : ∀ {n} → (p q : isFinSet (Fin n)) → isProp (p ≡ q)
  isPropIsFinSetPath = isProp→isSet isPropIsFinSet

  path*-refl : ∀ {n} → path* (refl {x = Fin n}) ≡ refl {x = obj* n}
  path*-refl {n = n} = λ i j → Fin n , isPropIsFinSetPath _ _ (cong snd (path* refl)) refl i j

  path*-comp : ∀ {m n o}
    → (p : Fin m ≡ Fin n)
    → (q : Fin n ≡ Fin o)
    → path* (p ∙ q) ≡ path* p ∙ path* q
  path*-comp p q = cong ΣPathP
    ( ΣPathP
      ( refl
      , isProp→SquareP (λ _ _ → isPropIsFinSet) refl refl
        (cong snd (path* (p ∙ q)))
        (cong snd (path* p ∙ path* q))
      )
    )

  hom* : {m n : ℕ} → (α : Fin m ≃ Fin n) → obj* m ≡ obj* n
  hom* α = path* (ua α)

  id-coh* : ∀ n → hom* (idEquiv (Fin n)) ≡ refl
  id-coh* n =
    path* (ua (idEquiv (Fin n)))
      ≡⟨ cong path* uaIdEquiv ⟩
    path* refl
      ≡⟨ path*-refl ⟩
    refl
      ∎

  comp-coh* : ∀ {m n o : ℕ} (α : Fin m ≃ Fin n) (β : Fin n ≃ Fin o)
    → hom* (α ∙ₑ β) ≡ hom* α ∙ hom* β
  comp-coh* α β =
    path* (ua (α ∙ₑ β))
      ≡⟨ cong path* (uaCompEquiv α β) ⟩
    path* (ua α ∙ ua β)
      ≡⟨ path*-comp (ua α) (ua β) ⟩
    hom* α ∙ hom* β
      ∎

FinSet→Bij : FinSet₀ → Bij
FinSet→Bij (Y , n , ∣α∣) = obj n

FinSet→Bij-cong : ∀ {X Y : FinSet₀} → (p : X ≡ Y) → cong FinSet→Bij p ≡ hom {! (cong (fst ∘ snd) p)  !}
FinSet→Bij-cong p = {!   !}

sectionFinSetBij : ∀ x → FinSet→Bij (Bij→FinSet x) ≡ x
sectionFinSetBij = Bij.elimSet (λ _ → isSetBijPath) on-obj on-hom where
  on-obj : ∀ n → FinSet→Bij (Bij→FinSet (obj n)) ≡ obj n
  on-obj n = refl

  p : ∀ {m n : ℕ} (α : Fin m ≃ Fin n)
    → obj m ≡ obj n
  p α = (λ j → FinSet→Bij (Bij→FinSet (hom α j)))

  p' : ∀ {m n : ℕ} (α : Fin m ≃ Fin n) → Bij→FinSet (obj m) ≡ Bij→FinSet (obj n)
  p' α = (λ j → (Bij→FinSet (hom α j)))

  p'' : ∀ {m n : ℕ} (α : Fin m ≃ Fin n) → Bij→FinSet (obj m) ≡ Bij→FinSet (obj n)
  p'' {m = m} {n = n} α = λ j → (ua α j) , {!   !}

  prf : ∀ {m n : ℕ} (α : Fin m ≃ Fin n) → p' α ≡ p'' α
  prf α = cong ΣPathP (ΣPathP (refl ,
    (isProp→SquareP (λ i j → isPropIsFinSet) _ _ (isProp→PathP (λ z → isPropIsFinSet) isFinSetFin isFinSetFin) ((isProp→PathP (λ z → isPropIsFinSet) isFinSetFin isFinSetFin)))))

  on-hom' : ∀ {m n : ℕ}
    → (α : Fin m ≃ Fin n)
    → (p α) ≡ (hom α)
  on-hom' α = {!   !}

  on-hom : ∀ {m n : ℕ}
    → (α : Fin m ≃ Fin n)
    → Square
      (on-obj m)
      (on-obj n)
      (p α)
      (hom α)
  on-hom α = {!   !}



retractionFinSetBij : ∀ x → Bij→FinSet (FinSet→Bij x) ≡ x
retractionFinSetBij (Y , n , ∣α∣) = PT.elim→Set {P = λ α → Bij→FinSet (FinSet→Bij (Y , n , α)) ≡ (Y , n , α)}
  {!   !} (λ α → Σ≡Prop (λ _ → isPropIsFinSet) (sym (ua α))) isConst ∣α∣ where
    isConst : ∀ α β → Square
      (Σ≡Prop (λ _ → isPropIsFinSet) (sym (ua α)))
      (Σ≡Prop (λ _ → isPropIsFinSet) (sym (ua β)))
      (λ i → (Fin n , isFinSetFin))
      λ i → (Y , n , PT.squash ∣ α ∣ ∣ β ∣ i)
    isConst α β = {!  !}


open Iso

FinSet≅Bij : Iso FinSet₀ Bij
FinSet≅Bij .fun = FinSet→Bij
FinSet≅Bij .inv = Bij→FinSet
FinSet≅Bij .rightInv = sectionFinSetBij
FinSet≅Bij .leftInv = {!   !}
