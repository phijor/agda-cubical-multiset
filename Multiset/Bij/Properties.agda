{-# OPTIONS --safe #-}

module Multiset.Bij.Properties where

open import Multiset.Bij.Base as Bij
open import Multiset.Bij.Path as Bij
open import Multiset.Util.Square

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Equiv.Properties using (invEquivEquiv)
open import Cubical.Foundations.Univalence
  using
    ( ua
    ; uaIdEquiv
    ; uaCompEquiv
    ; univalence
    )
open import Cubical.Foundations.Transport using (subst⁻)
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism
  using
    ( Iso
    ; isoToEquiv
    )
open import Cubical.Foundations.Function using (_∘_)
open import Cubical.Foundations.Structure

open import Cubical.Data.Sigma using (Σ≡Prop)
open import Cubical.Data.FinSet
open import Cubical.Data.SumFin as Fin
open import Cubical.Data.Nat as ℕ
  using
    ( ℕ
    )

open import Cubical.Functions.Embedding using (isEmbedding)
open import Cubical.Functions.Surjection
  using
    ( isSurjection
    ; isEmbedding×isSurjection→isEquiv
    )

open import Cubical.HITs.PropositionalTruncation as PT
  using
    ( ∣_∣₁
    ; ∥_∥₁
    )

FinSet₀ : Type₁
FinSet₀ = FinSet ℓ-zero

private

  ⟦_⟧ : ℕ → FinSet₀
  ⟦ n ⟧ = (Fin n) , isFinSetFin

  -- Explicit version of isPropIsFinSet
  isPropIsFinSet′ : (A : Type) → isProp (isFinSet A)
  isPropIsFinSet′ A = isPropIsFinSet {A = A}

  module _ {m n : ℕ} where
    FinPath→FinSetPath : Fin m ≡ Fin n → ⟦ m ⟧ ≡ ⟦ n ⟧
    FinPath→FinSetPath = Σ≡Prop isPropIsFinSet′

    FinPath→FinSetPathCong : (p : ⟦ m ⟧ ≡ ⟦ n ⟧) → FinPath→FinSetPath (cong ⟨_⟩ p) ≡ p
    FinPath→FinSetPathCong p =
      FinPath→FinSetPath (cong ⟨_⟩ p)     ≡⟨⟩
      Σ≡Prop isPropIsFinSet′ (cong ⟨_⟩ p) ≡⟨ ΣSquarePProp isPropIsFinSet′ refl ⟩
      p ∎

    open Iso
    FinPath≅FinSetPath : Iso (Fin m ≡ Fin n) (⟦ m ⟧ ≡ ⟦ n ⟧)
    FinPath≅FinSetPath .fun = FinPath→FinSetPath
    FinPath≅FinSetPath .inv = cong ⟨_⟩
    FinPath≅FinSetPath .rightInv = FinPath→FinSetPathCong
    FinPath≅FinSetPath .leftInv = λ _ → refl

    FinPath≃FinSetPath : (Fin m ≡ Fin n) ≃ (⟦ m ⟧ ≡ ⟦ n ⟧)
    FinPath≃FinSetPath = isoToEquiv FinPath≅FinSetPath

  FinPath→FinSetPathRefl : ∀ {n} → FinPath→FinSetPath (refl {x = Fin n}) ≡ refl {x = ⟦ n ⟧}
  FinPath→FinSetPathRefl = ΣSquarePProp isPropIsFinSet′ refl

  FinPath→FinSetPathComp : ∀ {m n o}
    → (p : Fin m ≡ Fin n)
    → (q : Fin n ≡ Fin o)
    → FinPath→FinSetPath (p ∙ q) ≡ FinPath→FinSetPath p ∙ FinPath→FinSetPath q
  FinPath→FinSetPathComp p q = ΣSquarePProp isPropIsFinSet′ refl

Bij→FinSet : Bij → FinSet₀
Bij→FinSet = rec isGroupoidFinSet obj* hom* id-coh* comp-coh* where
  obj* : ℕ → FinSet₀
  obj* = ⟦_⟧

  path* : ∀ {m n} → Fin m ≡ Fin n → obj* m ≡ obj* n
  path* = FinPath→FinSetPath

  hom* : {m n : ℕ} → (α : Fin m ≃ Fin n) → obj* m ≡ obj* n
  hom* α = path* (ua α)

  id-coh* : ∀ n → hom* (idEquiv (Fin n)) ≡ refl
  id-coh* n =
    FinPath→FinSetPath (ua (idEquiv (Fin n))) ≡⟨ cong FinPath→FinSetPath uaIdEquiv ⟩
    FinPath→FinSetPath refl                   ≡⟨ FinPath→FinSetPathRefl ⟩
    refl ∎

  comp-coh* : ∀ {m n o : ℕ} (α : Fin m ≃ Fin n) (β : Fin n ≃ Fin o)
    → hom* (α ∙ₑ β) ≡ hom* α ∙ hom* β
  comp-coh* α β =
    FinPath→FinSetPath (ua (α ∙ₑ β)) ≡⟨ cong FinPath→FinSetPath (uaCompEquiv α β) ⟩
    FinPath→FinSetPath (ua α ∙ ua β) ≡⟨ FinPath→FinSetPathComp (ua α) (ua β) ⟩
    hom* α ∙ hom* β ∎

module _ {m n : ℕ} where
  Bij→FinSetCongHom : (α : Fin m ≃ Fin n) → cong Bij→FinSet (hom α) ≡ FinPath→FinSetPath (ua α)
  Bij→FinSetCongHom α = refl

  Bij→FinSetCong : (p : obj m ≡ obj n) → cong Bij→FinSet p ≡ FinPath→FinSetPath (ua (invEquiv (encode p)))
  Bij→FinSetCong p =
    cong Bij→FinSet p         ≡⟨ cong (cong Bij→FinSet) p≡hom[α] ⟩
    cong Bij→FinSet (hom α)   ≡⟨ Bij→FinSetCongHom α ⟩
    FinPath→FinSetPath (ua α) ≡⟨⟩
    FinPath→FinSetPath (ua (invEquiv (encode p))) ∎
    where
      α : Fin m ≃ Fin n
      α = invEquiv (encode p)

      p≡hom[α] : p ≡ hom α
      p≡hom[α] =
        p                         ≡⟨ sym (decode∘encode p) ⟩
        decode (obj n) (encode p) ≡⟨⟩
        sym (hom (encode p))      ≡⟨ sym (inv-coh _) ⟩
        hom (invEquiv (encode p)) ≡⟨⟩
        hom α ∎

  chainedEquiv : (obj m ≡ obj n) ≃ (⟦ m ⟧ ≡ ⟦ n ⟧)
  chainedEquiv = BijPath≃Fin≃ {m = m} ∙ₑ invEquivEquiv ∙ₑ (invEquiv univalence) ∙ₑ FinPath≃FinSetPath

  -- From (Bij→FinSetCong) we know that (cong Bij→FinSetCong) is equal (as a function)
  -- to the above chain of equivalence.
  -- By substitution, we deduce from this that (cong Bij→FinSet) is an equivalences too.
  isEquivBij→FinSetCong : isEquiv {A = obj m ≡ obj n} (cong Bij→FinSet)
  isEquivBij→FinSetCong = subst⁻ isEquiv (funExt Bij→FinSetCong) is-equiv' where
    is-equiv' : isEquiv (FinPath→FinSetPath ∘ ua ∘ invEquiv ∘ (encode {x = obj n}))
    is-equiv' = equivIsEquiv chainedEquiv

isEmbeddingBij→FinSet : isEmbedding Bij→FinSet
isEmbeddingBij→FinSet = elimProp2 (λ x y → isPropIsEquiv _) (λ m n → isEquivBij→FinSetCong)

isSurjectionBij→FinSet : isSurjection Bij→FinSet
isSurjectionBij→FinSet (Y , n , ∣α∣) = PT.elim {P = λ ∣α∣ → ∥ fiber Bij→FinSet (Y , n , ∣α∣) ∥₁}
  (λ _ → PT.isPropPropTrunc) inhFiber ∣α∣ where
  inhFiber : (α : Y ≃ Fin n) → ∥ fiber Bij→FinSet (Y , n , ∣ α ∣₁) ∥₁
  inhFiber α = ∣ (obj n) , (Σ≡Prop (λ _ → isPropIsFinSet) (sym (ua α))) ∣₁

Bij≃FinSet : Bij ≃ FinSet₀
Bij≃FinSet = Bij→FinSet , isEmbedding×isSurjection→isEquiv (isEmbeddingBij→FinSet , isSurjectionBij→FinSet)

FinSet→Bij : FinSet₀ → Bij
FinSet→Bij = invEq Bij≃FinSet
