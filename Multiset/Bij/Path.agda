module Multiset.Bij.Path where

open import Multiset.Bij.Base as Bij

open import Multiset.Util.Square
  using
    ( ΣSquareP
    ; ΣSquarePProp
    )
open import Multiset.Util.Equiv
  using
    ( postComp
    ; postCompIdEquiv
    ; postCompCompEquiv
    )

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Equiv.Properties
open import Cubical.Foundations.Univalence
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Function using (_∘_)

open import Cubical.Foundations.Structure
open import Cubical.Syntax.⟨⟩

open import Cubical.Functions.FunExtEquiv
  using (funExtDep)

open import Cubical.Data.Sigma as Sigma
  using (Σ≡Prop ; ΣPathP)
open import Cubical.Data.Nat as ℕ
  using (ℕ)
open import Cubical.Data.SumFin as Fin
  using (Fin)

hSet₀ : Type₁
hSet₀ = hSet ℓ-zero

isSetFin≃ : (m n : ℕ) → isSet (Fin m ≃ Fin n)
isSetFin≃ m n = isOfHLevel≃ 2 (Fin.isSetFin) (Fin.isSetFin)

Fin≃ : (m n : ℕ) → hSet₀
Fin≃ m n = (Fin m ≃ Fin n) , isSetFin≃ m n

Fin≃Path : ∀ {m n : ℕ} (k : ℕ) → Fin m ≃ Fin n → Fin≃ k m ≡ Fin≃ k n
Fin≃Path {m = m} {n = n} k α = TypeOfHLevel≡ 2 path where
  path : (Fin k ≃ Fin m) ≡ (Fin k ≃ Fin n)
  path = ua (postComp α)

Fin≃PathId : (m n : ℕ) → Fin≃Path m (idEquiv (Fin n)) ≡ refl {x = Fin≃ m n}
Fin≃PathId m n = ΣSquarePProp (λ _ → isPropΠ2 (λ _ _ → isPropIsProp))
  (cong ua postCompIdEquiv ∙ uaIdEquiv)

Fin≃PathComp : ∀ {m n o : ℕ} (k : ℕ)
  → (α : Fin m ≃ Fin n)
  → (β : Fin n ≃ Fin o) →
      Fin≃Path k (α ∙ₑ β) ≡ Fin≃Path k α ∙ Fin≃Path k β
Fin≃PathComp k α β = ΣSquarePProp ((λ _ → isPropΠ2 (λ _ _ → isPropIsProp)))
  (cong ua (postCompCompEquiv α β) ∙ uaCompEquiv (postComp α) (postComp β))

Code : ℕ → Bij → hSet₀
Code m = rec (isOfHLevelTypeOfHLevel 2)
  (λ n → Fin≃ m n)
  (Fin≃Path m)
  (Fin≃PathId m)
  (Fin≃PathComp m)
