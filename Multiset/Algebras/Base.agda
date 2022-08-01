module Multiset.Algebras.Base where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
  using
    ( _∘_
    ; idfun
    )
open import Cubical.Reflection.RecordEquiv

private
  variable
    ℓ : Level
    X Y : Type ℓ

record TypeFunctor (ℓ : Level) : Type (ℓ-suc ℓ) where
  constructor functor
  field
    fob : Type ℓ → Type ℓ
    fhom : ∀ {X Y : Type ℓ}
      → (f : X → Y)
      → (fob X → fob Y)

  _ₒ_ = fob

  _ₕ_ = fhom

open TypeFunctor

-- TypeFunctorId : (F : TypeFunctor ℓ) → F ₕ (idfun X) ≡ idfun (F ₒ X)
-- TypeFunctorId F = {! !}

record Algebra (F : TypeFunctor ℓ) : Type (ℓ-suc ℓ) where
  field
    {carrier} : Type ℓ
    map : F ₒ carrier → carrier

record Coalgebra (F : TypeFunctor ℓ) : Type (ℓ-suc ℓ) where
  field
    {cocarrier} : Type ℓ
    comap : cocarrier → F ₒ cocarrier

record AlgebraMap {F : TypeFunctor ℓ} (α β : Algebra F) : Type (ℓ-suc ℓ) where
  open Algebra
  field
    hom : α .carrier → β .carrier
    nat-square :
      hom ∘ α .map ≡ β .map ∘ (F ₕ hom)

record CoalgebraMap {F : TypeFunctor ℓ} (ψ ω : Coalgebra F) : Type (ℓ-suc ℓ) where
  open Coalgebra
  field
    hom : ψ .cocarrier → ω .cocarrier
    nat-square :
      (F ₕ hom) ∘ ψ .comap ≡ ω .comap ∘ hom

record AlgebraCoalgebraMap
  {F : TypeFunctor ℓ}
  (α : Algebra F) (ω : Coalgebra F) : Type (ℓ-suc ℓ) where
  open Algebra
  open Coalgebra
    
  field
    hom : ω .cocarrier → α .carrier
    nat-square :
      α .map ∘ (F ₕ hom) ∘ ω .comap ≡ hom

unquoteDecl AlgebraCoalgebraMapIsoΣ = declareRecordIsoΣ AlgebraCoalgebraMapIsoΣ (quote AlgebraCoalgebraMap)

private
  variable
    F : TypeFunctor ℓ

isInitial : (α : Algebra F) → Type (ℓ-suc _)
isInitial α = ∀ β → isContr (AlgebraMap α β)

isFinal : (ω : Coalgebra F) → Type (ℓ-suc _)
isFinal ω = ∀ ψ → isContr (CoalgebraMap ψ ω)

isCorecursive : {F : TypeFunctor ℓ}
  → (α : Algebra F)
  → Type (ℓ-suc ℓ)
isCorecursive {F = F} α = ∀ ω → isContr (AlgebraCoalgebraMap α ω)
