module Multiset.Tree.Coalgebra where
-- TODO: show that this defines a final coalgebra.

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.Structure

open import Multiset.Base
  using (M)
  renaming (map to mapM)

open import Multiset.Tree.Base

private
  variable
    ℓ ℓ' : Level

CoAlg : Type (ℓ-suc ℓ)
CoAlg {ℓ} = TypeWithStr ℓ (λ X → (X → M X))

mor : (A : CoAlg {ℓ}) → ⟨ A ⟩ → M ⟨ A ⟩
mor = str

CoAlgHom : CoAlg → CoAlg → Type
CoAlgHom X Y = Σ[ f ∈ (⟨ X ⟩ → ⟨ Y ⟩) ] ((x : ⟨ X ⟩) → mapM f (mor X x) ≡ mor Y (f x))

ωTree-CoAlg : CoAlg
ωTree-CoAlg = ωTree , η where open M

module Final where
  final-mor : (A : CoAlg) → CoAlgHom A ωTree-CoAlg
  final-mor A = (λ a → (λ n → {! mor A a  !}) , {!   !}) , {!   !}
