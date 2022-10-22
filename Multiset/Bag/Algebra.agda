module Multiset.Bag.Algebra where

open import Multiset.Bag.Base
  renaming (map to bagMap)
open import Multiset.Bag.Properties
  using
    ( module Unzip
    ; module Zip
    ; ωTree
    ; bagLimitIso
    ; bagChain
    ; UnorderedTree
    ; ωTreePathP
    ; !^
    )

open import Multiset.Chains
  using
    ( module Limit
    )
open import Multiset.Algebras.Base
open import Multiset.Util using (the-syntax)

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Function
  using (_∘_)
open import Cubical.Foundations.Transport
  using (pathToIso)

open import Cubical.Data.Nat.Base
open import Cubical.Data.Unit
open import Cubical.Data.Sigma
  using
    ( Σ-cong-iso-fst
    ; Σ-cong-snd
    )

private
  variable
    ℓ : Level

open Iso
open TypeFunctor

bagFunctor : TypeFunctor ℓ-zero
bagFunctor .fob = Bag
bagFunctor .fhom = bagMap

private
  B = bagFunctor

  open Coalgebra {F = B}
  open Algebra {F = B}

  open AlgebraCoalgebraMap {F = B}

  open Limit bagChain
    renaming
      ( Cone to bagChainCone
      ; universalPropertyIso to ωTreeUP
      )

zipCoalgebra : Coalgebra B
zipCoalgebra .cocarrier = ωTree
zipCoalgebra .comap = bagLimitIso .fun ∶ (ωTree → Bag ωTree)

isFinalZipCoalgebra : isFinal zipCoalgebra
isFinalZipCoalgebra = {! !}

zipAlgebra : Algebra B
zipAlgebra .carrier = ωTree
zipAlgebra .map = bagLimitIso .inv ∶ (Bag ωTree → ωTree)

isCorecursiveZipAlgebra : isCorecursive (zipAlgebra)
isCorecursiveZipAlgebra = goal where
  module _ (ω : Coalgebra B) where

    _⇒_ : Algebra B → Coalgebra B → Type _
    α ⇒ ω = AlgebraCoalgebraMap α ω

    open bagChainCone

    A : Type
    A = ω .cocarrier

    γ : A → Bag A
    γ = ω .comap

    mapIso : Iso (zipAlgebra ⇒ ω) Unit
    mapIso =
      zipAlgebra ⇒ ω                          Iso⟨ AlgebraCoalgebraMapIsoΣ {- (17) -} ⟩
      Σ[ f ∈ (A → ωTree) ] (in′ ∘ step f ≡ f) Iso⟨ Σ-cong-iso-fst ωTreeUP {- (18) -} ⟩
      Σ[ c ∈ bagChainCone A ] (Ψ (e c) ≡ e c) Iso⟨ pathToIso (Σ-cong-snd {! Ψ-Φ-comm !}) ⟩
      Σ[ c ∈ bagChainCone A ] (e c ≡ e (Φ c)) Iso⟨ {! !} ⟩
      Σ[ c ∈ bagChainCone A ] (c ≡ Φ c)       Iso⟨ {! !} ⟩
      Unit ∎Iso where

      e : bagChainCone A → (A → ωTree)
      e = ωTreeUP .inv

      in′ : Bag ωTree → ωTree
      in′ = bagLimitIso .inv
      P = bagMap

      step : ∀ {Y : Type} → (A → Y) → (A → Bag Y)
      step f = P f ∘ γ

      Ψ : (A → ωTree)
        → (A → ωTree)
      Ψ f = in′ ∘ step f

      module _ (c@(cone u comm) : bagChainCone A) where
        φ : (n : ℕ) → A → UnorderedTree n
        φ zero = λ _ → tt
        φ (suc n) = step (u n)

        φ-commutes : ∀ n → !^ n ∘ step (c .leg n) ≡ φ n
        φ-commutes zero = refl
        φ-commutes (suc n) =
          !^ (suc n) ∘ step (u (suc n)) ≡⟨⟩
          P (!^ n) ∘ P (u (suc n)) ∘ γ  ≡⟨⟩
          P (!^ n ∘ u (suc n)) ∘ γ  ≡⟨ cong (λ f → P f ∘ γ) (comm n) ⟩
          P (u n) ∘ γ  ≡⟨⟩
          step (u n) ∎

      Φ : bagChainCone A → bagChainCone A
      Φ c .leg = φ c
      Φ c .commutes = φ-commutes c

      Ψ-Φ-comm : ∀ c → Ψ (e c) ≡ e (Φ c)
      Ψ-Φ-comm c = funExt λ (a : A) →
        ωTreePathP (λ n → {!refl !}) {! !}

    goal : isContr (zipAlgebra ⇒ ω)
    goal = isOfHLevelRetractFromIso 0 mapIso isContrUnit
