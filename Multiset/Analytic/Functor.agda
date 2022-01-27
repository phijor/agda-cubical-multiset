module Multiset.Analytic.Functor where

open import Cubical.Foundations.Prelude renaming (funExt⁻ to happly)
open import Cubical.Foundations.Structure
open import Cubical.Data.Nat.Base
open import Cubical.Data.Fin.Base
open import Cubical.Algebra.Group.Base

open import Cubical.HITs.TypeQuotients.Base

open import Multiset.GroupAction.Base
open import Multiset.GroupAction.Induced
open import Multiset.GroupAction.Orbit
open import Multiset.Analytic.Base

private
  variable
    ℓ ℓG ℓX ℓσ : Level

module Functor (Sig : Signature ℓσ ℓG) where
  module _ (X : Type ℓX) (σ : ⟨ Sig ⟩) where
    private
      open module Sig = SignatureStr (str Sig)

      Gσ : Group _
      Gσ = Action σ .fst

    coordAction : GroupAction (Sig.Action σ .fst) ℓX
    coordAction = Induced (permutationActionToAction (Action σ)) X

    --- Define the set of orbits X^σ/∼ where...
    ---
    --- * X is some type
    --- * X^σ is X to the power of the arity of an operation σ
    --- * ∼ is the orbit relation on X^σ under coordinate permutation,
    ---   as induced by G.
    _^_/∼ : Type (ℓ-max ℓG ℓX)
    _^_/∼ = Orbit coordAction

  _/∼ : {ℓX : Level} (X : Type ℓX) → Type _
  _/∼ {ℓX = ℓX} X = Σ[ σ ∈ ⟨ Sig ⟩ ] ( X ^ σ /∼ )

  private
    map-fin : {ℓX ℓY : Level} {X : Type ℓX} {Y : Type ℓY}
      → {n : ℕ}
      → (f : X → Y) (v : Fin n → X) → Fin n → Y
    map-fin f v k = f (v k)

  _^_/ₘ∼ : {ℓX ℓY : Level} {X : Type ℓX} {Y : Type ℓY}
    → (f : X → Y) (σ : ⟨ Sig ⟩)
    → X ^ σ /∼ → Y ^ σ /∼
  (f ^ σ /ₘ∼) [ v ] = [ map-fin f v ]
  _^_/ₘ∼ {X = X} {Y = Y} f σ (eq/ v w (g , g▸v≡w) i) = well-defined i
    where
      open SignatureStr (str Sig)

      Gσ : Group _
      Gσ = Action σ .fst

      Sσ : GroupAction Gσ ℓ-zero
      Sσ = permutationActionToAction (Action σ)

      open GroupStr (str Gσ)
      open GroupActionStr (str Sσ)
      open GroupActionStr (str (coordAction Y σ)) renaming (_▸_ to _▸Y_)

      aux : (s  : ⟨ Sσ ⟩) → (g ▸Y map-fin f v) s ≡ f (w s)
      aux s =
        ( (g ▸Y map-fin f v) s
            ≡⟨ refl ⟩
          f (v (inv g ▸ s))
            ≡⟨ cong f (happly g▸v≡w s) ⟩
          f (w s) ∎
        )

      well-defined : [ map-fin f v ] ≡ [ map-fin f w ]
      well-defined = eq/ _ _ (g , funExt aux)


module Example where
  open import Cubical.HITs.TypeQuotients.Base
  
  open import Multiset.GroupAction.Instances

  private
    arity : ℕ → ℕ
    arity n = n

  OrderedTreesSignature : Signature ℓ-zero ℓ-zero
  OrderedTreesSignature = ℕ , signaturestr arity UnitPermAction

  UnorderedTreesSignature : Signature ℓ-zero ℓ-zero
  UnorderedTreesSignature = ℕ , signaturestr arity SymPermAction

  open Functor UnorderedTreesSignature

  ex₁ : Type → Type
  ex₁ X =  X ^ 2 /∼

  ex₂ : (X : Type) (x₀ x₁ : X) → X /∼
  ex₂ X x₀ x₁ = 2 , [ v ]  where
    open import Cubical.Data.Nat.Order

    v : Fin 2 → X
    v (0 , _) = x₀
    v (1 , _) = x₁
    v (suc (suc k) , k' , p) = {! !}
