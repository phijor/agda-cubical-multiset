module Multiset.Limits where

open import Cubical.Core.Everything
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Path using (cong′)
open import Cubical.Foundations.Id using (ap)
open import Cubical.Foundations.Isomorphism renaming (Iso to _≅_)
open import Cubical.Data.Nat
open import Cubical.Data.Sigma

record ωCochain : Type₁ where
  field
    ob : ℕ → Type
    ∂ : (n : ℕ) → ob (suc n) → ob n

module ωCone (F : ωCochain) where

  record ωCone : Type₁ where
    open ωCochain
    field
      Apex : Type
      leg : (n : ℕ) → Apex → F .ob n
      cond : (n : ℕ) (v : Apex) → F .∂ n (leg (suc n) v) ≡ leg n v

  ωConeMap-commutes : (V W : ωCone) → (f : V .ωCone.Apex → W .ωCone.Apex) → Type
  ωConeMap-commutes V W f = (n : ℕ) → (v : V .ωCone.Apex) → W .ωCone.leg n (f v) ≡ V .ωCone.leg n v
  {-# INLINE ωConeMap-commutes #-}

  -- TODO: can we define this as a type alias for some sigma type and have nice aliases for .fst and .snd?
  record ωConeMap (V W : ωCone) : Type where
    open ωCone
    field
      map : V .Apex → W .Apex
      -- commutes : ωConeMap-commutes V W map
      commutes : (n : ℕ) → (v : V .Apex) → W .leg n (map v) ≡ V .leg n v

  open ωCone public
  open ωConeMap public

  ωConeMapToΣ : {V W : ωCone} → (f : ωConeMap V W) → Σ (V .Apex → W .Apex) λ m → (n : ℕ) → (v : V .Apex) → W .leg n (m v) ≡ V .leg n v
  ωConeMapToΣ f = f .map , f .commutes

  ωConeMap≅Σ : {V W : ωCone} → ωConeMap V W ≅ (Σ (V .Apex → W .Apex) λ m → (n : ℕ) → (v : V .Apex) → W .leg n (m v) ≡ V .leg n v)
  ωConeMap≅Σ = iso
    (λ f → ( f .map , f .commutes ))
    (λ ( map , commutes ) → record { map = map ; commutes = commutes })
    (λ _ → refl)
    (λ _ → refl)

  ωConeMapAux : (V W : ωCone) → Type
  ωConeMapAux V W = (Σ (V .Apex → W .Apex) λ m → (n : ℕ) → (v : V .Apex) → W .leg n (m v) ≡ V .leg n v)

  ωConeMap≡Σ : {V W : ωCone} → ωConeMap V W ≡ (Σ (V .Apex → W .Apex) λ m → (n : ℕ) → (v : V .Apex) → W .leg n (m v) ≡ V .leg n v)
  ωConeMap≡Σ = isoToPath ωConeMap≅Σ

  ≡ωConeMap : {V W : ωCone} → {f g : ωConeMap V W}
    → (
      Σ (f .map ≡ g .map)
      λ map≡ → (n : ℕ) → (v : V .Apex) →
        PathP (λ i → W .leg n (map≡ i v) ≡ V .leg n v) (f .commutes n v) (g .commutes n v) 
      )
    → f ≡ g
  ≡ωConeMap (≡map , ≡commutes) =
    λ i → record
      { map = ≡map i
      ; commutes = λ n v → ≡commutes n v i
      }

  open ωCochain
  ωConeMap≡Prop' : {V W : ωCone} → {f g : ωConeMapAux V W}
    → (FIsSet : (n : ℕ) → isSet (F .ob n))
    → (f .fst ≡ g .fst)
    → f ≡ g
  ωConeMap≡Prop' {V} {W} FIsSet map≡ = Σ≡Prop (λ h → isPropΠ2 λ n v → FIsSet n _ _) map≡

  ωConeMap≡Prop : {V W : ωCone} → {f g : ωConeMap V W}
    → (FIsSet : (n : ℕ) → let open ωCochain in isSet (F .ob n))
    → (f .map ≡ g .map)
    → f ≡ g
  ωConeMap≡Prop {V} {W} {f} {g} FIsSet map-≡ =
    isoFunInjective  ωConeMap≅Σ f g (ωConeMap≡Prop' {V} {W} FIsSet map-≡)
  
  is-Limit : (ωCone) → Type₁
  is-Limit L = (V : ωCone) → isContr (ωConeMap V L)
  