module Multiset.Limits where

open import Cubical.Core.Everything
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
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

  record ωConeMap (V W : ωCone) : Type where
    open ωCone
    field
      map : V .Apex → W .Apex
      commutes : ωConeMap-commutes V W map
      -- commutes : (n : ℕ) → (v : V .Apex) → W .leg n (map v) ≡ V .leg n v

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

  ωConeMap≡Σ : {V W : ωCone} → ωConeMap V W ≡ (Σ (V .Apex → W .Apex) λ m → (n : ℕ) → (v : V .Apex) → W .leg n (m v) ≡ V .leg n v)
  ωConeMap≡Σ = isoToPath ωConeMap≅Σ

  ≡ωConeMap : {V W : ωCone} → {f g : ωConeMap V W}
    → (
      Σ (f .map ≡ g .map)
      λ map≡ → (n : ℕ) → (v : V .Apex) → W .leg n {!   !} ≡ V .leg n v 
      )
    → f ≡ g
  ≡ωConeMap (≡map , ≡commutes) =
    λ i → record
      { map = ≡map i
      ; commutes = {!   !}
      }

  map-≡→≡ : {V W : ωCone} → {f g : ωConeMap V W} → (f .map ≡ g .map) → f ≡ g
  map-≡→≡ {V} {W} {f} {g} map-≡ = λ i → record
    { map = map-≡ i
    -- ; commutes = λ n v → J (λ f' f-map≡f' → {!   !}) {!   !} map-≡
    ; commutes = λ n v →
        let fc : W .leg n (map f v) ≡ V .leg n v
            fc = f .commutes n v in
        let gc : W .leg n (map g v) ≡ V .leg n v
            gc = g .commutes n v in
        let filler : f .commutes n v i ≡ g .commutes n v i
            filler = doubleCompPath-filler fc refl (sym gc) (~ i) in
        let sf = subst-filler (λ f' → W .leg n (f' v) ≡ V .leg n v) map-≡ fc in
        let sfi = sf i1 in
        {!   !}
    }
  
  is-Limit : (ωCone) → Type₁
  is-Limit L = (V : ωCone) → isContr (ωConeMap V L)
  