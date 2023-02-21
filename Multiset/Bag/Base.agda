{-# OPTIONS --safe #-}

module Multiset.Bag.Base where

open import Multiset.Bij as Bij

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Structure
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Function using (_∘_)

open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Isomorphism

open import Cubical.Functions.FunExtEquiv using (funExtDep)

open import Cubical.Data.FinSet using (FinSet)
open import Cubical.Data.Sigma as Σ
open import Cubical.Data.Nat as ℕ
  using (ℕ)

-- ⚠ WARNING: Load-bearing abstract block ⚠
--
-- Agda should under no circumstances be given the chance to
-- reduce the definition below.  For variables (x : Bij), the
-- term below *will* make Agda v2.6.2.2 loop forever.  Or at
-- least the last time it went on for more than 2h on a laptop.
--
-- The results at the end of this module, especially naturality
-- (isNaturalBagToteIso), can see through this abstract block.
-- They are defined carefully to not exhibit the loopy behaviour.
--
-- In a perfect world, unfolding would be controlled at use-site
-- (*ahem*, [1]), and these results could live in a module that
-- is not `Bag.Base`.
--
-- [1]: https://github.com/agda/agda/pull/6354
abstract
  Idx : Bij → Type ℓ-zero
  Idx = λ x → ⟨ Bij→FinSet x ⟩

  IdxEquiv : (x : Bij) → (Idx x) ≃ ⟨ Bij→FinSet x ⟩
  IdxEquiv x = idEquiv ⟨ Bij→FinSet x ⟩

Vect : ∀ {ℓ} → Type ℓ → Bij → Type ℓ
Vect X k = Idx k → X

module _ {ℓ} {X : Type ℓ} where
  VectIso : (x : Bij) → Iso (Vect X x) (⟨ equivFun Bij≃FinSet x ⟩ → X)
  VectIso x = equiv→Iso (IdxEquiv x) (idEquiv X)

  isOfHLevelVect : ∀ {k} (n : ℕ) → isOfHLevel n X → isOfHLevel n (Vect X k)
  isOfHLevelVect n hLevel = isOfHLevelΠ n (λ idx → hLevel)

Bag : ∀ {ℓ} → Type ℓ → Type ℓ
Bag X = Σ[ k ∈ Bij ] Vect X k

module _ {ℓ} {X : Type ℓ} where
  BagPathP : ∀ {m n : Bij}
    → (p : m ≡ n)
    → {v : Vect X m}
    → {w : Vect X n}
    → (q : PathP (λ i → Vect X (p i)) v w)
    → Path (Bag X) (m , v) (n , w)
  BagPathP p q i = p i , q i

  BagPathPExt : ∀ {m n : Bij}
    → (p : m ≡ n)
    → {v : Vect X m}
    → {w : Vect X n}
    → ({idx₀ : Idx m} {idx₁ : Idx n} (q : PathP (λ i → Idx (p i)) idx₀ idx₁) → v idx₀ ≡ w idx₁)
    → Path (Bag X) (m , v) (n , w)
  BagPathPExt p q = BagPathP p (funExtDep q)

  isGroupoidBag : isGroupoid X → isGroupoid (Bag X)
  isGroupoidBag gpdX = isGroupoidΣ isGroupoidBij (λ k → isOfHLevelVect {k = k} 3 gpdX)

private
  variable
    ℓX ℓY ℓZ : Level
    X : Type ℓX
    Y : Type ℓY
    Z : Type ℓZ

map : (f : X → Y) → (Bag X → Bag Y)
map f (k , members) = (k , f ∘ members)

mapId : (xs : Bag X) → map (λ x → x) xs ≡ xs
mapId xs = refl

map∘map : (f : X → Y) (g : Y → Z)
  → (xs : Bag X)
  → map g (map f xs) ≡ map (g ∘ f) xs
map∘map f g xs = refl

open Iso
open import Multiset.Tote.Base as Tote using (Tote)

abstract
  Bag-Tote-Iso : Iso (Bag X) (Tote X)
  Bag-Tote-Iso = Σ-cong-iso (equivToIso Bij≃FinSet) VectIso

Bag≃Tote : Bag X ≃ Tote X
Bag≃Tote = isoToEquiv Bag-Tote-Iso

isNaturalBagToteEquiv : (f : X → Y) → equivFun Bag≃Tote ∘ map f ≡ Tote.map f ∘ equivFun Bag≃Tote
abstract
  isNaturalBagToteEquiv f = refl
