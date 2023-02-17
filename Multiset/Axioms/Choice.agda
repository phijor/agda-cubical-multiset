{-# OPTIONS --safe #-}

module Multiset.Axioms.Choice where

open import Multiset.Prelude

open import Cubical.Foundations.Equiv
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Function

open import Cubical.Data.Nat.Base
open import Cubical.Data.Unit.Base
open import Cubical.Data.Sigma.Base

open import Cubical.HITs.SetTruncation as ST using (∥_∥₂)
open import Cubical.HITs.PropositionalTruncation as PT using (∥_∥₁)
open import Cubical.HITs.Truncation.FromNegTwo.Base using (∥_∥_)

--- The Axiom of Choice
AC : (ℓA ℓB ℓR : Level) → Type (ℓ-suc (ℓ-max ℓA (ℓ-max ℓB ℓR)))
AC ℓA ℓB ℓR =
  ∀ {A : Type ℓA} {B : A → Type ℓB}
  → (R : (a : A) → (B a) → Type ℓR)
  → isSet A
  → (∀ a → isSet (B a))
  → (∀ a b → isProp (R a b))
  → (∀ a → ∥ Σ[ b ∈ B a ] R a b ∥₁)
  → ∥ Σ[ f ∈ ((a : A) → B a) ] (∀ a → R a (f a)) ∥₁

isPropAC : ∀ {ℓA ℓB ℓR} → isProp (AC ℓA ℓB ℓR)
isPropAC = isPropImplicitΠ2 λ A B → isPropΠ5 λ _ _ _ _ _ → PT.isPropPropTrunc

module _ {ℓA ℓB ℓR : Level} {A : Type ℓA} {B : A → Type ℓB}
  (R : (a : A) → (B a) → Type ℓR)
  (setA : isSet A)
  (setB : ∀ a → isSet (B a))
  (propR : ∀ a b → isProp (R a b))
  where

  hasAC : Type _
  hasAC = (∀ a → ∥ Σ[ b ∈ B a ] R a b ∥₁) → ∥ Σ[ f ∈ ((a : A) → B a) ] (∀ a → R a (f a)) ∥₁

-- The (n, m)-truncated Axiom of Choice, as stated in Exercise I.7.8, HoTT book:
AC[_,_] : (n m : ℕ) → (ℓA ℓB : Level) → Type _
AC[_,_] n m ℓA ℓB =
  ∀ (A : Type ℓA) (B : A → Type ℓB)
  → isSet A
  → isOfHLevelDep n B
  → ((a : A) → ∥ B a ∥ m)
  → ∥ ((a : A) → B a) ∥ m

-- An instanciated version of AC[ 2 , 1 ]:
AC[Set,Prop] : (ℓA ℓB : Level) → Type _
AC[Set,Prop] ℓA ℓB =
  ∀ (A : Type ℓA) (B : A → Type ℓB)
  → isSet A
  → (∀ a → isSet (B a))
  → ((a : A) → ∥ B a ∥₁)
  → ∥ ((a : A) → B a) ∥₁

isPropAC[Set,Prop] : ∀ {ℓA ℓB} → isProp (AC[Set,Prop] ℓA ℓB)
isPropAC[Set,Prop] = isPropΠ5 λ _ _ _ _ _ → PT.isPropPropTrunc

module _ {ℓA ℓB} where
  AC→AC[Set,Prop] : AC ℓA ℓB ℓ-zero → AC[Set,Prop] ℓA ℓB
  AC→AC[Set,Prop] ac A B setA setB f = PT.map (λ { (f , _) a → f a })
    (ac {A = A} {B = B} (λ a b → Unit) setA setB (λ { _ _ tt tt → refl }) λ a → PT.map (λ b → b , tt) (f a))

  AC[Set,Prop]→AC : AC[Set,Prop] ℓA ℓB → AC ℓA ℓB ℓ-zero
  AC[Set,Prop]→AC ac {A = A} {B = B} R setA setB propR f = PT.map (λ { g → (fst ∘ g) , snd ∘ g })
    (ac A (λ a → Σ[ b ∈ (B a) ] R a b) setA (λ a → isSetΣ (setB a) (λ b → isProp→isSet (propR a b))) f)

  -- AC[ 2 , 1 ] is equivalent to AC as defined AC:
  AC≃AC[Set,Prop] : AC ℓA ℓB ℓ-zero ≃ AC[Set,Prop] ℓA ℓB
  AC≃AC[Set,Prop] = propBiimpl→Equiv isPropAC isPropAC[Set,Prop] AC→AC[Set,Prop] AC[Set,Prop]→AC

-- An instanciated version of AC[ 3 , 2 ]:
AC[Gpd,Set] : (ℓA ℓB : Level) → Type _
AC[Gpd,Set] ℓA ℓB =
  ∀ (A : Type ℓA) (B : A → Type ℓB)
  → isSet A
  → (∀ a → isGroupoid (B a))
  → ((a : A) → ∥ B a ∥₂)
  → ∥ ((a : A) → B a) ∥₂

AC[Gpd,Set]-Rel : (ℓA ℓB ℓR : Level) → Type _
AC[Gpd,Set]-Rel ℓA ℓB ℓR =
  ∀ {A : Type ℓA} {B : A → Type ℓB}
  → (R : (a : A) → B a → Type ℓR)
  → isSet A
  → (∀ a → isGroupoid (B a))
  → (∀ a b → isProp (R a b))
  → ((a : A) → ∥ (Σ[ b ∈ B a ] R a b ) ∥₂)
  → ∥ Σ[ f ∈ ((a : A) → B a) ] ((a : A) → R a (f a)) ∥₂

AC[Gpd,Set]→AC[Gpd,Set]-Rel : ∀ {ℓA ℓB} → AC[Gpd,Set] ℓA ℓB → AC[Gpd,Set]-Rel ℓA ℓB ℓB
AC[Gpd,Set]→AC[Gpd,Set]-Rel ac {A = A} {B = B} R setA grpB propR f =
  ST.map (λ g → (fst ∘ g) , (snd ∘ g))
    (ac A (λ a → Σ[ b ∈ (B a) ] R a b) setA (λ a → isGroupoidΣ (grpB a) λ b → isProp→isOfHLevelSuc 2 (propR a b)) f)
