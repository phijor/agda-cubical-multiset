{-# OPTIONS --safe #-}

module Multiset.FCM.Logic where

open import Multiset.Prelude
open import Multiset.FCM.Base as M
open import Multiset.FCM.Properties as M
  -- hiding (isSingleton ; isSingleton-η ; isEmpty)

open import Cubical.Foundations.Equiv
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Structure
open import Cubical.Foundations.Function
open import Cubical.Foundations.Structure
open import Cubical.Functions.Logic as Logic
  renaming
    (¬_ to ¬ₚ_
    ; inl to ⊔-inl
    ; inr to ⊔-inr
    )
open import Cubical.HITs.PropositionalTruncation as PT
  using
    ( ∣_∣₁
    ; ∥_∥₁
    ; isPropPropTrunc
    )
open import Cubical.Data.Nat as ℕ
  using
    ( ℕ
    ; zero
    ; suc
    )
open import Cubical.Data.Unit as Unit
  using (Unit)
import Cubical.Data.Empty as Empty
open import Cubical.Data.Sum as Sum
  using
    ( _⊎_
    )
open import Cubical.Data.Sigma as Sigma
  using
    ( _×_
    )

open import Cubical.Relation.Nullary.Base
  using
  (¬_)

private
  variable
    ℓ ℓX ℓY : Level
    X : Type ℓX
    Y : Type ℓY

⊥* : hProp ℓ
⊥* = Empty.⊥* , λ ()

⊔*-identityˡ : (P : hProp ℓ) → _⊔_ {ℓ = ℓ} ⊥* P ≡ P
⊔*-identityˡ P =
  ⇒∶ (⊔-elim ⊥* P (λ _ → P) (λ ()) λ p → p)
  ⇐∶ ⊔-inr

any : (p : X → hProp ℓ) → M X → hProp ℓ
any p = M.rec isSetHProp ⊥* p _⊔_ ⊔*-identityˡ ⊔-assoc ⊔-comm

all : (p : X → hProp ℓ) → M X → hProp ℓ
all p = M.rec isSetHProp ⊤ p _⊓_ ⊓-identityˡ ⊓-assoc ⊓-comm

both : (p q : M X → hProp ℓ) → M X → hProp ℓ
both p q xs = p xs ⊓ q xs

module _ (p : X → hProp ℓ) where
  ¬any-ε : ¬ ⟨ any p ε ⟩
  ¬any-ε ()

  any-⊕ˡ : ∀ (xs ys : M X)
    → ⟨ any p xs ⟩
    → ⟨ any p (xs ⊕ ys) ⟩
  any-⊕ˡ _ _ p-xs = ⊔-inl p-xs

  any-⊕ʳ : ∀ xs ys
    → ⟨ any p ys ⟩
    → ⟨ any p (xs ⊕ ys) ⟩
  any-⊕ʳ _ _ p-ys = ⊔-inr p-ys

  ¬any-⊕ : ∀ {xs ys}
    → ¬ ⟨ any p xs ⟩
    → ¬ ⟨ any p ys ⟩
    → ¬ ⟨ any p (xs ⊕ ys) ⟩
  ¬any-⊕ {xs = xs} {ys = ys} ¬p-xs ¬p-ys = ⊔-elim (any p xs) (any p ys) (λ _ → ⊥) ¬p-xs ¬p-ys

  all-ε : ⟨ all p ε ⟩
  all-ε = Unit.tt*

  all-⊕ : ∀ {xs ys}
    → ⟨ all p xs ⟩
    → ⟨ all p ys ⟩
    → ⟨ all p (xs ⊕ ys) ⟩
  all-⊕ {xs = xs} {ys = ys} p-xs p-ys = p-xs , p-ys

  ¬all-⊕ˡ : ∀ {xs ys}
    → ¬ ⟨ all p xs ⟩
    → ¬ ⟨ all p (xs ⊕ ys) ⟩
  ¬all-⊕ˡ ¬p-xs = ¬p-xs ∘ fst

  ¬all-⊕ʳ : ∀ {xs ys}
    → ¬ ⟨ all p ys ⟩
    → ¬ ⟨ all p (xs ⊕ ys) ⟩
  ¬all-⊕ʳ ¬p-ys = ¬p-ys ∘ snd


-- syntax any (λ x → p) xs = ∃[ x ∈ xs ] p
-- syntax all (λ x → p) xs = ∀[ x ∈ xs ] p

-- Membership
module _ {ℓ : Level} {X : Type ℓ} where
  _∈ₚ_ : X → M X → hProp ℓ
  x ∈ₚ xs = any (x ≡ₚ_) xs -- ∃[ z ∈ xs ] x ≡ₚ z

  _∈_ : X → M X → Type ℓ
  x ∈ xs = ⟨ x ∈ₚ xs ⟩

  infix 80 _∈ₚ_ _∈_

  ∈-η : ∀ x → x ∈ η x
  ∈-η x = ∣ refl ∣₁

  ∈-⊕ˡ : ∀ (xs ys : M X) (x : X)
    → x ∈ xs
    → x ∈ (xs ⊕ ys)
  ∈-⊕ˡ xs ys x = any-⊕ˡ (x ≡ₚ_) xs ys

  ∈-⊕ʳ : ∀ (xs ys : M X) (x : X)
    → x ∈ ys
    → x ∈ (xs ⊕ ys)
  ∈-⊕ʳ xs ys x = any-⊕ʳ (x ≡ₚ_) xs ys


∈-map-η : ∀ {f : X → Y} {y} x
  → y ∈ map f (η x)
  → ⟨ y ≡ₚ f x ⟩
∈-map-η x p = p

[_⁻¹_]∈_ : ∀ {X Y : Type ℓ} → (f : X → Y) → (y : Y) → (xs : M X) → hProp ℓ
[ f ⁻¹ y ]∈ xs = any (λ x → y ≡ₚ f x) xs


-- ∈-map-fiber : ∀ {f : X → Y} {y : Y} {xs : M X}
--   → y ∈ map f xs
--   → ⟨ ∃[ x ] x ∈ₚ xs ⊓ y ≡ₚ f x ⟩
-- ∈-map-fiber {X = X} {f = f} {y} {xs} = ind {P = λ xs → y ∈ map f xs → ⟨ (∃[ x ] x ∈ₚ xs ⊓ y ≡ₚ f x) ⟩}
--   (λ xs → isPropΠ (λ h → isProp⟨⟩ (∃[ x ] x ∈ₚ xs ⊓ y ≡ₚ f x)))
--   empty* singl* union* xs
--   where
--     empty* : y ∈ map f ε → ⟨ ∃[ x ] x ∈ₚ ε ⊓ y ≡ₚ f x ⟩
--     empty* ()

--     singl* : ∀ x → y ∈ map f (η x) → ⟨ ∃[ x′ ] x′ ∈ₚ η x ⊓ y ≡ₚ f x′ ⟩
--     singl* x p = ∣ x , ∣ refl {x = x} ∣₁ , p ∣₁ where
--       _ : ∥ y ≡ f x ∥₁
--       _ = p

--     union* : ∀ {xs₁ xs₂ : M X}
--       → (y ∈ map f xs₁ → ⟨ ∃[ x ] x ∈ₚ xs₁ ⊓ y ≡ₚ f x ⟩)
--       → (y ∈ map f xs₂ → ⟨ ∃[ x ] x ∈ₚ xs₂ ⊓ y ≡ₚ f x ⟩)
--       → (y ∈ map f (xs₁ ⊕ xs₂) → ⟨ ∃[ x ] x ∈ₚ (xs₁ ⊕ xs₂) ⊓ y ≡ₚ f x ⟩)
--     union* {xs₁ = xs₁} {xs₂} p-xs₁ p-xs₂ = PT.rec (isPropPropTrunc) (Sum.elim ∈ˡ ∈ʳ)
--       where

--       ∈ˡ : (y ∈ map f xs₁) → ⟨ ∃[ x ] x ∈ₚ (xs₁ ⊕ xs₂) ⊓ y ≡ₚ f x ⟩
--       ∈ˡ = PT.map (λ (x , h∈ , h≡) → x , ∈-⊕ˡ xs₁ xs₂ x h∈ , h≡) ∘ p-xs₁

--       ∈ʳ : (y ∈ map f xs₂) → ⟨ ∃[ x ] x ∈ₚ (xs₁ ⊕ xs₂) ⊓ y ≡ₚ f x ⟩
--       ∈ʳ = PT.map (λ (x , h∈ , h≡) → x , ∈-⊕ʳ xs₁ xs₂ x h∈ , h≡) ∘ p-xs₂

⊕≡ε→ε⊔ε : ∀ {xs ys : M X}
  → xs ⊕ ys ≡ ε
  → ⟨ xs ≡ₚ ε ⊔ ys ≡ₚ ε ⟩
⊕≡ε→ε⊔ε {X = X} {xs = xs} {ys = ys} = M.ind {P = λ xs → ∀ ys → xs ⊕ ys ≡ ε → ⟨ xs ≡ₚ ε ⊔ ys ≡ₚ ε ⟩}
  (λ xs → isPropΠ2 λ ys h → isProp⟨⟩ (xs ≡ₚ ε ⊔ ys ≡ₚ ε))
  empty* singl* union* xs ys where
    empty* : ∀ ys → ε ⊕ ys ≡ ε → ⟨ ε ≡ₚ ε ⊔ ys ≡ₚ ε ⟩
    empty* ys indH = ⊔-inr ∣ subst (_≡ ε) (unit ys) indH ∣₁

    singl* : ∀ (x : X) (ys : M X) → η x ⊕ ys ≡ ε → ⟨ η x ≡ₚ ε ⊔ ys ≡ₚ ε ⟩
    singl* x ys h = Empty.rec (η⊕≢ε h)

    union* : ∀ {xs₁ xs₂}
      → (∀ ys → xs₁ ⊕ ys ≡ ε → ⟨ xs₁ ≡ₚ ε ⊔ ys ≡ₚ ε ⟩)
      → (∀ ys → xs₂ ⊕ ys ≡ ε → ⟨ xs₂ ≡ₚ ε ⊔ ys ≡ₚ ε ⟩)
      → ∀ ys
      → (xs₁ ⊕ xs₂) ⊕ ys ≡ ε
      → ⟨ (xs₁ ⊕ xs₂) ≡ₚ ε ⊔ ys ≡ₚ ε ⟩
    union* {xs₁} {xs₂} indH-xs₁ indH-xs₂ ys h = PT.map2 goal (indH-xs₁ ys h₁) (indH-xs₂ ys h₂) where
      h₁ : xs₁ ⊕ ys ≡ ε
      h₁ = no-zero-divisorsˡ (
          (xs₁ ⊕ ys) ⊕ xs₂ ≡⟨ sym (assoc _ _ _) ⟩
          xs₁ ⊕ (ys ⊕ xs₂) ≡⟨ cong (xs₁ ⊕_) (comm ys xs₂) ⟩
          xs₁ ⊕ (xs₂ ⊕ ys) ≡⟨ assoc _ _ _ ⟩
          (xs₁ ⊕ xs₂) ⊕ ys ≡⟨ h ⟩
          ε ∎
        )

      h₂ : xs₂ ⊕ ys ≡ ε
      h₂ = no-zero-divisorsʳ (
          xs₁ ⊕ (xs₂ ⊕ ys) ≡⟨ assoc _ _ _ ⟩
          (xs₁ ⊕ xs₂) ⊕ ys ≡⟨ h ⟩
          ε ∎
        )

      goal :
          ⟨ xs₁ ≡ₚ ε ⟩ ⊎ ⟨ ys ≡ₚ ε ⟩
        → ⟨ xs₂ ≡ₚ ε ⟩ ⊎ ⟨ ys ≡ₚ ε ⟩
        → ⟨ (xs₁ ⊕ xs₂) ≡ₚ ε ⟩ ⊎ ⟨ ys ≡ₚ ε ⟩
      goal (Sum.inl xs₁≡ε) (Sum.inl xs₂≡ε) = Sum.inl (PT.map2 subst-ε⊕ε≡ε xs₁≡ε xs₂≡ε)
      goal (Sum.inl xs₁≡ε) (Sum.inr ys≡ε)  = Sum.inr ys≡ε
      goal (Sum.inr ys≡ε)  _               = Sum.inr ys≡ε

-- map-⊕-fiber : ∀ {f : X → Y}
--   → (ys₁ ys₂ : M Y)
--   → (xs : M X)
--   → map f xs ≡ ys₁ ⊕ ys₂
--   → ⟨ ∃[ xs₁ ] ∃[ xs₂ ]
--       (xs₁ ⊕ xs₂) ≡ₚ xs
--       ⊓ map f xs₁ ≡ₚ ys₁
--       ⊓ map f xs₂ ≡ₚ ys₂
--     ⟩
-- map-⊕-fiber {f = f} ys₁ ys₂ = M.ind {P = λ xs → map f xs ≡ ys₁ ⊕ ys₂ → ⟨ _ ⟩}
--   (λ xs → isPropΠ λ h → isProp⟨⟩ _)
--   empty* {! !} {! !} where
--     empty* : ε ≡ ys₁ ⊕ ys₂ → ⟨ ∃[ xs₁ ] ∃[ xs₂ ] _ ⟩
--     empty* h = ∣ xs₁ , ∣ xs₂ , ∣ xs₁⊕xs₂≡ε ∣₁ , ∣ sym ys₁≡ε ∣₁ , ∣ sym ys₂≡ε ∣₁ ∣₁ ∣₁ where
--       xs₁ = ε
--       xs₂ = ε

--       xs₁⊕xs₂≡ε : xs₁ ⊕ xs₁ ≡ ε
--       xs₁⊕xs₂≡ε = unit ε

--       ys₁≡ε : ys₁ ≡ ε
--       ys₁≡ε = no-zero-divisorsˡ (sym h)

--       ys₂≡ε : ys₂ ≡ ε
--       ys₂≡ε = no-zero-divisorsʳ (sym h)

-- TODO: Remove facts about xor
-- _xorₚ_ : (P Q : hProp ℓ) → hProp ℓ
-- P xorₚ Q = ⟨ P ⟩ xor ⟨ Q ⟩ , isPropXor (str P) (str Q)

-- xorₚ-identityˡ : (P : hProp ℓ) → ⊥* xorₚ P ≡ P
-- xorₚ-identityˡ P = hProp≡ $ xor-identityˡ ⟨ P ⟩

-- xorₚ-comm : (P Q : hProp ℓ) → P xorₚ Q ≡ Q xorₚ P
-- xorₚ-comm P Q = hProp≡ $ xor-comm ⟨ P ⟩ ⟨ Q ⟩

-- xorₚ-assoc : (P Q R : hProp ℓ) → P xorₚ (Q xorₚ R) ≡ (P xorₚ Q) xorₚ R
-- xorₚ-assoc P Q R = hProp≡ $ xor-assoc ⟨ P ⟩ ⟨ Q ⟩ ⟨ R ⟩

module _ {ℓ} {X : Type ℓ} where
  _≡ₘ_ : M X → M X → hProp ℓ
  xs ≡ₘ ys = (xs ≡ ys) , isSetM xs ys

  -- isEmptyₚ : M X → hProp ℓ
  -- isEmptyₚ xs = ε ≡ₘ xs

  isEmptyₚ : M X → hProp ℓ
  isEmptyₚ = all (λ _ → ⊥*)

  isEmpty : M X → Type ℓ
  isEmpty xs = ⟨ isEmptyₚ xs ⟩

  isEmpty-ε : isEmpty ε
  isEmpty-ε = Unit.tt*

  ¬isEmpty-η : ∀ {x} → ¬ (isEmpty (η x))
  ¬isEmpty-η ()

  isEmpty→≡ε : ∀ {xs} → isEmpty xs → xs ≡ ε
  isEmpty→≡ε {xs = xs} = M.ind {P = λ xs → isEmpty xs → xs ≡ ε}
    (λ xs → isPropΠ λ h → isSetM xs ε) (λ _ → refl) (λ x ()) union* xs
    where
    union* : ∀ {xs ys}
      → (isEmpty xs → xs ≡ ε)
      → (isEmpty ys → ys ≡ ε)
      → ⟨ isEmptyₚ xs ⊓ isEmptyₚ ys ⟩ → xs ⊕ ys ≡ ε
    union* indH-xs indH-ys (isEmpty-xs , isEmpty-ys) = subst-ε⊕ε≡ε (indH-xs isEmpty-xs) (indH-ys isEmpty-ys)

  isEmpty-⊕ : ∀ {xs ys : M X}
    → isEmpty xs
    → isEmpty ys
    → isEmpty (xs ⊕ ys)
  isEmpty-⊕ {xs = xs} {ys = ys} empty-xs empty-ys = subst isEmpty ε=xs⊕ys isEmpty-ε where
    ε=xs⊕ys : ε ≡ xs ⊕ ys
    ε=xs⊕ys = sym $ subst-ε⊕ε≡ε (isEmpty→≡ε empty-xs) (isEmpty→≡ε empty-ys)

  ≡ε→isEmpty : ∀ {xs : M X} → xs ≡ ε → isEmpty xs
  ≡ε→isEmpty {xs = xs} = M.ind {P = λ xs → xs ≡ ε → isEmpty xs}
    (λ xs → isPropΠ λ h → isProp⟨⟩ (isEmptyₚ xs))
    (λ _ → isEmpty-ε)
    (λ _ → Empty.rec ∘ η≢ε)
    (λ {xs} {ys} indH-xs indH-ys xs⊕ys≡ε
      → isEmpty-⊕ {xs} {ys}
        (indH-xs (no-zero-divisorsˡ xs⊕ys≡ε))
        (indH-ys (no-zero-divisorsʳ xs⊕ys≡ε))
    )
    xs

  -- isSingleton : X → M X → Type ℓ
  -- isSingleton x ys = η x ≡ ys

  -- isSingletonₚ : X → M X → hProp ℓ
  -- isSingletonₚ x ys = η x ≡ₘ ys
  
  -- private
  --   TaggedHProp = M X × hProp ℓ

  -- isEitherExactUnionₚ : TaggedHProp → TaggedHProp → hProp ℓ
  -- isEitherExactUnionₚ (xs , Pxs) (ys , Pys) =
  --   (Pxs ⊓ isEmptyₚ ys) ⊔ (Pys ⊓ isEmptyₚ xs)

  -- _⊔ₑ_ : TaggedHProp → TaggedHProp → TaggedHProp
  -- P ⊔ₑ Q = P .fst ⊕ Q .fst , isEitherExactUnionₚ P Q

  -- isEitherExactUnionₚ-identityˡ : ∀ {xs : M X} → (P : hProp ℓ) → isEitherExactUnionₚ (ε , ⊥*) (xs , P) ≡ P
  -- isEitherExactUnionₚ-identityˡ {xs = xs} P =
  --     ⇒∶ ⊔-elim (⊥* ⊓ isEmptyₚ xs) (P ⊓ isEmptyₚ ε) (λ _ → P) (λ ()) fst
  --     ⇐∶ ⊔-inr ∘ (_, isEmpty-ε)

  -- isEitherExactUnionₚ-assoc : (P Q R : TaggedHProp) → (P ⊔ₑ (Q ⊔ₑ R)) .snd ≡ ((P ⊔ₑ Q) ⊔ₑ R) .snd
  -- isEitherExactUnionₚ-assoc P Q R =
  --   ⇒∶ {! !}
  --   ⇐∶ {! !}

  -- isEitherExactUnionₚ-comm : (P Q : TaggedHProp) → isEitherExactUnionₚ P Q ≡ isEitherExactUnionₚ Q P
  -- isEitherExactUnionₚ-comm (xs , P) (ys , Q) = ⊔-comm (P ⊓ isEmptyₚ ys) (Q ⊓ isEmptyₚ xs)

  -- isSingletonₚ : X → (xs : M X) → hProp ℓ
  -- isSingletonₚ x = M.elim (λ xs → isSetHProp) ⊥* (x ≡ₚ_)
  --   (λ {xs} {ys} singl-xs singl-ys → isEitherExactUnionₚ (xs , singl-xs) (ys , singl-ys))
  --   (λ {xs} singl-xs → isEitherExactUnionₚ-identityˡ {xs = xs} singl-xs)
  --   (λ {xs} {ys} {zs} singl-xs singl-ys singl-zs → isEitherExactUnionₚ-assoc (xs , singl-xs) (ys , singl-ys) (zs , singl-zs))
  --   (λ {xs} {ys} singl-xs singl-ys → isEitherExactUnionₚ-comm (xs , singl-xs) (ys , singl-ys))

  -- isSingleton : X → M X → Type ℓ
  -- isSingleton x xs = ⟨ isSingletonₚ x xs ⟩

  -- ¬isSingletonₚ-ε : ∀ {ys} → ¬ ⟨ isSingletonₚ ys ε ⟩
  -- ¬isSingletonₚ-ε {ys = ys} ()

  -- isSingletonSelf : ∀ x → isSingleton x (η x)
  -- isSingletonSelf x = ∣ refl {x = x} ∣₁

  -- isSingleton-η : ∀ x y → isSingleton x (η y) → η x ≡ η y
  -- isSingleton-η x y = PT.rec (isSetM (η x) (η y)) (cong η)

  -- isSingleton→η≡ : ∀ x {xs} → isSingleton x xs → η x ≡ xs
  -- isSingleton→η≡ x {xs = xs} = M.ind
  --   {P = λ xs → isSingleton x xs → η x ≡ xs}
  --   (λ xs → isPropΠ λ _ → isSetM (η x) xs)
  --   (Empty.rec ∘ ¬isSingletonₚ-ε)
  --   (isSingleton-η x)
  --   union*
  --   xs where

  --   union* : ∀ {xs ys}
  --     → (isSingleton x xs → η x ≡ xs)
  --     → (isSingleton x ys → η x ≡ ys)
  --     → (isSingleton x (xs ⊕ ys) → η x ≡ xs ⊕ ys)
  --   union* {xs} {ys} indH-xs indH-ys =
  --     ⊔-elim (isSingletonₚ x xs ⊓ isEmptyₚ ys) (isSingletonₚ x ys ⊓ isEmptyₚ xs) (λ _ → η x ≡ₘ (xs ⊕ ys)) left right
  --     where
  --       left : ⟨ isSingletonₚ x xs ⊓ isEmptyₚ ys ⟩ → η x ≡ (xs ⊕ ys)
  --       left (singl-xs , empty-ys) =
  --         η x     ≡⟨ sym $ unit' _ ⟩
  --         η x ⊕ ε ≡⟨ cong₂ _⊕_ (indH-xs singl-xs) (sym $ isEmpty→≡ε empty-ys) ⟩
  --         xs ⊕ ys ∎

  --       right : ⟨ isSingletonₚ x ys ⊓ isEmptyₚ xs ⟩ → η x ≡ (xs ⊕ ys)
  --       right (singl-ys , empty-xs) =
  --         η x     ≡⟨ sym $ unit _ ⟩
  --         ε ⊕ η x ≡⟨ cong₂ _⊕_ (sym $ isEmpty→≡ε empty-xs) (indH-ys singl-ys) ⟩
  --         xs ⊕ ys ∎

  -- η≡→isSingleton : (x : X) → ∀ {xs} → η x ≡ xs → isSingleton x xs
  -- η≡→isSingleton x {xs = xs} = M.ind {P = λ xs → η x ≡ xs → isSingleton x xs }
  --   (λ xs → isPropΠ λ _ → isProp⟨⟩ (isSingletonₚ x xs))
  --   (Empty.rec ∘ η≢ε)
  --   (λ y ηx≡ηy → {! !})
  --   {! !}
  --   xs

  -- hasSplitOfₚ : (p q : M X → hProp ℓ) → (M X → hProp ℓ)
  -- hasSplitOfₚ p q ys = ∃[ (ys₁ , ys₂) ∶ (M X × M X) ] (ys₁ ⊕ ys₂) ≡ₘ ys ⊓ (p ys₁) ⊓ (q ys₂)

  -- hasSplitOfₚ-⊕ : (p q : M X → hProp ℓ)
  --   → ∀ {ys₁ ys₂}
  --   → ⟨ p ys₁ ⟩
  --   → ⟨ q ys₂ ⟩
  --   → ⟨ hasSplitOfₚ p q (ys₁ ⊕ ys₂) ⟩
  -- hasSplitOfₚ-⊕ p q {ys₁} {ys₂} p-ys₁ q-ys₂ = ∣ (ys₁ , ys₂) , refl , p-ys₁ , q-ys₂ ∣₁

  -- hasSplitOfₚ-identityˡ : ∀ (p : M X → hProp ℓ) → hasSplitOfₚ isEmptyₚ p ≡ p
  -- hasSplitOfₚ-identityˡ p = funExt λ ys →
  --   ⇒∶ imp⇒ₚ ys
  --   ⇐∶ imp⇐ₚ ys where module _ (ys : _) where

  --   P : M X → Type ℓ
  --   P = ⟨_⟩ ∘ p

  --   imp⇒ : ∀ ys₁ ys₂
  --     → (ys₁ ⊕ ys₂) ≡ ys
  --     → isEmpty ys₁
  --     → P ys₂
  --     → P ys
  --   imp⇒ ys₁ ys₂ ys-split isEmpty-ys₁ p-ys₂ = goal where
  --     ys₂≡ys : ys₂ ≡ ys
  --     ys₂≡ys = (sym $ unit ys₂) ∙∙ cong (_⊕ ys₂) (sym $ isEmpty→≡ε isEmpty-ys₁) ∙∙ ys-split

  --     goal : ⟨ p ys ⟩
  --     goal = subst P ys₂≡ys p-ys₂

  --   imp⇒ₚ : ⟨ hasSplitOfₚ isEmptyₚ p ys ⟩ → ⟨ p ys ⟩
  --   imp⇒ₚ = PT.rec (isProp⟨⟩ (p ys))
  --       λ { ((ys₁ , ys₂) , (ys-split , isEmpty-ys₁ , p-ys₂))
  --         → imp⇒ ys₁ ys₂ ys-split isEmpty-ys₁ p-ys₂
  --         }

  --   imp⇐ₚ : ⟨ p ys ⟩ → ⟨ hasSplitOfₚ isEmptyₚ p ys ⟩
  --   imp⇐ₚ p-ys = ∣ (ε , ys) , unit ys , isEmpty-ε , p-ys ∣₁

  -- hasSplitOfₚ-comm : (p q : M X → hProp ℓ) → hasSplitOfₚ p q ≡ hasSplitOfₚ q p
  -- hasSplitOfₚ-comm p q = funExt λ ys →
  --   ⇒∶ commₚ ys p q
  --   ⇐∶ commₚ ys q p where module _ (ys : _) where

  --   commₚ : ∀ p q → ⟨ hasSplitOfₚ p q ys ⟩ → ⟨ hasSplitOfₚ q p ys ⟩
  --   commₚ p q = PT.map
  --     λ { ((ys₁ , ys₂) , (ys-split , p-ys₁ , q-ys₂))
  --     → (ys₂ , ys₁) , comm ys₂ ys₁ ∙ ys-split , q-ys₂ , p-ys₁
  --     }

  -- hasSplitOfₚ-assoc : (p q r : M X → hProp ℓ) → hasSplitOfₚ p (hasSplitOfₚ q r) ≡ hasSplitOfₚ (hasSplitOfₚ p q) r
  -- hasSplitOfₚ-assoc p q r = funExt λ ys →
  --   ⇒∶ imp⇒ₚ ys
  --   ⇐∶ imp⇐ₚ ys where module _ (ys : _) where

  --   reassoc-split⇒ : ∀ {ys zs ys₁ ys₂ ys₃ : M X}
  --     → ys₁ ⊕ zs ≡ ys
  --     → ys₂ ⊕ ys₃ ≡ zs
  --     → (ys₁ ⊕ ys₂) ⊕ ys₃ ≡ ys
  --   reassoc-split⇒ split-ys split-zs = (sym $ assoc _ _ _) ∙∙ cong (_ ⊕_) split-zs ∙∙ split-ys

  --   reassoc-split⇐ : ∀ {ys zs ys₁ ys₂ ys₃ : M X}
  --     → zs ⊕ ys₃ ≡ ys
  --     → ys₁ ⊕ ys₂ ≡ zs
  --     → ys₁ ⊕ ys₂ ⊕ ys₃ ≡ ys
  --   reassoc-split⇐ split-ys split-zs = assoc _ _ _ ∙∙ cong (_⊕ _) split-zs ∙∙ split-ys

  --   imp⇒ₚ : ⟨ hasSplitOfₚ p (hasSplitOfₚ q r) ys ⟩ → ⟨ hasSplitOfₚ (hasSplitOfₚ p q) r ys ⟩
  --   imp⇒ₚ = PT.rec (isProp⟨⟩ (hasSplitOfₚ (hasSplitOfₚ p q) r ys))
  --     λ { ((ys₁ , zs) , (ys-split , p-ys₁ , split-q-r-zs))
  --       → PT.map
  --         ( λ { ((ys₂ , ys₃) , (zs-split , q-ys₂ , r-ys₃))
  --           → (ys₁ ⊕ ys₂ , ys₃) , reassoc-split⇒ ys-split zs-split , hasSplitOfₚ-⊕ p q p-ys₁ q-ys₂ , r-ys₃
  --           }
  --         ) split-q-r-zs
  --       }

  --   imp⇐ₚ : ⟨ hasSplitOfₚ (hasSplitOfₚ p q) r ys ⟩ → ⟨ hasSplitOfₚ p (hasSplitOfₚ q r) ys ⟩
  --   imp⇐ₚ = PT.rec (isProp⟨⟩ (hasSplitOfₚ p (hasSplitOfₚ q r) ys))
  --     λ { ((zs , ys₃) , (ys-split , split-p-q-zs , r-ys₃))
  --       → PT.map
  --         ( λ { ((ys₁ , ys₂) , (zs-split , p-ys₁ , q-ys₂))
  --           → (ys₁ , ys₂ ⊕ ys₃) , (reassoc-split⇐ ys-split zs-split , p-ys₁ , hasSplitOfₚ-⊕ q r q-ys₂ r-ys₃)
  --           }
  --         ) split-p-q-zs
  --     }

  -- infix 4 _≈ₚ_ _≈_

  -- _≈ₚ_ : M X → M X → hProp ℓ
  -- _≈ₚ_ = M.rec (isSetΠ λ ys → isSetHProp)
  --   isEmptyₚ isSingletonₚ hasSplitOfₚ
  --   hasSplitOfₚ-identityˡ hasSplitOfₚ-assoc hasSplitOfₚ-comm

  -- _≈ₚ_ : M X → M X → hProp ℓ
  -- _≈ₚ_ = M.rec (isSetΠ λ ys → isSetHProp)
  --   isEmptyₚ isSingletonₚ hasSplitOfₚ
  --   hasSplitOfₚ-identityˡ hasSplitOfₚ-assoc hasSplitOfₚ-comm

  -- _≈_ : M X → M X → Type ℓ
  -- xs ≈ ys = ⟨ xs ≈ₚ ys ⟩

  -- isProp≈ : ∀ xs ys → isProp (xs ≈ ys)
  -- isProp≈ xs ys = isProp⟨⟩ (xs ≈ₚ ys)

  -- ≈-refl : {xs : M X} → xs ≈ xs
  -- ≈-refl {xs = xs} = M.ind (λ xs → isProp≈ xs xs) Unit.tt* isSingletonSelf union* xs where
  --   union* : ∀ {xs ys}
  --     → xs ≈ xs
  --     → ys ≈ ys
  --     → (xs ⊕ ys) ≈ (xs ⊕ ys)
  --   union* {xs} {ys} xs≈xs ys≈ys = ∣ (xs , ys) , refl , xs≈xs , ys≈ys ∣₁

  -- ≈-⊕-β : ∀ {xs ys zs} → ((xs ⊕ ys) ≈ zs) ≡ ⟨ hasSplitOfₚ (xs ≈ₚ_) (ys ≈ₚ_) zs ⟩
  -- ≈-⊕-β = refl

  -- decode : (xs ys : M X) → ⟨ xs ≈ₚ ys ⟩ → xs ≡ ys
  -- decode = M.ind {P = λ xs → ∀ ys → xs ≈ ys → xs ≡ ys} (λ xs → isPropΠ2 λ ys _ → isSetM xs ys) empty* singl* union* where
  --   empty* : ∀ ys → isEmpty ys → ε ≡ ys
  --   empty* ys = sym ∘ isEmpty→≡ε

  --   singl* : ∀ x ys → isSingleton x ys → η x ≡ ys
  --   singl* x ys = isSingleton→η≡ x

  --   union* : ∀ {xs ys}
  --      → (∀ zs → xs ≈ zs → xs ≡ zs)
  --      → (∀ zs → ys ≈ zs → ys ≡ zs)
  --      → (∀ zs → ⟨ hasSplitOfₚ (xs ≈ₚ_) (ys ≈ₚ_) zs ⟩ → (xs ⊕ ys) ≡ zs)
  --   union* {xs} {ys} indH-xs indH-ys zs = PT.rec (isSetM (xs ⊕ ys) zs) step where

  --     step :
  --       Σ[ (zs₁ , zs₂) ∈ (M X × M X) ] ⟨ (zs₁ ⊕ zs₂) ≡ₘ zs ⊓ (xs ≈ₚ zs₁) ⊓ (ys ≈ₚ zs₂) ⟩
  --       → xs ⊕ ys ≡ zs
  --     step ((zs₁ , zs₂) , zs-split , xs≈zs₁ , ys≈zs₂) = goal where
  --       xs≡zs₁ = indH-xs zs₁ xs≈zs₁
  --       ys≡zs₂ = indH-ys zs₂ ys≈zs₂

  --       goal : xs ⊕ ys ≡ zs
  --       goal = (cong₂ _⊕_ xs≡zs₁ ys≡zs₂) ∙ zs-split

  -- encode : (xs ys : M X) → xs ≡ ys → xs ≈ ys
  -- encode = M.ind {P = λ xs → ∀ ys → xs ≡ ys → xs ≈ ys}
  --   (λ xs → isPropΠ2 λ ys p → isProp≈ xs ys) empty* singl* union* where
  --   empty* : ∀ ys → ε ≡ ys → ε ≈ ys
  --   empty* ys p = ≡ε→isEmpty $ sym p

  --   singl* : ∀ x ys → η x ≡ ys → η x ≈ ys
  --   singl* x = M.ind {P = λ ys → η x ≡ ys → η x ≈ ys} (λ ys → isProp≈ _ ys) (lift ∘ η≢ε) {! !} {! !}

  --   union* : ∀ {xs₁ xs₂}
  --     → (∀ ys → xs₁ ≡ ys → xs₁ ≈ ys)
  --     → (∀ ys → xs₂ ≡ ys → xs₂ ≈ ys)
  --     → (∀ ys → (xs₁ ⊕ xs₂) ≡ ys → (xs₁ ⊕ xs₂) ≈ ys)
  --   union* {xs₁} {xs₂} _ _ _ ys-split = ∣ (xs₁ , xs₂) , ys-split , ≈-refl , ≈-refl {xs = xs₂} ∣₁

  -- MPath≃Code≈ : ∀ {xs ys} → (xs ≡ ys) ≃ (xs ≈ ys)
  -- MPath≃Code≈ {xs} {ys} = propBiimpl→Equiv (isSetM xs ys) (isProp≈ xs ys) (encode xs ys) (decode xs ys)

-- η-merely-inj : {x y : X} → η x ≡ η y → ∥ x ≡ y ∥₁
-- η-merely-inj {x = x} {y = y} ηx≡ηy = ∥x≡y∥ where
--   ηx≈ηy : η x ≈ η y
--   ηx≈ηy = encode (η x) (η y) ηx≡ηy

--   -- spiderman_neat.jpg
--   ∥x≡y∥ : ∥ x ≡ y ∥₁
--   ∥x≡y∥ = ηx≈ηy

-- η-inj : isSet X → {x y : X} → η x ≡ η y → x ≡ y
-- η-inj setX {x} {y} ηx≡ηy = equivFun (PT.propTruncIdempotent≃ (setX x y)) $ η-merely-inj ηx≡ηy
