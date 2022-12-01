{-# OPTIONS --safe #-}

module Multiset.FCM.Limit where

open import Multiset.Prelude
open import Multiset.Util using (!_ ; isInjective)

open import Multiset.FCM.Base as M
open import Multiset.FCM.Properties as M
open import Multiset.FCM.Logic as M using (_∈_)

open import Multiset.Limit.Chain
open import Multiset.Limit.TerminalChain as TerminalChain
  hiding (cut ; pres)

open import Multiset.Omniscience using (LLPO)

open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Function using (_∘_)
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.HLevels

open import Cubical.Data.Unit as Unit using (Unit ; tt)
open import Cubical.Data.Sigma as Sigma using (_×_)
open import Cubical.Data.Sum as Sum using (_⊎_ ; inl ; inr)
open import Cubical.Data.Nat.Base hiding (_^_)
open import Cubical.Data.Bool.Base as Bool
  using (Bool ; if_then_else_ ; true ; false ; _and_ ; not)

open import Cubical.HITs.PropositionalTruncation as PT
  using
    ( ∥_∥₁
    ; ∣_∣₁
    )

open Limit using (elements ; is-lim)

instance
  FunctorM : Functor {ℓ-zero} M
  FunctorM .Functor.map = map
  FunctorM .Functor.map-id = mapId
  FunctorM .Functor.map-comp = mapComp

!^ : ∀ n → M ^ (suc n) → M ^ n
!^ n = M map-!^ n

shiftedLimitPath : ∀ {shlim₁ shlim₂} → (∀ n → shlim₁ .elements n ≡ shlim₂ .elements n) → shlim₁ ≡ shlim₂
shiftedLimitPath = isSet→LimitPathExt (shift (ch M)) (λ k → isSetM)

pres : M (Lim M) → ShLim M
pres = TerminalChain.pres M

infixr 6 _⊎₁_
_⊎₁_ : ∀ {ℓ ℓ'} → (A : Type ℓ) → (B : Type ℓ') → Type (ℓ-max ℓ ℓ')
A ⊎₁ B = ∥ A ⊎ B ∥₁

cut : (n : ℕ) → Lim M → M ^ n
cut = TerminalChain.cut M

module _ {ℓ} {X : Type ℓ} where
  ⟅_,_⟆ : X → X → M X
  ⟅ x , y ⟆ = η x ⊕ η y

  ⟅_,_⟆≡⟅_,_⟆ : (x y z w : X) → Type _
  ⟅ x , y ⟆≡⟅ z , w ⟆ = ∥ ((x ≡ z) × (y ≡ w)) ⊎ ((x ≡ w) × (y ≡ z)) ∥₁

  ⟅,⟆-comm : ∀ x y → ⟅ x , y ⟆ ≡ ⟅ y , x ⟆
  ⟅,⟆-comm x y = comm (η x) (η y)

diag : (ℕ → Lim M) → (n : ℕ) → M ^ n
diag z n = cut n (z n)

Complete : Type _
Complete = {x y₁ y₂ : Lim M}
  → (ys : ℕ → Lim M)
  → (p : ∀ n → (ys n ≡ y₁) ⊎ (ys n ≡ y₂))
  → (q : ∀ n → cut n x ≡ diag ys n)
  → (x ≡ y₁) ⊎₁ (x ≡ y₂)

isPropComplete : isProp Complete
isPropComplete =
  isPropImplicitΠ2 λ _ _ → isPropImplicitΠ λ _ → isPropΠ3 λ _ _ _ → PT.isPropPropTrunc

diag-ysᶜ-islim-alternating : ∀ {n} {a b : Lim M}
  → (x : Lim M)
  → (ys : ℕ → Lim M)
  → (∀ n → cut n x ≡ diag ys n)
  → (ys n ≡ a)
  → (ys (suc n) ≡ b)
  → !^ n (cut (suc n) a) ≡ cut n b
diag-ysᶜ-islim-alternating {n = n} {a} {b} x ys q ysₙ≡a ysₙ₊₁≡b =
  !^ n (cut (suc n) a)   ≡⟨ a .is-lim n ⟩
  cut n a                ≡⟨ cong (cut n) (sym ysₙ≡a) ⟩
  diag ys n              ≡⟨ sym (q n) ⟩
  cut n x                ≡⟨ sym (x .is-lim n) ⟩
  !^ n (cut (suc n) x)   ≡⟨ cong (!^ n) (q (suc n)) ⟩
  !^ n (diag ys (suc n)) ≡⟨ cong (!^ n ∘ cut (suc n)) ysₙ₊₁≡b ⟩
  !^ n (cut (suc n) b)   ≡⟨ b .is-lim n ⟩
  cut n b ∎

pres-inj⇒complete : isInjective pres → Complete
pres-inj⇒complete inj {x} {y₁} {y₂} ys p q = goal where

  ysᶜ : ℕ → Lim M
  ysᶜ n = Sum.elim (λ ysₙ≡y₁ → y₂) (λ ysₙ≡y₂ → y₁) (p n)

  p∧pᶜ : ∀ n → ⟅ ys n , ysᶜ n ⟆ ≡ ⟅ y₁ , y₂ ⟆
  p∧pᶜ n with p n
  ... | inl ysₙ≡y₁ = cong ⟅_, y₂ ⟆ ysₙ≡y₁
  ... | inr ysₙ≡y₂ = cong ⟅_, y₁ ⟆ ysₙ≡y₂ ∙ ⟅,⟆-comm y₂ y₁

  diag-ysᶜ-islim : ∀ n → !^ n (diag ysᶜ (suc n)) ≡ diag ysᶜ n
  diag-ysᶜ-islim n with (p (suc n)) | (p n)
  ... | inl ysₙ₊₁≡y₁ | inl ysₙ≡y₁ = y₂ .is-lim n
  ... | inl ysₙ₊₁≡y₁ | inr ysₙ≡y₂ = diag-ysᶜ-islim-alternating x ys q ysₙ≡y₂ ysₙ₊₁≡y₁
  ... | inr ysₙ₊₁≡y₂ | inl ysₙ≡y₁ = diag-ysᶜ-islim-alternating x ys q ysₙ≡y₁ ysₙ₊₁≡y₂
  ... | inr ysₙ₊₁≡y₂ | inr ysₙ≡y₂ = y₁ .is-lim n

  xᶜ : Lim M
  xᶜ .elements = diag ysᶜ
  xᶜ .is-lim = diag-ysᶜ-islim

  qᶜ : ∀ n → cut n xᶜ ≡ diag ysᶜ n
  qᶜ n with p n
  ... | inl _ = refl
  ... | inr _ = refl

  pres-diags-pair-path : pres ⟅ x , xᶜ ⟆ ≡ pres ⟅ y₁ , y₂ ⟆
  pres-diags-pair-path = shiftedLimitPath λ n →
    map (cut n) ⟅ x , xᶜ ⟆ ≡⟨⟩
    ⟅ cut n x , cut n xᶜ ⟆ ≡⟨ cong₂ ⟅_,_⟆ (q n) (qᶜ n) ⟩
    ⟅ diag ys n , diag ysᶜ n ⟆ ≡⟨⟩
    map (cut n) ⟅ ys n , ysᶜ n ⟆ ≡⟨ cong (map (cut n)) (p∧pᶜ n) ⟩
    map (cut n) ⟅ y₁   , y₂    ⟆ ∎

  diags-pair-path : ⟅ x , xᶜ ⟆ ≡ ⟅ y₁ , y₂ ⟆
  diags-pair-path = inj ⟅ x , xᶜ ⟆ ⟅ y₁ , y₂ ⟆ pres-diags-pair-path

  goal : ∥ (x ≡ y₁) ⊎ (x ≡ y₂) ∥₁
  goal = PT.rec PT.isPropPropTrunc (Sum.elim (PT.map inl) (PT.map inr)) x∈⟅y₁,y₂⟆ where
    x∈⟅x,xᶜ⟆ : x ∈ ⟅ x , xᶜ ⟆
    x∈⟅x,xᶜ⟆ = ∣ inl ∣ refl {x = x} ∣₁ ∣₁

    x∈⟅y₁,y₂⟆ : x ∈ ⟅ y₁ , y₂ ⟆
    x∈⟅y₁,y₂⟆ = subst (x ∈_) diags-pair-path x∈⟅x,xᶜ⟆
