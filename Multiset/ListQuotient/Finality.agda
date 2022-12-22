{-# OPTIONS --safe #-}

module Multiset.ListQuotient.Finality where

open import Multiset.Prelude
open import Multiset.Limit.Chain using (lim ; Limit)
open import Multiset.Limit.TerminalChain as TerminalChain
  using (Functor ; Lim ; ShLim ; _^_ ; _map-!^_)
open import Multiset.ListQuotient.Base

open import Cubical.Foundations.Function using (_∘_)
import Cubical.Data.Empty as Empty
open import Cubical.Data.Nat.Base as Nat using (ℕ ; suc ; zero)
open import Cubical.Data.Nat.Properties using (snotz)
open import Cubical.Data.SumFin as Fin using (Fin ; fzero ; fsuc)
open import Cubical.Data.Unit.Base using (Unit*)
open import Cubical.Data.List as List
  using (List ; [] ; _∷_)

module ListExt where
  private
    variable
      ℓ : Level
      A : Type ℓ

  map-id : (xs : List A) → List.map (λ x → x) xs ≡ xs
  map-id [] = refl
  map-id (x ∷ xs) = cong (x ∷_) (map-id xs)

  map-comp : {X Y Z : Type ℓ}
    → (g : Y → Z) → (f : X → Y)
    → ∀ xs → List.map (g ∘ f) xs ≡ List.map g (List.map f xs)
  map-comp g f [] = refl
  map-comp g f (x ∷ xs) = cong (g (f x) ∷_) (map-comp g f xs)

  length-map : {A B : Type ℓ} → (f : A → B)
    → ∀ xs → List.length (List.map f xs) ≡ List.length xs
  length-map f [] = refl
  length-map f (x ∷ xs) = cong suc (length-map f xs)

  lookup : (xs : List A) → (k : Fin (List.length xs)) → A
  lookup (x ∷ xs) fzero = x
  lookup (x ∷ xs) (fsuc k) = lookup xs k

  enumerate' : {A B : Type ℓ}
    → (xs : List A)
    → (k : Fin (List.length xs))
    → (f : Fin (List.length xs) → A → B) → List B
  enumerate' [] k f = []
  enumerate' (x ∷ xs) k f = {! enumerate' xs (fsuc k) !}

  enumerate : {A B : Type ℓ}
    → (xs : List A) → (f : Fin (List.length xs) → A → B) → List B
  enumerate [] f = []
  enumerate (x ∷ xs) f = enumerate' (x ∷ xs) {! !} f

  safe-head : {A : Type ℓ} → (xs : List A) → {k : ℕ} → suc k ≡ List.length xs → A
  safe-head [] p = Empty.rec (snotz p)
  safe-head (x ∷ xs) p = x

  choice : {B : (n : ℕ) → Type ℓ}
    → (xs : (n : ℕ) → List (B n))
    → (len : ℕ)
    → (∀ n → len ≡ List.length (xs n))
    → List (∀ n → B n)
  choice xs zero const-len = []
  choice xs (suc len) const-len = (λ n → safe-head (xs n) (const-len n)) ∷ {! choice (xs ∘ suc) (len) const-len !}

instance
  FunctorList : Functor {ℓ-zero} List
  FunctorList .Functor.map = List.map
  FunctorList .Functor.map-id = ListExt.map-id
  FunctorList .Functor.map-comp = ListExt.map-comp

Tree : Type
Tree = Lim List

pres : List (Lim List) → ShLim List
pres = TerminalChain.pres List

width : ShLim List → (d : ℕ) → ℕ
width tree d = List.length $ tree .Limit.elements d

widthConstSuc : ∀ (tree : ShLim List) n → width tree n ≡ width tree (suc n)
widthConstSuc (lim tree is-lim) n =
    List.length (tree n)                                  ≡⟨ cong (List.length) (sym (is-lim n)) ⟩
    List.length (List.map (List map-!^ n) (tree (suc n))) ≡⟨ ListExt.length-map (List map-!^ n) (tree (suc n)) ⟩∎
    List.length (tree (suc n)) ∎

widthConst : ∀ (tree : ShLim List) n → width tree 0 ≡ width tree n
widthConst tree zero = refl
widthConst tree (suc n) = widthConst tree n ∙ widthConstSuc tree n

subtree : (tree : ShLim List) → (k : Fin (width tree 0)) → Lim List
subtree tree k .Limit.elements n = ListExt.lookup (tree .Limit.elements n) (subst Fin (widthConst tree n) k)
subtree tree k .Limit.is-lim n = {! tree .Limit.elements n  !}

pres⁻¹ : ShLim List → List (Lim List)
pres⁻¹ (lim approx is-lim) = {!approx !} where
  approx₀ : List Unit*
  approx₀ = approx 0

  approx-length : ∀ n → List.length (approx n) ≡ List.length (approx (suc n))
  approx-length n =
    List.length (approx n)                                  ≡⟨ cong (List.length) (sym (is-lim n)) ⟩
    List.length (List.map (List map-!^ n) (approx (suc n))) ≡⟨ ListExt.length-map (List map-!^ n) (approx (suc n)) ⟩∎
    List.length (approx (suc n)) ∎
