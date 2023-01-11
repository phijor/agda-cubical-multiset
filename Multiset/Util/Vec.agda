{-# OPTIONS --safe #-}

module Multiset.Util.Vec where

open import Multiset.Prelude
open import Multiset.Limit.Chain
  using
    ( lim
    ; Limit
    ; Chain
    ; isSet→LimitPathExt
    ; isLimit
    ; isOfHLevelLimit
    )

open import Cubical.Foundations.Equiv using (invEquiv)
open import Cubical.Foundations.Function using (_∘_)
open import Cubical.Foundations.HLevels
open import Cubical.Data.Nat.Base as Nat using (ℕ ; suc ; zero)
open import Cubical.Data.Nat.Properties using (isSetℕ)
open import Cubical.Data.FinData as Fin using (Fin) renaming (zero to fzero ; suc to fsuc)
open import Cubical.Data.Unit.Properties using (isOfHLevelUnit*)
open import Cubical.Data.Vec.Base as Vec using (Vec ; [] ; _∷_)
open import Cubical.Reflection.RecordEquiv using (declareRecordIsoΣ)

record ΣVec {ℓ} (A : Type ℓ) : Type ℓ where
  constructor mk-vec
  field
    {length} : ℕ
    vec : Vec A length

Σ[] : ∀ {ℓ} {A : Type ℓ} → ΣVec A
Σ[] = mk-vec []

open ΣVec

unquoteDecl ΣVecIsoΣ = declareRecordIsoΣ ΣVecIsoΣ (quote ΣVec)

ΣVecPathP : ∀ {ℓ} {A : Type ℓ}
  → {xs ys : ΣVec A}
  → (p : xs .length ≡ ys .length)
  → PathP (λ i → Vec A (p i)) (xs .vec) (ys .vec)
  → xs ≡ ys
ΣVecPathP p q i = mk-vec {length = p i} (q i)

private
  variable
    A B C : Type

module VecExt where
  open import Cubical.Data.Vec.Properties
    using (module VecPath)
  open import Cubical.Data.Vec.Properties
    renaming
      ( FinVec→Vec to lookup⁻¹
      ; FinVec→Vec→FinVec to lookup-right-inv
      ; Vec→FinVec→Vec to lookup-left-inv
      ) public

  isOfHLevelVec : (h : HLevel) (n : ℕ)
                  → isOfHLevel (suc (suc h)) A → isOfHLevel (suc (suc h)) (Vec A n)
  isOfHLevelVec h zero ofLevelA [] [] =
    isOfHLevelRespectEquiv (suc h)
      (invEquiv (VecPath.≡Vec≃codeVec [] []))
      (isOfHLevelUnit* (suc h))
  isOfHLevelVec h (suc n) ofLevelA (x ∷ v) (x' ∷ v') =
    isOfHLevelRespectEquiv (suc h)
      (invEquiv (VecPath.≡Vec≃codeVec _ _))
      (isOfHLevelΣ (suc h) (ofLevelA x x') (λ _ → isOfHLevelVec h n ofLevelA v v'))

  isSetVec : ∀ {n} → isSet A → isSet (Vec A n)
  isSetVec = isOfHLevelVec 0 _

  vec-map-id : ∀ {n} → (xs : Vec A n) → Vec.map (λ x → x) xs ≡ xs
  vec-map-id [] = refl
  vec-map-id (x ∷ xs) = cong (x ∷_) (vec-map-id xs)

  vec-map-comp : (g : B → C) (f : A → B) → ∀ {n} → (xs : Vec A n) → Vec.map (g ∘ f) xs ≡ Vec.map g (Vec.map f xs)
  vec-map-comp g f [] = refl
  vec-map-comp g f (x ∷ xs) = cong (g (f x) ∷_) (vec-map-comp g f xs)

  module _ {A B : Type} where
    lookup-map : (f : A → B) → ∀ {n} (xs : Vec A n) k → Vec.lookup k (Vec.map f xs) ≡ f (Vec.lookup k xs)
    lookup-map f (x ∷ xs) (fzero) = refl {x = f x}
    lookup-map f (x ∷ xs) (fsuc k) = lookup-map f xs k

    lookup⁻¹-map : (f : A → B) → ∀ {n} (xs : Fin.FinVec A n) → Vec.map f (lookup⁻¹ xs) ≡ lookup⁻¹ (f ∘ xs)
    lookup⁻¹-map f {zero} xs = refl {x = []}
    lookup⁻¹-map f {suc n} xs = cong (f (xs fzero) ∷_) (lookup⁻¹-map f (xs ∘ fsuc))

map : (f : A → B) → ΣVec A → ΣVec B
map f (mk-vec xs) = mk-vec $ Vec.map f xs

map-id : ∀ xs → map (λ (x : A) → x) xs ≡ xs
map-id (mk-vec xs) = ΣVecPathP refl $ VecExt.vec-map-id xs

map-comp : (g : B → C) (f : A → B) → (xs : ΣVec A) → map (g ∘ f) xs ≡ map g (map f xs)
map-comp g f (mk-vec xs) = ΣVecPathP refl $ VecExt.vec-map-comp g f xs

isSetΣVec : ∀ {A} → isSet A → isSet (ΣVec A)
isSetΣVec setA = isOfHLevelRetractFromIso 2 ΣVecIsoΣ isSetΣℕVec where
  isSetΣℕVec : isSet (Σ ℕ (Vec _))
  isSetΣℕVec = isSetΣ isSetℕ λ n → VecExt.isOfHLevelVec 0 n setA
