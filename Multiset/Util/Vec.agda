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
open import Cubical.Data.Sigma.Base
import Cubical.Data.Empty.Base as Empty
open import Cubical.Data.Nat.Base as Nat using (ℕ ; suc ; zero)
open import Cubical.Data.Nat.Properties as Nat using (isSetℕ ; injSuc)
open import Cubical.Data.FinData as Fin using (Fin) renaming (zero to fzero ; suc to fsuc)
open import Cubical.Data.Unit.Properties using (isOfHLevelUnit*)
open import Cubical.Data.Vec.Base as Vec using (Vec ; [] ; _∷_)
open import Cubical.Relation.Nullary.Base using (¬_)
open import Cubical.Relation.Binary.Base using (Rel ; PropRel)
open import Cubical.Reflection.RecordEquiv using (declareRecordIsoΣ)
open import Cubical.HITs.PropositionalTruncation as PT using ()

record ΣVec {ℓ} (A : Type ℓ) : Type ℓ where
  constructor mk-vec
  pattern
  field
    {length} : ℕ
    vec : Vec A length

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
    ℓ : Level
    A B C : Type ℓ

pattern Σ[] = mk-vec []

infixr 9 _Σ∷_
_Σ∷_ : A → ΣVec A → ΣVec A
a Σ∷ as = mk-vec (a ∷ as .vec)

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

  data _∈_ {ℓ} {A : Type ℓ} (a : A) : {n : ℕ} → Vec A n → Type ℓ where
    here : ∀ {n} {as : Vec A n} → a ∈ (a ∷ as)
    there : ∀{n b} {as : Vec A n} → a ∈ as → a ∈ (b ∷ as)

  remove : ∀ {n} {a : A} (as : Vec A (suc n)) → a ∈ as → Vec A n
  remove (x ∷ xs) here = xs
  remove (y ∷ x ∷ xs) (there m) = y ∷ remove (x ∷ xs) m

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

isSetΣVec : ∀ {ℓ} {A : Type ℓ} → isSet A → isSet (ΣVec A)
abstract
  isSetΣVec {A = A} setA = isOfHLevelRetractFromIso 2 ΣVecIsoΣ isSetΣℕVec where
    isSetΣℕVec : isSet (Σ ℕ (Vec A))
    isSetΣℕVec = isSetΣ isSetℕ λ n → VecExt.isOfHLevelVec 0 n setA

_∈_ : ∀ {ℓ} {A : Type ℓ} (a : A) → (as : ΣVec A) → Type ℓ
a ∈ as = a VecExt.∈ as .vec

remove : ∀ {a : A} (as : ΣVec A) → a ∈ as → ΣVec A
remove {a = a} (mk-vec {suc l} as) m = mk-vec (VecExt.remove as m)

remove-length : ∀ {a : A} {as : ΣVec A} {n}
  → as .length ≡ suc n
  → (a∈as : a ∈ as)
  → remove as a∈as .length ≡ n
remove-length {as = mk-vec (_ ∷ _)} as-length _ = injSuc as-length

∈-map : ∀ {a as} (f : A → B) → a ∈ as → f a ∈ map f as
∈-map f VecExt.here = VecExt.here
∈-map f (VecExt.there m) = VecExt.there (∈-map f m)

map-remove : ∀ {a : A} {as} (f : A → B)
  → (a∈as : a ∈ as)
  → map f (remove as a∈as) ≡ remove (map f as) (∈-map f a∈as)
map-remove {as = mk-vec (x ∷ _)} f VecExt.here = refl
map-remove {as = mk-vec (x ∷ _ ∷ _)} f (VecExt.there a∈as) = cong (f x Σ∷_) (map-remove f a∈as)

¬∈-length-zero : ∀ {a : A} {as : ΣVec A} → as .length ≡ 0 → ¬ a ∈ as
¬∈-length-zero {as = mk-vec (_ ∷ _)} as-length _ = Nat.snotz as-length

data Relator {ℓ ℓ'} {A B : Type ℓ} (R : A → B → Type ℓ')
  : ΣVec A → ΣVec B → Type (ℓ-max ℓ ℓ') where

  rnil : Relator R Σ[] Σ[]
  rcons : {a : A} {as : ΣVec A} {bs : ΣVec B}
    → (∃b : ∃[ b ∈ B ] (R a b × (Σ[ m ∈ (b ∈ bs) ] Relator R as (remove bs m))))
    → Relator R (a Σ∷ as) bs

module _ {ℓ ℓ'} {A B : Type ℓ} (R : Rel A B ℓ') where
  isPropRelator : ∀ {as} {bs} → isProp (Relator R as bs)

  abstract
    isPropRelator rnil rnil = refl
    isPropRelator (rcons ∃b₁) (rcons ∃b₂) = cong rcons (PT.isPropPropTrunc ∃b₁ ∃b₂)

  PropRelator : PropRel (ΣVec A) (ΣVec B) (ℓ-max ℓ ℓ')
  PropRelator = Relator R , λ as bs → isPropRelator {as} {bs}

  record RelatorElim {ℓP} (P : ∀ {m n} {as : Vec A m} {bs : Vec B n} → (Relator R (mk-vec as) (mk-vec bs)) → Type ℓP) : Type (ℓ-max ℓP (ℓ-max ℓ ℓ')) where
    no-eta-equality
    field
      is-prop : ∀ {as bs} (r : Relator R as bs) → isProp (P r)
      rnil* : P rnil
      rcons* : ∀ {n} {a} {as : Vec A n} {bs}
        → (b : B)
        → (aRb : R a b)
        → (b∈bs : b ∈ bs)
        → (rel-remove : Relator R (mk-vec as) (remove bs b∈bs))
        → P rel-remove
        → P (rcons PT.∣ b , aRb , b∈bs , rel-remove ∣₁)

    elim-wf : ∀ {m n} {as : Vec A m} {bs : Vec B n} → (r : Relator R (mk-vec as) (mk-vec bs)) → P r
    elim-wf rnil = rnil*
    elim-wf {m = suc m} {as = (_ ∷ as)} {bs} (rcons ∃b) = PT.elim (is-prop ∘ rcons) (λ { (b , aRb , b∈bs , rel) → rcons* b aRb b∈bs rel (elim-wf rel) }) ∃b

    elim : ∀ {as : ΣVec A} {bs : ΣVec B} → (r : Relator R as bs) → P r
    elim {as = mk-vec as} {bs = mk-vec bs} = elim-wf {as = as} {bs = bs}

open import Cubical.Relation.Binary using (module BinaryRelation)
module _ (open BinaryRelation) {ℓ} {A : Type ℓ} {R : Rel A A ℓ} (is-refl : isRefl R) where
  open VecExt using (here ; there)
    
  isReflRelator : isRefl (Relator R)
  isReflRelator Σ[] = rnil
  isReflRelator (mk-vec (x ∷ xs)) = rcons PT.∣ x , is-refl x , here , isReflRelator (mk-vec xs) ∣₁

  Relator-∷-swap : ∀ a b {cs}
    → Relator R (a Σ∷ b Σ∷ cs) (b Σ∷ a Σ∷ cs)
  Relator-∷-swap a b = rcons PT.∣ a , is-refl a , there here , isReflRelator _ ∣₁

module _ {ℓ} {A A' B B' : Type ℓ}
  (R : Rel A B ℓ) (S : Rel A' B' ℓ)
  {f : A → A'} {g : B → B'}
  (f-rel : ∀ {a b} → R a b → S (f a) (g b)) where abstract
  Relator-map : ∀ {as bs}
    → Relator R as bs
    → Relator S (map f as) (map g bs)
  Relator-map {as} {bs} = RelatorElim.elim rec where
    open RelatorElim
    rec : RelatorElim R (λ {m n} {as} {bs} r → Relator S (map f (mk-vec as)) (map g (mk-vec bs)))
    rec .is-prop = λ _ → isPropRelator S
    rec .rnil* = rnil
    rec .rcons* b aRb b∈bs rel-remove cont = rcons PT.∣ g b , f-rel aRb , ∈-map g b∈bs , subst (Relator S _) (map-remove g b∈bs) cont ∣₁
