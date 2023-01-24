{-# OPTIONS --safe #-}

module Multiset.Util.Vec where

open import Multiset.Prelude

open import Cubical.Foundations.Equiv using (invEquiv)
open import Cubical.Foundations.Function using (_∘_)
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism
open import Cubical.Data.Sigma.Base
open import Cubical.Data.Nat.Base as Nat using (ℕ ; suc ; zero)
open import Cubical.Data.FinData as Fin using (Fin) renaming (zero to fzero ; suc to fsuc)
open import Cubical.Data.Unit.Base using (Unit*)
open import Cubical.Data.Unit.Properties using (isOfHLevelUnit* ; isContrUnit*)
open import Cubical.Data.Vec.Base as Vec using (Vec ; _∷_ ; [])
open import Cubical.Data.Vec.Properties as Vec renaming (module VecPath to VecPath')
open import Cubical.HITs.PropositionalTruncation as PT using (∥_∥₁ ; ∣_∣₁)
open import Cubical.Relation.Binary.Base using (Rel ; PropRel ; module BinaryRelation)

private
  variable
    ℓ : Level
    A B C : Type ℓ

open import Cubical.Data.Vec.Properties
  renaming
    ( FinVec→Vec to lookup⁻¹
    ; FinVec→Vec→FinVec to lookup-right-inv
    ; Vec→FinVec→Vec to lookup-left-inv
    ; module VecPath to VecPath'
    ) public

isOfHLevelVec : (h : HLevel) (n : ℕ)
                → isOfHLevel (suc (suc h)) A → isOfHLevel (suc (suc h)) (Vec A n)
isOfHLevelVec h zero ofLevelA [] [] =
  isOfHLevelRespectEquiv (suc h)
    (invEquiv (VecPath'.≡Vec≃codeVec [] []))
    (isOfHLevelUnit* (suc h))
isOfHLevelVec h (suc n) ofLevelA (x ∷ v) (x' ∷ v') =
  isOfHLevelRespectEquiv (suc h)
    (invEquiv (VecPath'.≡Vec≃codeVec _ _))
    (isOfHLevelΣ (suc h) (ofLevelA x x') (λ _ → isOfHLevelVec h n ofLevelA v v'))

isSetVec : ∀ {n} → isSet A → isSet (Vec A n)
isSetVec = isOfHLevelVec 0 _

vec-map-id : ∀ {n} → (xs : Vec A n) → Vec.map (λ x → x) xs ≡ xs
vec-map-id [] = refl
vec-map-id (x ∷ xs) = cong (x ∷_) (vec-map-id xs)

vec-map-comp : (g : B → C) (f : A → B) → ∀ {n} → (xs : Vec A n) → Vec.map (g ∘ f) xs ≡ Vec.map g (Vec.map f xs)
vec-map-comp g f [] = refl
vec-map-comp g f (x ∷ xs) = cong (g (f x) ∷_) (vec-map-comp g f xs)

isInjectiveSingleton : ∀ {ℓ} {A : Type ℓ} {x y : A} → x ∷ [] ≡ y ∷ [] → x ≡ y
isInjectiveSingleton singl-path = VecPath'.encode _ _ singl-path .fst

data _∈_ {ℓ} {A : Type ℓ} (a : A) : {n : ℕ} → Vec A n → Type ℓ where
  here : ∀ {n} {as : Vec A n} → a ∈ (a ∷ as)
  there : ∀{n b} {as : Vec A n} → a ∈ as → a ∈ (b ∷ as)

remove : ∀ {n} {a : A} (as : Vec A (suc n)) → a ∈ as → Vec A n
remove (x ∷ xs) here = xs
remove (y ∷ x ∷ xs) (there m) = y ∷ remove (x ∷ xs) m

remove-less : ∀ {n} {a a' : A} {as : Vec A (suc n)}
  → (a'∈as : a' ∈ as)
  → a ∈ remove as a'∈as → a ∈ as
remove-less {as = _ ∷ _ ∷ as} here p = there p
remove-less {as = _ ∷ _ ∷ as} (there _) here = here
remove-less {n = suc n} {as = _ ∷ _ ∷ as} (there p) (there q) = there (remove-less {n = n} p q)

remove-remove-less : ∀ {n} {a b : A} {as : Vec A (suc n)}
  → (a∈as : a ∈ as)
  → (b∈as-a : b ∈ remove as a∈as)
  → a ∈ remove as (remove-less a∈as b∈as-a)
remove-remove-less (here {as = _ ∷ _}) b∈as-a = here
remove-remove-less (there {as = _ ∷ _} a∈as) here = a∈as
remove-remove-less (there {as = as@(_ ∷ _)} a∈as) (there b∈as-a) = there (remove-remove-less {as = as} a∈as b∈as-a)

remove-there : ∀ {n} {a a' : A} {as : Vec A (suc n)}
  → (a'∈as : a' ∈ as)
  → remove (a ∷ as) (there a'∈as) ≡ a ∷ (remove as a'∈as)
remove-there here = refl
remove-there (there _) = refl

remove-par : ∀ {n} {a b : A} {as : Vec A (suc (suc n))}
  → (a∈as : a ∈ as)
  → (b∈as-a : b ∈ remove as a∈as)
  → let
      b∈as = remove-less a∈as b∈as-a
      a∈as-b = remove-remove-less a∈as b∈as-a
    in
      remove (remove as a∈as) b∈as-a ≡ remove (remove as b∈as) a∈as-b
remove-par (here {as = a ∷ as}) b∈as-a = refl {x = remove (a ∷ as) b∈as-a}
remove-par (there {as = a ∷ as} m) here = refl {x = remove (a ∷ as) m}
remove-par {n = suc n} (there {b = b} {as = as@(_ ∷ _ ∷ _)} m) (there k) =
  remove (b ∷ remove as m) (there k)                                        ≡⟨ remove-there {a = b} k ⟩
  b ∷ remove (remove as m) k                                                ≡⟨ cong (b ∷_) (remove-par m k) ⟩
  b ∷ remove (remove as (remove-less m k)) (remove-remove-less m k)         ≡⟨ sym (remove-there (remove-remove-less m k)) ⟩
  remove (_ ∷ remove as (remove-less m k)) (there (remove-remove-less m k)) ∎

module _ {A B : Type} where
  lookup-map : (f : A → B) → ∀ {n} (xs : Vec A n) k → Vec.lookup k (Vec.map f xs) ≡ f (Vec.lookup k xs)
  lookup-map f (x ∷ xs) (fzero) = refl {x = f x}
  lookup-map f (x ∷ xs) (fsuc k) = lookup-map f xs k

  lookup⁻¹-map : (f : A → B) → ∀ {n} (xs : Fin.FinVec A n) → Vec.map f (lookup⁻¹ xs) ≡ lookup⁻¹ (f ∘ xs)
  lookup⁻¹-map f {zero} xs = refl {x = []}
  lookup⁻¹-map f {suc n} xs = cong (f (xs fzero) ∷_) (lookup⁻¹-map f (xs ∘ fsuc))

isContrVec : ∀ {ℓ} {A : Type ℓ} {n} → isContr A → isContr (Vec A n)
isContrVec {A = A} contrA = center* , contr* where
  center* : ∀ {n} → Vec A n
  center* = Vec.replicate (contrA .fst)

  contr* : ∀ {n} (as : Vec A n) → center* ≡ as
  contr* [] = refl
  contr* (a ∷ as) = cong₂ _∷_ (contrA .snd a) (contr* as)

isContrVecUnit* : ∀ {ℓ} {n} → isContr (Vec {ℓ} Unit* n)
isContrVecUnit* = isContrVec isContrUnit*

module VecPath {ℓ} {A : Type ℓ} where
  open import Cubical.Data.Unit

  open import Multiset.Util.Square using (kiteFiller)

  Code : {n : ℕ} → (v v' : Vec A n) → Type ℓ
  Code [] [] = Unit*
  Code (a ∷ v) (a' ∷ v') = (a ≡ a') × Code v v'

  reflEncode : {n : ℕ} → (v : Vec A n) → Code v v
  reflEncode [] = tt*
  reflEncode (a ∷ v) = refl , (reflEncode v)

  encode : ∀ {n} → (v v' : Vec A n) → v ≡ v' → Code v v'
  encode {zero} [] [] _ = tt*
  encode {suc n} (a ∷ v) (a' ∷ v') p = (cong Vec.head p) , (encode v v' $ cong Vec.tail p)

  encodeRefl : ∀ {n} (v : Vec A n) → encode v v refl ≡ reflEncode v
  encodeRefl [] = refl
  encodeRefl (a ∷ v) = cong (refl ,_) (encodeRefl v)

  decode : {n : ℕ} → (v v' : Vec A n) → (r : Code v v') → (v ≡ v')
  decode [] [] _ = refl
  decode (a ∷ v) (a' ∷ v') (p , q) = cong₂ Vec._∷_ p (decode v v' q)

  decodeRefl : {n : ℕ} → (v : Vec A n) → decode v v (reflEncode v) ≡ refl
  decodeRefl [] = refl
  decodeRefl (a ∷ v) = cong (cong (a ∷_)) (decodeRefl v)

  ≡Vec-codeVec-Iso : {n : ℕ} → (v v' : Vec A n) → Iso (v ≡ v') (Code v v')
  ≡Vec-codeVec-Iso v v' .Iso.fun = encode v v'
  ≡Vec-codeVec-Iso v v' .Iso.inv = decode v v'
  ≡Vec-codeVec-Iso v v' .Iso.rightInv = sect v v' where
    sect : ∀ {n} (v v' : Vec A n) → section (encode v v') (decode v v')
    sect [] [] cnil = refl
    sect (a ∷ v) (a' ∷ v') (a≡a' , code-v≡v') = cong (a≡a' ,_) (sect v v' code-v≡v')
  ≡Vec-codeVec-Iso v v' .Iso.leftInv v≡v' =
    J (λ v' v≡v' → decode v v' (encode v v' v≡v') ≡ v≡v') (cong (decode _ _) (encodeRefl v) ∙ decodeRefl v) v≡v'

{-
module _ {ℓ ℓR} {A B : Type ℓ} (R : Rel A B ℓR) where
  data Relator∞ : {n : ℕ} → Rel (Vec A n) (Vec B n) (ℓ-max ℓ ℓR) where
    rnil∞ : Relator∞ [] []
    rcons∞ : ∀ {n} {a : A} {as : Vec A n} {bs : Vec B (suc n)}
      → (b : B)
      → R a b
      → (b∈bs : b ∈ bs)
      → Relator∞ as (remove bs b∈bs)
      → Relator∞ (a ∷ as) bs

  Relator : {n : ℕ} → Rel (Vec A n) (Vec B n) _
  Relator as bs = ∥ Relator∞ as bs ∥₁

  pattern rnil = ∣ rnil∞ ∣₁
  pattern rcons b aRb b∈bs rel = ∣ rcons∞ b aRb b∈bs rel ∣₁

module _ {ℓ ℓ'} {A B : Type ℓ} (R : Rel A B ℓ') {n : ℕ} where
  isPropRelator : {as : Vec A n} {bs : Vec B n} → isProp (Relator R as bs)
  isPropRelator = PT.isPropPropTrunc

  PropRelator : PropRel (Vec A n) (Vec B n) (ℓ-max ℓ ℓ')
  PropRelator = Relator R , λ as bs → isPropRelator {as} {bs}

module _ (open BinaryRelation) {ℓ ℓ′} {A : Type ℓ} {R : Rel A A ℓ′} (refl-≈ : isRefl R) where
  private
    variable
      n : ℕ

  isReflRelator∞ : isRefl (Relator∞ R {n})
  isReflRelator∞ [] = rnil∞
  isReflRelator∞ (x ∷ xs) = rcons∞ x (refl-≈ x) here (isReflRelator∞ xs)

  isReflRelator : isRefl (Relator R {n})
  isReflRelator = PT.∣_∣₁ ∘ isReflRelator∞

  Path→Relator∞ : {as bs : Vec A n}
    → as ≡ bs
    → Relator∞ R as bs
  Path→Relator∞ as≡bs = subst (Relator∞ _ _) as≡bs (isReflRelator∞ _)

  ∥Path∥→Relator : {as bs : Vec A n}
    → PT.∥ as ≡ bs ∥₁
    → Relator R as bs
  ∥Path∥→Relator = PT.map Path→Relator∞

  module _ {a a' : A} {as : Vec A n} (aRa' : R a a') where
    Relator∞-subst-head : Relator∞ R (a ∷ as) (a' ∷ as)
    Relator∞-subst-head = rcons∞ a' aRa' here (isReflRelator∞ _)

    Relator-subst-head : Relator R (a ∷ as) (a' ∷ as)
    Relator-subst-head = PT.∣ Relator∞-subst-head ∣₁

  Relator∞-cong-∷ : ∀ {a b} {as : Vec A n}
    → a ≡ b
    → Relator∞ R (a ∷ as) (b ∷ as)
  Relator∞-cong-∷ {a = a} {b} {as} a≡b = rcons∞ b (subst (R a) a≡b (refl-≈ a)) here (isReflRelator∞ as)

  Relator-cong-∷ : ∀ {a b} {as : Vec A n}
    → a ≡ b
    → Relator R (a ∷ as) (b ∷ as)
  Relator-cong-∷ a≡b = PT.∣ Relator∞-cong-∷ a≡b ∣₁

  Relator-∷-swap : ∀ a b {cs : Vec A n}
    → Relator R (a ∷ b ∷ cs) (b ∷ a ∷ cs)
  Relator-∷-swap a b = rcons a (refl-≈ a) (there here) (isReflRelator∞ _)
-}
