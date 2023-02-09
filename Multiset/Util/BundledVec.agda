{-# OPTIONS --safe #-}

module Multiset.Util.BundledVec where

open import Multiset.Prelude
open import Multiset.Util.Vec as VecExt using (here ; there)

open import Cubical.Foundations.Function using (_∘_)
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Transport using (subst⁻)
open import Cubical.Data.Sigma.Base
open import Cubical.Data.Sigma.Properties as Sigma using ()
import Cubical.Data.Empty as Empty
open import Cubical.Data.Nat.Base as Nat using (ℕ ; suc ; zero)
open import Cubical.Data.Nat.Properties as Nat using (isSetℕ ; injSuc)
open import Cubical.Data.Unit.Base using (Unit*)
open import Cubical.Data.Unit.Properties using (isOfHLevelUnit* ; isContrUnit*)
open import Cubical.Data.Vec.Base as Vec using (Vec ; _∷_)
open import Cubical.Data.Vec.Properties using (module VecPath)
open import Cubical.Relation.Nullary.Base using (¬_)
open import Cubical.Relation.Binary.Base using (Rel ; PropRel)
open import Cubical.Reflection.RecordEquiv using (declareRecordIsoΣ)
open import Cubical.HITs.PropositionalTruncation as PT using ()

record ΣVec {ℓ} (A : Type ℓ) : Type ℓ where
  constructor #_
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
ΣVecPathP p q i = #_ {length = p i} (q i)

isOfHLevelΣVec : ∀ {ℓ} {A : Type ℓ}
  → (lvl : HLevel)
  → isOfHLevel (suc (suc lvl)) A
  → isOfHLevel (suc (suc lvl)) (ΣVec A)
isOfHLevelΣVec lvl is-lvl+2 = isOfHLevelRetractFromIso (suc (suc lvl)) ΣVecIsoΣ $
  isOfHLevelΣ (suc (suc lvl))
    (isOfHLevelPlus' {n = lvl} 2 isSetℕ)
    λ len → VecPath.isOfHLevelVec lvl len is-lvl+2

isSet→isSetΣVec : ∀ {ℓ} {A : Type ℓ} → isSet A → isSet (ΣVec A)
isSet→isSetΣVec = isOfHLevelΣVec 0

private
  variable
    ℓ : Level
    A B C : Type ℓ

pattern [] = # Vec.[]
pattern [_] a = # a Vec.∷ Vec.[]

infixr 9 _#∷_
infix 5 #_

_#∷_ : A → ΣVec A → ΣVec A
a #∷ as = # (a Vec.∷ as .vec)

mk-vec-inj : ∀ {n} {xs ys : Vec A n}
  → # xs ≡ # ys
  → xs ≡ ys
mk-vec-inj {A = A} {n = n} {xs} {ys} p = subst (λ · → PathP (λ i → Vec A (· i)) xs ys) (isSetℕ _ _ (cong length p) refl) (cong vec p)

ΣVecPath→lengthPath : {as bs : ΣVec A}
  → as ≡ bs → as .length ≡ bs .length
ΣVecPath→lengthPath p = cong length p

ΣVecPath→vecPath : ∀ {n} {as bs : Vec A n}
  → # as ≡ # bs → as ≡ bs
ΣVecPath→vecPath {A = A} {n = n} {as} {bs} p = goal where
  goal-dep : PathP (λ i → Vec A (p i .length)) as bs
  goal-dep = cong vec p

  goal : as ≡ bs
  goal = subst (λ p → PathP (λ i → Vec A (p i)) as bs) (isSetℕ _ _ (cong length p) refl) goal-dep

[]-#∷-disjoint : ∀ {a : A} {as : ΣVec A} → ¬ ([] ≡ a #∷ as)
[]-#∷-disjoint p = Nat.znots (cong length p)

isEmpty : ΣVec A → Type _
isEmpty as = as ≡ []

isSet→isPropIsEmpty : isSet A → {as : ΣVec A} → isProp (isEmpty as)
isSet→isPropIsEmpty setA = isSet→isSetΣVec setA _ _

isInjectiveCons : ∀ {a b : A} {as : ΣVec A} → a #∷ as ≡ b #∷ as → a ≡ b
isInjectiveCons p = cong Vec.head (ΣVecPath→vecPath p)

isInjectiveSingleton : ∀ {a b : A} → [ a ] ≡ [ b ] → a ≡ b
isInjectiveSingleton p = isInjectiveCons {as = []} p

isSingleton : (as : ΣVec A) → Type _
isSingleton {A = A} as = Σ[ a ∈ A ] as ≡ [ a ]

isSet→isPropIsSingleton : isSet A → {as : ΣVec A} → isProp (isSingleton as)
isSet→isPropIsSingleton setA {as = as} (a₁ , as≡a₁) (a₂ , as≡a₂) = Sigma.Σ≡Prop
  (λ a → isSet→isSetΣVec setA as [ a ])
  (isInjectiveSingleton $ sym as≡a₁ ∙ as≡a₂)

map : (f : A → B) → ΣVec A → ΣVec B
map f (# xs) = # Vec.map f xs

map-id : ∀ xs → map (λ (x : A) → x) xs ≡ xs
map-id (# xs) = ΣVecPathP refl $ VecExt.vec-map-id xs

map-comp : (g : B → C) (f : A → B) → (xs : ΣVec A) → map (g ∘ f) xs ≡ map g (map f xs)
map-comp g f (# xs) = ΣVecPathP refl $ VecExt.vec-map-comp g f xs

isSetΣVec : ∀ {ℓ} {A : Type ℓ} → isSet A → isSet (ΣVec A)
abstract
  isSetΣVec {A = A} setA = isOfHLevelRetractFromIso 2 ΣVecIsoΣ isSetΣℕVec where
    isSetΣℕVec : isSet (Σ ℕ (Vec A))
    isSetΣℕVec = isSetΣ isSetℕ λ n → VecExt.isOfHLevelVec 0 n setA


open Iso
ΣVecMapIso : ∀ {ℓ ℓ'} {A : Type ℓ} {B : Type ℓ'}
  → Iso A B
  → Iso (ΣVec A) (ΣVec B)
ΣVecMapIso isom .fun = map (isom .fun)
ΣVecMapIso isom .inv = map (isom .inv)
ΣVecMapIso isom .rightInv bs = sym (map-comp _ _ bs) ∙∙ cong (λ · → map · bs) (funExt (isom .rightInv)) ∙∙ map-id bs
ΣVecMapIso isom .leftInv as = sym (map-comp _ _ as) ∙∙ cong (λ · → map · as) (funExt (isom .leftInv)) ∙∙ map-id as

module _ {ℓ} {A : Type ℓ} (contrA : isContr A) where
  ΣVecContr-ℕ-Iso : Iso (ΣVec A) ℕ
  ΣVecContr-ℕ-Iso .fun = length
  ΣVecContr-ℕ-Iso .inv n .length = n
  ΣVecContr-ℕ-Iso .inv n .vec = Vec.replicate {n = n} (contrA .fst)
  ΣVecContr-ℕ-Iso .rightInv _ = refl
  ΣVecContr-ℕ-Iso .leftInv a = ΣVecPathP refl (VecExt.isContrVec contrA .snd (a .vec))

ΣVecUnit*-ℕ-Iso : ∀ {ℓ} → Iso (ΣVec {ℓ} Unit*) ℕ
ΣVecUnit*-ℕ-Iso = ΣVecContr-ℕ-Iso isContrUnit*

_∈_ : ∀ {ℓ} {A : Type ℓ} (a : A) → (as : ΣVec A) → Type ℓ
a ∈ as = a VecExt.∈ as .vec

remove : ∀ {a : A} (as : ΣVec A) → a ∈ as → ΣVec A
remove {a = a} (#_ {suc l} as) m = # VecExt.remove as m

remove-length : ∀ {a : A} {as : ΣVec A} {n}
  → as .length ≡ suc n
  → (a∈as : a ∈ as)
  → remove as a∈as .length ≡ n
remove-length {as = # (_ Vec.∷ _)} as-length _ = injSuc as-length

remove-there : ∀ {a a' : A} {as : ΣVec A}
  → (a∈as : a ∈ as)
  → remove (a' #∷ as) (there a∈as) ≡ a' #∷ (remove as a∈as)
remove-there {a} {a'} {as = # (_ ∷ as)} a∈as = cong #_ (VecExt.remove-there a∈as)

remove-less : ∀ {a a' : A} {as : ΣVec A}
  → (a'∈as : a' ∈ as)
  → a ∈ remove as a'∈as → a ∈ as
remove-less {as = # (_ ∷ _ ∷ _)} = VecExt.remove-less

remove-remove-less : ∀ {a b : A} {as : ΣVec A}
  → (a∈as : a ∈ as)
  → (b∈as-a : b ∈ remove as a∈as)
  → a ∈ remove as (remove-less a∈as b∈as-a)
remove-remove-less {as = # (_ ∷ _ ∷ _)} = VecExt.remove-remove-less

remove-par : ∀ {a b : A} {as : ΣVec A}
  → (a∈as : a ∈ as)
  → (b∈as-a : b ∈ remove as a∈as)
  → let
      b∈as = remove-less a∈as b∈as-a
      a∈as-b = remove-remove-less a∈as b∈as-a
    in
      remove (remove as a∈as) b∈as-a ≡ remove (remove as b∈as) a∈as-b
remove-par {as = # (_ ∷ _ ∷ _)} a∈as b∈as-a = cong #_ (VecExt.remove-par a∈as b∈as-a)

∈-map : ∀ {a as} (f : A → B) → a ∈ as → f a ∈ map f as
∈-map f VecExt.here = VecExt.here
∈-map f (VecExt.there m) = VecExt.there (∈-map f m)

∈-map-fiber : ∀ {f : A → B} {as : ΣVec A} {b : B}
  → b ∈ map f as
  → Σ[ a ∈ A ] (a ∈ as) × (f a ≡ b)
∈-map-fiber {as = # (a ∷ as)} here = a , here , refl
∈-map-fiber {as = # (_ ∷ as)} (there b∈f[as]) =
  let (a , a∈as , fa≡b) = ∈-map-fiber {as = # as} b∈f[as]
  in a , there a∈as , fa≡b


∈-map-fiber-Path : ∀ {f : A → B} {b : B} {as : ΣVec A}
  → (b∈f[as] : b ∈ map f as)
  → let (a , a∈as , fa≡b) = ∈-map-fiber b∈f[as]
    in PathP (λ i → (fa≡b i) ∈ map f as) (∈-map f a∈as) b∈f[as]
∈-map-fiber-Path {as = # (_ ∷ _)} here = refl {x = here}
∈-map-fiber-Path {as = # (_ ∷ _ ∷ _)} (there b∈f[as]) = congP (λ _ → there) (∈-map-fiber-Path b∈f[as])

map-remove : ∀ {a : A} {as : ΣVec A} (f : A → B)
  → (a∈as : a ∈ as)
  → map f (remove as a∈as) ≡ remove (map f as) (∈-map f a∈as)
map-remove {as = # x ∷ _} f VecExt.here = refl
map-remove {as = # x ∷ _ ∷ _} f (VecExt.there a∈as) = cong (f x #∷_) (map-remove f a∈as)

¬∈-length-zero : ∀ {a : A} {as : ΣVec A} → as .length ≡ 0 → ¬ a ∈ as
¬∈-length-zero {as = # _ ∷ _} as-length _ = Nat.snotz as-length

module _ {ℓ ℓR} {A B : Type ℓ} (R : Rel A B ℓR) where

  data Relator∞ : Rel (ΣVec A) (ΣVec B) (ℓ-max ℓ ℓR) where
    rnil∞ : Relator∞ [] []
    rcons∞ : {a : A} {as : ΣVec A} {bs : ΣVec B}
      → (b : B)
      → R a b
      → (b∈bs : b ∈ bs)
      → Relator∞ as (remove bs b∈bs)
      → Relator∞ (a #∷ as) bs

  Relator : Rel (ΣVec A) (ΣVec B) _
  Relator as bs = PT.∥ Relator∞ as bs ∥₁

  pattern rnil = PT.∣ rnil∞ ∣₁
  pattern rcons b aRb b∈bs rel = PT.∣ rcons∞ b aRb b∈bs rel ∣₁

module _ {ℓ ℓ'} {A B : Type ℓ} (R : Rel A B ℓ') where
  isPropRelator : ∀ {as} {bs} → isProp (Relator R as bs)
  isPropRelator = PT.isPropPropTrunc

  PropRelator : PropRel (ΣVec A) (ΣVec B) (ℓ-max ℓ ℓ')
  PropRelator = Relator R , λ as bs → isPropRelator {as} {bs}

open import Cubical.Relation.Binary using (module BinaryRelation)
module _ (open BinaryRelation) {ℓ ℓ′} {A : Type ℓ} {_≈_ : Rel A A ℓ′} (refl-≈ : isRefl _≈_) where
  open VecExt using (here ; there)

  isReflRelator∞ : isRefl (Relator∞ _≈_)
  isReflRelator∞ [] = rnil∞
  isReflRelator∞ (# x ∷ xs) = rcons∞ x (refl-≈ x) here (isReflRelator∞ (# xs))

  isReflRelator : isRefl (Relator _≈_)
  isReflRelator = PT.∣_∣₁ ∘ isReflRelator∞

  Path→Relator∞ : {as bs : ΣVec A}
    → as ≡ bs
    → Relator∞ _≈_ as bs
  Path→Relator∞ as≡bs = subst (Relator∞ _ _) as≡bs (isReflRelator∞ _)

  ∥Path∥→Relator : {as bs : ΣVec A}
    → PT.∥ as ≡ bs ∥₁
    → Relator _≈_ as bs
  ∥Path∥→Relator = PT.map Path→Relator∞

  module _ {a a' : A} {as : ΣVec A} (a≈a' : a ≈ a') where
    Relator∞-subst-head : Relator∞ _≈_ (a #∷ as) (a' #∷ as)
    Relator∞-subst-head = rcons∞ a' a≈a' here (isReflRelator∞ _)

    Relator-subst-head : Relator _≈_ (a #∷ as) (a' #∷ as)
    Relator-subst-head = PT.∣ Relator∞-subst-head ∣₁

  Relator∞-cong-∷ : ∀ {a b} {as}
    → a ≡ b
    → Relator∞ _≈_ (a #∷ as) (b #∷ as)
  Relator∞-cong-∷ {a} {b} {as} a≡b = rcons∞ b (subst (a ≈_) a≡b (refl-≈ a)) here (isReflRelator∞ as)

  Relator-cong-∷ : ∀ {a b} {as}
    → a ≡ b
    → Relator _≈_ (a #∷ as) (b #∷ as)
  Relator-cong-∷ a≡b = PT.∣ Relator∞-cong-∷ a≡b ∣₁

  Relator-∷-swap : ∀ a b {cs : ΣVec A}
    → Relator _≈_ (a #∷ b #∷ cs) (b #∷ a #∷ cs)
  Relator-∷-swap a b = rcons a (refl-≈ a) (there here) (isReflRelator∞ _)


module _ {ℓ ℓ′} {A B : Type ℓ} {R : Rel A B ℓ′} where
  ¬Relator-∷-[] : ∀ {a : A} {as : ΣVec A} → ¬ (Relator R (a #∷ as) [])
  ¬Relator-∷-[] = PT.rec Empty.isProp⊥ λ { (rcons∞ _ _ () _) }

  Relator-∷ : ∀ {a b} {as bs}
    → R a b
    → Relator∞ R as bs
    → Relator∞ R (a #∷ as) (b #∷ bs)
  Relator-∷ Rab rel = rcons∞ _ Rab here rel

  --- If (a ∈ as), and we know that as ≈[ R ] bs, then
  --- find the (b : B) such that (R a b).
  --- Additionally, return the fact that (as - a) ≈[ R ] (bs - b).
  Relator-find' : ∀ {a : A} {as : ΣVec A}
    → (a∈as : a ∈ as)
    → (bs : ΣVec B)
    → Relator∞ R as bs
    → Σ[ b ∈ B ] (R a b × (Σ[ b∈bs ∈ (b ∈ bs) ] Relator∞ R (remove as a∈as) (remove bs b∈bs)))
  Relator-find' here _ (rcons∞ b aRb b∈bs rel) = b , aRb , b∈bs , rel
  Relator-find' {a = a} {as = as@(# a′ ∷ as′)}
    (there a∈as) bs@(# b″ ∷ bs″)
    (rcons∞ {a = a′} b′ a′Rb′ b′∈bs as-Rel-bs-b′)
    with Relator-find' a∈as (remove bs b′∈bs) as-Rel-bs-b′
  ... | (b , aRb , b∈bs-b′ , as-a≈bs-b′-b) = b , aRb , b∈bs , goal where
    b∈bs : b ∈ bs
    b∈bs = remove-less b′∈bs b∈bs-b′

    b′∈bs-b : b′ ∈ remove bs b∈bs
    b′∈bs-b = remove-remove-less b′∈bs b∈bs-b′

    module rw where
      remove-bs : remove (remove bs b′∈bs) b∈bs-b′ ≡ remove (remove bs b∈bs) b′∈bs-b
      remove-bs = remove-par b′∈bs b∈bs-b′

      remove-as : remove as (there a∈as) ≡ a′ #∷ remove _ a∈as
      remove-as = remove-there a∈as

    step₁ : Relator∞ R (remove _ a∈as) (remove (remove bs b∈bs) b′∈bs-b)
    step₁ = subst (Relator∞ R _) rw.remove-bs as-a≈bs-b′-b

    step₂ : Relator∞ R (a′ #∷ remove _ a∈as) (remove bs b∈bs)
    step₂ = rcons∞ b′ a′Rb′ b′∈bs-b step₁

    goal : Relator∞ R (remove as (there a∈as)) (remove bs b∈bs)
    goal = subst⁻ (λ · → Relator∞ R · (remove bs b∈bs)) rw.remove-as step₂

  Relator∞-remove : ∀ {a : A} {b : B} {as : ΣVec A} {bs : ΣVec B}
    → (a∈as : a ∈ as)
    → (Rab : R a b)
    → Relator∞ R (remove as a∈as) bs
    → Relator∞ R as (b #∷ bs)
  Relator∞-remove here Rab rel = rcons∞ _ Rab here rel
  Relator∞-remove {bs = # b ∷ bs} (there {as = _ ∷ as} a∈as) Rab (rcons∞ b′ Ra′b′ b′∈b∷bs rel) =
    rcons∞ b′ Ra′b′ (there b′∈b∷bs) (Relator∞-remove a∈as Rab rel)

module _ {ℓ ℓ′} {A : Type ℓ} {R : Rel A A ℓ′} (open BinaryRelation) (trans-R : isTrans R) where
  infixl 9 _∙R_

  _∙R_ : ∀ {a b c : A} → R a b → R b c → R a c
  r ∙R s = trans-R _ _ _ r s

  Relator∞-trans : ∀ {as bs cs : ΣVec A}
    → Relator∞ R as bs
    → Relator∞ R bs cs
    → Relator∞ R as cs
  Relator∞-trans rnil∞ rnil∞ = rnil∞
  Relator∞-trans {as = # a ∷ as} {bs = # bs@(b′ ∷ bs′)} {cs = cs@(# c″ ∷ cs″)}
    (rcons∞ b aRb b∈bs′ as≈bs′-b) r@(rcons∞ _ _ _ _) =
    let
      (c , bRc , c∈cs , bs′-b≈cs-c) = Relator-find' b∈bs′ cs r
    in rcons∞ c (aRb ∙R bRc) c∈cs (Relator∞-trans as≈bs′-b bs′-b≈cs-c)

  Relator-trans : ∀ {as bs cs : ΣVec A}
    → Relator R as bs
    → Relator R bs cs
    → Relator R as cs
  Relator-trans = PT.map2 Relator∞-trans

  isTransRelator : isTrans (Relator R)
  isTransRelator _ _ _ = Relator-trans

module _ {ℓ} {A A' B B' : Type ℓ}
  (R : Rel A B ℓ) (S : Rel A' B' ℓ)
  {f : A → A'} {g : B → B'}
  (f-rel : ∀ {a b} → R a b → S (f a) (g b)) where abstract
  Relator∞-map : ∀ {as bs}
    → Relator∞ R as bs
    → Relator∞ S (map f as) (map g bs)
  Relator∞-map rnil∞ = rnil∞
  Relator∞-map (rcons∞ b aRb b∈bs rel-remove) =
    rcons∞
      (g b)
      (f-rel aRb)
      (∈-map g b∈bs)
      (subst (Relator∞ S _) (map-remove g b∈bs) (Relator∞-map rel-remove))

  Relator-map : ∀ {as bs}
    → Relator R as bs
    → Relator S (map f as) (map g bs)
  Relator-map = PT.map Relator∞-map

module Reasoning {ℓ ℓ'} {A : Type ℓ} (R : Rel A A ℓ') (open BinaryRelation) (refl-R : isRefl R) (trans-R : isTrans R) where
  private
    _≈_ = Relator R

  _Rel⟨_⟩_ : (as : ΣVec A) {bs cs : ΣVec A} → as ≈ bs → bs ≈ cs → as ≈ cs
  _ Rel⟨ r ⟩ s = Relator-trans trans-R r s

  _Rel∎ : (as : ΣVec A) → as ≈ as
  as Rel∎ = isReflRelator refl-R as

  infix  3 _Rel∎
  infixr 2 _Rel⟨_⟩_

module _ {ℓ ℓ′} {A : Type ℓ} {R : Rel A A ℓ′} (open BinaryRelation) (sym-R : isSym R) where
  isSymRelator∞ : isSym (Relator∞ R)
  isSymRelator∞ _ _ rnil∞ = rnil∞
  isSymRelator∞ _ (# (y ∷ ys)) (rcons∞ b r mem rs) =
    Relator∞-remove mem (sym-R _ _ r) (isSymRelator∞ _ _ rs)

  isSymRelator : isSym (Relator R)
  isSymRelator _ _ = PT.map (isSymRelator∞ _ _)

module _ {ℓ ℓ′} {A : Type ℓ} {R : Rel A A ℓ′} (open BinaryRelation)
  (prop-R : isPropValued R)
  (equiv-R : isEquivRel R)
  where

  import Cubical.HITs.SetQuotients as SQ

  private
    [_]R = SQ.[_] {R = R}

    effective : ∀ {a a' : A} → [ a ]R ≡ [ a' ]R → R a a'
    effective {a} {a'} = SQ.effective prop-R equiv-R a a'

  effectiveRelator∞ : ∀ {as bs : ΣVec A}
    → Relator∞ _≡_ (map [_]R as) (map [_]R bs)
    → Relator∞ R as bs
  effectiveRelator∞ {as = []} {bs = []} rnil∞ = rnil∞
  effectiveRelator∞ {as = # (a ∷ as)} {bs = # (_ ∷ bs)} (rcons∞ b [a]R≡b b∈bs rel) =
    let
      (a' , a'∈bs , [a']R≡b) = ∈-map-fiber b∈bs
      [a]R≡[a']R = [a]R≡b ∙ sym [a']R≡b

      p =
        map [_]R (remove (# _ ∷ bs) a'∈bs)              ≡⟨ map-remove [_]R a'∈bs ⟩
        remove (map [_]R (# _ ∷ bs)) (∈-map [_]R a'∈bs) ≡⟨ congP (λ _ → remove _) (∈-map-fiber-Path b∈bs) ⟩∎
        remove (map [_]R (# _ ∷ bs)) b∈bs ∎

      rel' : Relator∞ _≡_ (map [_]R (# as)) (map [_]R (remove (# _ ∷ bs) a'∈bs))
      rel' = subst⁻ (Relator∞ _≡_ _) p rel
    in rcons∞ a' (effective [a]R≡[a']R) a'∈bs (effectiveRelator∞ rel')

  effectiveRelator : ∀ {as bs : ΣVec A}
    → Relator _≡_ (map [_]R as) (map [_]R bs)
    → Relator R as bs
  effectiveRelator = PT.map effectiveRelator∞

module _ {ℓ ℓ'} {A B : Type ℓ} {R : Rel A B ℓ'} where

  Relator∞-singleton : {a : A} {b : B}
    → Relator∞ R [ a ] [ b ]
    → R a b
  Relator∞-singleton (rcons∞ _ Rab here _) = Rab

  Relator-singleton : {a : A} {b : B}
    → Relator R [ a ] [ b ]
    → PT.∥ R a b ∥₁
  Relator-singleton = PT.map Relator∞-singleton

  Relator∞-empty→isEmpty : {as : ΣVec A}
    → Relator∞ R as []
    → as ≡ []
  Relator∞-empty→isEmpty rnil∞ = refl

  isSet→Relator-empty→isEmpty : {as : ΣVec A}
    → isSet A
    → Relator R as []
    → as ≡ []
  isSet→Relator-empty→isEmpty setA = PT.rec (isSet→isPropIsEmpty setA) Relator∞-empty→isEmpty

  Relator∞-singleton→isSingleton : {as : ΣVec A} {b : B}
    → Relator∞ R as [ b ]
    → Σ[ (a , _) ∈ (isSingleton as) ] R a b
  Relator∞-singleton→isSingleton {as = # a ∷ as} (rcons∞ b Rab here r) = a-is-singleton , Rab' where
    as-is-empty : # as ≡ []
    as-is-empty = Relator∞-empty→isEmpty r

    a-is-singleton : Σ[ a' ∈ A ] a #∷ (# as) ≡ [ a' ]
    a-is-singleton = subst (λ · → Σ[ a' ∈ A ] a #∷ · ≡ [ a' ]) (sym as-is-empty) (a , refl {x = [ a ]})

    -- Once again, the lack of regularity lets us down.
    Rab' : R (transport refl a) b
    Rab' = subst (λ a' → R a' b) (sym (transportRefl a)) Rab

  Relator-singleton→merelySingleton : {as : ΣVec A} {b : B}
    → Relator R as [ b ]
    → PT.∥ Σ[ (a , _) ∈ (isSingleton as) ] R a b ∥₁
  Relator-singleton→merelySingleton = PT.map Relator∞-singleton→isSingleton

  isSet→Relator-singleton→isSingleton : {as : ΣVec A} {b : B}
    → isSet A
    → (∀ a b → isProp (R a b))
    → Relator R as [ b ]
    → Σ[ (a , _) ∈ (isSingleton as) ] R a b
  isSet→Relator-singleton→isSingleton {b = b} setA propR = PT.rec
    (isPropΣ (isSet→isPropIsSingleton setA) λ { (a , _) → propR a b })
    Relator∞-singleton→isSingleton

-- module _ {ℓ} {A B : Type ℓ} {R : Rel A A ℓ} (α : Iso A B) where
--   RelatorIso : ∀ {as bs}
--     → Relator R as bs
--     → Relator (pulledbackRel (α .inv) R) (map (α .fun) as) (map (α .fun) bs)
--   RelatorIso = Relator-map R (pulledbackRel (α .inv) R) λ {a} {a'} → subst2 R (sym (α .leftInv a)) (sym (α .leftInv a'))
