{-# OPTIONS --safe #-}

module Multiset.ListQuotient.FMSetEquiv where

open import Cubical.Core.Everything
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Everything
open import Cubical.Data.List as List hiding ([_]) renaming (map to mapList)
open import Cubical.Data.Vec
open import Cubical.Data.Sigma
open import Cubical.Data.Empty as Empty
open import Cubical.Data.Nat
open import Cubical.Data.Nat.Order
  using (_≤_; zero-≤; suc-≤-suc; isProp≤; ≤-refl; ≤-trans; ≤-antisym)
open import Cubical.Data.Sum as Sum
open import Cubical.Data.SumFin as SumFin renaming (Fin to SumFin)
  hiding (discreteFin; Fin→SumFin; SumFin→Fin;
          SumFin→Fin→SumFin; Fin→SumFin→Fin; SumFin≃Fin)
open import Cubical.Data.FinData renaming (znots to znotsF; snotz to snotzF)
  hiding (eq)
open import Cubical.HITs.PropositionalTruncation as PropTrunc
  renaming (rec to ∥rec∥; map to ∥map∥)
open import Cubical.HITs.SetQuotients
  renaming (rec to recQ; rec2 to recQ2; elimProp2 to elimPropQ2; elimProp to elimPropQ)
open import Cubical.Relation.Binary
open BinaryRelation
open isEquivRel

open import Cubical.Functions.Embedding
open import Cubical.Relation.Nullary
open import Multiset.ListQuotient.Base
open import Multiset.FMSet.Base
open import Multiset.Ordering.Order
open import Multiset.FMSet.Properties using (isSetFMSet)

data DRelatorΣ {ℓ}{X Y : Type ℓ} (R : X → Y → Type ℓ)
     : List X → List Y → Type ℓ where
  nil  : ∀{ys} → DRelatorΣ R [] ys
  cons : ∀{x xs ys} (p : Σ[ y ∈ Y ] R x y × (Σ[ m ∈ (y ∈ ys) ] DRelatorΣ R xs (remove ys m)))
    → DRelatorΣ R (x ∷ xs) ys

RelatorΣ : ∀ {ℓ}{X : Type ℓ} (R : X → X → Type ℓ)
  → List X → List X → Type ℓ
RelatorΣ R xs ys = DRelatorΣ R xs ys × DRelatorΣ R ys xs

reflDRelatorΣ : ∀{ℓ}{X : Type ℓ} {R : X → X → Type ℓ}
  → (∀ x → R x x)
  → ∀ xs → DRelatorΣ R xs xs
reflDRelatorΣ reflR [] = nil
reflDRelatorΣ reflR (x ∷ xs) = cons (x , reflR x , here refl , reflDRelatorΣ reflR xs)

reflRelatorΣ : ∀{ℓ}{X : Type ℓ} {R : X → X → Type ℓ}
  → (∀ x → R x x)
  → ∀ xs → RelatorΣ R xs xs
reflRelatorΣ reflR xs = (reflDRelatorΣ reflR xs) , (reflDRelatorΣ reflR xs)

memDRelatorΣ : ∀{ℓ}{X : Type ℓ} {R : X → X → Type ℓ}
  → ∀ {x xs ys} (m : x ∈ xs) → DRelatorΣ R xs ys
  → Σ[ y ∈ X ] R x y × (Σ[ m' ∈ (y ∈ ys) ] DRelatorΣ R (remove xs m) (remove ys m'))
memDRelatorΣ {X = X}{R} {ys = ys} (here eq) (cons {xs = xs} p) =
  J (λ z _ → Σ[ y ∈ X ] R z y × (Σ[ m' ∈ (y ∈ ys) ] DRelatorΣ R xs (remove ys m'))) p (sym eq)
memDRelatorΣ (there m) (cons {x = z} (y , r , m' , p')) with memDRelatorΣ m p'
... | (y' , r' , m'' , p'') =
  y' , r' , remove∈ m' m'' ,
  cons (y , r , removeremove∈ m' m'' , subst (DRelatorΣ _ (remove _ m)) (remove-par m' m'') p'')

transDRelatorΣ : ∀{ℓ}{X : Type ℓ} {R : X → X → Type ℓ}
  → (∀ {x y z} → R x y → R y z → R x z)
  → ∀ {xs ys zs} → DRelatorΣ R xs ys → DRelatorΣ R ys zs → DRelatorΣ R xs zs
transDRelatorΣ transR nil q = nil
transDRelatorΣ transR (cons (y , r , m , p')) q with memDRelatorΣ m q
... | (z , r' , m' , q') = cons (z , transR r r' , m' , transDRelatorΣ transR p' q')

transRelatorΣ : ∀{ℓ}{X : Type ℓ} {R : X → X → Type ℓ}
  → (∀ {x y z} → R x y → R y z → R x z)
  → ∀ {xs ys zs} → RelatorΣ R xs ys → RelatorΣ R ys zs → RelatorΣ R xs zs
transRelatorΣ transR p q =
  (transDRelatorΣ transR (p .fst) (q .fst)) ,
  (transDRelatorΣ transR (q .snd) (p .snd))

-- skip k j =
--    if j < k then j
--             else j + 1
skip : ∀ {n} → Fin (suc n) → Fin n → Fin (suc n)
skip zero j = suc j
skip (suc k) zero = zero
skip (suc k) (suc j) = suc (skip k j)

skipSkips : ∀ {n} (k : Fin (suc n)) (j : Fin n)
  → skip k j ≡ k → ⊥
skipSkips zero j eq = znotsF (sym eq)
skipSkips (suc k) zero eq = znotsF eq
skipSkips (suc k) (suc j) eq = skipSkips k j (injSucFin eq)

suc-predFin : ∀ {n} (j : Fin (suc (suc n))) → (j ≡ zero → ⊥)
  → suc (predFin j) ≡ j
suc-predFin zero neq = Empty.rec (neq refl)
suc-predFin (suc k) neq = refl

-- lower-wrt k j =
--    if j < k then j
--             else j - 1
lower-wrt : {n : ℕ} → Fin (suc (suc n)) → Fin (suc (suc n)) → Fin (suc n)
lower-wrt k zero = zero
lower-wrt zero (suc j) = j
lower-wrt {zero} (suc k) (suc j) = zero
lower-wrt {suc n} (suc k) (suc j) = suc (lower-wrt k j)

skip-lower-wrt : {n : ℕ} (k : Fin (suc (suc n))) (j : Fin (suc (suc n)))
  → (j ≡ k → ⊥) → skip k (lower-wrt k j) ≡ j
skip-lower-wrt zero zero neq = Empty.rec (neq refl)
skip-lower-wrt (suc k) zero neq = refl
skip-lower-wrt zero (suc j) neq = refl
skip-lower-wrt {zero} one one neq = Empty.rec (neq refl)
skip-lower-wrt {suc n} (suc k) (suc j) neq = cong′ suc (skip-lower-wrt k j (neq ∘ cong suc))

lower-wrt-skip : {n : ℕ} (k : Fin (suc (suc n))) (j : Fin (suc n))
  → lower-wrt k (skip k j) ≡ j
lower-wrt-skip zero j = refl
lower-wrt-skip (suc k) zero = refl
lower-wrt-skip {suc n} (suc k) (suc j) = cong suc (lower-wrt-skip k j)

data RelatorF {ℓ}{X Y : Type ℓ} (R : X → Y → Type ℓ)
     : (n : ℕ) → (Fin n → X) → (Fin n → Y) → Type ℓ where
  nil  : {v : Fin 0 → X}{w : Fin 0 → Y} → RelatorF R 0 v w
  cons : ∀{n v w}
    → (p : ∃[ k ∈ Fin (suc n) ] R (v zero) (w k) × RelatorF R n (v ∘ suc) (w ∘ skip k))
    → RelatorF R (suc n) v w

data RelatorFΣ {ℓ}{X Y : Type ℓ} (R : X → Y → Type ℓ)
     : (n : ℕ) → (Fin n → X) → (Fin n → Y) → Type ℓ where
  nil  : {v : Fin 0 → X}{w : Fin 0 → Y} → RelatorFΣ R 0 v w
  cons : ∀{n v w}
    → (p : Σ[ k ∈ Fin (suc n) ] R (v zero) (w k) × RelatorFΣ R n (v ∘ suc) (w ∘ skip k))
    → RelatorFΣ R (suc n) v w

isPropRelatorF : ∀ {ℓ}{X Y : Type ℓ} (R : X → Y → Type ℓ)
  → {n : ℕ} {v : Fin n → X} {w : Fin n → Y}
  → isProp (RelatorF R n v w)
isPropRelatorF R nil nil = refl
isPropRelatorF R (cons p) (cons q) =
  cong′ cons (isPropPropTrunc p q)

SymAct : ∀{ℓ}{X : Type ℓ} (n : ℕ) (v w : Fin n → X) → Type ℓ
SymAct {X = X} n v w = ∃[ σ ∈ (Fin n ≃ Fin n) ] v ≡ w ∘ equivFun σ

SymActΣ : ∀{ℓ}{X : Type ℓ} (n : ℕ) (v w : Fin n → X) → Type ℓ
SymActΣ {X = X} n v w = Σ[ σ ∈ (Fin n ≃ Fin n) ] v ≡ w ∘ equivFun σ

symSymAct : ∀{ℓ}{X : Type ℓ} {n : ℕ} {v w : Fin n → X}
  → SymAct n v w → SymAct n w v
symSymAct {w = w} = ∥map∥ (λ { (σ , eq) → invEquiv σ ,
  funExt (λ k →
    cong′ w (sym (Iso.rightInv (equivToIso σ) k))
    ∙ λ i → eq (~ i) (invEq σ k)) })

Fin→SumFin : ∀{n} → Fin n → SumFin n
Fin→SumFin zero = fzero
Fin→SumFin (suc k) = fsuc (Fin→SumFin k)

SumFin→Fin : ∀{n} → SumFin n → Fin n
SumFin→Fin {suc n} fzero = zero
SumFin→Fin {suc n} (fsuc k) = suc (SumFin→Fin k)

SumFin→Fin→SumFin : ∀{n} (k : SumFin n)
  → Fin→SumFin (SumFin→Fin k) ≡ k
SumFin→Fin→SumFin {suc n} fzero = refl
SumFin→Fin→SumFin {suc n} (fsuc k) =
  cong′ fsuc (SumFin→Fin→SumFin k)

Fin→SumFin→Fin : ∀{n} (k : Fin n)
  → SumFin→Fin (Fin→SumFin k) ≡ k
Fin→SumFin→Fin zero = refl
Fin→SumFin→Fin (suc k) = cong suc (Fin→SumFin→Fin k)

SumFin≃Fin : ∀{n} → SumFin n ≃ Fin n
SumFin≃Fin =
  isoToEquiv (iso SumFin→Fin Fin→SumFin
    Fin→SumFin→Fin
    SumFin→Fin→SumFin)

SymmetricAction→SymAct : {X : Type} {n : ℕ}
  → (v w : SumFin n → X)
  → SymmetricAction n v w
  → SymAct n (v ∘ Fin→SumFin) (w ∘ Fin→SumFin)
SymmetricAction→SymAct v w =
  ∥map∥ (λ { (σ , eq) → compEquiv (invEquiv SumFin≃Fin) (compEquiv σ SumFin≃Fin) ,
    funExt (λ k → ua→⁻ eq (Fin→SumFin k) ∙ cong′ w (sym (SumFin→Fin→SumFin _)))})


SymmetricActionΣ : ∀{ℓ}{X : Type ℓ} (n : ℕ) → Rel (SumFin n → X) (SumFin n → X) _
SymmetricActionΣ {X = X} n v w = Σ[ σ ∈ (SumFin n ≃ SumFin n) ] PathP (λ i → (ua σ i → X)) v w

private
  isSetAut : ∀ {n} → isSet (SumFin n ≃ SumFin n)
  isSetAut {n} = isOfHLevel≃ 2 (isSetSumFin n) (isSetSumFin n)

isOfHLevelSymmetricActionΣ : ∀ {ℓ} {X : Type ℓ} {n : ℕ} {v w : SumFin n → X}
  → (lvl : ℕ)
  → isOfHLevel (2 + lvl) X
  → isOfHLevel (2 + lvl) (SymmetricActionΣ n v w)
isOfHLevelSymmetricActionΣ {X = X} {n} {v} {w} lvl lvlX = isOfHLevelΣ (2 + lvl) isOfHLevelAut isOfHLevelSymPath where
  isOfHLevelAut : isOfHLevel (2 + lvl) (SumFin n ≃ SumFin n)
  isOfHLevelAut = isOfHLevelPlus' 2 isSetAut

  isOfHLevelSymPath : (α : SumFin n ≃ SumFin n) → isOfHLevel (2 + lvl) (PathP (λ i → ua α i → X) v w)
  isOfHLevelSymPath α = isOfHLevelPathP (2 + lvl) (isOfHLevelΠ (2 + lvl) (λ _ → lvlX)) v w

isSetSymmetricActionΣ : ∀ {ℓ} {X : Type ℓ} {n : ℕ} {v w : SumFin n → X}
  → isSet X
  → isSet (SymmetricActionΣ n v w)
isSetSymmetricActionΣ setX = isOfHLevelSymmetricActionΣ 0 setX

SymmetricActionΣ→SymActΣ : {X : Type} {n : ℕ}
  → (v w : SumFin n → X)
  → SymmetricActionΣ n v w
  → SymActΣ n (v ∘ Fin→SumFin) (w ∘ Fin→SumFin)
SymmetricActionΣ→SymActΣ v w (σ , eq) =
  compEquiv (invEquiv SumFin≃Fin) (compEquiv σ SumFin≃Fin) ,
    funExt (λ k → ua→⁻ eq (Fin→SumFin k) ∙ cong′ w (sym (SumFin→Fin→SumFin _)))

SymAct→SymmetricAction : {X : Type} {n : ℕ}
  → (v w : Fin n → X)
  → SymAct n v w
  → SymmetricAction n (v ∘ SumFin→Fin) (w ∘ SumFin→Fin)
SymAct→SymmetricAction v w =
  ∥map∥ λ { (σ , eq) → compEquiv SumFin≃Fin (compEquiv σ (invEquiv SumFin≃Fin)) ,
    ua→ (λ k → (λ i → eq i (SumFin→Fin k)) ∙ cong′ w (sym (Fin→SumFin→Fin _))) }

SymActΣ→SymmetricActionΣ : {X : Type} {n : ℕ}
  → (v w : Fin n → X)
  → SymActΣ n v w
  → SymmetricActionΣ n (v ∘ SumFin→Fin) (w ∘ SumFin→Fin)
SymActΣ→SymmetricActionΣ v w (σ , eq) =
  compEquiv SumFin≃Fin (compEquiv σ (invEquiv SumFin≃Fin)) ,
  ua→ (λ k → (λ i → eq i (SumFin→Fin k)) ∙ cong′ w (sym (Fin→SumFin→Fin _)))

extend-with : {n : ℕ} → (Fin n → Fin n) → Fin (suc n)
  → Fin (suc n) → Fin (suc n)
extend-with σ k zero = k
extend-with σ k (suc j) = skip k (σ j)

extend-with-inv : {n : ℕ} → (Fin n → Fin n) → Fin (suc n)
  → Fin (suc n) → Fin (suc n)
extend-with-inv σ k j with discreteFin k j
... | yes eq = zero
extend-with-inv {zero} σ k j | no neq = zero
extend-with-inv {suc n} σ k j | no neq = suc (σ (lower-wrt k j))

extend-with-iso1 : {n : ℕ} (σ : Iso (Fin n) (Fin n))
  → (k j : Fin (suc n))
  → extend-with-inv (Iso.inv σ) k (extend-with (Iso.fun σ) k j) ≡ j
extend-with-iso1 σ k zero with discreteFin k k
... | yes eq = refl
... | no neq = Empty.rec (neq refl)
extend-with-iso1 σ k (suc j) with discreteFin k (skip k (Iso.fun σ j))
... | yes eq = Empty.rec (skipSkips k (Iso.fun σ j) (sym eq))
extend-with-iso1 {suc n} σ k (suc j) | no eq =
  cong′ suc (cong′ (Iso.inv σ) (lower-wrt-skip k _)
            ∙ Iso.leftInv σ j)

extend-with-iso2 : {n : ℕ} (σ : Iso (Fin n) (Fin n))
  → (k j : Fin (suc n))
  → extend-with (Iso.fun σ) k (extend-with-inv (Iso.inv σ) k j) ≡ j
extend-with-iso2 σ k j with discreteFin k j
... | yes eq = eq
extend-with-iso2 {zero} σ zero zero | no neq = refl
extend-with-iso2 {suc n} σ k j | no neq =
  cong′ (skip k) (Iso.rightInv σ (lower-wrt k j))
  ∙ skip-lower-wrt k j (neq ∘ sym)

extend-with≃ : {n : ℕ} (σ : Fin n ≃ Fin n) (k : Fin (suc n))
  → Fin (suc n) ≃ Fin (suc n)
extend-with≃ σ k = isoToEquiv
  (iso (extend-with (equivFun σ) k)
       (extend-with-inv (invEq σ) k)
       (extend-with-iso2 (equivToIso σ) k)
       (extend-with-iso1 (equivToIso σ) k))

RelatorF=→SymAct : {X : Type} {n : ℕ} (v w : Fin n → X)
  → RelatorF _≡_ n v w → SymAct n v w
RelatorF=→SymAct v w nil = ∣ idEquiv _ , funExt (λ { () }) ∣₁
RelatorF=→SymAct v w (cons p) =
  ∥rec∥ isPropPropTrunc
        (λ { (k , eqz , r) → ∥map∥ (λ { (σ , eqs) → extend-with≃ σ k ,
                                                    funExt (λ { zero → eqz ;
                                                                (suc j) → λ i → eqs i j }) })
                                  (RelatorF=→SymAct _ _ r) })
        p

RelatorFΣ=→SymActΣ : {X : Type} {n : ℕ} (v w : Fin n → X)
  → RelatorFΣ _≡_ n v w → SymActΣ n v w
RelatorFΣ=→SymActΣ v w nil = idEquiv _ , funExt (λ { () })
RelatorFΣ=→SymActΣ v w (cons (k , eqz , r)) with RelatorFΣ=→SymActΣ _ _ r
... | (σ , eqs) =
  extend-with≃ σ k ,
  funExt (λ { zero → eqz ;
             (suc j) → λ i → eqs i j })

SymAct→RelatorF=' : {X : Type} {n : ℕ} (v w : Fin n → X)
  → (σ : Fin n ≃ Fin n) → v ≡ w ∘ equivFun σ
  → RelatorF _≡_ n v w
SymAct→RelatorF=' {n = zero} v w σ eq = nil
SymAct→RelatorF=' {n = one} v w σeqv eq =
  cons ∣ zero , (λ i → eq i zero) ∙ cong′ w (sym (isContrFin1 .snd _)) , nil ∣₁
SymAct→RelatorF=' {n = suc (suc n)} v w σeqv eq =
  cons ∣ σ zero , (λ i → eq i zero) ,
        SymAct→RelatorF=' _ _ σ'≃ (funExt eq') ∣₁
  where
    σ : Fin (suc (suc n)) → Fin (suc (suc n))
    σ = equivFun σeqv

    σinv : Fin (suc (suc n)) → Fin (suc (suc n))
    σinv = invEq σeqv

    σ' : Fin (suc n) → Fin (suc n)
    σ' j = lower-wrt (σ zero) (σ (suc j))

    eq' : ∀ j → v (suc j) ≡ w (skip (σ zero) (σ' j))
    eq' j =
      (λ i → eq i (suc j))
      ∙ cong w (sym (skip-lower-wrt (σ zero) (σ (suc j))
          (λ p → znotsF (sym (isEquiv→isEmbedding (snd σeqv) (suc j) zero .equiv-proof p .fst .fst)))))

    σ'inv : Fin (suc n) → Fin (suc n)
    σ'inv j = predFin (σinv (skip (σ zero) j))

    σ'iso1 : ∀ j → σ'inv (σ' j) ≡ j
    σ'iso1 j =
      cong′ (λ x → predFin (σinv x)) (skip-lower-wrt (σ zero) (σ (suc j))
        λ p → znotsF (sym (isEquiv→isEmbedding (snd σeqv) (suc j) zero .equiv-proof p .fst .fst)))
      ∙ cong′ predFin (Iso.leftInv (equivToIso σeqv) (suc j))

    σ'iso2 : ∀ j → σ' (σ'inv j) ≡ j
    σ'iso2 j =
      cong′ (λ x → lower-wrt (σ zero) (σ x)) (suc-predFin (σinv (skip (σ zero) j))
          λ eq → skipSkips (σ zero) j (isEquiv→isEmbedding (snd (invEquiv σeqv)) _ _ .equiv-proof (eq ∙ sym (Iso.leftInv (equivToIso σeqv) _)) .fst .fst))
      ∙ cong′ (lower-wrt (σ zero)) (Iso.rightInv (equivToIso σeqv) (skip (σ zero) j))
      ∙ lower-wrt-skip (σ zero) j

    σ'≃ : Fin (suc n) ≃ Fin (suc n)
    σ'≃ = isoToEquiv (iso σ' σ'inv σ'iso2 σ'iso1)

SymAct→RelatorF= : {X : Type} {n : ℕ} (v w : Fin n → X)
  → SymAct n v w → RelatorF _≡_ n v w
SymAct→RelatorF= v w =
  ∥rec∥ (isPropRelatorF _≡_)
        (λ x → SymAct→RelatorF=' v w (x .fst) (x .snd))


-- ====================================================================

data _∈V_ {ℓ}{X : Type ℓ} (x : X) : {n : ℕ} → Vec X n → Type ℓ where
  here : ∀{n y} {xs : Vec X n} → x ≡ y → x ∈V (y ∷ xs)
  there : ∀{n y} {xs : Vec X n} → x ∈V xs → x ∈V (y ∷ xs)

removeV : ∀{ℓ}{A : Type ℓ}{n} {x : A} (xs : Vec A (suc n)) → x ∈V xs → Vec A n
removeV (x ∷ xs) (here eq) = xs
removeV (y ∷ x ∷ xs) (there m) = y ∷ removeV (x ∷ xs) m

positionV : ∀{ℓ}{A : Type ℓ}{n} {x : A} {xs : Vec A (suc n)} → x ∈V xs → Fin (suc n)
positionV (here x) = zero
positionV {n = suc n} (there m) = suc (positionV m)

lookup-positionV : ∀{ℓ}{A : Type ℓ}{n} {x : A} {xs : Vec A (suc n)} (m : x ∈V xs)
  → lookup (positionV m) xs ≡ x
lookup-positionV (here eq) = sym eq
lookup-positionV {n = suc n} (there m) = lookup-positionV m

data RelatorV {ℓ}{X Y : Type ℓ} (R : X → Y → Type ℓ)
     : (n : ℕ) → Vec X n → Vec Y n → Type ℓ where
  nil  : RelatorV R 0 [] []
  cons : ∀{n x xs ys}
    → (p : ∃[ y ∈ Y ] R x y × (Σ[ m ∈ y ∈V ys ] RelatorV R n xs (removeV ys m)))
    → RelatorV R (suc n) (x ∷ xs) ys

data RelatorVΣ {ℓ}{X Y : Type ℓ} (R : X → Y → Type ℓ)
     : (n : ℕ) → Vec X n → Vec Y n → Type ℓ where
  nil  : RelatorVΣ R 0 [] []
  cons : ∀{n x xs ys}
    → (p : Σ[ y ∈ Y ] R x y × (Σ[ m ∈ y ∈V ys ] RelatorVΣ R n xs (removeV ys m)))
    → RelatorVΣ R (suc n) (x ∷ xs) ys

∈FinVec : ∀{ℓ}{X : Type ℓ} {n : ℕ} (w : Fin n → X)
  → ∀ k → w k ∈V FinVec→Vec w
∈FinVec w zero = here refl
∈FinVec w (suc k) = there (∈FinVec (w ∘ suc) k)

FinVec-remove : ∀{ℓ}{X : Type ℓ} {n : ℕ}
  → (w : Fin (suc n) → X) (k : Fin (suc n))
  → FinVec→Vec (w ∘ skip k) ≡ removeV (FinVec→Vec w) (∈FinVec w k)
FinVec-remove w zero = refl
FinVec-remove {n = suc n} w (suc k) =
  cong′ (w zero ∷_) (FinVec-remove (w ∘ suc) k)

Vec-remove : ∀{ℓ}{X : Type ℓ} {n y} {ys : Vec X (suc n)}
  → ∀ (m : y ∈V ys) j
  → Vec→FinVec (removeV ys m) j ≡
      Vec→FinVec ys (skip (positionV m) j)
Vec-remove (here eq) j = refl
Vec-remove (there {xs = x ∷ xs} m) zero = refl
Vec-remove (there {xs = x ∷ xs} m) (suc j) = Vec-remove m j

RelatorF→RelatorV : ∀{ℓ}{X Y : Type ℓ} (R : X → Y → Type ℓ)
  → {n : ℕ} (v : Fin n → X) (w : Fin n → Y)
  → RelatorF R n v w → RelatorV R n (FinVec→Vec v) (FinVec→Vec w)
RelatorF→RelatorV R v w nil = nil
RelatorF→RelatorV R v w (cons p) =
  cons (∥map∥ (λ { (k , r , rs) → w k , r , ∈FinVec w k ,
                                  subst (RelatorV R _ (FinVec→Vec (v ∘ suc)))
                                        (FinVec-remove w k)
                                        (RelatorF→RelatorV R (v ∘ suc) (w ∘ skip k) rs) })
              p)

RelatorV→RelatorF : ∀{ℓ}{X Y : Type ℓ} (R : X → Y → Type ℓ)
  → {n : ℕ} (xs : Vec X n) (ys : Vec Y n)
  → RelatorV R n xs ys → RelatorF R n (Vec→FinVec xs) (Vec→FinVec ys)
RelatorV→RelatorF R [] .[] nil = nil
RelatorV→RelatorF R (x ∷ xs) ys (cons p) =
  cons (∥map∥ (λ { (y , r , m , rs) → positionV m ,
                                      subst (R _) (sym (lookup-positionV m)) r ,
                                      subst (RelatorF R _ (Vec→FinVec xs))
                                            (funExt (Vec-remove m))
                                            (RelatorV→RelatorF R xs (removeV ys m) rs) })
              p)

RelatorVΣ→RelatorFΣ : ∀{ℓ}{X Y : Type ℓ} (R : X → Y → Type ℓ)
  → {n : ℕ} (xs : Vec X n) (ys : Vec Y n)
  → RelatorVΣ R n xs ys → RelatorFΣ R n (Vec→FinVec xs) (Vec→FinVec ys)
RelatorVΣ→RelatorFΣ R [] .[] nil = nil
RelatorVΣ→RelatorFΣ R (x ∷ xs) ys (cons (y , r , m , rs)) =
  cons (positionV m ,
        subst (R _) (sym (lookup-positionV m)) r ,
        subst (RelatorFΣ R _ (Vec→FinVec xs))
              (funExt (Vec-remove m))
              (RelatorVΣ→RelatorFΣ R xs (removeV ys m) rs))


-- =================================================================

Vec→List : ∀{ℓ}{X : Type ℓ}{n : ℕ} → Vec X n → List X
Vec→List [] = []
Vec→List (x ∷ xs) = x ∷ Vec→List xs

List→Vec : ∀{ℓ}{X : Type ℓ} (xs : List X) → Vec X (List.length xs)
List→Vec [] = []
List→Vec (x ∷ xs) = x ∷ List→Vec xs

Vec→List→Vec : ∀{ℓ}{X : Type ℓ} (xs : List X)
  → Vec→List (List→Vec xs) ≡ xs
Vec→List→Vec [] = refl
Vec→List→Vec (x ∷ xs) = cong′ (x ∷_) (Vec→List→Vec xs)

lengthVec→List : ∀{ℓ}{X : Type ℓ} {n} (xs : Vec X n)
  → List.length (Vec→List xs) ≡ n
lengthVec→List [] = refl
lengthVec→List (x ∷ xs) = cong suc (lengthVec→List xs)

substVec : ∀{ℓ}{A : Type ℓ} {n m : ℕ}
  → {y : A} {xs : Vec A n}
  → (eq : n ≡ m)
  → Path (Vec A (suc m)) (y ∷ subst (Vec A) eq xs) (subst (Vec A) (cong suc eq) (y ∷ xs))
substVec {A = A}{y = y}{xs} =
  J (λ x eq → Path (Vec A (suc x)) (y ∷ subst (Vec A) eq xs) (subst (Vec A) (cong suc eq) (y ∷ xs)))
    (cong′ (y ∷_) (substRefl {B = Vec A} xs)
     ∙ sym (substRefl {B = Vec A} _))

List→Vec→List : ∀{ℓ}{X : Type ℓ}{n : ℕ} (xs : Vec X n)
  → subst (Vec X) (lengthVec→List xs) (List→Vec (Vec→List xs)) ≡ xs
List→Vec→List [] = substRefl {B = Vec _} []
List→Vec→List (x ∷ xs) =
  sym (substVec (lengthVec→List xs))
  ∙ cong′ (x ∷_) (List→Vec→List xs)

∈→∈V : ∀{ℓ}{X : Type ℓ} {x : X} {xs : List X}
  → x ∈ xs → x ∈V List→Vec xs
∈→∈V (here eq) = here eq
∈→∈V (there m) = there (∈→∈V m)

∈V→∈ : ∀{ℓ}{X : Type ℓ} {n : ℕ} {x : X} {xs : Vec X n}
  → x ∈V xs → x ∈ Vec→List xs
∈V→∈ (here x) = here x
∈V→∈ (there m) = there (∈V→∈ m)


removeV→remove : ∀{ℓ}{X : Type ℓ} {n : ℕ} {x : X} {xs : Vec X (suc n)}
  → (m : x ∈V xs)
  → Vec→List (removeV xs m) ≡ remove (Vec→List xs) (∈V→∈ m)
removeV→remove (here x) = refl
removeV→remove (there {y = y} {xs = x ∷ xs} m) =
  cong′ (y ∷_) (removeV→remove m)

RelatorV→DRelator : ∀{ℓ}{X : Type ℓ} (R : X → X → Type ℓ)
  → {n : ℕ} (xs ys : Vec X n)
  → RelatorV R n xs ys → DRelator R (Vec→List xs) (Vec→List ys)
RelatorV→DRelator R .[] .[] nil = nil
RelatorV→DRelator R (x ∷ xs) ys (cons p) =
  cons (∥map∥ (λ { (y , r , m , rs) → y , r , ∈V→∈ m ,
                                      subst (DRelator R (Vec→List xs))
                                            (removeV→remove m)
                                            (RelatorV→DRelator R xs (removeV ys m) rs) })
              p)

data RelatorV' {ℓ}{X Y : Type ℓ} (R : X → Y → Type ℓ)
     : {n m : ℕ} → Vec X n → Vec Y m → Type ℓ where
  nil  : RelatorV' R [] []
  cons : ∀{n m x} {xs : Vec X n} {ys : Vec Y (suc m)}
    → (p : ∃[ y ∈ Y ] R x y × (Σ[ m ∈ y ∈V ys ] RelatorV' R xs (removeV ys m)))
    → RelatorV' R (x ∷ xs) ys

data RelatorV'Σ {ℓ}{X Y : Type ℓ} (R : X → Y → Type ℓ)
     : {n m : ℕ} → n ≡ m → Vec X n → Vec Y m → Type ℓ where
  nil  : RelatorV'Σ R refl [] []
  cons : ∀{n m} {eq : n ≡ m} {x xs ys}
    → (p : Σ[ y ∈ Y ] R x y × (Σ[ m ∈ y ∈V ys ] RelatorV'Σ R eq xs (removeV ys m)))
    → RelatorV'Σ R (cong suc eq) (x ∷ xs) ys

length-remove : ∀{ℓ}{A : Type ℓ}{x : A} {xs : List A}
  → (m : x ∈ xs)
  → List.length xs ≡ suc (List.length (remove xs m))
length-remove (here x) = refl
length-remove (there m) = cong suc (length-remove m)

length-remove' : ∀{ℓ}{A : Type ℓ}{x y : A} {xs : List A}
  → (m : x ∈ (y ∷ xs))
  → List.length xs ≡ List.length (remove (y ∷ xs) m)
length-remove' (here eq) = refl
length-remove' (there m) = length-remove m


remove→removeV : ∀{ℓ}{X : Type ℓ} {x y : X} {xs : List X}
  → (m : x ∈ xs)
  → y ∷ List→Vec (remove xs m)
      ≡ subst (Vec X) (length-remove m) (removeV (List→Vec (y ∷ xs)) (there (∈→∈V m)))
remove→removeV (here eq) = sym (substRefl {B = Vec _} _)
remove→removeV {y = y} (there m) =
  cong′ (y ∷_) (remove→removeV m)
  ∙ substVec _

remove→removeV' : ∀{ℓ}{X : Type ℓ} {x y : X} {xs : List X}
  → (m : x ∈ (y ∷ xs))
  → List→Vec (remove (y ∷ xs) m)
      ≡ subst (Vec X) (length-remove' m) (removeV (List→Vec (y ∷ xs)) (∈→∈V m))
remove→removeV' (here eq) = sym (substRefl {B = Vec _} _)
remove→removeV' (there m) = remove→removeV m

RelatorV'N : ∀ {ℓ}{X Y : Type ℓ} (R : X → Y → Type ℓ)
  → {n m m' : ℕ} 
  → {xs : Vec X n} {ys : Vec Y m}
  → (eq' : m ≡ m') {ys' : Vec Y m'}
  → ys' ≡ subst (Vec Y) eq' ys
  → RelatorV' R xs ys'
  → RelatorV' R xs ys
RelatorV'N R {n}{m' = m'} {xs} {ys} =
    J (λ m eq → {ys' : Vec _ m} → ys' ≡ subst (Vec _) eq ys → RelatorV' R xs ys' → RelatorV' R xs ys)
      λ eq r → subst (RelatorV' R xs) (eq ∙ substRefl {B = Vec _} ys) r 

RelatorV'ΣN : ∀ {ℓ}{X Y : Type ℓ} (R : X → Y → Type ℓ)
  → {n m m' : ℕ} (eq : n ≡ m)
  → {xs : Vec X n} {ys : Vec Y m}
  → (eq' : m ≡ m') {ys' : Vec Y m'}
  → ys' ≡ subst (Vec Y) eq' ys
  → RelatorV'Σ R (eq ∙ eq') xs ys'
  → RelatorV'Σ R eq xs ys
RelatorV'ΣN R {n}{m' = m'} =
  J (λ m eq → {xs : Vec _ n} {ys : Vec _ m} (eq' : m ≡ m') {ys' : Vec _ m'} → ys' ≡ subst (Vec _) eq' ys → RelatorV'Σ R (eq ∙ eq') xs ys' → RelatorV'Σ R eq xs ys)
    (λ {xs}{ys} →
    J (λ m eq → {ys' : Vec _ m} → ys' ≡ subst (Vec _) eq ys → RelatorV'Σ R (refl ∙ eq) xs ys' → RelatorV'Σ R refl xs ys)
      λ {ys'} eq r → subst (RelatorV'Σ R refl xs) (eq ∙ substRefl {B = Vec _} ys) (subst (λ z → RelatorV'Σ R z xs ys') (sym (rUnit _)) r))


DRelator→RelatorV' : ∀{ℓ}{X : Type ℓ} (R : X → X → Type ℓ)
  → (xs ys : List X) (eq : List.length xs ≡ List.length ys)
  → DRelator R xs ys → RelatorV' R (List→Vec xs) (List→Vec ys)
DRelator→RelatorV' R .[] [] eq nil = nil 
DRelator→RelatorV' R .[] (x ∷ xs) eq nil = Empty.rec (znots eq) 
DRelator→RelatorV' R .(_ ∷ _) [] eq (cons p) = Empty.rec (snotz eq)
DRelator→RelatorV' R (x ∷ xs) (y' ∷ ys) eq (cons p) =
        (cons (∥map∥ (λ { (y , r , m , rs) →
          let rs' : RelatorV' R (List→Vec xs) (List→Vec (remove (y' ∷ ys) m))
              rs' = DRelator→RelatorV' R xs (remove (y' ∷ ys) m) (eq' ∙ length-remove' m) rs
              rs'' : RelatorV' R (List→Vec xs) (removeV (List→Vec (y' ∷ ys)) (∈→∈V m))
              rs'' = RelatorV'N R (length-remove' m) (remove→removeV' m) rs'
          in y , r , ∈→∈V m , rs'' })
                     p))
  where
    eq' : List.length xs ≡ List.length ys
    eq' = injSuc eq

DRelatorΣ→RelatorV'Σ : ∀{ℓ}{X : Type ℓ} (R : X → X → Type ℓ)
  → (xs ys : List X) (eq : List.length xs ≡ List.length ys)
  → DRelatorΣ R xs ys → RelatorV'Σ R eq (List→Vec xs) (List→Vec ys)
DRelatorΣ→RelatorV'Σ R .[] [] eq nil = subst (λ x → RelatorV'Σ R x [] []) (isSetℕ _ _ _ _) nil
DRelatorΣ→RelatorV'Σ R .[] (x ∷ xs) eq nil = Empty.rec (znots eq)
DRelatorΣ→RelatorV'Σ R .(_ ∷ _) [] eq (cons p) = Empty.rec (snotz eq)
DRelatorΣ→RelatorV'Σ R (x ∷ xs) (y' ∷ ys) eq (cons (y , r , m , rs)) =
  subst (λ p → RelatorV'Σ R p (x ∷ List→Vec xs) (y' ∷ List→Vec ys))
        (isSetℕ _ _ _ _)
        (cons (y , r , ∈→∈V m , rs''))
  where
    eq' : List.length xs ≡ List.length ys
    eq' = injSuc eq
    rs' : RelatorV'Σ R (eq' ∙ length-remove' m) (List→Vec xs) (List→Vec (remove (y' ∷ ys) m))
    rs' = DRelatorΣ→RelatorV'Σ R xs (remove (y' ∷ ys) m) (eq' ∙ length-remove' m) rs
    rs'' : RelatorV'Σ R eq' (List→Vec xs) (removeV (List→Vec (y' ∷ ys)) (∈→∈V m))
    rs'' = RelatorV'ΣN R eq' (length-remove' m) (remove→removeV' m) rs'

RelatorV'→RelatorV : ∀{ℓ}{X : Type ℓ} (R : X → X → Type ℓ)
  → {n m : ℕ} (eq : n ≡ m) (xs : Vec X n) (ys : Vec X m)
  → RelatorV' R xs ys → RelatorV R m (subst (Vec X) eq xs) ys
RelatorV'→RelatorV R eq .[] .[] nil = subst (λ z → RelatorV R 0 z []) (sym (isSet-subst {B = Vec _} isSetℕ eq [])) nil
RelatorV'→RelatorV {X = X} R {n = suc n} {m = suc m} eq (x ∷ xs) ys (cons p) =
  subst (λ eq → RelatorV R (suc m) (subst (Vec X) eq (x ∷ xs)) ys) (isSetℕ _ _ (cong suc eq') eq)
    (J (λ a eq → (ys : Vec _ (suc a))
                (p : ∃[ y ∈ _ ] R x y × (Σ[ m ∈ y ∈V ys ] RelatorV' R xs (removeV ys m)))
                → RelatorV R (suc a) (subst (Vec X) (cong suc eq) (x ∷ xs)) ys)
       (λ ys' p' → subst (λ z → RelatorV R (suc _) z ys')
                        (sym (substRefl {B = Vec _} (x ∷ xs)))
                        (cons (∥map∥ (λ { (y , r , y∈ , rs) →
                              y , r , y∈ , subst (λ z → RelatorV R _ z (removeV ys' y∈))
                                                 (substRefl {B = Vec X} xs)
                                                 (RelatorV'→RelatorV R refl xs _ rs) })
                                      p')))
       eq' ys p)

  where
    eq' : n ≡ m
    eq' = injSuc eq

RelatorV'Σ→RelatorVΣ : ∀{ℓ}{X : Type ℓ} (R : X → X → Type ℓ)
  → {n m : ℕ} (eq : n ≡ m) (xs : Vec X n) (ys : Vec X m)
  → RelatorV'Σ R eq xs ys → RelatorVΣ R m (subst (Vec X) eq xs) ys
RelatorV'Σ→RelatorVΣ R .refl .[] .[] nil = subst (λ z → RelatorVΣ R 0 z []) (sym (substRefl {B = Vec _} [])) nil
RelatorV'Σ→RelatorVΣ {X = X} R {m = suc m} .(cong suc eq) (x ∷ xs) ys (cons {eq = eq} p) =
  J (λ a eq → (ys : Vec _ (suc a))
               (p : Σ[ y ∈ _ ] R x y × (Σ[ m ∈ y ∈V ys ] RelatorV'Σ R eq xs (removeV ys m)))
               → RelatorVΣ R (suc a) (subst (Vec X) (cong suc eq) (x ∷ xs)) ys)
  (λ { ys' (y , r , y∈ , rs) →
    subst (λ z → RelatorVΣ R (suc _) z ys')
          (sym (substRefl {B = Vec _} (x ∷ xs)))
          (cons (y , r , y∈ , subst (λ z → RelatorVΣ R _ z (removeV ys' y∈))
                                    (substRefl {B = Vec X} xs)
                                    (RelatorV'Σ→RelatorVΣ R refl xs _ rs))) })
  eq ys p


-- Putting everything together:

SymAct→Relator= : {X : Type}{n : ℕ}
  → (v w : Fin n → X)
  → SymAct n v w
  → Relator _≡_ (Vec→List (FinVec→Vec v)) (Vec→List (FinVec→Vec w))
SymAct→Relator= v w r =
  (RelatorV→DRelator _≡_ _ _ (RelatorF→RelatorV _≡_ _ _ (SymAct→RelatorF= _ _ r))) ,
  (RelatorV→DRelator _≡_ _ _ (RelatorF→RelatorV _≡_ _ _ (SymAct→RelatorF= _ _ (symSymAct r))))

lengthDRelator : {X : Type} {xs ys : List X}
  → DRelator _≡_ xs ys → List.length xs ≤ List.length ys
lengthDRelator nil = zero-≤
lengthDRelator {ys = ys} (cons p) =
  ∥rec∥ isProp≤
       (λ { (y , eq , m , rs) →
           ≤-trans (suc-≤-suc (lengthDRelator rs))
                   (subst (suc (List.length (remove ys m)) ≤_)
                          (sym (length-remove m))
                          ≤-refl) })
        p

lengthRelator : {X : Type} {xs ys : List X}
  → Relator _≡_ xs ys → List.length xs ≡ List.length ys
lengthRelator (p , q) = ≤-antisym (lengthDRelator p) (lengthDRelator q)

lengthDRelatorΣ : {X : Type} {xs ys : List X}
  → DRelatorΣ _≡_ xs ys → List.length xs ≤ List.length ys
lengthDRelatorΣ nil = zero-≤
lengthDRelatorΣ {ys = ys} (cons (y , eq , m , rs)) =
  ≤-trans (suc-≤-suc (lengthDRelatorΣ rs))
          (subst (suc (List.length (remove ys m)) ≤_)
                 (sym (length-remove m))
                 ≤-refl)

lengthRelatorΣ : {X : Type} {xs ys : List X}
  → RelatorΣ _≡_ xs ys → List.length xs ≡ List.length ys
lengthRelatorΣ (p , q) = ≤-antisym (lengthDRelatorΣ p) (lengthDRelatorΣ q)

Relator=→SymAct : {X : Type}
  → (xs ys : List X)
  → (rs : Relator _≡_ xs ys)
  → SymAct (List.length ys) (Vec→FinVec (subst (Vec X) (lengthRelator rs) (List→Vec xs))) (Vec→FinVec (List→Vec ys))
Relator=→SymAct xs ys rs =
  RelatorF=→SymAct _ (Vec→FinVec (List→Vec ys))
                   (RelatorV→RelatorF _≡_ _ _
                                      (RelatorV'→RelatorV _≡_ (lengthRelator rs) (List→Vec xs) _
                                                          (DRelator→RelatorV' _≡_ _ _ (lengthRelator rs) (rs .fst))))

RelatorΣ=→SymActΣ : {X : Type}
  → (xs ys : List X)
  → (rs : RelatorΣ _≡_ xs ys)
  → SymActΣ (List.length ys) (Vec→FinVec (subst (Vec X) (lengthRelatorΣ rs) (List→Vec xs))) (Vec→FinVec (List→Vec ys))
RelatorΣ=→SymActΣ xs ys rs =
  RelatorFΣ=→SymActΣ _ (Vec→FinVec (List→Vec ys))
                   (RelatorVΣ→RelatorFΣ _≡_ _ _
                                      (RelatorV'Σ→RelatorVΣ _≡_ (lengthRelatorΣ rs) (List→Vec xs) _
                                                          (DRelatorΣ→RelatorV'Σ _≡_ _ _ _ (rs .fst))))


FMSet→List/Relator= : {X : Type} → FMSet X → List X / Relator _≡_
FMSet→List/Relator= (n , x) =
  recQ squash/
       (λ v → [ Vec→List (FinVec→Vec (λ k → v (Fin→SumFin k))) ])
       (λ v w r → eq/ _ _ (SymAct→Relator= _ _ (SymmetricAction→SymAct v w r)))
       x

substPVect : ∀ {ℓ} {X : Type ℓ} {n m} (xs : Vec X n) (eq : n ≡ m)
  → subst (PVect X) eq [ Vec→FinVec xs ∘ SumFin→Fin ]
       ≡ [ Vec→FinVec (subst (Vec X) eq xs) ∘ SumFin→Fin ]
substPVect {X = X} xs =
  J (λ m eq → subst (PVect X) eq [ Vec→FinVec xs ∘ SumFin→Fin ]
                   ≡ [ Vec→FinVec (subst (Vec X) eq xs) ∘ SumFin→Fin ])
    (substRefl {B = PVect X} [ Vec→FinVec xs ∘ SumFin→Fin ]
     ∙ sym (cong′ (λ x → [ Vec→FinVec x ∘ SumFin→Fin ]) (substRefl {B = Vec X} xs)))

List/Relator=→FMSet : {X : Type} → List X / Relator _≡_ → FMSet X
List/Relator=→FMSet {X} =
  recQ isSetFMSet
       (λ xs → List.length xs , [ (λ k → Vec→FinVec (List→Vec xs) (SumFin→Fin k)) ])
       λ xs ys rs → ΣPathP (lengthRelator rs , toPathP
         (subst (PVect X) (lengthRelator rs) [ Vec→FinVec (List→Vec xs) ∘ SumFin→Fin ]
             ≡⟨ substPVect (List→Vec xs) (lengthRelator rs) ⟩
          [ Vec→FinVec (subst (Vec X) (lengthRelator rs) (List→Vec xs)) ∘ SumFin→Fin ]
             ≡⟨ eq/ _ _
                  (SymAct→SymmetricAction (Vec→FinVec (subst (Vec X) (lengthRelator rs) (List→Vec xs)))
                                           (Vec→FinVec (List→Vec ys))
                                           (Relator=→SymAct xs ys rs)) ⟩
          [ Vec→FinVec (List→Vec ys) ∘ SumFin→Fin ]
             ∎))

FMSet→List/Relator=→FMSet : {X : Type} (x : List X / Relator _≡_)
  → FMSet→List/Relator= (List/Relator=→FMSet x) ≡ x
FMSet→List/Relator=→FMSet =
  elimPropQ (λ _ → squash/ _ _)
            λ xs → cong′ [_] ((λ i → Vec→List (FinVec→Vec (λ k → Vec→FinVec (List→Vec xs) (Fin→SumFin→Fin k i))))
                              ∙ (λ i → Vec→List (Vec→FinVec→Vec (List→Vec xs) i))
                              ∙ Vec→List→Vec xs)

List/Relator=→FMSet→List/Relator= : {X : Type} (n : ℕ) (x : PVect X n)
  → List/Relator=→FMSet (FMSet→List/Relator= (n , x)) ≡ (n , x)
List/Relator=→FMSet→List/Relator= {X} n =
  elimPropQ (λ _ → isSetFMSet _ _)
            (λ v →
              ΣPathP (lengthVec→List (FinVec→Vec (v ∘ Fin→SumFin)) ,
                          toPathP
                            (subst (PVect X) (lengthVec→List (FinVec→Vec (v ∘ Fin→SumFin))) [ Vec→FinVec (List→Vec (Vec→List (FinVec→Vec (v ∘ Fin→SumFin)))) ∘ SumFin→Fin ]
                               ≡⟨ substPVect (List→Vec (Vec→List (FinVec→Vec (v ∘ Fin→SumFin)))) _ ⟩
                             [ Vec→FinVec (subst (Vec X) (lengthVec→List (FinVec→Vec (v ∘ Fin→SumFin))) (List→Vec (Vec→List (FinVec→Vec (v ∘ Fin→SumFin))))) ∘ SumFin→Fin ]
                               ≡⟨ cong′ [_] (λ i → Vec→FinVec (List→Vec→List (FinVec→Vec (v ∘ Fin→SumFin)) i) ∘ SumFin→Fin) ⟩
                             [ Vec→FinVec (FinVec→Vec (v ∘ Fin→SumFin)) ∘ SumFin→Fin ]
                               ≡⟨ cong′ [_] (λ i → FinVec→Vec→FinVec (v ∘ Fin→SumFin) i ∘ SumFin→Fin) ⟩
                             [ v ∘ Fin→SumFin ∘ SumFin→Fin ]
                               ≡⟨ cong′ [_] (λ i k → v (SumFin→Fin→SumFin k i)) ⟩
                             [ v ]
                               ∎)))

FMSet≃List/Relator= : {X : Type} → FMSet X ≃ List X / Relator _≡_
FMSet≃List/Relator= =
  isoToEquiv
    (iso FMSet→List/Relator=
         List/Relator=→FMSet
         FMSet→List/Relator=→FMSet
         λ x → List/Relator=→FMSet→List/Relator= (x .fst) (x .snd))
