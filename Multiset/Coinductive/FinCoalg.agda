{-# OPTIONS --sized-types #-}

module Multiset.Coinductive.FinCoalg where

open import Multiset.Coinductive.Size

open import Cubical.Core.Everything
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Everything
open import Cubical.Data.List hiding ([_]) renaming (map to mapList)
open import Cubical.Data.Sigma
open import Cubical.Data.Nat
open import Cubical.Data.Fin
  hiding (_/_)
open import Cubical.HITs.PropositionalTruncation as PropTrunc
  renaming (rec to ∥rec∥; map to ∥map∥)
open import Cubical.HITs.SetQuotients
  renaming (rec to recQ; rec2 to recQ2; elimProp2 to elimPropQ2; elimProp to elimPropQ)
open import Cubical.Relation.Binary
open BinaryRelation
open isEquivRel
open import Multiset.Inductive.Base
open import Multiset.Inductive.Properties

-- ================================================ 

-- The coinductive type of infinite unordered trees
record νM (i : Size) : Type where
  constructor buildM
  coinductive
  field
    subtreesM : {j : Size< i} → M (νM j)
open νM

-- νM is a set
isSetνM : isSet (νM ∞)
subtreesM (isSetνM x y p q j k) =
  trunc (subtreesM x) (subtreesM y)
        (λ i → subtreesM (p i)) (λ i → subtreesM (q i))
        j k 

-- νM is the final coalgebra of the bag functor
-- Given a coalgebra c : X → M X, there exists a unique coalgebra
-- morphism from X to νM.

-- -- Existence
anaM : {X : Type} (c : X → M X) (j : Size) → X → νM j
subtreesM (anaM c j x) {k} = map (anaM c k) (c x)

anaMEq : {X : Type} (c : X → M X) (x : X)
  → subtreesM (anaM c ∞ x) ≡ map (anaM c ∞) (c x)
anaMEq c x = refl

-- -- Uniqueness
anaMUniq' : {X : Type} (c : X → M X)
  → (f : (s : Size) → X → νM s)
  → (eq : ∀ (s : Size) (s' : Size< s) x
    → subtreesM (f s x) {s'} ≡ map (f s') (c x))
  → (s : Size) → ∀ x → f s x ≡ anaM c s x
subtreesM (anaMUniq' c f eq s x i) {s'}
  = hcomp (λ j → λ { (i = i0) → eq s s' x (~ j)
                    ; (i = i1) → map (anaM c s') (c x) })
          (map (λ x' → anaMUniq' c f eq s' x' i) (c x))

anaMUniq : {X : Type} (c : X → M X)
  → (f : X → νM ∞)
  → (eq : ∀ {s : Size} x → subtreesM (f x) {s} ≡ map f (c x))
  → f ≡ anaM c ∞
anaMUniq c f eq i x = anaMUniq' c (λ _ → f) (λ { _ _ → eq }) ∞ x i

-- ================================================ 

-- Coinduction principle:
-- Bisimilarity is equivalent to path equality on νM

-- Graph of a relation
Tot : ∀{ℓ}{X Y : Type ℓ}
  → (R : X → Y → Type ℓ)
  → Type ℓ
Tot R = Σ[ x ∈ _ ] Σ[ y ∈ _ ] R x y  

module _ {ℓ} {X Y : Type ℓ} {R : X → Y → Type ℓ} (p : Tot R) where
  fstTot = p .fst
  sndTot = p .snd .fst
  relTot = p .snd .snd

reflTot : ∀{ℓ}{X : Type ℓ}
  → {R : X → X → Type ℓ}
  → (reflR : ∀ {x} → R x x)
  → X → Tot R
reflTot reflR x = x , x , reflR  

mapTot : ∀{ℓ}{X Y : Type ℓ}
  → {R S : X → Y → Type ℓ}
  → (∀ {x y} → R x y → S x y)
  → Tot R → Tot S
mapTot rs (x , y , r) = (x , y , rs r)  

-- Relation lifting
-- (NB: this is very general, not specific too finite bags!)
MRel : ∀{ℓ}{X Y : Type ℓ}
  → (R : X → Y → Type ℓ)
  → M X → M Y → Type ℓ
MRel R s t =
  ∃[ u ∈ M (Tot R) ] (map fstTot u ≡ s) × (map sndTot u ≡ t)  

reflMRel : ∀{ℓ}{X : Type ℓ}
  → {R : X → X → Type ℓ}
  → (reflR : ∀ {x} → R x x)
  → ∀ s → MRel R s s
reflMRel reflR s =
  ∣ map (reflTot reflR) s ,
   map-comp fstTot (reflTot reflR) s ∙ map-id s ,
   map-comp sndTot (reflTot reflR) s ∙ map-id s ∣₁

mapMRel : ∀{ℓ}{X Y : Type ℓ}
  → {R S : X → Y → Type ℓ}
  → (∀ {x y} → R x y → S x y)
  → ∀ {t u} → MRel R t u → MRel S t u
mapMRel rs = ∥map∥ lem
  where
    lem : _
    lem (r , p , q) = 
      map (mapTot rs) r  ,
      map-comp fstTot (mapTot rs) r ∙ p ,
      map-comp sndTot (mapTot rs) r ∙ q

-- The lifting of path equality is equivalent to path equality on M X
MRel≡→≡' : ∀{ℓ} {X : Type ℓ} (r : M (Tot {X = X} _≡_))
  → map fstTot r ≡ map sndTot r
MRel≡→≡' =
  ind (λ _ → isSetM _ _)
      refl
      (λ { (x , y , eq) → cong η eq })
      λ ih1 ih2 → cong₂ _⊕_ ih1 ih2

MRel≡→≡ : ∀{ℓ} {X : Type ℓ} {s t : M X} → MRel _≡_ s t → s ≡ t
MRel≡→≡ {s = s}{t} = ∥rec∥ (isSetM _ _) lem
  where
    lem : _
    lem (r , p , q) =
      s ≡⟨ sym p ⟩
      map fstTot r ≡⟨ MRel≡→≡' r ⟩
      map sndTot r ≡⟨ q ⟩
      t ∎

MRel≡is≡ : ∀{ℓ} {X : Type ℓ} {s t : M X} → (MRel _≡_ s t) ≡ (s ≡ t)
MRel≡is≡ =
  hPropExt isPropPropTrunc (isSetM _ _)
           MRel≡→≡
           (J (λ t eq → MRel _≡_ _ t) (reflMRel refl _))

-- The bisimilarity relation, defined coinductively
record νMB (i : Size) (s t : νM i) : Type where
  coinductive
  field
    subtreesMB : {j : Size< i} → MRel (νMB j) (subtreesM s) (subtreesM t)
open νMB

reflνMB : (i : Size) (t : νM i) → νMB i t t
subtreesMB (reflνMB i t) {j} =
  reflMRel (reflνMB j _) (subtreesM t)

isPropνMB : (i : Size) {t u : νM i} → isProp (νMB i t u)
subtreesMB (isPropνMB i p q j) =
  isPropPropTrunc (subtreesMB p) (subtreesMB q) j

-- The coinduction principle
bisim : (i : Size) {t u : νM i} → νMB i t u → t ≡ u
subtreesM (bisim i b j) {k} = MRel≡→≡ (mapMRel (bisim k) (subtreesMB b)) j

coind-princ : {t u : νM ∞} → (νMB ∞ t u) ≡ (t ≡ u)
coind-princ =
  hPropExt (isPropνMB ∞) (isSetνM _ _)
           (bisim ∞)
           (J (λ u eq → νMB ∞ _ u) (reflνMB ∞ _))






-- record νMB' (i : Size) (s t : νM i) : Type where
--   coinductive
--   field
--     subtreesMB' : {j : Size< i} → MRel' (νMB' j) (subtreesM s) (subtreesM t)
-- open νMB'

--   swap-tot : (symR : ∀ {x y} → R x y → R y x)
--     → tot R
--   swap-tot symR = 

-- refl-tot : ∀{ℓ}{X : Type ℓ}
--   → {R : X → X → Type ℓ}
--   → (∀ x → R x x)
--   → X → tot R
-- refl-tot reflR x = x , x , reflR x



-- bisimilarity is symmetric and reflexive
-- symνMB : ∀ (j : Size) {t t₁} → νMB j t t₁ → νMB j t₁ t
-- subtreesMB (symνMB j b) with subtreesMB b
-- ... | (r , p , q) = 
--       map (swap-tot (symνMB _)) r ,
--       map-comp fst-tot (swap-tot (symνMB _)) r ∙ q ,
--       map-comp snd-tot (swap-tot (symνMB _)) r ∙ p
-- 
-- reflνMB : (i : Size) (t : νM i) → νMB i t t
-- subtreesMB (reflνMB i t) {j} = 
--     map (refl-tot (reflνMB _)) (subtreesM t) ,
--     map-comp fst-tot (refl-tot (reflνMB _)) (subtreesM t) ∙ map-id (subtreesM t) ,
--     map-comp snd-tot (refl-tot (reflνMB _)) (subtreesM t) ∙ map-id (subtreesM t) 

-- isPropνMB : (i : Size) (t u : νM i) → isProp (νMB i t u)
-- subtreesMB (isPropνMB i t u p q j) = isPropPropTrunc (subtreesMB p) (subtreesMB q) j


-- MEq→Eq : ∀{ℓ} {X : Type ℓ} {s t : M X} → MRel _≡_ s t → s ≡ t
-- MEq→Eq {s = s}{t} (r , p , q) =
--     s ≡⟨ sym p ⟩
--     map fst-tot r ≡⟨ MEq-lem r ⟩
--     map snd-tot r ≡⟨ q ⟩
--     t ∎



-- bisim' : (i : Size) (t u : νM i) → νMB' i t u → t ≡ u
-- subtreesM (bisim' i t u b j) {k} = MEq→Eq' (mapMRel' (bisim' k) (subtreesMB' b)) j

--bisim' : (i : Size) (t u : νM i) (k : Size< i) → MRel (νMB k) (subtreesM t) (subtreesM u) → MRel _≡_ (subtreesM t) (subtreesM u)

--bisim' i t u k = mapMRel (bisim k)


-- MRel⊕ : ∀{ℓ} {X Y : Type ℓ} {R : X → Y → Type ℓ}
--   → {s s' : M X} {t t' : M Y}
--   → MRel R s t → MRel R s' t'
--   → MRel R (s ⊕ s') (t ⊕ t')
-- MRel⊕ (r , p , q) (r' , p' , q') =
--   r ⊕ r' , cong₂ _⊕_ p p' , cong₂ _⊕_ q q'

