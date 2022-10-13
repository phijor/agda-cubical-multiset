{-# OPTIONS --sized-types #-}

module Multiset.Coinductive.Setoid where

open import Multiset.Coinductive.Size
open import Multiset.Coinductive.Trees

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
open import Cubical.Relation.Binary hiding (Rel)
open BinaryRelation 
open isEquivRel

open import Multiset.ListQuotient.Base

-- type of setoids
record Setoid ℓ : Type (ℓ-suc ℓ) where
  constructor setoid
  field
    Carr : Type ℓ
    Rel : Carr → Carr → Type ℓ
    propRel : isPropValued Rel
    eqrRel : isEquivRel Rel
open Setoid public

Setoid₀ = Setoid ℓ-zero

-- type of setoid morphisms
record _→S_ {ℓ} (S₁ S₂ : Setoid ℓ) : Type ℓ where
  constructor _,_
  field
    mor : S₁ .Carr → S₂ .Carr
    morRel : ∀{x y} → S₁ .Rel x y → S₂ .Rel (mor x) (mor y)
open _→S_ public

-- equality of setoid morphisms
_≡S_ : ∀{ℓ} {S₁ S₂ : Setoid ℓ} (f g : S₁ →S S₂) → Type ℓ
_≡S_ {S₂ = S₂} f g = ∀ x → S₂ .Rel (f .mor x) (g .mor x)

-- the identity setoid morphism
idS : ∀{ℓ} {S : Setoid ℓ} → S →S S
idS = (λ x → x) , λ r → r

-- composition of setoid morphisms
infix 21 _∘S_
_∘S_ : ∀{ℓ} {S₁ S₂ S₃ : Setoid ℓ}
  → (g : S₂ →S S₃) (f : S₁ →S S₂)
  → S₁ →S S₃
(g , gr) ∘S (f , fr) = g ∘ f , gr ∘ fr

-- from sets to setoids
Set→Setoid : ∀{ℓ} → hSet ℓ → Setoid ℓ
Set→Setoid (X , Xset) =
  setoid X _≡_  Xset (equivRel (λ _ → refl) (λ _ _ → sym) λ _ _ _ → _∙_)

-- surjective setoid morphisms
isSurjectionS : ∀{ℓ}{S T : Setoid ℓ} → S →S T → Type ℓ
isSurjectionS {T = T} (f , _) = ∀ y → ∃[ x ∈ _ ] T .Rel (f x) y

-- the finite bag functor on setoids
MS : Setoid₀ → Setoid₀
MS (setoid A R propR eqrR) =
  setoid (List A) (Relator R) (isPropRelator R) (isEquivRelRelator eqrR)

-- the final coalgebra of MS
νMS : Setoid₀
νMS = setoid (Tree ∞) (ExtEq ∞) isPropExtEq isEquivRelExtEq

subtreesS : νMS →S MS νMS
subtreesS = (λ x → subtrees x) , (λ r → subtreesE r)

mapMS : {S₁ S₂ : Setoid₀} (f : S₁ →S S₂)
  → MS S₁ →S MS S₂
mapMS {_}{S₂} (f , fr) = mapList f , mapRelator' fr

module _
  (S : Setoid₀)
  (cS : S →S MS S)
  where

  c = cS .mor
  cRel = cS .morRel

-- existence of anamorphism in setoids
  anaMS : S →S νMS
  anaMS = anaTree c ∞ , λ r → anaTreeRel _ cRel _ r --anaTreeRel r ∞

  anaMSEq : subtreesS ∘S anaMS ≡S mapMS anaMS ∘S cS
  anaMSEq x = reflRelator (reflExtEq ∞) _

-- uniqueness
  anaPfinUniq' : (fS : S →S νMS)
    → (∀ (s : Size) x → Relator (ExtEq s) (subtrees (fS .mor x)) (mapList (fS .mor) (c x)))
    → (j : Size) → ∀ x → ExtEq j (fS .mor x) (anaTree c ∞ x)
  subtreesE (anaPfinUniq' fS fSeq j x) {k} = 
    transRelator (transExtEq k)
                 (fSeq k x)
                 (ListRel→Relator (symExtEq k) (mapListRel-fun (anaPfinUniq' fS fSeq k) _))

  anaPfinUniq : (fS : S →S νMS)
    → subtreesS ∘S fS ≡S mapMS fS ∘S cS
    → fS ≡S anaMS
  anaPfinUniq fS fSeq = anaPfinUniq' fS (λ s x → fSeq x .fst , fSeq x .snd) ∞

