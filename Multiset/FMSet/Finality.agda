{-# OPTIONS --safe #-}

module Multiset.FMSet.Finality where

open import Cubical.Foundations.Everything
open import Multiset.Prelude
open import Multiset.Util.SetTruncation using (setTruncEquiv)
open import Multiset.Tote as Tote
open import Multiset.FMSet as FMSet

open import Multiset.Bij
open import Multiset.Bag.Base as Bag
  using
    ( Bag
    ; Vect
    ; BagIsoΣ
    ; ⟨Bij→FinSet⟩≃Idx
    ; isGroupoidBag
    )
open import Multiset.Bag.Properties as Bag
  using (BagLim ; bagLimitEquiv; isGroupoidBagLim)


open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Equiv.Properties using (preCompEquiv)
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Structure
open import Cubical.Data.Nat
open import Cubical.Data.Unit
open import Cubical.Data.Sigma
open import Cubical.HITs.PropositionalTruncation as PT
open import Cubical.HITs.SetTruncation as ST --using (∥_∥₂)
open import Cubical.HITs.SetQuotients as SQ
open import Cubical.Data.Sigma.Properties using (Σ-cong-equiv)

import Multiset.Axioms.Choice as AOC

-- Set truncation is isomorphic to the quotient by the discrete relation

SetTrunc≅SetQuot : {X : Type} → Iso ∥ X ∥₂ (X / _≡_)
Iso.fun SetTrunc≅SetQuot = ST.rec squash/ SQ.[_]
Iso.inv SetTrunc≅SetQuot = SQ.rec isSetSetTrunc ∣_∣₂ (λ _ _ → cong ∣_∣₂)
Iso.rightInv SetTrunc≅SetQuot = SQ.elimProp (λ _ → squash/ _ _) (λ _ → refl)
Iso.leftInv SetTrunc≅SetQuot = ST.elim (λ _ → isProp→isSet (isSetSetTrunc _ _)) (λ _ → refl)

-- Propositonal truncation is isomorphic to the quotient by the total relation

Tot : {X : Type} → X → X → Type
Tot _ _ = Unit

PropTrunc≅SetQuot : {X : Type} → Iso ∥ X ∥₁ (X / Tot)
Iso.fun PropTrunc≅SetQuot = rec→Set squash/ SQ.[_] (λ _ _ → eq/ _ _ tt)
Iso.inv PropTrunc≅SetQuot = SQ.rec (isProp→isSet squash₁) ∣_∣₁ (λ _ _ _ → squash₁ _ _)
Iso.rightInv PropTrunc≅SetQuot = SQ.elimProp (λ _ → squash/ _ _) (λ _ → refl)
Iso.leftInv PropTrunc≅SetQuot = PT.elim (λ _ → isProp→isSet squash₁ _ _) (λ _ → refl)

-- Assuming the axiom of choice, ∥ BagLim ∥₂ is the final coalgebra of FMSet

-- Below, we will assume AC(3,2) and AC(2,1).
-- Here's the precise consequences of these versions of choice that we'll need:
module Choice
  (ac32 : AOC.AC[Gpd,Set] ℓ-zero ℓ-zero)
  (ac : AOC.AC[Set,Prop] ℓ-zero ℓ-zero)
  where
  open import Cubical.HITs.PropositionalTruncation as PT

  ∥θ∥₂ : {A B : Type} → ∥ (A → B) ∥₂ → A → ∥ B ∥₂
  ∥θ∥₂ = ST.rec (isSetΠ (λ _ → squash₂)) (∣_∣₂ ∘_)

  ∥θ∥₁ : {X : Type} {Y : X → Type} → ∥ ((x : X) → Y x) ∥₁ → (x : X) → ∥ Y x ∥₁
  ∥θ∥₁ = PT.rec (isPropΠ (λ _ → squash₁)) (∣_∣₁ ∘_)

  module Hyps {X : Type} {Y : Type} (setX : isSet X) (grpdY : isGroupoid Y) where abstract

    ∥surjective∥₂ : (g : X → ∥ Y ∥₂) → ∥ Σ[ f ∈ (X → Y) ] ((x : X) → ∣ f x ∣₂ ≡ g x) ∥₂
    ∥surjective∥₂ g = AOC.AC[Gpd,Set]→AC[Gpd,Set]-Rel ac32
        (λ x y → ∣ y ∣₂ ≡ g x)
        setX (λ _ → grpdY) (λ _ _ → squash₂ _ _)
        (ST.elim {B = λ z → ∥ Σ[ y ∈ Y ] (∣ y ∣₂ ≡ z) ∥₂}
                  (λ _ → squash₂)
                  (λ y → ∣ y , refl ∣₂) ∘ g)

    ∥θ∥₂InvSec :  (g : X → ∥ Y ∥₂) → Σ[ f ∈ ∥ (X → Y) ∥₂ ] ∥θ∥₂ f ≡ g
    ∥θ∥₂InvSec g =
      ST.rec (isSetΣ squash₂ (λ _ → isProp→isSet (isSetΠ (λ _ → squash₂) _ _)))
             (λ { (f , eq) → ∣ f ∣₂ , funExt eq  })
             (∥surjective∥₂ g)

    ∥θ∥₂Inv :  (X → ∥ Y ∥₂) → ∥ (X → Y) ∥₂
    ∥θ∥₂Inv g = ∥θ∥₂InvSec g .fst

    ∥θ∥₂Sec :  (g : X → ∥ Y ∥₂) → ∥θ∥₂ (∥θ∥₂Inv g) ≡ g
    ∥θ∥₂Sec g = ∥θ∥₂InvSec g .snd

    ∥θ∥₂-inj : (f f' : ∥ (X → Y) ∥₂) → ∥θ∥₂ f ≡ ∥θ∥₂ f' → f ≡ f'
    ∥θ∥₂-inj =
      ST.elim2 (λ _ _ → isSetΠ λ _ → isProp→isSet (squash₂ _ _))
               λ f f' eq →
                 PathIdTrunc₀Iso .Iso.inv
                   (PT.map funExt
                          (ac X (λ x → f x ≡ f' x)
                               setX (λ _ → grpdY _ _)
                               (λ x → PathIdTrunc₀Iso .Iso.fun (λ i → eq i x))))

    ∥θ∥₂Inv-β : (f : X → Y) → ∥θ∥₂Inv (∣_∣₂ ∘ f) ≡ ∣ f ∣₂
    ∥θ∥₂Inv-β f = ∥θ∥₂-inj (∥θ∥₂Inv (∣_∣₂ ∘ f)) ∣ f ∣₂ (∥θ∥₂Sec (∣_∣₂ ∘ f))

    recColl₂ : {A : Type} → isSet A
      → ((X → Y) → A)
      → (X → ∥ Y ∥₂) → A
    recColl₂ setA h g = ST.rec setA h (∥θ∥₂Inv g)

    recCollβ₂ : {A : Type} (setA : isSet A)
      → (g : (X → Y) → A)
      → (f : X → Y) → recColl₂ setA g (∣_∣₂ ∘ f) ≡ g f
    recCollβ₂ {A} setA h f = cong (ST.rec setA h) (∥θ∥₂Inv-β f)

    elimCollProp₂' : (B : (X → ∥ Y ∥₂) → Type) → (∀ c → isProp (B c))
      → ((c : X → Y) → B (∣_∣₂ ∘ c))
      → (c : ∥ (X → Y) ∥₂) → B (∥θ∥₂ c)
    elimCollProp₂' B propB h = ST.elim (λ _ → isProp→isSet (propB _)) h

    elimCollProp₂ : (B : (X → ∥ Y ∥₂) → Type) → (∀ c → isProp (B c))
      → ((c : X → Y) → B (∣_∣₂ ∘ c))
      → (c : X → ∥ Y ∥₂) → B c
    elimCollProp₂ B propB h c =
      subst B (∥θ∥₂Sec c) (elimCollProp₂' B propB h (∥θ∥₂Inv c))

  module Hyps2 {X : Type} (Y : X → Type)
               (setX : isSet X) (setY : ∀ x → isSet (Y x))
               where abstract

    ∥θ∥₁Inv : ((x : X) → ∥ Y x ∥₁) → ∥ ((x : X) → Y x) ∥₁
    ∥θ∥₁Inv = ac X Y setX setY

    elimCollProp₁' :  (B : ((x : X) → ∥ Y x ∥₁) → Type) → (∀ c → isProp (B c))
      → ((c : (x : X) → Y x) → B (∣_∣₁ ∘ c))
      → (c : ∥ ((x : X) → Y x) ∥₁) → B (∥θ∥₁ c)
    elimCollProp₁' B propB h = PT.elim (λ _ → propB _) h

    elimCollProp₁ :  (B : ((x : X) → ∥ Y x ∥₁) → Type) → (∀ c → isProp (B c))
      → ((c : (x : X) → Y x) → B (∣_∣₁ ∘ c))
      → (c : (x : X) → ∥ Y x ∥₁) → B c
    elimCollProp₁ B propB h c =
      subst B (isPropΠ (λ _ → squash₁) _ _) (elimCollProp₁' B propB h (∥θ∥₁Inv c))


module FinalityWithChoice

-- -- BagLim is the final coalgebra of Bag [Ahrens 2015]
  (ana : {X : Type} → (c : X → Bag X) → X → BagLim)
  (anaEq : {X : Type} (c : X → Bag X) 
    → ana c ≡ Bag.fix⁺ ∘ Bag.map (ana c) ∘ c)
  (anaUniq : {X : Type} (c : X → Bag X)
    → (h : X → BagLim)
    → h ≡ Bag.fix⁺ ∘ (Bag.map h) ∘ c
    → ana c ≡ h)

-- -- ∥ Bag Y ∥₂ is naturally equivalent to FMSet Y, which follows from Theorems 6 and 8.
-- -- For reasons beyond our understanding, Agda has trouble type-checking a particular
-- -- equivalence, so we postulate it here.  See the comment in Multiset.FMSet.Fixpoint
-- -- for an explanation of what goes wrong.
   (e : {Y : Type} → ∥ Bag Y ∥₂ ≃ FMSet Y)
   (eNat : ∀{Y Z} (f : Y → Z)→ equivFun e ∘ ST.map (Bag.map f) ≡ FMSet.map f ∘ equivFun e)

-- Two forms of axiom of choice
  (ac32 : AOC.AC[Gpd,Set] ℓ-zero ℓ-zero)
  (ac : AOC.AC[Set,Prop] ℓ-zero ℓ-zero)
   (X : Type) (setX : isSet X)
   where

  open Choice ac32 ac
  open Hyps setX (isGroupoidBag (isSet→isGroupoid setX))
  module Hyps' = Hyps {Y = BagLim} setX isGroupoidBagLim
  module Hyps2' {c : X → Bag X} {h : X → BagLim} = Hyps2 (λ x → h x ≡ (Bag.fix⁺ ∘ Bag.map h ∘ c) x) setX (λ x → isGroupoidBagLim _ _)

  unfold : FMSet ∥ BagLim ∥₂ ≃ ∥ BagLim ∥₂
  unfold = compEquiv STInvariance.STInvarianceEquiv (compEquiv (invEquiv e) (setTruncEquiv bagLimitEquiv))

  unfoldEq : compEquiv (invEquiv (STInvariance.STInvarianceEquiv)) unfold ≡ compEquiv (invEquiv e) (setTruncEquiv bagLimitEquiv)
  unfoldEq =
    compEquiv-assoc _ _ _
    ∙ cong (λ x → compEquiv x (compEquiv (invEquiv e) (setTruncEquiv bagLimitEquiv))) (invEquiv-is-linv _)
    ∙ compEquivIdEquiv _
  
  ana₂' : (c : X → Bag X) → X → ∥ BagLim ∥₂
  ana₂' c = ∣_∣₂ ∘ ana c

  ana₂ : (c : X → FMSet X) → X → ∥ BagLim ∥₂
  ana₂ c = recColl₂ (isSetΠ (λ _ → isSetSetTrunc)) ana₂' (invEq e ∘ c)

  ana₂Eq : (c : X → FMSet X) 
    → ana₂ c ≡ equivFun unfold ∘ FMSet.map (ana₂ c) ∘ c
  ana₂Eq c =
    elimCollProp₂ (λ c → recColl₂ (isSetΠ (λ _ → isSetSetTrunc)) ana₂' c ≡ equivFun unfold ∘ FMSet.map (recColl₂ (isSetΠ (λ _ → isSetSetTrunc)) ana₂' c) ∘ equivFun e ∘ c)
                 (λ c → isSetΠ (λ _ → isSetSetTrunc) _ _)
                 (λ c → recCollβ₂ (isSetΠ (λ _ → isSetSetTrunc)) ana₂' c
                        ∙ cong (∣_∣₂ ∘_) (anaEq c)
                        ∙ cong (λ x → ST.map Bag.fix⁺ ∘ x ∘ ST.map (Bag.map (ana c)) ∘ ∣_∣₂ ∘ c) (sym (funExt (retEq e)))
                        ∙ cong (λ x → ST.map Bag.fix⁺ ∘ invEq e ∘ x ∘ ∣_∣₂ ∘ c) (eNat (ana c))
                        ∙ cong (λ x → x ∘ FMSet.map (ana c) ∘ equivFun e ∘ ∣_∣₂ ∘ c) (sym (cong equivFun unfoldEq))
                        ∙ cong (λ x → equivFun unfold ∘ x ∘ equivFun e ∘ ∣_∣₂ ∘ c) (funExt (mapComp ∣_∣₂ (ana c))) 
                        ∙ cong (λ x → equivFun unfold ∘ FMSet.map x ∘ equivFun e ∘ ∣_∣₂ ∘ c) (sym (recCollβ₂ (isSetΠ (λ _ → isSetSetTrunc)) ana₂' c)))
                 (invEq e ∘ c)
    ∙ cong (λ x → equivFun unfold ∘ FMSet.map (ana₂ c) ∘ x ∘ c) (funExt (secEq e))


  ana₂Uniq : (c : X → FMSet X)
    → (h : X → ∥ BagLim ∥₂)
    → h ≡ equivFun unfold ∘ FMSet.map h ∘ c
    → ana₂ c ≡ h
  ana₂Uniq c h eq =
    elimCollProp₂ (λ c → (h : X → ∥ BagLim ∥₂) → h ≡ equivFun unfold ∘ FMSet.map h ∘ equivFun e ∘ c → recColl₂ (isSetΠ (λ _ → isSetSetTrunc)) ana₂' c ≡ h)
                 (λ _ → isPropΠ (λ _ → isPropΠ (λ _ → isSetΠ (λ _ → isSetSetTrunc) _ _)))
                 (λ c → Hyps'.elimCollProp₂ 
                                      (λ h → h ≡ equivFun unfold ∘ FMSet.map h ∘ equivFun e ∘ ∣_∣₂ ∘ c → recColl₂ (isSetΠ (λ _ → isSetSetTrunc)) ana₂' (∣_∣₂ ∘ c) ≡ h)
                                      (λ _ → isPropΠ (λ _ → isSetΠ (λ _ → isSetSetTrunc) _ _))
                                      λ h eq → let eq' = eq
                                                         ∙ cong (λ x → equivFun unfold ∘ x ∘ equivFun e ∘ ∣_∣₂ ∘ c) (sym (funExt (FMSet.mapComp ∣_∣₂ h)))
                                                         ∙ cong (λ x → x ∘ FMSet.map h ∘ equivFun e ∘ ∣_∣₂ ∘ c) (cong equivFun unfoldEq)
                                                         ∙ cong (λ x → ST.map Bag.fix⁺ ∘ invEq e ∘ x ∘ ∣_∣₂ ∘ c) (sym (eNat h))
                                                         ∙ cong (λ x → ST.map Bag.fix⁺ ∘ x ∘ ST.map (Bag.map h) ∘ ∣_∣₂ ∘ c) (funExt (retEq e)) in
                                                Hyps2'.elimCollProp₁ 
                                                              (λ _ → recColl₂ (isSetΠ (λ _ → isSetSetTrunc)) ana₂' (∣_∣₂ ∘ c) ≡ ∣_∣₂ ∘ h)
                                                              (λ _ → isSetΠ (λ _ → isSetSetTrunc) _ _)
                                                              (λ eq'' → recCollβ₂ (isSetΠ (λ _ → isSetSetTrunc)) ana₂' c ∙ cong (∣_∣₂ ∘_) (anaUniq c h (funExt eq'')))
                                                              (λ x → Iso.fun PathIdTrunc₀Iso (funExt⁻ eq' x)))
                 _
                 h
                 (eq ∙ cong (λ x → equivFun unfold ∘ FMSet.map h ∘ x ∘ c) (sym (funExt (secEq e))))

  
  isContrAna : (c : X → FMSet X)
    → isContr (Σ[ h ∈ (X → ∥ BagLim ∥₂) ] h ≡ equivFun unfold ∘ FMSet.map h ∘ c)
  isContrAna c =
    ( (ana₂ c , ana₂Eq c) -- existence
    , λ { (h , is-ana)
        → Σ≡Prop (λ c → isOfHLevelPath' 1 (isSetΠ λ _ → isSetSetTrunc) c _) (ana₂Uniq c h is-ana) -- uniqueness
      }
    )
