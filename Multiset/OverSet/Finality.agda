{-# OPTIONS --safe #-}

module Multiset.OverSet.Finality where

open import Cubical.Foundations.Everything
open import Multiset.Prelude
open import Multiset.Util.SetTruncation using (setTruncEquiv)
open import Multiset.OverGroupoid as OverGroupoid renaming (FMSet to Tote)
open import Multiset.OverSet as OverSet 
open import Multiset.Chains
open Limit
open ChainLimit

open import Multiset.Bij
open import Multiset.OverBij.Base as OverBij
  using
    ( Bag
    ; Vect
    ; BagIsoΣ
    ; ⟨Bij→FinSet⟩≃Idx
    )
open import Multiset.OverBij.Properties as OverBij
--  using (bagLimitIso)
  renaming (ωTree to BagLim)


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

open import Multiset.AxiomChoice

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

module _

-- -- BagLim is the final coalgebra of Bag [Ahrens 2015]
  (ana : {X : Type} → (c : X → Bag X) → X → BagLim)
  (anaEq : {X : Type} (c : X → Bag X) 
    → ana c ≡ Iso.inv bagLimitIso ∘ OverBij.map (ana c) ∘ c)
  (anaUniq : {X : Type} (c : X → Bag X)
    → (h : X → BagLim)
    → h ≡ Iso.inv bagLimitIso ∘ (OverBij.map h) ∘ c
    → ana c ≡ h)

-- -- ∥ Bag Y ∥₂ is naturally equivalent to FMSet Y, which follows from Theorems 6 and 8.
-- -- For reasons beyond our understanding, Agda has trouble type-checking a particular
-- -- equivalence, so we postulate it here.  See the comment in Multiset.OverSet.Fixpoint
-- -- for an explanation of what goes wrong.
   (e : {Y : Type} → ∥ Bag Y ∥₂ ≃ FMSet Y)
   (eNat : ∀{Y Z} (f : Y → Z)→ equivFun e ∘ ST.map (OverBij.map f) ≡ OverSet.map f ∘ equivFun e)

-- -- The consequences of the axiom of choice that we need
   (recColl : {A : Type}{B : A → Type}
      → (R : ∀ a → B a → B a → Type){C : Type}
      → (setC : isSet C)
      → ([_]C : (g : ∀ a → B a) → C)
      → (eqC : ∀ g g' (r : PW-d R g g') → [ g ]C ≡ [ g' ]C)
      → (f : ∀ a → B a / R a) → C)
   (recCollβ : {A : Type}{B : A → Type}
      → (R : ∀ a → B a → B a → Type)
      → {C : Type}
      → (setC : isSet C)
      → ([_]C : (g : ∀ a → B a) → C)
      → (eqC : ∀ g g' (r : PW-d R g g') → [ g ]C ≡ [ g' ]C)
      → (g : ∀ a → B a)
      → recColl R setC [_]C eqC (SQ.[_] ∘ g) ≡ [ g ]C)
    (elimCollProp : {A : Type}{B : A → Type}
      → (R : ∀ a → B a → B a → Type)
      → (C : (∀ a → B a / R a) → Type)
      → (propC : ∀ f → isProp (C f))
      → ([_]C : (g : ∀ a → B a) → C (SQ.[_] ∘ g))
      → (f : ∀ a → B a / R a) → C f) where


  unfold : FMSet ∥ BagLim ∥₂ ≃ ∥ BagLim ∥₂
  unfold = compEquiv STInvariance.STInvarianceEquiv (compEquiv (invEquiv e) (setTruncEquiv (invEquiv bagLimitEquiv)))

  unfoldEq : compEquiv (invEquiv (STInvariance.STInvarianceEquiv)) unfold ≡ compEquiv (invEquiv e) (setTruncEquiv (invEquiv bagLimitEquiv))
  unfoldEq =
    compEquiv-assoc _ _ _
    ∙ cong (λ x → compEquiv x (compEquiv (invEquiv e) (setTruncEquiv (invEquiv bagLimitEquiv)))) (invEquiv-is-linv _)
    ∙ compEquivIdEquiv _
  
  recColl₂ : {X Y A : Type} → isSet A
    → ((X → Y) → A)
    → (X → ∥ Y ∥₂) → A
  recColl₂ {X}{Y}{A} setA g f =
    recColl (λ _ → _≡_) setA g (λ _ _ p → cong g (funExt p)) (Iso.fun SetTrunc≅SetQuot ∘ f) 

  recCollβ₂ : {X Y A : Type} (setA : isSet A)
    → (g : (X → Y) → A)
    → (f : X → Y) → recColl₂ setA g (∣_∣₂ ∘ f) ≡ g f
  recCollβ₂ {X}{Y}{A} setA g f =
    recCollβ (λ _ → _≡_) setA g (λ _ _ p → cong g (funExt p)) f

  elimCollProp₂' : {X Y : Type} (B : (X → ∥ Y ∥₂) → Type) → (∀ c → isProp (B c))
    → ((c : X → Y) → B (∣_∣₂ ∘ c))
    → (c : X → Y / _≡_) → B (Iso.inv SetTrunc≅SetQuot ∘ c)
  elimCollProp₂' B propB g f =
    elimCollProp (λ _ → _≡_)
                 (λ h → B (Iso.inv SetTrunc≅SetQuot ∘ h))
                 (λ _ → propB _)
                 g
                 f

  elimCollProp₂ : {X Y : Type} (B : (X → ∥ Y ∥₂) → Type) → (∀ c → isProp (B c))
    → ((c : X → Y) → B (∣_∣₂ ∘ c))
    → (c : X → ∥ Y ∥₂) → B c
  elimCollProp₂ B propB g f =
    subst B
          (funExt (λ x → Iso.leftInv SetTrunc≅SetQuot (f x)))
          (elimCollProp₂' B propB g (Iso.fun SetTrunc≅SetQuot ∘ f))

  elimCollProp₁' : {X : Type} {Y : X → Type}
    → (B : ((x : X) → ∥ Y x ∥₁) → Type) → (∀ c → isProp (B c))
    → ((c : (x : X) → Y x) → B (∣_∣₁ ∘ c))
    → (c : (x : X) → (Y x) / Tot) → B (Iso.inv PropTrunc≅SetQuot ∘ c)
  elimCollProp₁' B propB g c =
    elimCollProp (λ _ _ _ → Unit)
                 (λ f → B (Iso.inv PropTrunc≅SetQuot ∘ f))
                 (λ _ → propB _)
                 g
                 c

  elimCollProp₁ : {X : Type} {Y : X → Type}
    → (B : ((x : X) → ∥ Y x ∥₁) → Type) → (∀ c → isProp (B c))
    → ((c : (x : X) → Y x) → B (∣_∣₁ ∘ c))
    → (c : (x : X) → ∥ Y x ∥₁) → B c
  elimCollProp₁ B propB g f = 
    subst B
          (funExt (λ x → Iso.leftInv PropTrunc≅SetQuot (f x)))
          (elimCollProp₁' B propB g (Iso.fun PropTrunc≅SetQuot ∘ f))


  ana₂' : {X : Type} (c : X → Bag X) → X → ∥ BagLim ∥₂
  ana₂' c = ∣_∣₂ ∘ ana c

  ana₂ : {X : Type} (c : X → FMSet X) → X → ∥ BagLim ∥₂
  ana₂ c = recColl₂ (isSetΠ (λ _ → isSetSetTrunc)) ana₂' (invEq e ∘ c)

  ana₂Eq : {X : Type} (c : X → FMSet X) 
    → ana₂ c ≡ equivFun unfold ∘ OverSet.map (ana₂ c) ∘ c
  ana₂Eq c =
    elimCollProp₂ (λ c → recColl₂ (isSetΠ (λ _ → isSetSetTrunc)) ana₂' c ≡ equivFun unfold ∘ OverSet.map (recColl₂ (isSetΠ (λ _ → isSetSetTrunc)) ana₂' c) ∘ equivFun e ∘ c)
                 (λ c → isSetΠ (λ _ → isSetSetTrunc) _ _)
                 (λ c → recCollβ₂ (isSetΠ (λ _ → isSetSetTrunc)) ana₂' c
                        ∙ cong (∣_∣₂ ∘_) (anaEq c)
                        ∙ cong (λ x → ST.map (Iso.inv bagLimitIso) ∘ x ∘ ST.map (OverBij.map (ana c)) ∘ ∣_∣₂ ∘ c) (sym (funExt (retEq e)))
                        ∙ cong (λ x → ST.map (Iso.inv bagLimitIso) ∘ invEq e ∘ x ∘ ∣_∣₂ ∘ c) (eNat (ana c))
                        ∙ cong (λ x → x ∘ OverSet.map (ana c) ∘ equivFun e ∘ ∣_∣₂ ∘ c) (sym (cong equivFun unfoldEq))
                        ∙ cong (λ x → equivFun unfold ∘ x ∘ equivFun e ∘ ∣_∣₂ ∘ c) (funExt (mapComp ∣_∣₂ (ana c))) 
                        ∙ cong (λ x → equivFun unfold ∘ OverSet.map x ∘ equivFun e ∘ ∣_∣₂ ∘ c) (sym (recCollβ₂ (isSetΠ (λ _ → isSetSetTrunc)) ana₂' c)))
                 (invEq e ∘ c)
    ∙ cong (λ x → equivFun unfold ∘ OverSet.map (ana₂ c) ∘ x ∘ c) (funExt (secEq e))


  ana₂Uniq : {X : Type} (c : X → FMSet X)
    → (h : X → ∥ BagLim ∥₂)
    → h ≡ equivFun unfold ∘ OverSet.map h ∘ c
    → ana₂ c ≡ h
  ana₂Uniq {X} c h eq =
    elimCollProp₂ (λ c → (h : X → ∥ BagLim ∥₂) → h ≡ equivFun unfold ∘ OverSet.map h ∘ equivFun e ∘ c → recColl₂ (isSetΠ (λ _ → isSetSetTrunc)) ana₂' c ≡ h)
                 (λ _ → isPropΠ (λ _ → isPropΠ (λ _ → isSetΠ (λ _ → isSetSetTrunc) _ _)))
                 (λ c → elimCollProp₂ (λ h → h ≡ equivFun unfold ∘ OverSet.map h ∘ equivFun e ∘ ∣_∣₂ ∘ c → recColl₂ (isSetΠ (λ _ → isSetSetTrunc)) ana₂' (∣_∣₂ ∘ c) ≡ h)
                                      (λ _ → isPropΠ (λ _ → isSetΠ (λ _ → isSetSetTrunc) _ _))
                                      λ h eq → let eq' = eq
                                                         ∙ cong (λ x → equivFun unfold ∘ x ∘ equivFun e ∘ ∣_∣₂ ∘ c) (sym (funExt (OverSet.mapComp ∣_∣₂ h)))
                                                         ∙ cong (λ x → x ∘ OverSet.map h ∘ equivFun e ∘ ∣_∣₂ ∘ c) (cong equivFun unfoldEq)
                                                         ∙ cong (λ x → ST.map (Iso.inv bagLimitIso) ∘ invEq e ∘ x ∘ ∣_∣₂ ∘ c) (sym (eNat h))
                                                         ∙ cong (λ x → ST.map (Iso.inv bagLimitIso) ∘ x ∘ ST.map (OverBij.map h) ∘ ∣_∣₂ ∘ c) (funExt (retEq e)) in
                                                elimCollProp₁ (λ _ → recColl₂ (isSetΠ (λ _ → isSetSetTrunc)) ana₂' (∣_∣₂ ∘ c) ≡ ∣_∣₂ ∘ h)
                                                              (λ _ → isSetΠ (λ _ → isSetSetTrunc) _ _)
                                                              (λ eq'' → recCollβ₂ (isSetΠ (λ _ → isSetSetTrunc)) ana₂' c ∙ cong (∣_∣₂ ∘_) (anaUniq c h (funExt eq'')))
                                                              (λ x → Iso.fun PathIdTrunc₀Iso (funExt⁻ eq' x)))
                 _
                 h
                 (eq ∙ cong (λ x → equivFun unfold ∘ OverSet.map h ∘ x ∘ c) (sym (funExt (secEq e))))

  
  isContrAna : ∀ {X : Type} → (c : X → FMSet X)
    → isContr (Σ[ h ∈ (X → ∥ BagLim ∥₂) ] h ≡ equivFun unfold ∘ OverSet.map h ∘ c)
  isContrAna c =
    ( (ana₂ c , ana₂Eq c) -- existence
    , λ { (h , is-ana)
        → Σ≡Prop (λ c → isOfHLevelPath' 1 (isSetΠ λ _ → isSetSetTrunc) c _) (ana₂Uniq c h is-ana) -- uniqeness
      }
    )
