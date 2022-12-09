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
   (ac32 : {A : Type} {B : A → Type} (R : (a : A) → B a → Type)
     → isSet A → (∀ a → isGroupoid (B a)) → (∀ a b → isProp (R a b))
     → ((a : A) → ∥ (Σ[ b ∈ B a ] R a b ) ∥₂)
     → ∥ Σ[ f ∈ ((a : A) → B a) ] ((a : A) → R a (f a)) ∥₂)
   (ac : {A : Type} (B : A → Type)
     → isSet A → (∀ a → isSet (B a))
     → ((a : A) → ∥ B a ∥₁)
     → ∥ ((a : A) → B a) ∥₁)
   (X : Type) (setX : isSet X)
   where

  open ChoiceForTheorem11 ac32 ac
  open Hyps setX (isGroupoidBag (isSet→isGroupoid setX))
  module Hyps' = Hyps {Y = BagLim} setX {!!} 
  module Hyps2' {c : X → Bag X} {h : X → BagLim} = Hyps2 (λ x → h x ≡ (Bag.fix⁺ ∘ Bag.map h ∘ c) x) setX (λ x → {!!})

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
