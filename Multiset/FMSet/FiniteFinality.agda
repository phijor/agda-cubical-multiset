{-# OPTIONS --safe #-}

module Multiset.FMSet.FiniteFinality where

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

open import Multiset.FMSet.Finality
open import Multiset.FiniteChoice
open import Cubical.Data.SumFin

module FinalityFinite

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

  (n : ℕ)
  where

  unfold : FMSet ∥ BagLim ∥₂ ≃ ∥ BagLim ∥₂
  unfold = compEquiv STInvariance.STInvarianceEquiv (compEquiv (invEquiv e) (setTruncEquiv bagLimitEquiv))

  unfoldEq : compEquiv (invEquiv (STInvariance.STInvarianceEquiv)) unfold ≡ compEquiv (invEquiv e) (setTruncEquiv bagLimitEquiv)
  unfoldEq =
    compEquiv-assoc _ _ _
    ∙ cong (λ x → compEquiv x (compEquiv (invEquiv e) (setTruncEquiv bagLimitEquiv))) (invEquiv-is-linv _)
    ∙ compEquivIdEquiv _
  
  ana₂' : (c : Fin n → Bag (Fin n)) → Fin n → ∥ BagLim ∥₂
  ana₂' c = ∣_∣₂ ∘ ana c

  ana₂ : (c : Fin n → FMSet (Fin n)) → Fin n → ∥ BagLim ∥₂
  ana₂ c = recₙ (isSetΠ (λ _ → isSetSetTrunc)) ana₂' (invEq e ∘ c)

  ana₂Eq : (c : Fin n → FMSet (Fin n)) 
    → ana₂ c ≡ equivFun unfold ∘ FMSet.map (ana₂ c) ∘ c
  ana₂Eq c =
    elimₙ {B = λ c → recₙ (isSetΠ (λ _ → isSetSetTrunc)) ana₂' c ≡ equivFun unfold ∘ FMSet.map (recₙ (isSetΠ (λ _ → isSetSetTrunc)) ana₂' c) ∘ equivFun e ∘ c}
          (λ c → isProp→isSet (λ x y i j k → isSetSetTrunc _ _ (λ i → x i k) (λ i → y i k) i j))
          (λ c → elimₙ-comp {B = λ _ → Fin n → ∥ BagLim ∥₂} (λ _ → isSetΠ (λ _ → isSetSetTrunc)) ana₂' c
                  ∙ cong (∣_∣₂ ∘_) (anaEq c)
                  ∙ cong (λ x → ST.map Bag.fix⁺ ∘ x ∘ ST.map (Bag.map (ana c)) ∘ ∣_∣₂ ∘ c) (sym (funExt (retEq e)))
                  ∙ cong (λ x → ST.map Bag.fix⁺ ∘ invEq e ∘ x ∘ ∣_∣₂ ∘ c) (eNat (ana c))
                  ∙ cong (λ x → x ∘ FMSet.map (ana c) ∘ equivFun e ∘ ∣_∣₂ ∘ c) (sym (cong equivFun unfoldEq))
                  ∙ cong (λ x → equivFun unfold ∘ x ∘ equivFun e ∘ ∣_∣₂ ∘ c) (funExt (mapComp ∣_∣₂ (ana c))) 
                  ∙ cong (λ x → equivFun unfold ∘ FMSet.map x ∘ equivFun e ∘ ∣_∣₂ ∘ c) (sym (elimₙ-comp {B = λ _ → Fin n → ∥ BagLim ∥₂} (λ _ → isSetΠ (λ _ → isSetSetTrunc)) ana₂' c)))
          (invEq e ∘ c)
    ∙ cong (λ x → equivFun unfold ∘ FMSet.map (ana₂ c) ∘ x ∘ c) (funExt (secEq e))

  ana₂Uniq : (c : Fin n → FMSet (Fin n))
    → (h : Fin n → ∥ BagLim ∥₂)
    → h ≡ equivFun unfold ∘ FMSet.map h ∘ c
    → ana₂ c ≡ h
  ana₂Uniq c h eq =
    elim2ₙ {B = λ c h → h ≡ equivFun unfold ∘ FMSet.map h ∘ equivFun e ∘ c → recₙ (isSetΠ (λ _ → isSetSetTrunc)) ana₂' c ≡ h}
          (λ _ _ → isSetΠ (λ _ → isProp→isSet (λ x y i j k → isSetSetTrunc _ _ (λ i → x i k) (λ i → y i k) i j)))
          (λ c h eq → let eq' = eq
                                 ∙ cong (λ x → equivFun unfold ∘ x ∘ equivFun e ∘ ∣_∣₂ ∘ c) (sym (funExt (FMSet.mapComp ∣_∣₂ h)))
                                 ∙ cong (λ x → x ∘ FMSet.map h ∘ equivFun e ∘ ∣_∣₂ ∘ c) (cong equivFun unfoldEq)
                                 ∙ cong (λ x → ST.map Bag.fix⁺ ∘ invEq e ∘ x ∘ ∣_∣₂ ∘ c) (sym (eNat h))
                                 ∙ cong (λ x → ST.map Bag.fix⁺ ∘ x ∘ ST.map (Bag.map h) ∘ ∣_∣₂ ∘ c) (funExt (retEq e)) in elimₙ-comp {B = λ _ → Fin n → ∥ BagLim ∥₂} (λ _ → isSetΠ (λ _ → isSetSetTrunc)) ana₂' c ∙ funExt (Iso.inv PathIdTrunc₀Iso ∘ unbox₁ (PT.map (λ r → funExt⁻ (anaUniq c h (funExt r))) (box₁ (Iso.fun PathIdTrunc₀Iso ∘ funExt⁻ eq')))))
          (invEq e ∘ c)
          h
          (eq ∙ cong (λ x → equivFun unfold ∘ FMSet.map h ∘ x ∘ c) (sym (funExt (secEq e))))

  isContrAna : (c : Fin n → FMSet (Fin n))
    → isContr (Σ[ h ∈ (Fin n → ∥ BagLim ∥₂) ] h ≡ equivFun unfold ∘ FMSet.map h ∘ c)
  isContrAna c =
    ( (ana₂ c , ana₂Eq c) -- existence
    , λ { (h , is-ana)
        → Σ≡Prop (λ c → isOfHLevelPath' 1 (isSetΠ λ _ → isSetSetTrunc) c _) (ana₂Uniq c h is-ana) -- uniqueness
      }
    )
