{-# OPTIONS --safe #-}

module Multiset.FMSet.Fixpoint where

open import Multiset.Prelude
open import Multiset.Functor
open import Multiset.Limit.TerminalChain using (_^_)
open import Multiset.Util.SetTruncation as STExt using (setTruncEquiv)
open import Multiset.Tote as Tote using (Tote ; FMSet≃∥Tote∥₂ ; ∥Tote∥₂→FMSet)
open import Multiset.FMSet as FMSet

open import Multiset.Bag.Base as Bag using (Bag ; Bag≃Tote ; isNaturalBagToteEquiv)
open import Multiset.Bag.Properties as Bag
  using (bagLimitEquiv ; BagLim)


open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Function using (_∘_)
open import Cubical.Foundations.Transport using (substEquiv)
open import Cubical.Foundations.Univalence using (ua)
open import Cubical.Data.Nat.Base using (zero ; suc)
open import Cubical.Data.Unit.Properties using (isSetUnit*)
open import Cubical.HITs.SetTruncation as ST using (∥_∥₂)

TruncBagFMSetEquiv : ∀ {ℓ} {X : Type ℓ} → ∥ Bag X ∥₂ ≃ FMSet X
TruncBagFMSetEquiv = setTruncEquiv Bag≃Tote ∙ₑ invEquiv (FMSet≃∥Tote∥₂)

IterTruncBagFMSetEquiv : ∀ n → ∥ Bag ^ n ∥₂ ≃ FMSet ^ n
IterTruncBagFMSetEquiv zero = ST.setTruncIdempotent≃ isSetUnit*
IterTruncBagFMSetEquiv (suc n) =
  ∥ Bag (Bag ^ n) ∥₂  ≃⟨ TruncBagFMSetEquiv {X = Bag ^ n} ⟩
  FMSet (Bag ^ n)     ≃⟨ invEquiv STInvarianceEquiv ⟩
  FMSet ∥ Bag ^ n ∥₂  ≃⟨ substEquiv FMSet (ua (IterTruncBagFMSetEquiv n)) ⟩
  FMSet (FMSet ^ n)   ■

abstract
  isNaturalTruncBagFMSetEquiv : ∀ {X Y : Type}
    → (f : X → Y) → equivFun TruncBagFMSetEquiv ∘ ST.map (Bag.map f) ≡ FMSet.map f ∘ equivFun TruncBagFMSetEquiv
  isNaturalTruncBagFMSetEquiv {X = X} {Y = Y} f =
    let
      Bag→Tote : ∀ {Z} → Bag Z → Tote Z
      Bag→Tote = equivFun Bag≃Tote
    in
    equivFun TruncBagFMSetEquiv ∘ ST.map (Bag.map f) ≡⟨⟩
    ∥Tote∥₂→FMSet ∘ (ST.map Bag→Tote ∘ ST.map (Bag.map f)) ≡⟨ cong (invEq FMSet≃∥Tote∥₂ ∘_) (funExt (STExt.map∘map (Bag.map f) Bag→Tote)) ⟩
    ∥Tote∥₂→FMSet ∘ (ST.map (Bag→Tote ∘ Bag.map f))        ≡⟨ cong (λ γ → ∥Tote∥₂→FMSet ∘ (ST.map γ)) (isNaturalBagToteEquiv f) ⟩
    ∥Tote∥₂→FMSet ∘ (ST.map (Tote.map f ∘ Bag→Tote))       ≡⟨ cong (∥Tote∥₂→FMSet ∘_) (sym (funExt (STExt.map∘map Bag→Tote (Tote.map f)))) ⟩
    ∥Tote∥₂→FMSet ∘ ST.map (Tote.map f) ∘ ST.map Bag→Tote  ≡⟨ cong (_∘ ST.map Bag→Tote) (Tote.isNatural-∥Tote∥₂≃FMSet f) ⟩
    FMSet.map f ∘ (invEq FMSet≃∥Tote∥₂) ∘ ST.map Bag→Tote  ≡⟨⟩
    FMSet.map f ∘ equivFun TruncBagFMSetEquiv ∎

FMSetFixSetTruncTree : FMSet ∥ BagLim ∥₂ ≃ ∥ BagLim ∥₂
FMSetFixSetTruncTree =
  FMSet ∥ BagLim ∥₂ ≃⟨ FMSet.STInvarianceEquiv ⟩
  FMSet BagLim      ≃⟨ invEquiv TruncBagFMSetEquiv ⟩
  ∥ Bag BagLim ∥₂   ≃⟨ setTruncEquiv (bagLimitEquiv) ⟩
  ∥ BagLim ∥₂       ■
