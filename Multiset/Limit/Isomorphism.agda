{-# OPTIONS --safe #-}

module Multiset.Limit.Isomorphism where

open import Multiset.Limit.Chain

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Structure
open import Cubical.Foundations.Function
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.HLevels
open import Cubical.Data.Nat.Base as ℕ
  using (ℕ ; zero ; suc)
open import Cubical.Data.Sigma
open import Cubical.Relation.Nullary.Base using (Discrete)
open import Cubical.Reflection.RecordEquiv
open import Cubical.Foundations.Equiv.HalfAdjoint
open import Cubical.Foundations.Path
open import Cubical.Foundations.GroupoidLaws

open Iso
open isHAEquiv


open Chain
open Limit

-- ==================================================================

-- Chains with naturally equivalent components have equivalent limits.

-- ==================================================================

reshapeSquare : ∀{ℓ} {A : Type ℓ}
  {a₀₀ a₀₁ : A} {p : a₀₀ ≡ a₀₁}
  {a₁₀ a₁₁ : A} {q : a₁₀ ≡ a₁₁}
  {r : a₀₀ ≡ a₁₀} {s : a₀₁ ≡ a₁₁}
  → Square p q r s
  → Square (q ∙ sym s ∙ sym p) refl refl r
reshapeSquare {p = p} {q = q} {r} {s} sq = 
  compPathL→PathP
    (refl ∙ (q ∙ sym s ∙ sym p) ∙ r          ≡⟨ sym (lUnit _) ⟩
     (q ∙ sym s ∙ sym p) ∙ r                 ≡⟨ (λ i → (PathP→compPathL sq (~ i) ∙ sym s ∙ sym p) ∙ r ) ⟩
     ((sym r ∙ p ∙ s) ∙ sym s ∙ sym p) ∙ r   ≡⟨ cong (_∙ r) (sym (assoc _ _ _)) ⟩
     (sym r ∙ (p ∙ s) ∙ sym s ∙ sym p) ∙ r   ≡⟨ cong (_∙ r) (cong (sym r ∙_) (sym (assoc _ _ _))) ⟩
     (sym r ∙ p ∙ s ∙ sym s ∙ sym p) ∙ r     ≡⟨ cong (_∙ r) (cong (λ x → sym r ∙ p ∙ x) (assoc _ _ _)) ⟩
     (sym r ∙ p ∙ (s ∙ sym s) ∙ sym p) ∙ r   ≡⟨ cong (_∙ r) (cong (λ x → sym r ∙ p ∙ x ∙ sym p) (rCancel s)) ⟩
     (sym r ∙ p ∙ refl ∙ sym p) ∙ r          ≡⟨ cong (_∙ r) (cong (λ x → sym r ∙ p ∙ x) (sym (lUnit _))) ⟩
     (sym r ∙ p ∙ sym p) ∙ r                 ≡⟨ cong (λ x → (sym r ∙ x) ∙ r) (rCancel p) ⟩
     (sym r ∙ refl) ∙ r                      ≡⟨ cong (_∙ r) (sym (rUnit _)) ⟩
     sym r ∙ r                               ≡⟨ lCancel r ⟩
     refl                                    ∎)

-- Equivalence of chains C and C'
record ChainEquiv {ℓ} (C C' : Chain ℓ) : Type ℓ where
  constructor chain-equiv
  field
    α : (n : ℕ) → C .Ob n → C' .Ob n
    α-nat : ∀ n x → C' .π n (α (suc n) x) ≡ α n (C .π n x)
    α-eq : ∀ n → isEquiv (α n)

-- Half-adjoint equivalence of chains C and C'
record ChainHAEquiv {ℓ} (C C' : Chain ℓ) : Type ℓ where
  constructor chain-ha
  field
    α : (n : ℕ) → C .Ob n → C' .Ob n
    α-nat : ∀ n x → C' .π n (α (suc n) x) ≡ α n (C .π n x)
    α-ha : ∀ n → isHAEquiv (α n)

  α-inv : (n : ℕ) → C' .Ob n → C .Ob n
  α-inv n = α-ha n .g

ChainEquiv→ChainHAEquiv : ∀ {ℓ} {C C' : Chain ℓ}
  → ChainEquiv C C' → ChainHAEquiv C C'
ChainEquiv→ChainHAEquiv (chain-equiv α α-nat α-eq) =
  chain-ha α α-nat (λ n → equiv→HAEquiv (α n , α-eq n) .snd)

open ChainHAEquiv

-- The inverse of a chain equivalence also enjoys the naturality property
inv-nat : ∀ {ℓ} {C C' : Chain ℓ}
  → (f : ChainHAEquiv C C')
  → ∀ n x → C .π n (α-inv f (suc n) x) ≡ α-inv f n (C' .π n x)
inv-nat {C' = C'} f@(chain-ha f₀ f₁ fha) n x =
  sym (fha n .linv _) ∙ cong (α-inv f n) (sym (f₁ n _) ∙ cong (C' .π n) (fha (suc n) .rinv _))

-- Maps between chains lift to maps between limits
mapLimit : ∀ {ℓ} {C C' : Chain ℓ}
  → (f₀ : (n : ℕ) → C .Ob n → C' .Ob n)
  → (∀ n x → C' .π n (f₀ (suc n) x) ≡ f₀ n (C .π n x))
  → Limit C → Limit C'
mapLimit f₀ f₁ (lim x₀ x₁) .elements n = f₀ n (x₀ n)
mapLimit f₀ f₁ (lim x₀ x₁) .is-lim n = f₁ n (x₀ (suc n)) ∙ cong (f₀ n) (x₁ n)

-- Half-adjoint equivalences between chains lift to isomosphisms between limits
mapLimit-pres-iso : ∀ {ℓ} {C C' : Chain ℓ} → ChainHAEquiv C C' → Iso (Limit C) (Limit C')
mapLimit-pres-iso (chain-ha α α-nat α-ha) .fun = mapLimit α α-nat
mapLimit-pres-iso f@(chain-ha α α-nat α-ha) .inv = mapLimit (α-inv f) (inv-nat f)
mapLimit-pres-iso {C = C}{C'} f@(chain-ha α α-nat α-ha) .rightInv (lim x₀ x₁) =
  LimitPathPExt _ (λ n → αrinv n _) rinv₂
  where
    αinv = α-inv f
    
    αlinv : ∀ n → _
    αlinv n = α-ha n .linv
 
    αrinv : ∀ n → _
    αrinv n = α-ha n .rinv
    
    rinv₂ : ∀ n →
      Square (α-nat n (αinv (suc n) (x₀ (suc n)))
               ∙ cong (α n) (inv-nat f n (x₀ (suc n)) ∙ cong (αinv n) (x₁ n)))
             (x₁ n)
             (cong (C' .π n) (αrinv (suc n) (x₀ (suc n))))
             (αrinv n (x₀ n))
    rinv₂ n = 
      path ◁ sq ∙₂ flipSquare (λ i → αrinv n (x₁ n i)) ▷ sym (lUnit _)
      where    
        h₀ = cong (α n) (cong (αinv n) (α-nat n (αinv (suc n) (x₀ (suc n)))))
        h₁ = α-nat n (αinv (suc n) (x₀ (suc n)))
        v₀ = αrinv n (C' .π n (α (suc n) (αinv (suc n) (x₀ (suc n)))))
        v₁ = cong (α n) (αlinv n (C .π n (αinv (suc n) (x₀ (suc n)))))
        v₁' = αrinv n (α n (C .π n (αinv (suc n) (x₀ (suc n)))))
        w₀ = cong (α n) (cong (αinv n) (cong (C' .π n) (αrinv (suc n) (x₀ (suc n)))))
        w₁ = αrinv n (C' .π n (x₀ (suc n)))
        z = cong (C' .π n) (αrinv (suc n) (x₀ (suc n)))
    
        path =
          cong (λ x → h₁ ∙ x)
               (cong-∙ (α n) _ _
                ∙ cong (λ x → x ∙ cong (α n) (λ i → αinv n (x₁ n i)))
                       (cong-∙ (α n) _ _
                        ∙ cong (λ x → sym v₁ ∙ x)
                               (cong-∙ (λ x → α n (αinv n x)) _ _)))
          ∙ assoc _ _ _
        
        sq2' : Square h₀ h₁ v₀ v₁'
        sq2' = flipSquare (λ i → αrinv n (α-nat n (αinv (suc n) (x₀ (suc n))) i))
    
        sq2 : Square h₀ h₁ v₀ v₁
        sq2 = subst (Square h₀ h₁ v₀) (sym (α-ha n .com _)) sq2'
    
        sq'' : Square ((h₁ ∙ sym v₁ ∙ sym h₀) ∙ w₀) (refl ∙ z) refl w₁
        sq'' = reshapeSquare sq2 ∙₂ flipSquare (λ i → αrinv n (C' .π n (αrinv (suc n) (x₀ (suc n)) i)))
    
        sq' : Square (h₁ ∙ sym v₁ ∙ sym h₀ ∙ w₀) z refl w₁
        sq' = (assoc _ _ _ ∙ assoc _ _ _ ∙ cong (_∙ w₀) (sym (assoc _ _ _))) ◁ sq'' ▷ sym (lUnit _)
    
        sq : Square (h₁ ∙ sym v₁ ∙ sym h₀ ∙ w₀) refl z w₁
        sq = flipSquare (invEq slideSquareEquiv (flipSquare sq'))
        
mapLimit-pres-iso {C = C}{C'} f@(chain-ha α α-nat α-ha) .leftInv (lim x₀ x₁) =
  LimitPathPExt _ (λ n → αlinv n _) linv₂
  where
    αinv = α-inv f
    
    αlinv : ∀ n → _
    αlinv n = α-ha n .linv
 
    αrinv : ∀ n → _
    αrinv n = α-ha n .rinv
    
    linv₂ : ∀ n →
      Square (inv-nat f n (α (suc n) (x₀ (suc n)))
               ∙ cong (αinv n) (α-nat n (x₀ (suc n)) ∙ cong (α n) (x₁ n)))
             (x₁ n)
             (cong (C .π n) (αlinv (suc n) (x₀ (suc n))))
             (αlinv n (x₀ n))
    linv₂ n = 
     path ◁ sq ∙₂ flipSquare (λ i → αlinv n (x₁ n i)) ▷ sym (lUnit _) 
      where
        h₀ = cong (αinv n) (α-nat n (αinv (suc n) (α (suc n) (x₀ (suc n)))))
        h₁ = cong (αinv n) (α-nat n (x₀ (suc n)))
        v₀ = cong (αinv n) (cong (α n) (cong (C .π n) (αlinv (suc n) (x₀ (suc n)))))
        v₁ = αlinv n (C .π n (αinv (suc n) (α (suc n) (x₀ (suc n)))))
        w₀ = cong (αinv n) (cong (C' .π n) (αrinv (suc n) (α (suc n) (x₀ (suc n)))))
        w₀' = cong (αinv n) (cong (C' .π n) (cong (α (suc n)) (αlinv (suc n) (x₀ (suc n)))))
        w₁ = αlinv n (C .π n (x₀ (suc n)))
        z = cong (C .π n) (αlinv (suc n) (x₀ (suc n)))

        path =
          cong (λ x → inv-nat f n (α (suc n) (x₀ (suc n))) ∙ x) (cong-∙ (αinv n) _ _)
          ∙ assoc _ _ _
          ∙ cong (λ x → x ∙ cong (αinv n) (cong (α n) (x₁ n)))
                 (sym (assoc _ _ _)
                  ∙ cong (sym v₁ ∙_)
                         (cong (_∙ h₁) (cong-∙ (αinv n) _ _)
                          ∙ sym (assoc _ _ _)))

        sq2' : Square w₀' v₀ h₀ h₁
        sq2' = flipSquare λ i → cong (αinv n) (α-nat n (αlinv (suc n) (x₀ (suc n)) i))

        sq2 : Square w₀ v₀ h₀ h₁
        sq2 = subst (λ x → Square x v₀ h₀ h₁) (cong (cong (αinv n)) (cong (cong (C' .π n)) (com (α-ha (suc n)) _))) sq2'

        sq''' : Square (sym h₀ ∙ w₀ ∙ h₁) refl v₀ refl
        sq''' = compPathL→PathP (cong (sym v₀ ∙_) (sym (rUnit _) ∙ PathP→compPathL sq2) ∙ lCancel v₀)

        sq'' : Square (sym v₁ ∙ sym h₀ ∙ w₀ ∙ h₁) (sym w₁ ∙ refl) z refl
        sq'' = (λ i → sym (αlinv n (C .π n (αlinv (suc n) (x₀ (suc n)) i)))) ∙₂ sq'''

        sq' : Square (sym v₁ ∙ sym h₀ ∙ w₀ ∙ h₁) refl (z ∙ refl) (refl ∙ w₁)
        sq' =
          (sq'' ▷ sym (rUnit _))
            ∙v
          compPathL→PathP
            (refl ∙ sym w₁ ∙ w₁  ≡⟨ sym (lUnit _) ⟩
             sym w₁ ∙ w₁         ≡⟨ lCancel _ ⟩
             refl ∎)

        sq : Square (sym v₁ ∙ sym h₀ ∙ w₀ ∙ h₁) refl z w₁
        sq = flipSquare (rUnit _ ◁ flipSquare sq' ▷ sym (lUnit _))

-- Equivalences between chains lift to equivalences between limits
mapLimit-pres-equiv : ∀ {ℓ} {C C' : Chain ℓ} → ChainEquiv C C' → Limit C ≃ Limit C'
mapLimit-pres-equiv C≃C' = isoToEquiv (mapLimit-pres-iso (ChainEquiv→ChainHAEquiv C≃C'))

