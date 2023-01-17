{-# OPTIONS --safe #-}

module Multiset.ListQuotient.Finality where

open import Multiset.Prelude
open import Multiset.ListQuotient.ListFinality
  using
    ( FunctorΣVec
    ; !^
    ; cut
    ; Tree
    ; fix⁺
    ; ΣVecLimitPath
    ; pres
    )

open import Multiset.Util.Vec as ΣVec
  using
    ( ΣVec
    ; mk-vec
    ; Σ[]
    ; _Σ∷_
    ; ∈-map
    ; remove
    ; map-remove
    ; Relator
    ; Relator-map
    ; isPropRelator
    ; isReflRelator
    ; Relator-∷-swap
    ; _∈_
    )
open import Multiset.Limit.Chain
  using
    ( lim
    ; Limit
    ; Chain
    ; isPropChain→Limit
    ; isOfHLevelLimit
    )
open import Multiset.Limit.TerminalChain as TerminalChain
  using
    ( Functor
    ; Lim
    ; _^_
    )

open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Function using (_∘_)
open import Cubical.Foundations.HLevels
open import Cubical.Data.Nat.Base as Nat using (ℕ ; suc ; zero)
open import Cubical.Data.Unit.Base using (Unit* ; Unit ; tt* ; tt)
open import Cubical.Data.Unit.Properties using (isPropUnit ; isOfHLevelUnit*)
open import Cubical.HITs.PropositionalTruncation as PT using ()
open import Cubical.HITs.SetQuotients as SQ using () renaming (_/_ to _/₂_)
open import Cubical.Relation.Binary using (module BinaryRelation)

open ΣVec.ΣVec
open Limit using (elements ; is-lim)
open Functor ⦃...⦄

Approx : (n : ℕ) → (s t : ΣVec ^ n) → Type
Approx zero = λ { tt* tt* → Unit }
Approx (suc n) = Relator (Approx n)

isPropApprox : ∀ n (s t : ΣVec ^ n) → isProp (Approx n s t)
isPropApprox zero s t = isPropUnit
isPropApprox (suc n) s t = isPropRelator (Approx n)

Approx-π : ∀ n {s t} → Approx (suc n) s t → Approx n (!^ n s) (!^ n t)
Approx-π zero _ = tt
Approx-π (suc n) rel = Relator-map (Approx (suc n)) _ (Approx-π n) rel

RelatorLim^ : ℕ → (s t : Lim ΣVec) → Type
RelatorLim^ n s t = Approx n (cut n s) (cut n t)

isPropRelatorLim^ : ∀ s t n → isProp (RelatorLim^ n s t)
isPropRelatorLim^ s t n = isPropApprox n (cut n s) (cut n t)

module _ (s t : Lim ΣVec) where
  RelatorLimSuc→RelatorLim : ∀ n → RelatorLim^ (suc n) s t → RelatorLim^ n s t
  RelatorLimSuc→RelatorLim n rel = subst2 (Approx n) (s .is-lim n) (t .is-lim n) (Approx-π n rel)

  RelatorChain : Chain ℓ-zero
  RelatorChain .Chain.Ob n = RelatorLim^ n s t
  RelatorChain .Chain.π = RelatorLimSuc→RelatorLim

  Bisim : Type
  Bisim = Limit RelatorChain

  isPropBisim : isProp Bisim
  isPropBisim = isOfHLevelLimit _ 1 (isPropRelatorLim^ s t)

bisim : {s t : Lim ΣVec} → (∀ n → RelatorLim^ n s t) → Bisim s t
bisim {s} {t} = isPropChain→Limit (RelatorChain s t) (isPropRelatorLim^ s t)

infix 5 _≈_
_≈_ = Bisim

syntax Approx n s t = s ≈[ n ] t

module _ where
  open BinaryRelation

  isReflApprox : ∀ n → isRefl (Approx n)
  isReflApprox zero = λ { tt* → tt }
  isReflApprox (suc n) = isReflRelator (isReflApprox n)
  
  isReflBisim : isRefl Bisim
  isReflBisim t = bisim {s = t} {t = t} λ { n → (isReflApprox n (t .elements n)) }

  BisimApproxEquiv : ∀ {s t} → Bisim s t ≃ (∀ n → Approx n (cut n s) (cut n t))
  BisimApproxEquiv {s} {t} = propBiimpl→Equiv (isPropBisim _ _) (isPropΠ (isPropRelatorLim^ s t)) elements bisim

Unorderedtree : Type _
Unorderedtree = Tree /₂ Bisim

module _ (a b : Tree) (cs : ΣVec Tree) where
  ∷-swap-approx : Relator Bisim (a Σ∷ b Σ∷ cs) (b Σ∷ a Σ∷ cs)
  ∷-swap-approx = Relator-∷-swap isReflBisim a b

module _ where
  open ΣVec.RelatorElim

  fix⁺-preserves-bisim : ∀ {s t} → Relator Bisim s t → Bisim (fix⁺ s) (fix⁺ t)
  fix⁺-preserves-bisim = elim goal where
    goal : ΣVec.RelatorElim Bisim (λ {m} {n} {s} {t} rel → Bisim (fix⁺ (mk-vec s)) (fix⁺ (mk-vec t)))
    goal .is-prop _ = isPropBisim _ _
    goal .rnil* = isReflBisim (fix⁺ Σ[])
    goal .rcons* {a = a} {as} {bs} b aRb b∈bs rel-remove cont = bisim approx where abstract
      approx : ∀ n → (cut n $ fix⁺ (a Σ∷ mk-vec as)) ≈[ n ] (cut n $ fix⁺ bs)
      approx zero = tt
      approx (suc n) = Relator.rcons PT.∣ bₙ , a′ₙ∼bₙ , bₙ∈bs′ₙ , subst (Relator (Approx n) _) rel-remove′ (cont .elements (suc n)) ∣₁ where
        aₙ a′ₙ : ΣVec ^ n
        aₙ = cut n a
        a′ₙ = !^ n (cut (suc n) a)

        aₙ≡a′ₙ : a′ₙ ≡ aₙ
        aₙ≡a′ₙ = a .is-lim n

        bₙ b′ₙ : ΣVec ^ n
        bₙ = cut n b
        b′ₙ = !^ n (cut (suc n) b)

        a′ₙ∼bₙ : a′ₙ ≈[ n ] bₙ
        a′ₙ∼bₙ = subst (λ · → · ≈[ n ] bₙ) (sym aₙ≡a′ₙ) (aRb .elements n)

        bₙ≡b′ₙ : b′ₙ ≡ bₙ
        bₙ≡b′ₙ = b .is-lim n

        bsₙ bs′ₙ : ΣVec (ΣVec ^ n)
        bsₙ = map (cut n) bs
        bs′ₙ = cut (suc n) (fix⁺ bs)

        bsₙ≡bs′ₙ : bsₙ ≡ bs′ₙ
        bsₙ≡bs′ₙ = sym $
          map (!^ n) (map (cut (suc n)) bs) ≡⟨ pres bs .is-lim n ⟩∎
          map (cut n) bs ∎

        bₙ∈bsₙ : bₙ ∈ bsₙ
        bₙ∈bsₙ = ∈-map (cut n) b∈bs

        bₙ∈bs′ₙ : bₙ ∈ bs′ₙ
        bₙ∈bs′ₙ = subst (bₙ ∈_) bsₙ≡bs′ₙ bₙ∈bsₙ

        rel-remove′ : cut (suc n) (fix⁺ (remove bs b∈bs)) ≡ remove bs′ₙ bₙ∈bs′ₙ
        rel-remove′ =
          (map (!^ n) $ map (cut (suc n)) $ remove bs b∈bs) ≡⟨ pres (remove bs b∈bs) .is-lim n ⟩
          (map (cut n)                    $ remove bs b∈bs) ≡⟨ map-remove (cut n) b∈bs ⟩
          remove bsₙ  bₙ∈bsₙ   ≡⟨ congP₂ (λ i → remove) bsₙ≡bs′ₙ (subst-filler (bₙ ∈_) bsₙ≡bs′ₙ bₙ∈bsₙ) ⟩
          remove bs′ₙ bₙ∈bs′ₙ  ∎


infixr 9 _T∷_
_T∷_ : (a : Tree) → (as : Tree) → Tree
_T∷_ a = subst (λ A → A → A) ΣVecLimitPath (a Σ∷_)

module _ (a b : Tree) (cs : Tree) where
  T∷-swap-approx : ∀ n → RelatorLim^ n (a T∷ b T∷ cs) (b T∷ a T∷ cs)
  T∷-swap-approx zero = tt
  T∷-swap-approx (suc n) = goal where
    goal : Relator (Approx n) _ _
    goal = {! !}

  T∷-swap : a T∷ b T∷ cs ≈ b T∷ a T∷ cs
  T∷-swap .elements n = {! !}
  T∷-swap .is-lim = {! !}
