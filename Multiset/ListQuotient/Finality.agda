{-# OPTIONS --safe #-}

module Multiset.ListQuotient.Finality where

open import Multiset.Prelude
open import Multiset.ListQuotient.ListFinality
  using
    ( FunctorΣVec
    ; !^
    ; cut
    ; Tree
    ; fix ; fix⁺ ; fix⁻
    ; ΣVecLimitPath
    ; pres ; pres⁺ ; pres⁻
    ; pres-Iso ; pres′ ; pres′⁻ -- ; pres′⁻≡pres⁻
    ; subtree
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
    ; RelatorElim
    ; Relator-map
    ; isPropRelator
    ; isReflRelator
    ; Relator-∷-swap
    ; _∈_
    )
open import Multiset.Util.Relation
open import Multiset.Util.SetQuotients
  using (relBiimpl→QuotIso)
  renaming (map to map/₂)
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
  hiding (pres)

open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Function using (_∘_)
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism
open import Cubical.Data.Nat.Base as Nat using (ℕ ; suc ; zero)
open import Cubical.Data.Unit.Base using (Unit* ; Unit ; tt* ; tt)
open import Cubical.Data.Unit.Properties using (isPropUnit ; isOfHLevelUnit*)
open import Cubical.Data.List.Base as List using (List)
open import Cubical.HITs.PropositionalTruncation as PT using ()
open import Cubical.HITs.SetQuotients as SQ using () renaming (_/_ to _/₂_ ; [_] to [_]₂ ; eq/ to eq/₂)
open import Cubical.Relation.Binary using (module BinaryRelation ; pulledbackRel ; RelIso ; Rel)

open ΣVec.ΣVec
open Limit using (elements ; is-lim)
open Iso
open Functor ⦃...⦄

-- Tot : ∀ {ℓ} {X : Type ℓ} → Rel X X ℓ-zero
-- Tot {X = X} = λ _ _ → Unit

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
          map (!^ n) (map (cut (suc n)) bs) ≡⟨ pres⁺ bs .is-lim n ⟩∎
          map (cut n) bs ∎

        bₙ∈bsₙ : bₙ ∈ bsₙ
        bₙ∈bsₙ = ∈-map (cut n) b∈bs

        bₙ∈bs′ₙ : bₙ ∈ bs′ₙ
        bₙ∈bs′ₙ = subst (bₙ ∈_) bsₙ≡bs′ₙ bₙ∈bsₙ

        rel-remove′ : cut (suc n) (fix⁺ (remove bs b∈bs)) ≡ remove bs′ₙ bₙ∈bs′ₙ
        rel-remove′ =
          (map (!^ n) $ map (cut (suc n)) $ remove bs b∈bs) ≡⟨ pres⁺ (remove bs b∈bs) .is-lim n ⟩
          (map (cut n)                    $ remove bs b∈bs) ≡⟨ map-remove (cut n) b∈bs ⟩
          remove bsₙ  bₙ∈bsₙ   ≡⟨ congP₂ (λ i → remove) bsₙ≡bs′ₙ (subst-filler (bₙ ∈_) bsₙ≡bs′ₙ bₙ∈bsₙ) ⟩
          remove bs′ₙ bₙ∈bs′ₙ  ∎

  -- TODO:
  --
  -- 1. Attempt to prove the two lemmata below, start with the harder one (pres⁺).
  -- 2. If that fails, redo list-finality proof with FinVec, use RelatorF from FMSetEquiv as the relator.
  -- 3. ???
  -- 4. PROFIT

  S : Rel (Limit (TerminalChain.sh ΣVec)) (Limit (TerminalChain.sh ΣVec)) _
  S = {! !}

  private
    open TerminalChain using (ShLim→Lim)

  pres⁺-reflects-bisim : ReflectsRel (Relator Bisim) S pres⁺
  pres⁺-reflects-bisim = {! !}

  ShLim→Lim-reflects : ReflectsRel S Bisim (TerminalChain.ShLim→Lim ΣVec)
  ShLim→Lim-reflects = {! !}

  fix⁺-reflects-bisim : ∀ {s t} → Bisim (fix⁺ s) (fix⁺ t) → Relator Bisim s t
  fix⁺-reflects-bisim = ReflectsRelComp (Relator Bisim) S Bisim {f = pres⁺} {g = TerminalChain.ShLim→Lim ΣVec} pres⁺-reflects-bisim ShLim→Lim-reflects

  module _ where
    fix⁻-pres-bisim : ∀ {s t : Tree} → Bisim s t → Relator Bisim (fix⁻ s) (fix⁻ t)
    fix⁻-pres-bisim {s} {t} = ReflectsRel→SectionPreservesRel (Relator Bisim) Bisim fix⁺ fix⁻ (secEq fix) fix⁺-reflects-bisim

  fix⁺-lift : ΣVec Tree /₂ pulledbackRel fix⁺ Bisim → Tree /₂ Bisim
  fix⁺-lift = map/₂ fix⁺ λ { rel → rel }

  fix⁻-lift : Tree /₂ Bisim → ΣVec Tree /₂ pulledbackRel fix⁺ Bisim
  fix⁻-lift = map/₂ fix⁻ pres-bisim where
    pres-bisim : ∀ {a} {a'} → a ≈ a' → (fix⁺ $ fix⁻ a) ≈ (fix⁺ $ fix⁻ a')
    pres-bisim {a} {a'} a≈a' = subst2 _≈_ (sym (secEq fix a)) (sym (secEq fix a')) a≈a'

  fix-lift-iso : Iso (ΣVec Tree /₂ pulledbackRel fix⁺ Bisim) (Tree /₂ Bisim)
  fix-lift-iso .fun = fix⁺-lift
  fix-lift-iso .inv = fix⁻-lift
  fix-lift-iso .rightInv = SQ.elimProp (λ _ → SQ.squash/ _ _) (cong [_]₂ ∘ secEq fix)
  fix-lift-iso .leftInv = SQ.elimProp (λ _ → SQ.squash/ _ _) (cong [_]₂ ∘ retEq fix)


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

FMSet : Type → Type
FMSet X = ΣVec X /₂ (Relator _≡_)

_ : Iso (FMSet Unorderedtree) Unorderedtree
_ =
  FMSet Unorderedtree Iso⟨ idIso ⟩
  ΣVec (Tree /₂ Bisim) /₂ (Relator _≡_) Iso⟨ {! !} ⟩
  Tree /₂ Bisim  Iso⟨ idIso ⟩
  Unorderedtree ∎Iso where

  eq/Relator : ∀ {X : Type} {R : X → X → Type}
    → ∀ {xs ys}
    → Relator R xs ys
    → Relator {A = X /₂ R} _≡_ (map [_]₂ xs) (map [_]₂ ys)
  eq/Relator {R = R} = Relator-map R _≡_ (eq/₂ _ _)

  α : Tree /₂ Bisim → ΣVec (Tree /₂ Bisim) /₂ (Relator _≡_)
  α = map/₂ (ΣVec.map [_]₂ ∘ fix⁻) λ {a} {a'} a≈a' → eq/Relator (fix⁻-pres-bisim a≈a')

  -- TODO: ΣVecPar : Rel A B → Rel (ΣVec A) (ΣVec B),
  --
  -- prove: ΣVec (X /₂ R) ≃ ΣVec X /₂ ΣVecPar R

  β : ΣVec (Tree /₂ Bisim) /₂ (Relator _≡_) → Tree /₂ Bisim
  β = SQ.rec SQ.squash/ (fix⁺-lift ∘ {! !}) {! !}
