{-# OPTIONS --safe #-}

module Multiset.ListQuotient.VecFinality where

open import Multiset.Prelude
open import Multiset.Util.Vec as ΣVec
  using
    ( ΣVec
    ; mk-vec
    ; Σ[]
    ; _Σ∷_
    ; ΣVecPathP
    ; module VecExt
    ; ΣVecIsoΣ
    ; Relator
    ; isPropRelator
    ; _∈_
    )
open import Multiset.Limit.Chain
  using
    ( lim
    ; Limit
    ; Chain
    ; isSet→LimitPathExt
    ; isPropChain→Limit
    ; isLimit
    ; isOfHLevelLimit
    )
open import Multiset.Coalgebra
  using
    ( CoalgebraMorphism
    ; isCoalgebraMorphism
    ; isTerminal
    ; isSet→isPropIsCoalgebraMorphism
    )
open import Multiset.Limit.TerminalChain as TerminalChain
  using
    ( Functor
    ; Lim
    ; ShLim
    ; _^_
    ; _map-!^_
    ; isShLim
    ; isLim
    ; isLimitPreserving
    ; Lim→ShLim
    ; ShLim→Lim
    )
open import Multiset.ListQuotient.Base hiding (Relator ; isPropRelator ; _∈_ ; [])
open import Multiset.ListQuotient.FMSetEquiv

open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Function using (_∘_ ; ∘-assoc ; flip)
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Univalence using (ua)
open import Cubical.Data.Sigma as Sigma using (ΣPathP ; _×_)
open import Cubical.Data.Nat.Base as Nat using (ℕ ; suc ; zero)
open import Cubical.Data.FinData as Fin using (Fin) renaming (zero to fzero ; suc to fsuc)
open import Cubical.Data.Unit.Base using (Unit* ; Unit ; tt* ; tt)
open import Cubical.Data.Unit.Properties as Unit using (isOfHLevelUnit*)
open import Cubical.Data.Vec as Vec
  using (Vec ; module VecPath)
open import Cubical.HITs.PropositionalTruncation as PT using ()
open import Cubical.HITs.SetQuotients as SQ using () renaming (_/_ to _/₂_)
open import Cubical.Relation.Binary using (module BinaryRelation)

open ΣVec.ΣVec

Vec' : ℕ → Type → Type
Vec' n A = Vec A n

instance
  FunctorVec : ∀ {n} → Functor {ℓ-zero} (Vec' n)
  FunctorVec .Functor.map = Vec.map
  FunctorVec .Functor.map-id = VecExt.vec-map-id
  FunctorVec .Functor.map-comp = λ g f as → VecExt.vec-map-comp g f as

  FunctorΣVec : Functor {ℓ-zero} ΣVec
  FunctorΣVec .Functor.map = ΣVec.map
  FunctorΣVec .Functor.map-id = ΣVec.map-id
  FunctorΣVec .Functor.map-comp = ΣVec.map-comp

open Functor ⦃...⦄

isSetΣVec^ : ∀ n → isSet (ΣVec ^ n)
isSetΣVec^ zero = isOfHLevelUnit* 2
isSetΣVec^ (suc n) = ΣVec.isSetΣVec (isSetΣVec^ n)

!^ : (n : ℕ) → ΣVec ^ (suc n) → ΣVec ^ n
!^ = ΣVec map-!^_

Tree : Type
Tree = Lim ΣVec

pres : ΣVec (Lim ΣVec) → ShLim ΣVec
pres = TerminalChain.pres ΣVec

cut : (n : ℕ) → Lim ΣVec → ΣVec ^ n
cut = TerminalChain.cut ΣVec

width : ShLim ΣVec → (d : ℕ) → ℕ
width tree d = length $ tree .Limit.elements d

vecs : (tree : ShLim ΣVec) → (d : ℕ) → Vec (ΣVec ^ d) (width tree d)
vecs tree d = tree .Limit.elements d .vec

widthConstSuc : ∀ (tree : ShLim ΣVec) n → width tree n ≡ width tree (suc n)
widthConstSuc (lim tree is-lim) n = cong length (sym $ is-lim n)

open Iso

private
  open import Multiset.Util.Trace as Trace
    using (Trace ; constTrace ; TraceIso)

  OverTrace : Trace ℕ → Type
  OverTrace as =
    Σ[ vs ∈ ((n : ℕ) → Vec (ΣVec ^ n) (as .Trace.step n)) ]
    ∀ (n : ℕ) →
      PathP (λ i → Vec (ΣVec ^ n) (as .Trace.connect n i))
        (vs n)
        (Vec.map (!^ n) (vs (suc n)))

abstract
  pres-Iso : Iso (ShLim ΣVec) (ΣVec (Lim ΣVec))
  pres-Iso =
    let snd-iso : ∀ n → Iso (OverTrace (constTrace n)) (Vec (Lim ΣVec) n)
        snd-iso n =
          OverTrace (constTrace n)  Iso⟨ toVecLimit n ⟩
          Limit (vecChain n)        Iso⟨ toFinVecOfLimits n ⟩
          Fin.FinVec (Lim ΣVec) n   Iso⟨ Vec.FinVecIsoVec n ⟩
          Vec (Lim ΣVec) n          ∎Iso
    in
    ShLim ΣVec                    Iso⟨ toTraceFirstIso ⟩
    TraceFirst                    Iso⟨ invIso (Sigma.Σ-cong-iso-fst (invIso TraceIso)) ⟩
    Σ ℕ (OverTrace ∘ constTrace)  Iso⟨ Sigma.Σ-cong-iso-snd snd-iso ⟩
    Σ ℕ (Vec (Lim ΣVec))          Iso⟨ invIso ΣVecIsoΣ ⟩
    ΣVec (Lim ΣVec) ∎Iso
    where

    TraceFirst : Type
    TraceFirst = Σ (Trace ℕ) OverTrace

    toTraceFirstIso : Iso (ShLim ΣVec) TraceFirst
    toTraceFirstIso .fun tree = trace , vecs tree , vecs-coh where
      trace : Trace ℕ
      trace = width tree , widthConstSuc tree

      vecs-coh : ∀ n
        → PathP (λ i → Vec (ΣVec ^ n) (widthConstSuc tree n i))
          (vecs tree n)
          (Vec.map (!^ n) (vecs tree (suc n)))
      vecs-coh n = cong vec (sym (tree .Limit.is-lim n))
    toTraceFirstIso .inv (trace , vecs , vecs-coh) = lim elements is-lim where
      elements : (n : ℕ) → ΣVec ^ (suc n)
      elements n = mk-vec {length = trace .Trace.step n} $ vecs n

      is-lim : ∀ n → !^ (suc n) (elements (suc n)) ≡ elements n
      is-lim n = sym $ ΣVecPathP (trace .Trace.connect n) (vecs-coh n)
    toTraceFirstIso .rightInv _ = refl
    toTraceFirstIso .leftInv _ = refl

    module _ (sz : ℕ) where
      open Limit
      open VecExt using (lookup-map ; lookup⁻¹ ; lookup-right-inv ; lookup-left-inv)

      vecChain : Chain _
      vecChain .Chain.Ob n = Vec (ΣVec ^ n) sz
      vecChain .Chain.π n = Vec.map (!^ n)

      toVecLimit : Iso (OverTrace (constTrace sz)) (Limit vecChain)
      toVecLimit .fun (vecs , vecs-coh) = lim vecs (sym ∘ vecs-coh)
      toVecLimit .inv (lim elements is-lim) = elements , sym ∘ is-lim
      toVecLimit .rightInv _ = refl
      toVecLimit .leftInv _ = refl

      toFinVecOfLimits-fun : Limit vecChain → Fin.FinVec (Lim ΣVec) sz
      toFinVecOfLimits-fun (lim elements is-lim) k = lim (Vec.lookup k ∘ elements) is-lim' where
        is-lim' : isLim ΣVec (Vec.lookup k ∘ elements)
        is-lim' n =
          (!^ n) (Vec.lookup k $ elements (suc n))           ≡⟨ sym (lookup-map (!^ n) (elements (suc n)) k) ⟩
          (Vec.lookup k $ Vec.map (!^ n) (elements (suc n))) ≡⟨ cong (Vec.lookup k) (is-lim n) ⟩∎
          (Vec.lookup k $ elements n) ∎

      toFinVecOfLimits : Iso (Limit vecChain) (Fin.FinVec (Lim ΣVec) sz)
      toFinVecOfLimits = go where
        module _ (vec : Limit vecChain) where
          f-elements : Fin.FinVec (∀ n → ΣVec ^ n) sz
          f-elements k = Vec.lookup k ∘ (vec .elements)

          f-is-lim : ∀ k → isLim ΣVec (f-elements k)
          f-is-lim k n =
            (!^ n) (Vec.lookup k $ vec .elements (suc n))           ≡⟨ sym (VecExt.lookup-map (!^ n) (vec .elements (suc n)) k) ⟩
            (Vec.lookup k $ Vec.map (!^ n) (vec .elements (suc n))) ≡⟨ cong (Vec.lookup k) (vec .is-lim n) ⟩∎
            (Vec.lookup k $ vec .elements n) ∎

          f : Fin.FinVec (Lim ΣVec) sz
          f k .elements = f-elements k
          f k .is-lim = f-is-lim k

        module _ (vec : Fin.FinVec (Lim ΣVec) sz) where
          f⁻¹-elements : ∀ n → Vec (ΣVec ^ n) sz
          f⁻¹-elements n = Vec.map (cut n) (lookup⁻¹ vec)

          f⁻¹-is-lim : isLimit vecChain f⁻¹-elements
          f⁻¹-is-lim n =
            map (!^ n) (map (cut (suc n)) (lookup⁻¹ vec)) ≡⟨ sym (map-comp (!^ n) (cut (suc n)) _) ⟩
            map (!^ n ∘ (cut (suc n))) (lookup⁻¹ vec)     ≡⟨ cong (λ f → map f (lookup⁻¹ vec)) (TerminalChain.cut-is-lim ΣVec n) ⟩
            map (cut n) (lookup⁻¹ vec) ∎

          f⁻¹ : Limit vecChain
          f⁻¹ .elements = f⁻¹-elements
          f⁻¹ .is-lim = f⁻¹-is-lim

        go : Iso _ _
        go .fun = f
        go .inv = f⁻¹
        go .rightInv vec-of-lim = funExt λ { k → isSet→LimitPathExt _ isSetΣVec^ (right-inv k) } where
          right-inv : ∀ k n → f-elements (f⁻¹ vec-of-lim) k n ≡ vec-of-lim k .elements n
          right-inv k n =
            Vec.lookup k (Vec.map (cut n) (lookup⁻¹ vec-of-lim))  ≡⟨ VecExt.lookup-map (cut n) (lookup⁻¹ vec-of-lim) k ⟩
            (cut n $ Vec.lookup k (lookup⁻¹ vec-of-lim))          ≡⟨ cong (cut n) (funExt⁻ (lookup-right-inv vec-of-lim) k) ⟩
            (cut n $ vec-of-lim k) ∎
        go .leftInv lim-of-vec = isSet→LimitPathExt vecChain (λ k → VecExt.isSetVec (isSetΣVec^ k)) left-inv where
          left-inv : ∀ n → f⁻¹ (f lim-of-vec) .elements n ≡ lim-of-vec .elements n
          left-inv n =
            Vec.map (cut n) (lookup⁻¹ (f lim-of-vec))                 ≡⟨ VecExt.lookup⁻¹-map (cut n) _ ⟩
            lookup⁻¹ (cut n ∘ f lim-of-vec)                           ≡⟨⟩
            lookup⁻¹ (λ k → f-elements lim-of-vec k n)                ≡⟨⟩
            lookup⁻¹ (λ k → (Vec.lookup k $ lim-of-vec .elements n))  ≡⟨ lookup-left-inv _ ⟩
            lim-of-vec .elements n ∎

  presIsoInv≡pres : pres-Iso .inv ≡ pres
  presIsoInv≡pres = funExt $ TerminalChain.isSet→ShLimPath ΣVec (isSetΣVec^ ∘ suc) ∘ goal where
    open Limit
    goal : ∀ (xs : ΣVec (Lim ΣVec)) n → pres-Iso .inv xs .elements n ≡ pres xs .elements n
    goal xs n = ΣVecPathP refl $ cong (Vec.map (cut n)) (VecExt.lookup-left-inv (xs .vec))

isLimitPreservingΣVec : isLimitPreserving ΣVec
isLimitPreservingΣVec = subst isEquiv presIsoInv≡pres (isoToIsEquiv (invIso pres-Iso))

open TerminalChain.Fixpoint isLimitPreservingΣVec
  using (fix⁺ ; fix⁻ ; fix⁻-step-ext)
  renaming (fix to ΣVecLimitEquiv)
  public

isSetLimΣVec : isSet (Lim ΣVec)
isSetLimΣVec = isOfHLevelLimit _ 2 isSetΣVec^

open Limit

LimΣVecPathExt : ∀ {l₁ l₂ : Lim ΣVec} → (∀ n → l₁ .elements n ≡ l₂ .elements n) → l₁ ≡ l₂
LimΣVecPathExt = isSet→LimitPathExt _ isSetΣVec^

module _ {C : Type} (γ : C → ΣVec C) where
  step : (n : ℕ) → C → ΣVec ^ n
  step zero _ = tt*
  step (suc n) c = map (step n) (γ c)

  is-lim-step : ∀ c → isLimit (TerminalChain.ch ΣVec) (flip step c)
  is-lim-step c zero = refl
  is-lim-step c (suc n) = goal where abstract
    goal : map (!^ n) (step (suc $ suc n) c) ≡ step (suc n) c
    goal =
      (map (!^ n) $ map (step (suc n)) $ γ c) ≡⟨ sym (map-comp (!^ n) _ (γ c)) ⟩
      (map (!^ n ∘ step (suc n)) $ γ c)       ≡⟨ cong (λ f → map f (γ c)) (funExt λ c' → is-lim-step c' n) ⟩
      (map (step n) $ γ c) ∎

  unfold : C → Lim ΣVec
  unfold c .elements = flip step c
  unfold c .is-lim = is-lim-step c

  abstract
    step-unfold : ∀ c n → step n c ≡ fix⁺ (map unfold (γ c)) .elements n
    step-unfold c zero = refl {x = tt*}
    step-unfold c (suc n) =
      map (step n) (γ c)                                      ≡⟨⟩
      map (cut n ∘ unfold) (γ c)                              ≡⟨ map-comp (cut n) unfold _ ⟩
      map (cut n)              (map unfold (γ c))             ≡⟨ cong-map-ext {{FunctorΣVec}} (sym $ TerminalChain.cut-is-lim _ n) _ ⟩
      map (!^ n ∘ cut (suc n)) (map unfold (γ c))             ≡⟨ map-comp (!^ n) (cut (suc n)) _ ⟩
      map (!^ n) (map (cut (suc n)) $ map unfold (γ c))       ≡⟨⟩
      !^ (suc n) (pres (map unfold (γ c)) .elements (suc n))  ≡⟨⟩
      ShLim→Lim _ (pres (map unfold (γ c))) .elements (suc n) ≡⟨⟩
      fix⁺ (map unfold (γ c)) .elements (suc n) ∎

    unfold-fix⁺ : ∀ c → unfold c ≡ fix⁺ (map unfold (γ c))
    unfold-fix⁺ c = isSet→LimitPathExt _ isSetΣVec^ (step-unfold c)

  isCoalgebraMorphismUnfold : isCoalgebraMorphism ΣVec γ fix⁻ unfold
  isCoalgebraMorphismUnfold = funExt goal where abstract
    goal : ∀ c → fix⁻ (unfold c) ≡ ΣVec.map unfold (γ c)
    goal c =
      fix⁻ (unfold c) ≡⟨ cong fix⁻ (unfold-fix⁺ c) ⟩
      fix⁻ (fix⁺ (ΣVec.map unfold (γ c))) ≡⟨ retEq ΣVecLimitEquiv (ΣVec.map unfold (γ c)) ⟩
      map unfold (γ c) ∎

isTerminalFix⁻ : isTerminal ΣVec fix⁻
isTerminalFix⁻ {B = B} β = ana , anaEq where
  open TerminalChain.Fixpoint isLimitPreservingΣVec
    using (fix⁺-step-ext)

  ana : CoalgebraMorphism ΣVec β fix⁻
  ana = unfold β , isCoalgebraMorphismUnfold β

  anaEq : ∀ f → ana ≡ f
  anaEq (f , f-is-mor) = Sigma.Σ≡Prop isPropIsCoalgebraMorphism' eq where abstract
    isPropIsCoalgebraMorphism' : (u : B → Lim ΣVec) → isProp (isCoalgebraMorphism ΣVec β fix⁻ u)
    isPropIsCoalgebraMorphism' u = isSet→isPropIsCoalgebraMorphism ΣVec β fix⁻ u (ΣVec.isSetΣVec isSetLimΣVec)

    eq : unfold β ≡ f
    eq = funExt $ LimΣVecPathExt ∘ λ b n → funExt⁻ (goal n) b where
      goal : ∀ n → step β n ≡ cut n ∘ f
      goal zero = refl
      goal (suc n) =
        map (step β n) ∘ β        ≡⟨ cong (λ g → map g ∘ β) (goal n) ⟩
        map (cut n ∘ f) ∘ β       ≡⟨ cong (_∘ β) (map-comp-ext (cut n) f) ⟩
        (map (cut n) ∘ map f) ∘ β ≡⟨ ∘-assoc (map (cut n)) (map f) β ⟩
        map (cut n) ∘ (map f ∘ β) ≡⟨ cong (map (cut n) ∘_) (sym f-is-mor) ⟩
        map (cut n) ∘ (fix⁻ ∘ f)  ≡⟨ sym (∘-assoc (map (cut n)) fix⁻ f) ⟩
        (map (cut n) ∘ fix⁻) ∘ f  ≡⟨ cong (_∘ f) (fix⁻-step-ext n) ⟩
        cut (suc n) ∘ f ∎

Approx : (n : ℕ) → (s t : ΣVec ^ n) → Type
Approx zero = λ { tt* tt* → Unit }
Approx (suc n) = Relator (Approx n)

isPropApprox : ∀ n (s t : ΣVec ^ n) → isProp (Approx n s t)
isPropApprox zero s t = Unit.isPropUnit
isPropApprox (suc n) s t = isPropRelator {! !}

Approx-π : ∀ n {s t} → Approx (suc n) s t → Approx n (!^ n s) (!^ n t)
Approx-π zero _ = tt
Approx-π (suc n) rel = ΣVec.Relator-map (Approx (suc n)) _ (Approx-π n) rel

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

infix 5 _≈_ -- _≈[_]_
_≈_ = Bisim

-- syntax RelatorLim^ s t n = s ≈[ n ] t

module _ where
  open BinaryRelation

  isReflApprox : ∀ n → isRefl (Approx n)
  isReflApprox zero = λ { tt* → tt }
  isReflApprox (suc n) = ΣVec.isReflRelator (isReflApprox n)
  
  isReflBisim : isRefl Bisim
  isReflBisim t = bisim {s = t} {t = t} λ { n → (isReflApprox n (t .elements n)) }

  BisimApproxEquiv : ∀ {s t} → Bisim s t ≃ (∀ n → Approx n (cut n s) (cut n t))
  BisimApproxEquiv {s} {t} = propBiimpl→Equiv (isPropBisim _ _) (isPropΠ (isPropRelatorLim^ s t)) elements bisim

Unorderedtree : Type _
Unorderedtree = Tree /₂ Bisim

module _ (a b : Tree) (cs : ΣVec Tree) where
  ∷-swap-approx : Relator Bisim (a Σ∷ b Σ∷ cs) (b Σ∷ a Σ∷ cs)
  ∷-swap-approx = ΣVec.Relator-∷-swap isReflBisim a b

module _ where
  open ΣVec.RelatorElim

  fix⁺-preserves-bisim : ∀ {s t} → Relator Bisim s t → Bisim (fix⁺ s) (fix⁺ t)
  fix⁺-preserves-bisim = elim goal where
    goal : ΣVec.RelatorElim Bisim (λ {m} {n} {s} {t} rel → Bisim (fix⁺ (mk-vec s)) (fix⁺ (mk-vec t)))
    goal .is-prop _ = isPropBisim _ _
    goal .rnil* = isReflBisim (fix⁺ Σ[])
    goal .rcons* {a = a} {as} {bs} b aRb b∈bs rel-remove cont = bisim approx where
      approx : ∀ n → Approx n (cut n (fix⁺ $ (a Σ∷ mk-vec as))) (cut n (fix⁺ bs))
      approx zero = tt
      approx (suc n) = Relator.rcons PT.∣ bₙ , aₙ∼bₙ , bₙ∈bs′ₙ , subst2 (Relator (Approx n)) {! sym (bsₙ≡bs′ₙ)!} {! !} (cont .elements (suc n)) ∣₁ where
        -- This is propositionally equal to (cut n b), but involves less substitutions
        -- to fill the remaining goals.
        aₙ : ΣVec ^ n
        aₙ = !^ n (cut (suc n) a)

        -- Similarly:
        _ : !^ n (cut (suc n) b) ≡ cut n b
        _ = b .is-lim n

        bₙ : ΣVec ^ n
        bₙ = !^ n (cut (suc n) b)

        b′ₙ = cut n b
        bsₙ = map (cut n) bs
        bs′ₙ = cut (suc n) (fix⁺ bs)

        bₙ≡b′ₙ : b′ₙ ≡ bₙ
        bₙ≡b′ₙ = sym (b .is-lim n)

        b′ₙ∈bsₙ : b′ₙ ∈ bsₙ
        b′ₙ∈bsₙ = ΣVec.∈-map (cut n) b∈bs

        aₙ∼bₙ : Approx n aₙ bₙ
        aₙ∼bₙ = subst2 (Approx n) (sym (a .is-lim n)) bₙ≡b′ₙ (aRb .elements n)

        bsₙ≡bs′ₙ : bsₙ ≡ bs′ₙ
        bsₙ≡bs′ₙ =
          map (cut n) bs                    ≡⟨ sym (cong-map-ext (TerminalChain.cut-is-lim _ n) bs) ⟩
          map (!^ n ∘ cut (suc n)) bs       ≡⟨ ΣVec.map-comp (!^ n) (cut (suc n)) bs ⟩
          map (!^ n) (map (cut (suc n)) bs) ∎

        bₙ∈bs′ₙ : bₙ ∈ bs′ₙ
        bₙ∈bs′ₙ = transport (cong₂ _∈_ bₙ≡b′ₙ bsₙ≡bs′ₙ) b′ₙ∈bsₙ

infixr 9 _T∷_
_T∷_ : (a : Tree) → (as : Tree) → Tree
_T∷_ a = subst (λ A → A → A) (ua ΣVecLimitEquiv) (a Σ∷_)

module _ (a b : Tree) (cs : Tree) where
  T∷-swap-approx : ∀ n → RelatorLim^ n (a T∷ b T∷ cs) (b T∷ a T∷ cs)
  T∷-swap-approx zero = tt
  T∷-swap-approx (suc n) = goal where
    goal : Relator (Approx n) _ _
    goal = {! (cut (suc n) (a T∷ b T∷ cs))!}

  T∷-swap : a T∷ b T∷ cs ≈ b T∷ a T∷ cs
  T∷-swap .elements n = {! !}
  T∷-swap .is-lim = {! !}
