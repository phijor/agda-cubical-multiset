{-# OPTIONS --safe #-}

module Multiset.ListQuotient.ListFinality where

open import Multiset.Prelude
open import Multiset.Util.Path using (substIso)
open import Multiset.Functor using (NatTrans ; NatEquiv)
open import Multiset.Util.Vec as VecExt using ()
open import Multiset.Util.BundledVec as BVec
  using
    ( ΣVec
    ; #_
    ; ΣVecPathP
    ; ΣVecIsoΣ
    ; ΣVecUnit*-ℕ-Iso
    )
open import Multiset.Limit.Chain as Chain
  using
    ( lim
    ; Limit
    ; Chain
    ; isSet→LimitPathExt
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
    ; ShLim→Lim
    )

open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Function using (_∘_ ; ∘-assoc ; flip)
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Transport using (substEquiv)
open import Cubical.Foundations.Univalence using (ua)
open import Cubical.Functions.FunExtEquiv using (funExtDep)
open import Cubical.Data.Sigma as Sigma
  using
    ( ΣPathP
    ; Σ≡Prop
    ; Σ-cong-iso-fst
    ; Σ-cong-iso-snd
    )
open import Cubical.Data.Nat.Base as Nat using (ℕ ; suc ; zero ; _+_)
open import Cubical.Data.FinData as Fin using (FinVec)
open import Cubical.Data.Unit.Base using (Unit* ; tt*)
open import Cubical.Data.Unit.Properties as Unit using (isOfHLevelUnit*)
open import Cubical.Data.Vec.Base as Vec using (Vec)
open import Cubical.Data.Vec.Properties as Vec using (FinVecIsoVec)

open ΣVec

instance
  FunctorVec : ∀ {n} → Functor {ℓ-zero} (λ A → Vec A n)
  FunctorVec .Functor.map = Vec.map
  FunctorVec .Functor.map-id = VecExt.vec-map-id
  FunctorVec .Functor.map-comp = λ g f as → VecExt.vec-map-comp g f as

  FunctorΣVec : Functor {ℓ-zero} ΣVec
  FunctorΣVec .Functor.map = BVec.map
  FunctorΣVec .Functor.map-id = BVec.map-id
  FunctorΣVec .Functor.map-comp = BVec.map-comp

module _ where private
  open import Cubical.Data.List as List using (List)
  instance
    FunctorList : Functor {ℓ-zero} List
    FunctorList .Functor.map = List.map
    FunctorList .Functor.map-id {X = X} = go where
      go : (xs : List X) → _
      go List.[] = refl
      go (x List.∷ xs) = cong (x List.∷_) (go xs)
    FunctorList .Functor.map-comp {X} {Y} {Z} g f = go where
      go : (xs : List X) → _
      go List.[] = refl
      go (x List.∷ xs) = cong (g (f x) List.∷_) (go xs)

  ΣVec→List : {A : Type} → ΣVec A → List A
  ΣVec→List (# Vec.[]) = List.[]
  ΣVec→List (# (a Vec.∷ as)) = a List.∷ ΣVec→List (# as)

  List→ΣVec : {A : Type} → List A → ΣVec A
  List→ΣVec List.[] = BVec.[]
  List→ΣVec (a List.∷ as) = a BVec.#∷ List→ΣVec as

  ΣVec⇒List : NatTrans {ℓ = ℓ-zero} ΣVec List
  ΣVec⇒List .NatTrans.mor = ΣVec→List
  ΣVec⇒List .NatTrans.is-nat {X = X} f = funExt is-nat where
    is-nat : (xs : ΣVec X) → ΣVec→List (BVec.map f xs) ≡ List.map f (ΣVec→List xs)
    is-nat (# Vec.[]) = refl {x = List.[]}
    is-nat (# (x Vec.∷ xs)) = cong (f x List.∷_) (is-nat (# xs))

  ΣVec-List-EquivNat : NatEquiv ΣVec List
  ΣVec-List-EquivNat .fst = ΣVec⇒List
  ΣVec-List-EquivNat .snd {X} = isoToIsEquiv nat-iso where
    nat-iso : Iso (ΣVec X) (List X)
    nat-iso .Iso.fun = ΣVec→List
    nat-iso .Iso.inv = List→ΣVec
    nat-iso .Iso.rightInv = right-inv where
      right-inv : (xs : List _) → _ ≡ xs
      right-inv List.[] = refl
      right-inv (x List.∷ xs) = cong (x List.∷_) (right-inv xs)
    nat-iso .Iso.leftInv = left-inv where
      left-inv : (xs : ΣVec _) → _ ≡ xs
      left-inv (# Vec.[]) = refl
      left-inv (# (x Vec.∷ xs)) = cong (x BVec.#∷_) (left-inv (# xs))

open Functor ⦃...⦄

isSetΣVec^ : ∀ n → isSet (ΣVec ^ n)
isSetΣVec^ zero = isOfHLevelUnit* 2
isSetΣVec^ (suc n) = BVec.isSetΣVec (isSetΣVec^ n)

!^ : (n : ℕ) → ΣVec ^ (suc n) → ΣVec ^ n
!^ = ΣVec map-!^_

Tree : Type
Tree = Lim ΣVec

isTree : ((n : ℕ) → ΣVec ^ n) → Type
isTree = isLim ΣVec

pres⁺ : ΣVec (Lim ΣVec) → ShLim ΣVec
pres⁺ = TerminalChain.pres ΣVec

cut : (n : ℕ) → Lim ΣVec → ΣVec ^ n
cut = TerminalChain.cut ΣVec

width : ShLim ΣVec → (d : ℕ) → ℕ
width tree d = length $ tree .Limit.elements d

vecs : (tree : ShLim ΣVec) → (d : ℕ) → Vec (ΣVec ^ d) (width tree d)
vecs tree d = tree .Limit.elements d .vec

widthConstSuc : ∀ (tree : ShLim ΣVec) n → width tree n ≡ width tree (suc n)
widthConstSuc (lim tree is-lim) n = cong length (sym $ is-lim n)

open Iso
open Limit

module ConstLength (len₀ : ℕ) (xs : (d : ℕ) → Vec (ΣVec ^ d) len₀) where
  
  constLengthApprox : (d : ℕ) → ΣVec ^ (suc d)
  constLengthApprox d .length = len₀
  constLengthApprox d .vec = xs d

  module _ (islim : isShLim ΣVec constLengthApprox) where

    constLengthLim : ShLim ΣVec
    constLengthLim .elements = constLengthApprox
    constLengthLim .is-lim = islim

    inh' : FinVec (Lim ΣVec) len₀
    inh' k .elements = Vec.lookup k ∘ xs
    inh' k .is-lim d =
      (!^ d) (Vec.lookup k $ xs (suc d))           ≡⟨ sym (VecExt.lookup-map (!^ d) (xs (suc d)) k) ⟩
      (Vec.lookup k $ Vec.map (!^ d) (xs (suc d))) ≡⟨ cong (Vec.lookup k) (BVec.mk-vec-inj (islim d)) ⟩∎
      (Vec.lookup k $ xs d) ∎

    inh : ΣVec (Lim ΣVec)
    inh .length = len₀
    inh .vec = Vec.FinVec→Vec inh'

    abstract
      inh∈fiber : pres⁺ inh ≡ constLengthLim
      inh∈fiber = TerminalChain.isSet→ShLimPath ΣVec (isSetΣVec^ ∘ suc) ptwise where
        ptwise : ∀ n →  pres⁺ inh .elements n ≡ constLengthApprox n
        ptwise n = cong #_ $
          Vec.map (cut n) (Vec.FinVec→Vec inh') ≡⟨ VecExt.lookup⁻¹-map (cut n) inh' ⟩
          Vec.FinVec→Vec (cut n ∘ inh')         ≡⟨ Vec.Vec→FinVec→Vec (xs n) ⟩∎
          xs n ∎

    inhFibers : fiber pres⁺ constLengthLim
    inhFibers = inh , inh∈fiber

inhFibers : (base : ShLim ΣVec) → fiber pres⁺ base
inhFibers base = subst (fiber pres⁺) shlim≡ (ConstLength.inhFibers length₀ approx approx-is-shlim) where
  length₀ : ℕ
  length₀ = base .elements 0 .length

  constLength : ∀ d → base .elements d .length ≡ length₀
  constLength zero = refl
  constLength (suc d) = cong length (base .is-lim d) ∙ constLength d

  approx : (d : ℕ) → Vec (ΣVec ^ d) length₀
  approx d = subst (Vec (ΣVec ^ d)) (constLength d) (base .elements d .vec)

  approx≡ : ∀ d → base .elements d ≡ # (approx d)
  approx≡ d = ΣVecPathP (constLength d) $ subst-filler (Vec (ΣVec ^ d)) (constLength d) (base .elements d .vec)

  approx-is-shlim : isShLim ΣVec (ConstLength.constLengthApprox length₀ approx)
  approx-is-shlim = subst (isShLim ΣVec) (funExt approx≡) (base .is-lim)

  shlim≡ : ConstLength.constLengthLim length₀ approx approx-is-shlim ≡ base
  shlim≡ = TerminalChain.isSet→ShLimPath ΣVec (isSetΣVec^ ∘ suc) (sym ∘ approx≡)

module Direct where
  pres⁻ : ShLim ΣVec → ΣVec (Lim ΣVec)
  pres⁻ = fst ∘ inhFibers

  pres-section : section pres⁺ pres⁻
  pres-section = snd ∘ inhFibers

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

pres-Iso : Iso (ShLim ΣVec) (ΣVec (Lim ΣVec))
pres-Iso =
  let snd-iso : ∀ n → Iso (OverTrace (constTrace n)) (Vec (Lim ΣVec) n)
      snd-iso n =
        OverTrace (constTrace n)  Iso⟨ toVecLimit n ⟩
        Limit (vecChain n)        Iso⟨ toFinVecOfLimits n ⟩
        FinVec (Lim ΣVec) n   Iso⟨ Vec.FinVecIsoVec n ⟩
        Vec (Lim ΣVec) n          ∎Iso
  in
  ShLim ΣVec                    Iso⟨ toTraceFirstIso ⟩
  Σ (Trace ℕ) OverTrace         Iso⟨ invIso (Σ-cong-iso-fst (invIso TraceIso)) ⟩
  Σ ℕ (OverTrace ∘ constTrace)  Iso⟨ Σ-cong-iso-snd snd-iso ⟩
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
  toTraceFirstIso .inv (trace , vecs , vecs-coh) .elements n = #_ {length = trace .fst n} $ vecs n
  toTraceFirstIso .inv (trace , vecs , vecs-coh) .is-lim n = sym $ ΣVecPathP (trace .snd n) (vecs-coh n)
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

    toFinVecOfLimits : Iso (Limit vecChain) (FinVec (Lim ΣVec) sz)
    toFinVecOfLimits = go where
      module _ (vec : Limit vecChain) where
        f-elements : FinVec (∀ n → ΣVec ^ n) sz
        f-elements k = Vec.lookup k ∘ (vec .elements)

        f-is-lim : ∀ k → isTree (f-elements k)
        f-is-lim k n =
          (!^ n) (Vec.lookup k $ vec .elements (suc n))           ≡⟨ sym (VecExt.lookup-map (!^ n) (vec .elements (suc n)) k) ⟩
          (Vec.lookup k $ Vec.map (!^ n) (vec .elements (suc n))) ≡⟨ cong (Vec.lookup k) (vec .is-lim n) ⟩∎
          (Vec.lookup k $ vec .elements n) ∎

        f : FinVec (Lim ΣVec) sz
        f k .elements = f-elements k
        f k .is-lim = f-is-lim k

      module _ (vec : FinVec (Lim ΣVec) sz) where
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
      go .rightInv vec-of-lim = funExt λ { k → isSet→LimitPathExt _ isSetΣVec^ (right-inv k) } where abstract
        right-inv : ∀ k n → f-elements (f⁻¹ vec-of-lim) k n ≡ vec-of-lim k .elements n
        right-inv k n =
          Vec.lookup k (Vec.map (cut n) (lookup⁻¹ vec-of-lim))  ≡⟨ VecExt.lookup-map (cut n) (lookup⁻¹ vec-of-lim) k ⟩
          (cut n $ Vec.lookup k (lookup⁻¹ vec-of-lim))          ≡⟨ cong (cut n) (funExt⁻ (lookup-right-inv vec-of-lim) k) ⟩
          (cut n $ vec-of-lim k) ∎
      go .leftInv lim-of-vec = isSet→LimitPathExt vecChain (λ k → VecExt.isSetVec (isSetΣVec^ k)) left-inv where abstract
        left-inv : ∀ n → f⁻¹ (f lim-of-vec) .elements n ≡ lim-of-vec .elements n
        left-inv n =
          Vec.map (cut n) (lookup⁻¹ (f lim-of-vec))                 ≡⟨ VecExt.lookup⁻¹-map (cut n) _ ⟩
          lookup⁻¹ (cut n ∘ f lim-of-vec)                           ≡⟨⟩
          lookup⁻¹ (λ k → f-elements lim-of-vec k n)                ≡⟨⟩
          lookup⁻¹ (λ k → (Vec.lookup k $ lim-of-vec .elements n))  ≡⟨ lookup-left-inv _ ⟩
          lim-of-vec .elements n ∎

pres′⁺ : ΣVec (Lim ΣVec) → ShLim ΣVec
pres′⁺ = pres-Iso .inv

pres′⁺≡pres : pres′⁺ ≡ pres⁺
pres′⁺≡pres = funExt $ TerminalChain.isSet→ShLimPath ΣVec (isSetΣVec^ ∘ suc) ∘ goal where
  open Limit
  goal : ∀ (xs : ΣVec (Lim ΣVec)) n → pres-Iso .inv xs .elements n ≡ pres⁺ xs .elements n
  goal xs n = ΣVecPathP refl $ cong (Vec.map (cut n)) (VecExt.lookup-left-inv (xs .vec))

abstract
  isLimitPreservingΣVec : isLimitPreserving ΣVec
  isLimitPreservingΣVec = subst isEquiv pres′⁺≡pres (isoToIsEquiv (invIso pres-Iso))

pres : ΣVec (Lim ΣVec) ≃ ShLim ΣVec
pres = pres⁺ , isLimitPreservingΣVec

pres′ : ΣVec (Lim ΣVec) ≃ ShLim ΣVec
pres′ = pres′⁺ , isoToIsEquiv (invIso pres-Iso)

pres′≡pres : pres′ ≡ pres
pres′≡pres = equivEq pres′⁺≡pres

open TerminalChain.Fixpoint isLimitPreservingΣVec
  using (fix ; fix⁺ ; fix⁻ ; fix⁻-step-ext ; pres⁻)
  public

ΣVecLimitEquiv : ΣVec (Lim ΣVec) ≃ Lim ΣVec
ΣVecLimitEquiv = fix

ΣVecLimitPath : ΣVec (Lim ΣVec) ≡ Lim ΣVec
ΣVecLimitPath = ua ΣVecLimitEquiv

isSetLimΣVec : isSet (Lim ΣVec)
isSetLimΣVec = isOfHLevelLimit _ 2 isSetΣVec^

isSetTree = isSetLimΣVec

open Limit

TreePath : ∀ {l₁ l₂ : Lim ΣVec} → (∀ n → l₁ .elements n ≡ l₂ .elements n) → l₁ ≡ l₂
TreePath = isSet→LimitPathExt _ isSetΣVec^

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
      !^ (suc n) (pres⁺ (map unfold (γ c)) .elements (suc n))  ≡⟨⟩
      ShLim→Lim _ (pres⁺ (map unfold (γ c))) .elements (suc n) ≡⟨⟩
      fix⁺ (map unfold (γ c)) .elements (suc n) ∎

    unfold-fix⁺ : ∀ c → unfold c ≡ fix⁺ (map unfold (γ c))
    unfold-fix⁺ c = isSet→LimitPathExt _ isSetΣVec^ (step-unfold c)

  isCoalgebraMorphismUnfold : isCoalgebraMorphism ΣVec γ fix⁻ unfold
  isCoalgebraMorphismUnfold = funExt goal where abstract
    goal : ∀ c → fix⁻ (unfold c) ≡ BVec.map unfold (γ c)
    goal c =
      fix⁻ (unfold c) ≡⟨ cong fix⁻ (unfold-fix⁺ c) ⟩
      fix⁻ (fix⁺ (BVec.map unfold (γ c))) ≡⟨ retEq ΣVecLimitEquiv (BVec.map unfold (γ c)) ⟩
      map unfold (γ c) ∎

tree-width : Tree → ℕ
tree-width = length ∘ fix⁻

isTerminalFix⁻ : isTerminal ΣVec fix⁻
isTerminalFix⁻ {B = B} β = ana , anaEq where
  open TerminalChain.Fixpoint isLimitPreservingΣVec
    using (fix⁺-step-ext)

  ana : CoalgebraMorphism ΣVec β fix⁻
  ana = unfold β , isCoalgebraMorphismUnfold β

  anaEq : ∀ f → ana ≡ f
  anaEq (f , f-is-mor) = Σ≡Prop isPropIsCoalgebraMorphism' eq where abstract
    isPropIsCoalgebraMorphism' : (u : B → Lim ΣVec) → isProp (isCoalgebraMorphism ΣVec β fix⁻ u)
    isPropIsCoalgebraMorphism' u = isSet→isPropIsCoalgebraMorphism ΣVec β fix⁻ u (BVec.isSetΣVec isSetLimΣVec)

    eq : unfold β ≡ f
    eq = funExt $ TreePath ∘ λ b n → funExt⁻ (goal n) b where
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
