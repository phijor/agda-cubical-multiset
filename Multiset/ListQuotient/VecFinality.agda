{-# OPTIONS --safe #-}

module Multiset.ListQuotient.VecFinality where

open import Multiset.Prelude
open import Multiset.Limit.Chain
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
    ; Lim→ShLim
    ; ShLim→Lim
    )
open import Multiset.ListQuotient.Base

open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Function using (_∘_ ; ∘-assoc ; flip)
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Transport using (substCommSlice ; substComposite)
import Cubical.Data.Empty as Empty
open import Cubical.Data.Sigma as Sigma using (ΣPathP ; _×_)
open import Cubical.Data.Nat.Base as Nat using (ℕ ; suc ; zero)
open import Cubical.Data.Nat.Properties as Nat using ()
open import Cubical.Data.Nat.Properties using (snotz)
open import Cubical.Data.FinData as Fin using (Fin) renaming (zero to fzero ; suc to fsuc)
open import Cubical.Data.Unit.Base using (Unit* ; Unit ; tt*)
open import Cubical.Data.Unit.Properties using (isOfHLevelUnit*)
open import Cubical.Data.Vec as Vec
  using (Vec ; [] ; _∷_ ; module VecPath)
  renaming
    ( FinVec→Vec to lookup⁻¹
    ; FinVec→Vec→FinVec to lookup-right-inv
    ; Vec→FinVec→Vec to lookup-left-inv
    )

ΣVec : Type → Type
ΣVec A = Σ ℕ (Vec A)

length : {A : Type} → ΣVec A → ℕ
length = fst

vec : {A : Type} → (as : ΣVec A) → Vec A (length as)
vec = snd

Index : {A : Type} → (xs : ΣVec A) → Type
Index xs = Fin (length xs)

module ΣVec where
  private
    variable
      A B C : Type

  isOfHLevelVec : (h : HLevel) (n : ℕ)
                  → isOfHLevel (suc (suc h)) A → isOfHLevel (suc (suc h)) (Vec A n)
  isOfHLevelVec h zero ofLevelA [] [] =
    isOfHLevelRespectEquiv (suc h)
      (invEquiv (Vec.VecPath.≡Vec≃codeVec [] []))
      (isOfHLevelUnit* (suc h))
  isOfHLevelVec h (suc n) ofLevelA (x ∷ v) (x' ∷ v') =
    isOfHLevelRespectEquiv (suc h)
      (invEquiv (Vec.VecPath.≡Vec≃codeVec _ _))
      (isOfHLevelΣ (suc h) (ofLevelA x x') (λ _ → isOfHLevelVec h n ofLevelA v v'))

  isSetVec : ∀ {n} → isSet A → isSet (Vec A n)
  isSetVec = isOfHLevelVec 0 _

  module _ {A B : Type} where
    lookup-map : (f : A → B) → ∀ {n} (xs : Vec A n) k → Vec.lookup k (Vec.map f xs) ≡ f (Vec.lookup k xs)
    lookup-map f (x ∷ xs) (fzero) = refl {x = f x}
    lookup-map f (x ∷ xs) (fsuc k) = lookup-map f xs k

    lookup⁻¹-map : (f : A → B) → ∀ {n} (xs : Fin.FinVec A n) → Vec.map f (lookup⁻¹ xs) ≡ lookup⁻¹ (f ∘ xs)
    lookup⁻¹-map f {zero} xs = refl {x = []}
    lookup⁻¹-map f {suc n} xs = cong (f (xs fzero) ∷_) (lookup⁻¹-map f (xs ∘ fsuc))

  map : (f : A → B) → ΣVec A → ΣVec B
  map f (n , xs)= n , Vec.map f xs

  vec-map-id : ∀ {n} → (xs : Vec A n) → Vec.map (λ x → x) xs ≡ xs
  vec-map-id [] = refl
  vec-map-id (x ∷ xs) = cong (x ∷_) (vec-map-id xs)

  vec-map-comp : (g : B → C) (f : A → B) → ∀ {n} → (xs : Vec A n) → Vec.map (g ∘ f) xs ≡ Vec.map g (Vec.map f xs)
  vec-map-comp g f [] = refl
  vec-map-comp g f (x ∷ xs) = cong (g (f x) ∷_) (vec-map-comp g f xs)

  map-id : ∀ xs → map (λ (x : A) → x) xs ≡ xs
  map-id (n , xs) = ΣPathP (refl , vec-map-id xs)

  map-comp : (g : B → C) (f : A → B) → (xs : ΣVec A) → map (g ∘ f) xs ≡ map g (map f xs)
  map-comp g f (n , xs) = ΣPathP (refl , vec-map-comp g f xs)

Vec' : ℕ → Type → Type
Vec' n A = Vec A n

instance
  FunctorVec : ∀ {n} → Functor {ℓ-zero} (Vec' n)
  FunctorVec .Functor.map = Vec.map
  FunctorVec .Functor.map-id = ΣVec.vec-map-id
  FunctorVec .Functor.map-comp = λ g f as → ΣVec.vec-map-comp g f as

  FunctorΣVec : Functor {ℓ-zero} ΣVec
  FunctorΣVec .Functor.map = ΣVec.map
  FunctorΣVec .Functor.map-id = ΣVec.map-id
  FunctorΣVec .Functor.map-comp = ΣVec.map-comp

isSetΣVec : ∀ {A} → isSet A → isSet (ΣVec A)
isSetΣVec setA = isSetΣ Nat.isSetℕ λ n → ΣVec.isOfHLevelVec 0 n setA

isSetΣVec^ : ∀ n → isSet (ΣVec ^ n)
isSetΣVec^ zero = isOfHLevelUnit* 2
isSetΣVec^ (suc n) = isSetΣVec (isSetΣVec^ n)

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
vecs tree d = tree .Limit.elements d .snd

widthConstSuc : ∀ (tree : ShLim ΣVec) n → width tree n ≡ width tree (suc n)
widthConstSuc (lim tree is-lim) n = cong length (sym $ is-lim n)

open Iso

pres-Iso : Iso (ShLim ΣVec) (ΣVec (Lim ΣVec))
pres-Iso =
  ShLim ΣVec                        Iso⟨ toTraceFirstIso ⟩
  TraceFirst                        Iso⟨ invIso (Sigma.Σ-cong-iso-fst (invIso TraceIso)) ⟩
  Σ ℕ (OverTrace ∘ constTrace)      Iso⟨ Sigma.Σ-cong-iso-snd toVecLimit ⟩
  Σ ℕ (Limit ∘ vecChain)            Iso⟨ Sigma.Σ-cong-iso-snd toFinVecOfLimits ⟩
  Σ ℕ (Fin.FinVec (Lim ΣVec))       Iso⟨ Sigma.Σ-cong-iso-snd Vec.FinVecIsoVec ⟩
  ΣVec (Lim ΣVec) ∎Iso
  where

  open import Multiset.Util.Trace as Trace
    using (Trace ; step ; connect ; constTrace ; TraceIso ; start ; to0)

  OverTrace : Trace ℕ → Type
  OverTrace as =
    Σ[ vs ∈ ((n : ℕ) → Vec (ΣVec ^ n) (as .step n)) ]
    ∀ (n : ℕ) →
      PathP (λ i → Vec (ΣVec ^ n) (as .connect n i))
        (vs n)
        (Vec.map (!^ n) (vs (suc n)))

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
    elements n = trace .step n , vecs n

    is-lim : ∀ n → !^ (suc n) (elements (suc n)) ≡ elements n
    is-lim n = sym $ ΣPathP (trace .connect n , vecs-coh n)
  toTraceFirstIso .rightInv _ = refl
  toTraceFirstIso .leftInv _ = refl

  module _ (sz : ℕ) where
    open Limit
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
        (!^ n) (Vec.lookup k $ elements (suc n))           ≡⟨ sym (ΣVec.lookup-map (!^ n) (elements (suc n)) k) ⟩
        (Vec.lookup k $ Vec.map (!^ n) (elements (suc n))) ≡⟨ cong (Vec.lookup k) (is-lim n) ⟩∎
        (Vec.lookup k $ elements n) ∎

    toFinVecOfLimits : Iso (Limit vecChain) (Fin.FinVec (Lim ΣVec) sz)
    toFinVecOfLimits = go where
      module _ (vec : Limit vecChain) where
        f-elements : Fin.FinVec (∀ n → ΣVec ^ n) sz
        f-elements k = Vec.lookup k ∘ (vec .elements)

        f-is-lim : ∀ k → isLim ΣVec (f-elements k)
        f-is-lim k n =
          (!^ n) (Vec.lookup k $ vec .elements (suc n))           ≡⟨ sym (ΣVec.lookup-map (!^ n) (vec .elements (suc n)) k) ⟩
          (Vec.lookup k $ Vec.map (!^ n) (vec .elements (suc n))) ≡⟨ cong (Vec.lookup k) (vec .is-lim n) ⟩∎
          (Vec.lookup k $ vec .elements n) ∎

        f : Fin.FinVec (Lim ΣVec) sz
        f k .elements = f-elements k
        f k .is-lim = f-is-lim k

      module _ (vec : Fin.FinVec (Lim ΣVec) sz) where
        open Functor ⦃...⦄

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
          Vec.lookup k (Vec.map (cut n) (lookup⁻¹ vec-of-lim))  ≡⟨ ΣVec.lookup-map (cut n) (lookup⁻¹ vec-of-lim) k ⟩
          (cut n $ Vec.lookup k (lookup⁻¹ vec-of-lim))          ≡⟨ cong (cut n) (funExt⁻ (lookup-right-inv vec-of-lim) k) ⟩
          (cut n $ vec-of-lim k) ∎
      go .leftInv lim-of-vec = isSet→LimitPathExt vecChain (λ k → ΣVec.isSetVec (isSetΣVec^ k)) left-inv where
        left-inv : ∀ n → f⁻¹ (f lim-of-vec) .elements n ≡ lim-of-vec .elements n
        left-inv n =
          Vec.map (cut n) (lookup⁻¹ (f lim-of-vec)) ≡⟨ ΣVec.lookup⁻¹-map (cut n) _ ⟩
          lookup⁻¹ (cut n ∘ f lim-of-vec) ≡⟨⟩
          lookup⁻¹ (λ k → f-elements lim-of-vec k n) ≡⟨⟩
          lookup⁻¹ (λ k → (Vec.lookup k $ lim-of-vec .elements n)) ≡⟨ lookup-left-inv _ ⟩
          lim-of-vec .elements n ∎

presIsoInv≡pres : pres-Iso .inv ≡ pres
presIsoInv≡pres = funExt λ vec → TerminalChain.isSet→ShLimPath ΣVec (isSetΣVec^ ∘ suc) (goal vec) where
  module _ (vec : ΣVec (Lim ΣVec)) where abstract
    open Limit
    goal : ∀ n → pres-Iso .inv vec .elements n ≡ pres vec .elements n
    goal n = ΣPathP (refl , cong (Vec.map (cut n)) (lookup-left-inv (vec .snd)))

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

  open Functor ⦃...⦄

  step : (n : ℕ) → C → ΣVec ^ n
  step zero _ = tt*
  step (suc n) c = map (step n) (γ c)

  is-lim-step : ∀ c → isLimit (TerminalChain.ch ΣVec) (flip step c)
  is-lim-step c zero = refl
  is-lim-step c (suc n) = goal where abstract
    goal : ΣVec.map (!^ n) (step (suc $ suc n) c) ≡ step (suc n) c
    goal =
      (map (!^ n) $ map (step (suc n)) $ γ c) ≡⟨ sym (map-comp (!^ n) _ (γ c)) ⟩
      (map (!^ n ∘ step (suc n)) $ γ c)       ≡⟨ cong (λ f → map f (γ c)) (funExt λ c' → is-lim-step c' n) ⟩
      (map (step n) $ γ c) ∎

  unfold : C → Lim ΣVec
  unfold c .elements = flip step c
  unfold c .is-lim = is-lim-step c

  abstract
    step-unfold : ∀ c n → step n c ≡ fix⁺ (ΣVec.map unfold (γ c)) .elements n
    step-unfold c zero = refl {x = tt*}
    step-unfold c (suc n) =
      ΣVec.map (step n) (γ c)                                       ≡⟨⟩
      ΣVec.map (cut n ∘ unfold) (γ c)                               ≡⟨ map-comp (cut n) unfold _ ⟩
      ΣVec.map (cut n)              (ΣVec.map unfold (γ c))         ≡⟨ cong-map-ext (sym $ TerminalChain.cut-is-lim _ n) _ ⟩
      ΣVec.map (!^ n ∘ cut (suc n)) (ΣVec.map unfold (γ c))         ≡⟨ map-comp (!^ n) (cut (suc n)) _ ⟩
      ΣVec.map (!^ n) (map (cut (suc n)) $ ΣVec.map unfold (γ c))   ≡⟨⟩
      !^ (suc n) (pres (ΣVec.map unfold (γ c)) .elements (suc n))   ≡⟨⟩
      ShLim→Lim _ (pres (ΣVec.map unfold (γ c))) .elements (suc n)  ≡⟨⟩
      fix⁺ (ΣVec.map unfold (γ c)) .elements (suc n) ∎

    unfold-fix⁺ : ∀ c → unfold c ≡ fix⁺ (map unfold (γ c))
    unfold-fix⁺ c = isSet→LimitPathExt _ isSetΣVec^ (step-unfold c)

  isCoalgebraMorphismUnfold : isCoalgebraMorphism ΣVec γ fix⁻ unfold
  isCoalgebraMorphismUnfold = funExt goal where abstract
    goal : ∀ c → fix⁻ (unfold c) ≡ map unfold (γ c)
    goal c =
      fix⁻ (unfold c) ≡⟨ cong fix⁻ (unfold-fix⁺ c) ⟩
      fix⁻ (fix⁺ (ΣVec.map unfold (γ c))) ≡⟨ retEq ΣVecLimitEquiv (ΣVec.map unfold (γ c)) ⟩
      map unfold (γ c) ∎

isTerminalFix⁻ : isTerminal ΣVec fix⁻
isTerminalFix⁻ {B = B} β = ana , anaEq where
  open Functor FunctorΣVec

  open TerminalChain.Fixpoint isLimitPreservingΣVec
    using (fix⁺-step-ext)

  ana : CoalgebraMorphism ΣVec β fix⁻
  ana = unfold β , isCoalgebraMorphismUnfold β

  anaEq : ∀ f → ana ≡ f
  anaEq (f , f-is-mor) = Sigma.Σ≡Prop isPropIsCoalgebraMorphism' eq where
    isPropIsCoalgebraMorphism' : (u : B → Lim ΣVec) → isProp (isCoalgebraMorphism ΣVec β fix⁻ u)
    isPropIsCoalgebraMorphism' u = isSet→isPropIsCoalgebraMorphism ΣVec β fix⁻ u (isSetΣVec isSetLimΣVec)

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
