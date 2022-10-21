{-# OPTIONS --safe #-}

module Multiset.OverBij.Properties where

open import Multiset.Prelude
open import Multiset.Util using (!_)
open import Multiset.OverBij.Base as OverBij
  using
    ( Bag ; BagIsoΣ
    ; ⟅⟆-syntax
    ; map
    ; Idx
    ; Vect
    ; BagPathExt ; BagPathP
    )
open import Multiset.Bij as Bij
open import Multiset.Chains using (Chain ; module Limit)
open import Multiset.Chains.FunctorChain as FunctorChain
open import Multiset.Util.Path
  using
    ( subst⁻-filler
    ; transport⁻Domain
    )

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Isomorphism
  renaming (compIso to infixl 20 _∙≅_)
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Path
open import Cubical.Foundations.Transport
open import Cubical.Foundations.Function using (_∘_)

open import Cubical.Functions.FunExtEquiv using (funExtDep ; funExtDep⁻)

open import Cubical.Data.Sigma as Σ
  using (ΣPathP)
open import Cubical.Data.Nat as ℕ
  using (ℕ ; zero ; suc)
open import Cubical.Data.Unit as Unit
  using
    ( Unit
    ; tt
    )

private
  variable
    ℓ : Level

open Bag using (card ; members)
open Limit using (lim ; ChainLimit)
open ChainLimit using (elements ; isChainLimit)

instance
  BagFunctor : Functor Bag
  BagFunctor .Functor.map = OverBij.map
  BagFunctor .Functor.map-id = OverBij.mapId
  BagFunctor .Functor.map-comp g f xs = sym (OverBij.map∘map f g xs)

BagUnit≃Bij : Bag Unit ≃ Bij
BagUnit≃Bij = isoToEquiv BagIsoΣ ∙ₑ Σ.Σ-contractSnd {B = λ (x : Bij) → Idx x → Unit} (λ _ → isContrΠUnit) where
  isContrΠUnit : {X : Type} → isContr (X → Unit)
  isContrΠUnit {X} = !_ , λ f → refl

private
  !^ : ∀ n → Bag ^ (suc n) → Bag ^ n
  !^ n = Bag map-!^ n

-- Zipping and unzipping non-wellfounded trees

{- Unzipping

Given a bag of non-wellfounded trees, we can "unzip" it into
a limiting sequences of bags of trees.

At step n in the sequence, the resulting bag contains a tree
of depth n, obtained by mapping the "cut at depth n"-function
over the input bag.
-}
module Unzip (trees : Bag (Lim Bag)) where
  unzip : (n : ℕ) → Bag (Bag ^ n)
  unzip n = OverBij.map (λ tree → tree .elements n) trees

  isChainLimitUnzip : (n : ℕ) → map (!^ n) (unzip (suc n)) ≡ unzip n
  isChainLimitUnzip n = BagPathExt (λ idx → trees .members idx .isChainLimit n)

  unzipped : ShLim Bag
  unzipped = lim unzip isChainLimitUnzip

open Iso

zipUnzipIso : Iso (ShLim Bag) (Bag (Lim Bag))
zipUnzipIso =
  ShLim Bag       Iso⟨ toTraceFirstIso ⟩
  TraceFirst      Iso⟨ toVectLimitBag ⟩
  Σ Bij VectLimit Iso⟨ toBagOfTrees ⟩
  Bag (Lim Bag)   ∎Iso where

  open Limit

  open import Cubical.Reflection.StrictEquiv
    using (strictEquiv ; strictIsoToEquiv)

  open import Multiset.Util.Trace as Trace
    using (Trace ; step ; connect ; constTrace ; TraceIso ; start)

  TraceFirst-snd : Trace Bij → Type
  TraceFirst-snd cardAt =
    Σ[ vs ∈ ((n : ℕ) → Vect (Bag ^ n) (cardAt .step n)) ]
    ∀ (n : ℕ) →
      PathP (λ i → Vect (Bag ^ n) (cardAt .connect n i))
        (vs n)
        (!^ n ∘ vs (suc n))

  TraceFirst : Type
  TraceFirst = Σ (Trace Bij) TraceFirst-snd

  toTraceFirstIso : Iso (ShLim Bag) TraceFirst
  toTraceFirstIso = go where
    go : Iso _ _
    fun go (lim elements isChainLimit) = trace , vects , vects-coh where
      step' : ℕ → Bij
      step' n = elements n .card

      connect' : ∀ n → step' n ≡ step' (suc n)
      connect' n = cong card (sym (isChainLimit n))

      trace : Trace Bij
      trace = step' , connect'

      vects : (n : ℕ) → Vect (Bag ^ n) (step' n)
      vects n = elements n .members

      vects-coh : ∀ n → PathP (λ i → Vect (Bag ^ n) (connect' n i)) (vects n) (λ idx → !^ n (vects (suc n) idx))
      vects-coh n = cong members (sym (isChainLimit n))
    inv go (trace , vects , vects-coh) = lim elements' isChainLimit' where
      elements' : (n : ℕ) → Bag (Bag ^ n)
      elements' n = ⟅ vects n idx ∣ idx ∈ trace .step n ⟆

      isChainLimit' : ∀ n → map (!^ n) (elements' (suc n)) ≡ elements' n
      isChainLimit' n = BagPathP (sym (trace .connect n)) (symP (vects-coh n))
    rightInv go (trace , vects , vects-coh) = ΣPathP (refl , ΣPathP (refl {x = vects} , refl {x = vects-coh}))
    leftInv go _ = refl

  vectChain : Bij → Chain ℓ-zero
  vectChain card .Chain.Ob n = Vect (Bag ^ n) card
  vectChain card .Chain.π n = !^ n ∘_

  VectLimit : (card : Bij) → Type
  VectLimit card = Limit.ChainLimit (vectChain card)

  toVectLimit : (card : Bij) → Iso (TraceFirst-snd (constTrace card)) (VectLimit card)
  toVectLimit card = go where
    go : Iso _ _
    go .fun (vects , vects-coh) = lim vects (sym ∘ vects-coh)
    go .inv (lim elements isChainLimit) = elements , sym ∘ isChainLimit
    go .rightInv _ = refl
    go .leftInv _ = refl

  toVectLimitBag : Iso TraceFirst (Σ Bij VectLimit)
  toVectLimitBag =
    TraceFirst                          Iso⟨ invIso (Σ.Σ-cong-iso-fst (invIso TraceIso)) ⟩
    Σ Bij (TraceFirst-snd ∘ constTrace) Iso⟨ Σ.Σ-cong-iso-snd toVectLimit ⟩
    Σ Bij VectLimit                     ∎Iso

  toBagOfTrees : Iso (Σ Bij VectLimit) (Bag (Lim Bag))
  toBagOfTrees = go where
    -- This is essentially the UP of limits of chains.
    go : Iso _ _
    go .fun (card , lim vects vects-coh) = ⟅ lim (λ n → vects n idx) (λ n → funExt⁻ (vects-coh n) idx) ∣ idx ∈ card ⟆
    go .inv bagOfTrees =
      ( bagOfTrees .card
      , lim
        (λ n idx → bagOfTrees .members idx .elements n)
        (λ n → funExt λ idx → bagOfTrees .members idx .isChainLimit n)
      )
    go .rightInv _ = refl
    go .leftInv _ = refl

zipUnzipIsoInv≡unzipped : zipUnzipIso .inv ≡ Unzip.unzipped
zipUnzipIsoInv≡unzipped = refl

isLimitPreservingBag : isLimitPreserving Bag
isLimitPreservingBag = isoToEquiv (invIso zipUnzipIso)

bagLimitEquiv : Bag (Lim Bag) ≃ Lim Bag
bagLimitEquiv = FunctorChain.fix isLimitPreservingBag

fix⁺ : Bag (Lim Bag) → Lim Bag
fix⁺ = equivFun bagLimitEquiv

fix⁻ : Lim Bag → Bag (Lim Bag)
fix⁻ = invEq bagLimitEquiv

BagLim = Lim Bag
