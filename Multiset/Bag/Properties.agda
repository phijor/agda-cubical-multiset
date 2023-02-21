{-# OPTIONS --safe #-}

module Multiset.Bag.Properties where

open import Multiset.Prelude
open import Multiset.Bag.Base as Bag
  using
    ( Bag
    ; map ; mapId ; map∘map
    ; Vect
    ; isGroupoidBag
    )
open import Multiset.Tote as Tote using (Tote)
open import Multiset.Bij as Bij
open import Multiset.Limit.Chain as Chain using (Limit ; lim ; Chain)
open import Multiset.Limit.TerminalChain as TerminalChain hiding (cut ; pres)
open import Multiset.Util.Path
  using
    ( subst⁻-filler
    ; transport⁻Domain
    )

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Isomorphism
  renaming (compIso to infixl 20 _∙≅_)
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.HLevels
  using (isContr→isOfHLevel ; isOfHLevelRespectEquiv)
open import Cubical.Foundations.Path
open import Cubical.Foundations.Transport
open import Cubical.Foundations.Structure using (⟨_⟩)
open import Cubical.Foundations.Function using (_∘_)

open import Cubical.Functions.FunExtEquiv using (funExtDep ; funExtDep⁻)

open import Cubical.Data.Sigma as Σ
  using (ΣPathP)
open import Cubical.Data.Nat as ℕ
  using (ℕ ; zero ; suc)
open import Cubical.Data.Unit as Unit
  using
    ( Unit*
    ; tt*
    ; isContrUnit*
    )

private
  variable
    ℓ : Level

open Limit using (elements ; is-lim)

instance
  BagFunctor : Functor {ℓ-zero} Bag
  BagFunctor .Functor.map = map
  BagFunctor .Functor.map-id = mapId
  BagFunctor .Functor.map-comp g f xs = sym (map∘map f g xs)

open Iso

BagUnit≃Bij : ∀ {ℓ} → Bag (Unit* {ℓ = ℓ}) ≃ Bij
BagUnit≃Bij = isoToEquiv goal
  where
    goal : Iso (Bag Unit*) Bij
    goal .fun = fst
    goal .inv card = card , λ _ → tt*
    goal .rightInv _ = refl
    goal .leftInv _ = refl

private
  !^ : ∀ n → Bag ^ (suc n) → Bag ^ n
  !^ n = Bag map-!^ n

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
      step' n = elements n .fst

      connect' : ∀ n → step' n ≡ step' (suc n)
      connect' n = cong fst (sym (isChainLimit n))

      trace : Trace Bij
      trace = step' , connect'

      vects : (n : ℕ) → Vect (Bag ^ n) (step' n)
      vects n = elements n .snd

      vects-coh : ∀ n → PathP (λ i → Vect (Bag ^ n) (connect' n i)) (vects n) (λ idx → !^ n (vects (suc n) idx))
      vects-coh n = cong snd (sym (isChainLimit n))
    inv go (trace , vects , vects-coh) = lim elements' isChainLimit' where
      elements' : (n : ℕ) → Bag (Bag ^ n)
      elements' n = trace .step n , vects n

      isChainLimit' : ∀ n → map (!^ n) (elements' (suc n)) ≡ elements' n
      isChainLimit' n = λ i → (trace .connect n (~ i)) , (vects-coh n (~ i))
    rightInv go (trace , vects , vects-coh) = λ i → trace , (vects , vects-coh)
    leftInv go _ = refl

  vectChain : Bij → Chain ℓ-zero
  vectChain card .Chain.Ob n = Vect (Bag ^ n) card
  vectChain card .Chain.π n = !^ n ∘_

  VectLimit : (card : Bij) → Type
  VectLimit card = Chain.Limit (vectChain card)

  toVectLimit : (card : Bij) → Iso (TraceFirst-snd (constTrace card)) (VectLimit card)
  toVectLimit card = go where
    go : Iso (TraceFirst-snd (constTrace card)) (VectLimit card)
    go .fun (vects , vects-coh) = lim vects λ n i → vects-coh n (~ i)
    go .inv (lim elements isChainLimit) = elements , (λ n i → isChainLimit n (~ i))
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
    go : Iso (Σ Bij VectLimit) (Bag (Lim Bag))
    go .fun (card , lim vects vects-coh) = (card , λ idx → lim (λ n → vects n idx) (λ n → funExt⁻ (vects-coh n) idx))
    go .inv (card , trees) = card , (lim (λ n idx → trees idx .elements n) λ n → funExt λ idx → trees idx .is-lim n)
    go .rightInv _ = refl 
    go .leftInv _ = refl 

zipUnzipIsoInv≡pres : zipUnzipIso .inv ≡ TerminalChain.pres Bag
zipUnzipIsoInv≡pres = funExt λ xs → ShLimPathPExt Bag (λ n → refl) (is-lim-coh xs) where
  open import Cubical.Foundations.GroupoidLaws using (lUnit)

  module _ (xs : Bag (Lim Bag)) (n : ℕ) where
    is-lim′ = zipUnzipIso .inv xs .is-lim n

    is-lim-coh : is-lim′ ≡ TerminalChain.pres Bag xs .is-lim n
    is-lim-coh =
      is-lim′         ≡⟨ lUnit is-lim′ ⟩∎
      refl ∙ is-lim′  ∎

isEquivUnzip : isEquiv (zipUnzipIso .inv)
isEquivUnzip = isoToIsEquiv (invIso zipUnzipIso)

isLimitPreservingBag : isLimitPreserving Bag
isLimitPreservingBag = subst isEquiv zipUnzipIsoInv≡pres isEquivUnzip

open TerminalChain.Fixpoint isLimitPreservingBag
  using (fix⁺ ; fix⁻)
  renaming (fix to bagLimitEquiv)
  public

BagLim : Type
BagLim = Lim Bag

isGroupoidBag^ : ∀ n → isGroupoid (Bag ^ n)
isGroupoidBag^ 0 = isContr→isOfHLevel 3 isContrUnit*
isGroupoidBag^ 1 = isOfHLevelRespectEquiv 3 (invEquiv BagUnit≃Bij) isGroupoidBij 
isGroupoidBag^ (suc (suc n)) = isGroupoidBag (isGroupoidBag^ (suc n))

isGroupoidBagLim : isGroupoid BagLim
isGroupoidBagLim = isOfHLevelLim Bag 3 isGroupoidBag^
