module Multiset.FCM.AlternativeLimit where

open import Multiset.Prelude
open import Multiset.Util using (!_)

open import Multiset.Chains

open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Function using (_∘_ ; const)
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.HLevels

open import Cubical.Data.Unit as Unit using (Unit ; tt)
import Cubical.Data.Empty as Empty
open import Cubical.Data.Sigma as Sigma
open import Cubical.Data.Nat as Nat using ( ℕ ; zero ; suc )

open import Cubical.Relation.Nullary

open import Cubical.HITs.FiniteMultiset as FMSet
open import Cubical.HITs.PropositionalTruncation as PT
  using
    ( ∥_∥₁
    ; ∣_∣₁
    )

isSetFMSet : ∀ {ℓ} {X : Type ℓ} → isSet (FMSet X)
isSetFMSet = FMSet.trunc

map : ∀ {ℓ ℓ′} {X : Type ℓ} {Y : Type ℓ′}
  → (f : X → Y)
  → FMSet X → FMSet Y
map f = FMSet.Rec.f isSetFMSet [] (λ x → f x ∷_) λ x y → comm (f x) (f y)

elim = FMSet.Elim.f
rec = FMSet.Rec.f

elimProp = FMSet.ElimProp.f


mapId : ∀ {ℓ} {X : Type ℓ} (xs : FMSet X) → map (λ x → x) xs ≡ xs
mapId = elimProp (isSetFMSet _ _) refl λ x → cong (x ∷_)

mapComp : ∀ {ℓ ℓ′ ℓ″} {X : Type ℓ} {Y : Type ℓ′} {Z : Type ℓ″}
  → (g : Y → Z)
  → (f : X → Y)
  → ∀ xs → map g (map f xs) ≡ map (g ∘ f) xs
mapComp g f = elimProp (isSetFMSet _ _) refl λ x → cong (g (f x) ∷_)

module _ where
  variable
    ℓ ℓ′ : Level
    X : Type ℓ
    Y : Type ℓ′

  length : (xs : FMSet X) → ℕ
  length = rec Nat.isSetℕ 0 (λ _ → suc) λ _ _ _ → refl

  ∷-[]-disjoint : ∀ {x : X} {xs : FMSet X}
    → ¬ (x ∷ xs ≡ [])
  ∷-[]-disjoint {x = x} {xs} = Nat.snotz ∘ cong length

  map-fiber-[] : ∀ {xs : FMSet X}
    → (f : X → Y)
    → map f xs ≡ []
    → xs ≡ []
  map-fiber-[] {X = X} {xs = xs} f = elimProp {B = λ xs → map f xs ≡ [] → xs ≡ []}
    (isPropΠ (λ h → isSetFMSet _ []))
    []* cons* xs where
    []* : map f [] ≡ [] → [] ≡ []
    []* _ = refl

    cons* : ∀ x {xs}
      → (map f xs ≡ [] → xs ≡ [])
      → map f (x ∷ xs) ≡ [] → x ∷ xs ≡ []
    cons* x {xs} indH-xs = Empty.rec ∘ ∷-[]-disjoint

  ∷-mere-injective : ∀ {x y : X} {zs}
    → x ∷ zs ≡ y ∷ zs
    → ∥ x ≡ y ∥₁
  ∷-mere-injective {X = X} {x} {y} {zs} = elimProp {B = λ zs → (x ∷ zs ≡ y ∷ zs) → ∥ x ≡ y ∥₁}
    (isPropΠ (λ _ → PT.isPropPropTrunc))
    {! !} {! !} zs

  module _ (setX : isSet X) where
    ∷-injective : ∀ {x y : X} {zs}
      → x ∷ zs ≡ y ∷ zs
      → x ≡ y
    ∷-injective {x} {y} {zs} = elimProp {B = λ zs → (x ∷ zs ≡ y ∷ zs) → x ≡ y}
      (isPropΠ (λ _ → setX _ _))
      {! !} {! !} zs

    map-fiber-∷ : ∀ {y : Y} {ys : FMSet Y}
      → (f : X → Y)
      → (xs : FMSet X)
      → map f xs ≡ y ∷ ys
      → ∃[ (h , ts) ∈ (X × FMSet X) ] (xs ≡ h ∷ ts) × (f h ≡ y) × (map f ts ≡ ys)
    map-fiber-∷ {y = y} {ys} f = elimProp {B = P}
      (isPropΠ λ _ → PT.isPropPropTrunc) []* cons* where

      P : FMSet X → Type _
      P xs = map f xs ≡ y ∷ ys → ∃[ (h , ts) ∈ (X × FMSet X) ] (xs ≡ h ∷ ts) × (f h ≡ y) × (map f ts ≡ ys)

      []* : map f [] ≡ y ∷ ys → _
      []* = Empty.rec ∘ ∷-[]-disjoint ∘ sym

      cons* : ∀ x {xs}
        → P xs
        → P (x ∷ xs)
      cons* x {xs} indH-xs p = PT.map {!indH-xs !} (indH-xs {! p!}) where
        _ : map f (x ∷ xs) ≡ y ∷ ys
        _ = p


  map-mere-fiber-∷ : ∀ {xs : FMSet X} {y} {ys}
    → (f : X → Y)
    → map f xs ≡ y ∷ ys
    → ∥ fiber f y × fiber (map f) ys ∥₁
  map-mere-fiber-∷ {X = X} {xs = xs} {y} {ys} f = elimProp {B = P}
    (isPropΠ (λ h → PT.isPropPropTrunc)) []* {! !} xs where

    P : FMSet X → Type _
    P xs = map f xs ≡ y ∷ ys → ∥ fiber f y × fiber (map f) ys ∥₁

    []* : map f [] ≡ y ∷ ys → _
    []* = Empty.rec ∘ ∷-[]-disjoint ∘ sym

    cons* : ∀ x {xs}
      → P xs
      → P (x ∷ xs)
    cons* x {xs} indH-xs p = {! p !} where
      _ : f x ∷ map f xs ≡ y ∷ ys
      _ = p

open module BagChain = FunctorChain FMSet map Unit (!_)

  renaming
    ( IteratedLimit to Lim
    ; ShiftedLimit to LimFMSet
    ; iterObj to UnorderedTree
    ; iterInit to !^_
    )

isSetLimFMSet : isSet LimFMSet
isSetLimFMSet = Limit.isOfHLevelChainLimit _ 2 (λ n → isSetFMSet)

isSetUnorderedTree : ∀ {n : ℕ} → isSet (UnorderedTree n)
isSetUnorderedTree {zero} = Unit.isSetUnit
isSetUnorderedTree {suc n} = isSetFMSet

open Limit.ChainLimit

LimFMSet≡ = Limit.isSet→ChainLimitPathExt BagChain.shifted λ k → isSetFMSet {X = UnorderedTree k}

unzipEls : FMSet Lim → ∀ n → FMSet (UnorderedTree n)
unzipEls = rec (isSetΠ (λ n → isSetFMSet)) (λ n → []) cons* {! !} where
  cons* : Lim
    → ((n : ℕ) → FMSet (UnorderedTree n))
    → ((n : ℕ) → FMSet (UnorderedTree n))
  cons* l f n = l .elements n ∷ f n

unzip : FMSet Lim → LimFMSet
unzip = rec isSetLimFMSet Lim[] _∷Lim_ ∷Lim-swap where
  Lim[] : LimFMSet
  Lim[] .elements n = []
  Lim[] .isChainLimit n = refl {x = []}

  _∷Lim_ : (l : Lim) → LimFMSet → LimFMSet
  (l ∷Lim ls) .elements n = l .elements n ∷ ls .elements n
  (l ∷Lim ls) .isChainLimit n = cong₂ _∷_ (l .isChainLimit n) (ls .isChainLimit n)

  infixr 8 _∷Lim_

  ∷Lim-swap : ∀ (x y : Lim) (b : LimFMSet)
    → (x ∷Lim y ∷Lim b) ≡ (y ∷Lim x ∷Lim b)
  ∷Lim-swap x y b = LimFMSet≡ λ n → comm (x .elements n) (y .elements n) (b .elements n)


hasTrace : (xs₀ : FMSet Unit) → (el : (n : ℕ) → FMSet (UnorderedTree n)) → Type _
hasTrace xs₀ el = ∀ n → map !_ (el n) ≡ xs₀

isPropHasTrace : ∀ {xs₀} {el} → isProp (hasTrace xs₀ el)
isPropHasTrace = isPropΠ λ n → isSetFMSet _ _

limitHasTrace : (lim : LimFMSet) → hasTrace (lim .elements 0) (lim .elements)
limitHasTrace (Limit.lim el islim) = go where
  go : hasTrace (el 0) el
  go zero = mapId (el 0)
  go (suc n) =
    map (!_)             (el (suc n))   ≡⟨⟩
    map (!_ ∘ !^ n)      (el (suc n))   ≡⟨ mapComp !_ (!^ n) _ ⟩
    map (!_) (map (!^ n) (el (suc n)))  ≡⟨ cong (map !_) (islim n) ⟩
    map (!_) (el n)                     ≡⟨ go n ⟩
    el 0 ∎

contrFiberFromHasTrace : ∀ (xs₀ : FMSet Unit) (lim : LimFMSet) → Type _
contrFiberFromHasTrace xs₀ lim = hasTrace xs₀ (lim .elements) → isContr (fiber unzip lim)

isEquivUnzip : isEquiv unzip
isEquivUnzip .equiv-proof shlim = elimProp {B = λ xs → ∀ lim → contrFiberFromHasTrace xs lim}
  (isPropΠ2 (λ _ _ → isPropIsContr)) []* cons*
  (shlim .elements 0) shlim (limitHasTrace shlim) where

  []* : (shlim : LimFMSet) → hasTrace [] (shlim .elements) → isContr (fiber unzip shlim)
  []* shlim tr = fibInh , contrFiber where
    all-[] : ∀ n → shlim .elements n ≡ []
    all-[] n = map-fiber-[] !_ (tr n)

    fibInh : fiber unzip shlim
    fibInh = [] , LimFMSet≡ (sym ∘ all-[])

    contrFiber : ∀ fib → ([] , _) ≡ fib
    contrFiber (xs , unzip-xs≡shlim) = Sigma.Σ≡Prop (λ _ → isSetLimFMSet _ _) []≡xs where
      []≡xs : [] ≡ xs
      []≡xs = elimProp {B = λ xs → unzip xs ≡ shlim → [] ≡ xs}
        (isPropΠ (λ _ → isSetFMSet _ _))
        (λ _ → refl) cons* xs unzip-xs≡shlim
        where

        cons* : ∀ x {xs}
          → (unzip xs ≡ shlim → [] ≡ xs)
          → unzip (x ∷ xs) ≡ shlim → [] ≡ x ∷ xs
        cons* x {xs} indH-xs p = Empty.rec $ ∷-[]-disjoint contra where
          contra : x .elements 0 ∷ unzip xs .elements 0 ≡ []
          contra =
            unzip (x ∷ xs) .elements 0 ≡⟨ cong (λ xs → xs .elements 0) p ⟩
            shlim .elements 0 ≡⟨ all-[] 0 ⟩
            [] ∎

  cons* : ∀ (⋆ : Unit) → {⋆s : FMSet Unit}
    → ((shlim : LimFMSet) → contrFiberFromHasTrace ⋆s shlim)
    → ((shlim : LimFMSet) → contrFiberFromHasTrace (⋆ ∷ ⋆s) shlim)
  cons* tt {⋆s} indH shlim tr = fibInh , {! !} where
    b : (n : ℕ) → FMSet $ UnorderedTree n
    b n = shlim .elements n

    all-cons : ∀ n → ∃[ (t , ts) ∈ (UnorderedTree n × FMSet (UnorderedTree n)) ] (b n ≡ t ∷ ts) × _ × (map !_ ts ≡ ⋆s)
    all-cons n = map-fiber-∷ {X = UnorderedTree n} isSetUnorderedTree !_ (b n) (tr n)

    foo : (n : ℕ) → _
    foo n = PT.rec {! !} (λ { ((t , ts) , split , _ , trace) → {! !} }) (all-cons n)

    _ = {! subst (Limit.IsChainLimit _)  !}

    hasTrace-tail : hasTrace ⋆s (shlim .elements)
    hasTrace-tail = {! !}

    all-cons-choice : ∀ n → Σ[ (t , ts) ∈ (UnorderedTree n × FMSet (UnorderedTree n)) ] (b n ≡ t ∷ ts) × (map !_ ts ≡ ⋆s)
    all-cons-choice n = {! !}

    conslim : LimFMSet
    conslim .elements n = all-cons-choice n .fst .snd
    conslim .isChainLimit n = {! (all-cons-choice n .snd .fst)  !}

    fibCenter : FMSet Lim
    fibCenter = h ∷ {! !} where
      h-elements : ∀ n → UnorderedTree n
      h-elements n = all-cons-choice n .fst .fst

      h : Lim
      h .elements = h-elements
      h .isChainLimit n = islim n where
        islim : ∀ n → (!^ n) (h-elements (suc n)) ≡ h-elements n
        islim zero = Unit.isPropUnit _ _
        islim (suc n) =
          (!^ suc n) (h-elements (suc (suc n))) ≡⟨⟩
          map (!^ n) (h-elements (suc (suc n))) ≡⟨ {! all-cons-choice n .snd .fst !} ⟩
          h-elements (suc n) ∎

      hs : FMSet Lim
      hs = indH shlim {! !} .fst .fst
  
    fibInh : fiber unzip shlim
    fibInh = Limit.lim (λ n → all-cons-choice n .fst .fst) (λ { n → {! !} }) ∷ {! !} , {! !}
