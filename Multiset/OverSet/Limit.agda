module Multiset.OverSet.Limit where

open import Multiset.Prelude
open import Multiset.Util using (!_)
open import Multiset.Util.Path using (substDomain ; subst⁻Domain)

open import Multiset.OverSet.Base as FMSet
open import Multiset.OverSet.Properties as FMSet

open import Multiset.Chains

open import Cubical.Foundations.Function using (_∘_ ; flip ; ∘-assoc)
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Transport
open import Cubical.Foundations.Path
open import Cubical.Foundations.GroupoidLaws using (symDistr)

open import Cubical.HITs.SetQuotients as SQ hiding (effective)
open import Cubical.HITs.PropositionalTruncation as PT
  using (∥_∥₁ ; ∣_∣₁)

open import Cubical.Data.Sigma as Sigma
open import Cubical.Data.Nat as Nat
open import Cubical.Data.SumFin
open import Cubical.Data.Unit as Unit using (Unit ; tt)

open import Cubical.Relation.Binary.Base
  using
    (module BinaryRelation)

open module BagChain = FunctorChain FMSet map Unit !_
  renaming
    ( IteratedLimit to ωTree
    ; ShiftedLimit to ωBagOfTrees
    ; iterObj to UnorderedTree
    ; iterInit to !^
    ; iterated to bagChain
    )

open Iso
open Limit BagChain.iterated
open Limit.ChainLimit

isSetUnorderedTrees : ∀ n → isSet (UnorderedTree n)
isSetUnorderedTrees 0 = Unit.isSetUnit
isSetUnorderedTrees (suc n) = isSetFMSet

IsShiftedLimit = Limit.IsChainLimit BagChain.shifted

isSetShiftedLimit : isSet (Limit.ChainLimit BagChain.shifted)
isSetShiftedLimit = Limit.isOfHLevelChainLimit shifted 2 (λ n → isSetFMSet)

iteratedLimitPath : ∀ {lim₁ lim₂} → (∀ n → lim₁ .elements n ≡ lim₂ .elements n) → lim₁ ≡ lim₂
iteratedLimitPath = Limit.isSet→ChainLimitPathExt BagChain.iterated (λ k → isSetUnorderedTrees k)

shiftedLimitPath : ∀ {shlim₁ shlim₂} → (∀ n → shlim₁ .elements n ≡ shlim₂ .elements n) → shlim₁ ≡ shlim₂
shiftedLimitPath = Limit.isSet→ChainLimitPathExt shifted (λ k → isSetFMSet)

private
  Sym : ℕ → Type
  Sym n = Fin n ≃ Fin n

  isSetSym : ∀ n → isSet (Sym n)
  isSetSym n = isOfHLevel≃ 2 isSetFin isSetFin

  cut : (n : ℕ) → ωTree → UnorderedTree n
  cut n tree = tree .elements n

zip : FMSet ωTree → ωBagOfTrees
zip xs = Limit.lim trees islim where
  open ωTree

  trees : (n : ℕ) → FMSet (UnorderedTree n)
  trees n = FMSet.map (cut n) xs

  islim : ∀ n → !^ (suc n) (trees (suc n)) ≡ trees n
  islim n = FMSet.elimProp {P = λ xs → !^ (suc n) (map (cut (suc n)) xs) ≡ map (cut n) xs}
    (λ xs → isSetFMSet _ (FMSet.map (cut n) xs)) goal xs where
    module _ {sz} (xs : Fin sz → ωTree) where
      goal : map (!^ n) (map (cut (suc n)) (sz , [ xs ])) ≡ map (cut n) (sz , [ xs ])
      goal =
        map (!^ n) (map (cut (suc n)) (sz , [ xs ])) ≡⟨⟩
        (sz , ([ (!^ n) ∘ cut (suc n) ∘ xs ]))       ≡⟨ FMSetPathP (refl {x = sz}) (cong [_] (funExt λ k → xs k .isChainLimit n)) ⟩
        (sz , [ (cut n) ∘ xs ])                      ≡⟨⟩
        map (cut n) (sz , [ xs ])                    ∎

module _ where
  hasTrace : (xs₀ : FMSet Unit) → (el : (n : ℕ) → FMSet (UnorderedTree n)) → Type _
  hasTrace xs₀ el = ∀ n → FMSet.map !_ (el n) ≡ xs₀

  isPropHasTrace : ∀ {xs₀} {el} → isProp (hasTrace xs₀ el)
  isPropHasTrace = isPropΠ λ n → isSetFMSet _ _

  limitHasTrace : (lim : ωBagOfTrees) → hasTrace (lim .elements 0) (lim .elements)
  limitHasTrace (Limit.lim el islim) zero = mapId (el 0)
  limitHasTrace (Limit.lim el islim) (suc n) =
      map (!_)             (el (suc n))   ≡⟨⟩
      map (!_ ∘ !^ n)      (el (suc n))   ≡⟨ sym $ mapComp !_ (!^ n) (el (suc n)) ⟩
      map (!_) (map (!^ n) (el (suc n)))  ≡⟨ cong (map !_) (islim n) ⟩
      map (!_) (el n)                     ≡⟨ limitHasTrace (Limit.lim el islim) n ⟩
      el 0 ∎

  contrFiberFromHasTrace : ∀ (xs₀ : FMSet Unit) (lim : ωBagOfTrees) → Type _
  contrFiberFromHasTrace xs₀ lim′ = hasTrace xs₀ (lim′ .elements) → isContr (fiber zip lim′)

injZip-sizeAt : ∀ n xs ys → zip xs ≡ zip ys → xs .size ≡ ys .size
injZip-sizeAt n xs ys zip-p = cong (λ l → l .elements n .size) zip-p

injZip-sizeAtConst : ∀ n xs ys → (p : zip xs ≡ zip ys) → injZip-sizeAt 0 xs ys p ≡ injZip-sizeAt n xs ys p
injZip-sizeAtConst n xs ys p = isSetℕ _ _ _ _

InjZip : Type _
InjZip = ∀ xs ys → zip xs ≡ zip ys → xs ≡ ys

injZip : (xs ys : FMSet ωTree) → zip xs ≡ zip ys → xs ≡ ys
injZip xs ys zip-p = J
  ( λ sz (p : xs .size ≡ sz)
  → ∀ ys'
  → ((n : ℕ) → PathP (λ i → PVect (UnorderedTree n) (p i)) (FMSet.map (cut n) xs .members) (FMSet.map (cut n) (sz , ys') .members))
  → xs ≡ (sz , ys')
  )
  injZip-refl
  {y = ys .size}
  (injZip-sizeAt 0 xs ys zip-p)
  (ys .snd)
  zip-p-members
  where
    zip-p-members : ∀ n → PathP (λ i → PVect (UnorderedTree n) (injZip-sizeAt 0 xs ys zip-p i)) (map (cut n) xs .members) (map (cut n) ys .members)
    zip-p-members n =
      subst
        (λ p → PathP (λ i → PVect (UnorderedTree n) (p i)) (map (cut n) xs .members) (map (cut n) ys .members))
        (sym $ injZip-sizeAtConst n xs ys zip-p)
        (cong (λ l → l .elements n .snd) zip-p)

    injZip-refl : ∀ ys' → (∀ n → FMSet.map (cut n) xs .members ≡ map (cut n) (xs .size , ys') .members) → xs ≡ (xs .size , ys')
    injZip-refl = SQ.elimProp2
      {P = λ v w → (∀ n → map-members (cut n) v ≡ map-members (cut n) w) → (xs .size , v) ≡ (xs .size , w)}
      (λ _ _ → isPropΠ λ _ → isSetFMSet _ _) (λ v w q → ΣPathP (refl , goal v w q)) (xs .members) where
      module _ (v w : Fin (xs .size) → ωTree) (q : ∀ n → [ cut n ∘ v ] ≡ [ cut n ∘ w ]) where
        goal : [ v ] ≡ [ w ]
        goal = {! v !}

Complete : Type _
Complete = {x₁ x₂ y₁ y₂ : ωTree}
  → (ys₁ ys₂ : ℕ → ωTree)
  → (p : ∀ n → ys₁ n ∷ ys₂ n ∷ [] ≡ y₁ ∷ y₂ ∷ [])
  → (q₁ : ∀ n → cut n x₁ ≡ cut n (ys₁ n))
  → (q₂ : ∀ n → cut n x₂ ≡ cut n (ys₂ n))
  → x₁ ∷ x₂ ∷ [] ≡ y₁ ∷ y₂ ∷ []

inj⇒complete : InjZip → Complete
inj⇒complete inj {x₁} {x₂} {y₁} {y₂} ys₁ ys₂ p q₁ q₂ = inj _ _ goal where
  goal : zip (x₁ ∷ x₂ ∷ []) ≡ zip (y₁ ∷ y₂ ∷ [])
  goal = shiftedLimitPath λ n →
    zip (x₁ ∷ x₂ ∷ []) .elements n          ≡⟨⟩
    map (cut n) (x₁ ∷ x₂ ∷ [])              ≡⟨ {! !} ⟩
    (cut n x₁) ∷ (cut n x₂) ∷ []            ≡⟨ cong₂ (λ x y → x ∷ y ∷ []) (q₁ n) (q₂ n) ⟩
    (cut n $ ys₁ n) ∷ (cut n $ ys₂ n) ∷ []  ≡⟨ {! !} ⟩
    map (cut n) (ys₁ n ∷ ys₂ n ∷ [])        ≡⟨ cong (map (cut n)) (p n) ⟩
    map (cut n) (y₁ ∷ y₂ ∷ [])              ≡⟨⟩
    zip (y₁ ∷ y₂ ∷ []) .elements n ∎

{-
module _ (base : ωBagOfTrees) where
  open import Multiset.AxiomChoice using (elimCollProp ; hasChoice ; [_⇒-d_]/_ ; θ-d)

  open import Cubical.Foundations.Univalence

  sizeAt : ℕ → ℕ
  sizeAt n = base .elements n .size

  sizeAtConstSuc : ∀ n → sizeAt (suc n) ≡ sizeAt n
  sizeAtConstSuc n = cong size (base .isChainLimit n)

  sz₀ : ℕ
  sz₀ = base .elements 0 .size

  A = ℕ

  A' = ℕ × ℕ

  B : A → Type _
  B = λ n → Fin (sizeAt n) → UnorderedTree n

  B' : A' → Type _
  B' (sz , step) = Fin sz → UnorderedTree step

  R : ∀ n → B n → B n → Type _
  R n = SymmetricAction {X = UnorderedTree n} (sizeAt n)

  R' : ∀ a' → B' a' → B' a' → Type _
  R' (sz , step) = SymmetricAction {X = UnorderedTree step} sz

  RProp : ∀ n → BinaryRelation.isPropValued (R n)
  RProp = FMSet.isPropValued-∼ ∘ sizeAt

  RProp' : ∀ a' → BinaryRelation.isPropValued (R' a')
  RProp' = FMSet.isPropValued-∼ ∘ fst

  REquivRel : ∀ n → BinaryRelation.isEquivRel (R n)
  REquivRel = isEquivRel-∼ ∘ sizeAt

  REquivRel' : ∀ n → BinaryRelation.isEquivRel (R' n)
  REquivRel' = isEquivRel-∼ ∘ fst

  Reffective : ∀ n → (v w : B n) → [ v ] ≡ [ w ] → R n v w
  Reffective n v w = FMSet.effective (sizeAt n) {v = v} {w = w}

  Reffective' : ∀ a' → (v w : B' a') → [ v ] ≡ [ w ] → R' a' v w
  Reffective' (n , _) w v = FMSet.effective n

  C : (∀ n → B n / R n) → Type _
  C members = ∀ (islim : IsShiftedLimit (λ n → sizeAt n , members n))
    → isContr (fiber zip (Limit.lim (λ n → sizeAt n , members n) islim))

  C' : ℕ → (∀ a' → B' a' / R' a') → Type _
  C' sz members = (islim : IsShiftedLimit (λ n → sz , members (sz , n)))
    → isContr (fiber zip (Limit.lim (λ n → sz , members (sz , n)) islim))

  isPropC : ∀ members → isProp (C members)
  isPropC members = isPropΠ λ islim → isPropIsContr

  Motive : _ → Type _
  Motive = C

  postulate
    θInv-d : (∀ n → B n / R n) → [ A ⇒-d B ]/ R

    sectionθ-d : section (θ-d R) θInv-d


  module Choice
    (sz : ℕ)
    (vs : (n : ℕ) → Fin sz → UnorderedTree n)
    (ws : (n : ℕ) → Fin sz → UnorderedTree n)
    where

    isPropP : ∀ n σ → isProp (PathP (λ i → ua σ i → UnorderedTree n) (vs n) (ws n))
    isPropP n σ p q = isSet→SquareP (λ i j → isSetΠ λ _ → isSetUnorderedTrees n) p q refl refl

    postulate
      choseFamOfPermutations : hasChoice
        {A = ℕ}
        {B = λ _ → Sym sz}
        {P = λ n σ → PathP (λ i → ua σ i → UnorderedTree n) (vs n) (ws n)}
        isSetℕ (λ _ → isSetSym _) isPropP

    _ : (∀ n → vs n ∼ ws n)
      → ∃[ σn ∈ (ℕ → Sym sz) ] ∀ n → PathP (λ i → ua (σn n) i → UnorderedTree n) (vs n) (ws n)
    _ = choseFamOfPermutations

  choice : ((g : (a : A) → B a) → C ([_] ∘ g))
    → (f : (a : A) → B a / R a)
    → C f
  choice = elimCollProp {A = A} B R RProp REquivRel θInv-d sectionθ-d C isPropC

  -- choice' : ((g : (a : A') → B' a) → C' 0 ([_] ∘ g))
  --   → (f : (a : A') → B' a / R' a)
  --   → C' 0 f
  -- choice' = elimCollProp {A = A'} B' R' {! !} {! !} {! !} {! !} (C' 0) {! !}

  inhFibers : ∥ fiber zip base ∥₁
  inhFibers = elimCollProp {A = ℕ × ℕ} B' R' RProp' REquivRel' {! !} _ {! !} {! !} {! !} {! !}

  contrFibers : isContr (fiber zip base)
  contrFibers = choice g f (base .isChainLimit) where
    g : (trees : (n : ℕ) → Fin (sizeAt n) → UnorderedTree n) → C ([_] ∘ trees)
    g trees islim = goal where
      constSizeSuc : ∀ n → sizeAt (suc n) ≡ sizeAt n
      constSizeSuc n = cong size $ islim n

      constSizeTo0 : ∀ n → sizeAt n ≡ sizeAt 0
      constSizeTo0 zero = refl
      constSizeTo0 (suc n) = constSizeSuc n ∙ constSizeTo0 n

      permSuc : ∀ n → Fin (sizeAt n) ≃ Fin (sizeAt (suc n))
      permSuc n = substEquiv Fin (sym $ constSizeSuc n)

      permFrom0 : ∀ n → Fin (sizeAt 0) ≃ Fin (sizeAt n)
      permFrom0 zero = idEquiv (Fin (sizeAt 0))
      permFrom0 (suc n) = permFrom0 n ∙ₑ permSuc n

      permFrom0′ : ∀ n → Fin (sizeAt 0) ≃ Fin (sizeAt n)
      permFrom0′ n = substEquiv Fin (sym (constSizeTo0 n))


      permFrom0≡permFrom0′ : ∀ n → permFrom0 n ≡ permFrom0′ n
      permFrom0≡permFrom0′ zero = equivEq (funExt $ sym ∘ transportRefl)
      permFrom0≡permFrom0′ (suc n) = equivEq
        (funExt λ k →
          (equivFun (permSuc n) $ equivFun (permFrom0 n) $ k) ≡⟨ (λ i → equivFun (permSuc n) $ equivFun (permFrom0≡permFrom0′ n i) k) ⟩
          (equivFun (permSuc n) $ equivFun (permFrom0′ n) $ k) ≡⟨⟩
          (subst Fin (sym $ constSizeSuc n) $ subst Fin (sym (constSizeTo0 n)) $ k) ≡⟨ sym (substComposite Fin (sym (constSizeTo0 n)) (sym (constSizeSuc n)) k) ⟩
          subst Fin (sym (constSizeTo0 n) ∙ sym (constSizeSuc n)) k ≡⟨ (λ i → (subst Fin) (symDistr (constSizeSuc n) (constSizeTo0 n) (~ i)) k) ⟩
          subst Fin (sym (constSizeSuc n ∙ constSizeTo0 n)) k ∎
        )


      trees′ : ∀ n → Fin (sizeAt 0) → UnorderedTree n
      trees′ n = trees n ∘ equivFun (permFrom0 n)

      -- Extract paths between all members of the limit from the limit-property
      step₁ : ∀ n
        → PathP (λ i → PVect (UnorderedTree n) (islim n i .size))
          [ !^ n ∘ trees (suc n) ]
          [ trees n ]
      step₁ n = cong snd (islim n)

      step₂ : ∀ n → subst (PVect (UnorderedTree n)) (constSizeSuc n) [ !^ n ∘ trees (suc n) ] ≡ [ trees n ]
      step₂ n = fromPathP $ step₁ n

      step₄ : ∀ n →
        subst (λ k → Fin k → UnorderedTree n) (constSizeSuc n) (!^ n ∘ trees (suc n))
        ≡ !^ n ∘ trees (suc n) ∘ equivFun (permSuc n)
      step₄ n = substDomain {B = Fin} {C = UnorderedTree n} (!^ n ∘ trees (suc n)) (constSizeSuc n)

      step₃ : ∀ n → [ !^ n ∘ trees (suc n) ∘ equivFun (permSuc n) ] ≡ [ trees n ]
      step₃ n = (sym $ cong [_] $ step₄ n) ∙ step₂ n

      step₃′ : ∀ n → [ !^ n ∘ trees′ (suc n) ] ≡ [ trees′ n ]
      step₃′ n =
        [ !^ n ∘ trees′ (suc n) ] ≡⟨⟩
        [ !^ n ∘ trees (suc n) ∘ equivFun (permSuc n) ∘ equivFun (permFrom0 n) ] ≡⟨ isPermutationInvariant (permFrom0 n) (step₃ n) ⟩
        [ trees n ∘ equivFun (permFrom0 n) ] ≡⟨⟩
        [ trees′ n ] ∎

      relFrom0 : ∀ n → SymmetricAction (sizeAt 0) (!^ n ∘ trees′ (suc n)) (trees′ n)
      relFrom0 n = Reffective' (sizeAt 0 , n) (!^ n ∘ trees′ (suc n)) (trees′ n) (step₃′ n)

      allPermsFrom0 :
        ∃[ σs ∈ (ℕ → Sym (sizeAt 0)) ]
          ∀ n → PathP (λ i → ua (σs n) i → UnorderedTree n) (!^ n ∘ trees′ (suc n)) (trees′ n)
      allPermsFrom0 = Choice.choseFamOfPermutations (sizeAt 0) (λ n → !^ n ∘ trees′ (suc n)) trees′ relFrom0
            
      islim′ : Limit.IsChainLimit shifted (λ n → sizeAt 0 , [ trees′ n ])
      islim′ n = ΣPathP (refl {x = sizeAt 0} , step₃′ n)

      lim′ : _
      lim′ = Limit.lim (λ n → sizeAt 0 , [ trees′ n ]) islim′

      goal′ : isContr (fiber zip lim′)
      goal′ = PT.rec {P = isContr (fiber zip lim′)}
        isPropIsContr (λ { (σs , p) → contr-proof σs p }) allPermsFrom0 where
        module _ (σs : ℕ → Sym (sizeAt 0)) (p : ∀ n → PathP (λ i → ua (σs n) i → UnorderedTree n) _ _) where

          permutedIndicesEquiv : (n : ℕ) → Sym (sizeAt 0)
          permutedIndicesEquiv zero = idEquiv _
          permutedIndicesEquiv (suc n) = permutedIndicesEquiv n ∙ₑ invEquiv (σs n)

          permutedIndices : (n : ℕ) → Fin (sizeAt 0) → Fin (sizeAt 0)
          permutedIndices n = equivFun $ permutedIndicesEquiv n

          permutedElements : ∀ n k → UnorderedTree n
          permutedElements n k = trees′ n (permutedIndices n k)

          permutedElementsPath : (n : ℕ) → [ permutedElements n ] ≡ [ trees′ n ]
          permutedElementsPath n = FMSet.isPermutationInvariantˡ (trees′ n) (permutedIndicesEquiv n)

          p' : ∀ n → (k : Fin (sizeAt 0)) → (!^ n $ trees′ (suc n) k) ≡ trees′ n (equivFun (σs n) k)
          p' n = ua→⁻ (p n)

          isLimPermuted : ∀ (k : Fin (sizeAt 0)) n → !^ n (permutedElements (suc n) k) ≡ permutedElements n k
          isLimPermuted k n =
            !^ n (permutedElements (suc n) k) ≡⟨⟩
            !^ n (trees′ (suc n) $ invEq (σs n) $ permutedIndices n k) ≡⟨ p' n (invEq (σs n) (permutedIndices n k)) ⟩
            (trees′ n $ equivFun (σs n) $ invEq (σs n) $ permutedIndices n k) ≡⟨ cong (trees′ n) (secEq (σs n) _) ⟩
            permutedElements n k ∎

          centerMembers : PVect ωTree (sizeAt 0)
          centerMembers = [ (λ { k → Limit.lim (λ n → permutedElements n k) (isLimPermuted k) }) ]

          center : FMSet ωTree
          center = sizeAt 0 , centerMembers

          in-fiber : zip center ≡ lim′
          in-fiber = shiftedLimitPath goal where
            goal : ∀ n → zip center .elements n ≡ lim′ .elements n
            goal n =
              zip center .elements n     ≡⟨⟩
              map (cut n) center                  ≡⟨⟩
              (sizeAt 0 , [ permutedElements n ]) ≡⟨ FMSetPathP refl (permutedElementsPath n) ⟩
              lim′ .elements n ∎

          membersConsSizeContraction : (xs : PVect ωTree (sizeAt 0)) → zip (sizeAt 0 , xs) ≡ lim′ → centerMembers ≡ xs
          membersConsSizeContraction = SQ.elimProp {P = λ xs → ∀ _ → centerMembers ≡ xs}
            (λ xs → isPropΠ λ _ → squash/ centerMembers xs) on-rep
            where module _ (rep : Fin (sizeAt 0) → ωTree) (rep-in-fiber : zip ⟅ [ rep ] ⟆ ≡ lim′) where

              inFiberAt : (n : ℕ) → ⟅ [ cut n ∘ rep ] ⟆ ≡ ⟅ [ trees′ n ] ⟆
              inFiberAt n = cong (λ l → l .elements n) rep-in-fiber

              _ = λ (n : ℕ) → {! cong members (inFiberAt n)!}

              trees″ : _
              trees″ = λ (n : ℕ) → trees′ n ∘ subst Fin (cong size (inFiberAt n))

              cutRel : ∀ n → (cut n ∘ rep) ∼ (trees″ n)
              cutRel n = FMSet.effectiveDep (cong size $ inFiberAt n) (cut n ∘ rep) (trees′ n) (cong members (inFiberAt n))

              cutPerms : ∃[ τs ∈ (ℕ → Sym (sizeAt 0)) ] ∀ n → PathP (λ i → ua (τs n) i → UnorderedTree n) (cut n ∘ rep) (trees″ n)
              cutPerms = Choice.choseFamOfPermutations (sizeAt 0) (λ n → cut n ∘ rep) _ cutRel

              module _ (τs : ℕ → Sym (sizeAt 0)) (ps : ∀ n k → cut n (rep k) ≡ (trees″ n (equivFun (τs n) k))) where
                σ : Sym (sizeAt 0)
                σ = {! !}

                rel : ∀ k → Limit.lim (λ n → permutedElements n k) (isLimPermuted k) ≡ rep (equivFun σ k)
                rel k = iteratedLimitPath λ n →
                  permutedElements n k ≡⟨⟩
                  (trees′ n $ permutedIndices n k) ≡⟨ {! permutedIndices (suc n) !} ⟩
                  (trees′ n $ subst Fin (cong size (inFiberAt n)) $ equivFun (τs n) $ equivFun σ k) ≡⟨⟩
                  (trees″ n                                       $ equivFun (τs n) $ equivFun σ k) ≡⟨ sym $ ps n (equivFun σ k) ⟩
                  cut n (rep (equivFun σ k)) ∎

                  -- Q : centerMembers ≡ [ rep ]
                  -- Q = FMSet.eq/∼ {! !}

              on-rep : [ (λ k → Limit.lim (λ n → permutedElements n k) (isLimPermuted k)) ] ≡ [ rep ]
              -- on-rep = eq/∼ $ PT.map (λ { (τs , pn) → {! !} , ua→ {! !} }) cutPerms
              -- on-rep = eq/∼ $ PT.rec {P = _ ∼ rep} PT.isPropPropTrunc (λ { (τs , pn) → {! !} }) cutPerms
              on-rep = PT.rec {P = centerMembers ≡ [ rep ]} (squash/ centerMembers [ rep ]) (λ { (τs , pn) → {! !} }) cutPerms

          contraction : (ys : FMSet ωTree) → zip ys ≡ lim′ → center ≡ ys
          contraction (sz , trees) trees-in-fiber = FMSetPathP sizePath membersPathP where
            sizePath : sizeAt 0 ≡ sz
            sizePath = sym (cong (λ l → l .elements 0 .size) trees-in-fiber)
              -- sz                                          ≡⟨⟩
              -- map (cut 0) (sz , trees) .size              ≡⟨⟩
              -- zip (sz , trees) .elements 0 .size ≡⟨ cong (λ l → l .elements 0 .size) trees-in-fiber ⟩
              -- lim′ .elements 0 .size                      ≡⟨⟩
              -- sizeAt 0 ∎
              --
            membersPathP : PathP (λ i → PVect ωTree (sizePath i)) centerMembers trees
            membersPathP = J {x = sizeAt 0} P membersConsSizeContraction {y = sz} sizePath trees trees-in-fiber where
              P : (sz : ℕ) → (p : sizeAt 0 ≡ sz) → Type _
              P sz p = (xs : PVect ωTree sz) → (zip (sz , xs) ≡ lim′) → PathP (λ i → PVect ωTree (p i)) centerMembers xs

          contr-proof : isContr (fiber zip lim′)
          contr-proof =
            (center , in-fiber) ,
            λ { (ys , ys-in-fiber) →
              Σ≡Prop (λ ys → isSetShiftedLimit (zip ys) lim′) (contraction ys ys-in-fiber)
            }

      lim′≡lim : lim′ ≡ Limit.lim (λ n → sizeAt n , [ trees n ]) islim
      lim′≡lim = shiftedLimitPath
        λ { n →
            (sizeAt 0 , [ trees n ∘ (equivFun $ permFrom0  n) ]) ≡⟨ cong (λ σ → sizeAt 0 , [ trees n ∘ σ ]) (lem₁ n) ⟩
            (sizeAt 0 , [ trees n ∘ (equivFun $ permFrom0′ n) ]) ≡⟨ sym (lem₂ n) ⟩
            (sizeAt n , [ trees n ]) ∎
          }
        where module _ (n : ℕ) where
          lem₁ : equivFun (permFrom0 n) ≡ equivFun (permFrom0′ n)
          lem₁ = cong equivFun (permFrom0≡permFrom0′ n)

          lem₂ : (sizeAt n , [ trees n ]) ≡ (sizeAt 0 , [ trees n ∘ (equivFun $ permFrom0′ n) ])
          lem₂ = FMSetPathP (constSizeTo0 n) (toPathP (cong [_] (substDomain {B = Fin} {C = UnorderedTree n} (trees n) (constSizeTo0 n))))

      goal : isContr (fiber zip (Limit.lim (λ n → sizeAt n , [ trees n ]) islim))
      goal = subst (isContr ∘ (fiber zip)) lim′≡lim goal′

    f : (n : ℕ) → B n / R n
    f n = base .elements n .snd
-}

isEquiv-zip : isEquiv zip
isEquiv-zip .equiv-proof base = {! !}

preservesLimits : BagChain.isLimitPreserving
preservesLimits = zip , isEquiv-zip
