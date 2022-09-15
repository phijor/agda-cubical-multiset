module Multiset.Inductive.Limit where

open import Multiset.Prelude
open import Multiset.Util using (!_ ; isInjective)

open import Multiset.Inductive.Base as M
open import Multiset.Inductive.Properties as M
open import Multiset.Inductive.Logic as M

open import Multiset.Chains

open import Multiset.Omniscience using (LLPO)

open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Function using (_∘_)
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.HLevels

open import Cubical.Data.Unit as Unit using (Unit ; tt)
open import Cubical.Data.Empty as Empty
open import Cubical.Data.Sigma as Sigma
open import Cubical.Data.Sum as Sum using (_⊎_)
open import Cubical.Data.Nat.Base
open import Cubical.Data.Bool.Base as Bool
  using (Bool ; if_then_else_ ; true ; false)

open import Cubical.Relation.Nullary

open import Cubical.HITs.PropositionalTruncation as PT
  using
    ( ∥_∥₁
    ; ∣_∣₁
    )

open module BagChain = FunctorChain M map Unit (!_)

  renaming
    ( IteratedLimit to ωTree
    ; ShiftedLimit to shωTree
    ; iterObj to UnorderedTree
    ; iterInit to !^
    )

isSetωMTree : isSet shωTree
isSetωMTree = Limit.isOfHLevelChainLimit _ 2 (λ n → isSetM)

isSetUnorderedTree : ∀ {n} → isSet (UnorderedTree n)
isSetUnorderedTree {zero} = Unit.isSetUnit
isSetUnorderedTree {suc n} = isSetM

shiftedLimitPath : ∀ {shlim₁ shlim₂} → (∀ n → shlim₁ .shωTree.elements n ≡ shlim₂ .shωTree.elements n) → shlim₁ ≡ shlim₂
shiftedLimitPath = Limit.isSet→ChainLimitPathExt shifted (λ k → isSetM)

module _ {ℓ ℓ′ : Level} {A : Type ℓ} {B : A → Type ℓ′} where
  unzipDep : M ((x : A) → B x) → (x : A) → M (B x)
  unzipDep = M.rec (isSetΠ λ x → isSetM) ε* η* _⊕*_ unit* assoc* comm* where
    ε* : ∀ x → M (B x)
    ε* = λ _ → ε

    η* : ∀ f x → M (B x)
    η* f x = η (f x)

    _⊕*_ : ∀ f g x → M (B x)
    _⊕*_ f g x = f x ⊕ g x

    unit* : ∀ f → ε* ⊕* f ≡ f
    unit* f = funExt $ unit ∘ f

    assoc* : ∀ f g h
      → (f ⊕* (g ⊕* h)) ≡ ((f ⊕* g) ⊕* h)
    assoc* f g h = funExt λ x → assoc (f x) (g x) (h x)

    comm* : ∀ f g
      → f ⊕* g ≡ g ⊕* f
    comm* f g = funExt λ x → comm (f x) (g x)

module _ where
  open Limit
  open ChainLimit

  cut : (n : ℕ) → ωTree → UnorderedTree n
  cut n l = l .elements n

  unzip₁ : M ωTree → ∀ n → M (UnorderedTree n)
  unzip₁ xs = unzipDep (map elements xs)

  unzip₁-islim : (xs : M ωTree) → IsChainLimit BagChain.shifted (unzip₁ xs)
  unzip₁-islim = ind {P = λ xs → IsChainLimit shifted (unzip₁ xs)}
    (λ xs → isPropΠ λ n → isSetM _ _)
    (λ n → refl {x = ε}) singl* union* where

    singl* : (x : ωTree) → ∀ n → map (!^ n) (unzip₁ (η x) (suc n)) ≡ unzip₁ (η x) n
    singl* x n = cong η (x .isChainLimit n)
    
    union*
      : ∀ {xs ys : M ωTree}
      → IsChainLimit shifted (unzip₁ xs)
      → IsChainLimit shifted (unzip₁ ys)
      → IsChainLimit shifted (unzip₁ (xs ⊕ ys))
    union* indH-xs indH-ys n = cong₂ _⊕_ (indH-xs n) (indH-ys n)

unzip : M ωTree → shωTree
unzip xs .shωTree.elements = unzip₁ xs
unzip xs .shωTree.isChainLimit = unzip₁-islim xs

module _ {ℓ} {X : Type ℓ} where
  pair : X → X → M X
  pair x y = η x ⊕ η y

  ⟨_,_⟩≡_ : X → X → M X → Type _
  ⟨ x , y ⟩≡ zs = {! !}

  ⟨_,_⟩≡⟨_,_⟩ : (x y z w : X) → Type _
  ⟨ x , y ⟩≡⟨ z , w ⟩ = ∥ ((x ≡ z) × (y ≡ w)) ⊎ ((x ≡ w) × (y ≡ z)) ∥₁

  ⟨,⟩≡⟨,⟩→Path : ∀ {x y z w} → ⟨ x , y ⟩≡⟨ z , w ⟩ → pair x y ≡ pair z w
  ⟨,⟩≡⟨,⟩→Path {x} {y} {z} {w} = PT.rec (isSetM _ _) (Sum.elim left right) where
    left : ((x ≡ z) × (y ≡ w)) → pair x y ≡ pair z w
    left (p , q) = cong₂ pair p q

    right : ((x ≡ w) × (y ≡ z)) → pair x y ≡ pair z w
    right (p , q) = cong₂ pair p q ∙ comm _ _

  Path→⟨,⟩≡⟨,⟩ : ∀ {x y z w} → pair x y ≡ pair z w → ⟨ x , y ⟩≡⟨ z , w ⟩
  Path→⟨,⟩≡⟨,⟩ p = {! !}

Complete : Type _
Complete = {x₁ x₂ y₁ y₂ : ωTree}
  → (ys₁ ys₂ : ℕ → ωTree)
  → (p : ∀ n → pair (ys₁ n) (ys₂ n) ≡ pair y₁ y₂)
  → (q₁ : ∀ n → cut n x₁ ≡ cut n (ys₁ n))
  → (q₂ : ∀ n → cut n x₂ ≡ cut n (ys₂ n))
  → pair x₁ x₂ ≡ pair y₁ y₂

isPropComplete : isProp Complete
isPropComplete =
  isPropImplicitΠ2 λ _ _ → isPropImplicitΠ2 λ _ _ → isPropΠ5 λ _ _ _ _ _ → isSetM _ _

unzip-inj⇒complete : isInjective unzip → Complete
unzip-inj⇒complete inj {x₁} {x₂} {y₁} {y₂} ys₁ ys₂ p q₁ q₂ =
  inj (pair x₁ x₂) (pair y₁ y₂)
  (shiftedLimitPath goal) where

  goal : ∀ n → unzip₁ (pair x₁ x₂) n ≡ unzip₁ (pair y₁ y₂) n
  goal n =
    unzip₁ (pair x₁ x₂) n                 ≡⟨⟩
    pair (cut n x₁)      (cut n x₂)       ≡⟨ cong₂ pair (q₁ n) (q₂ n) ⟩
    pair (cut n $ ys₁ n) (cut n $ ys₂ n)  ≡⟨⟩
    unzip₁ (pair (ys₁ n) (ys₂ n)) n       ≡⟨ cong (λ xs → unzip₁ xs n) (p n) ⟩
    unzip₁ (pair y₁ y₂)           n       ∎

long : (n : ℕ) → UnorderedTree n
long zero = tt
long (suc n) = η (long n)

long-istree : ∀ n → !^ n (long (suc n)) ≡ long n
long-istree zero = refl {x = tt}
long-istree (suc n) = cong η (long-istree n)

long-tree : ωTree
long-tree .ωTree.elements = long
long-tree .ωTree.isChainLimit = long-istree

long? : (a : ℕ → Bool) → (n : ℕ) → UnorderedTree n
long? a zero = tt
long? a (suc n) =
  if (a 0)
    then ε
    else η (long? (a ∘ suc) n)

long?-istree : ∀ a n → !^ n (long? a (suc n)) ≡ long? a n
long?-istree a zero = refl {x = tt}
long?-istree a (suc n) with a 0
... | true = refl {x = ε}
... | false = cong η (long?-istree (a ∘ suc) n)

long?-tree : (a : ℕ → Bool) → ωTree
long?-tree a .ωTree.elements = long? a
long?-tree a .ωTree.isChainLimit = long?-istree a

sequence : (a : ℕ → Bool) (x y : ωTree) → ℕ → ωTree
sequence a x y with a 0
... | true = λ n → y
... | false = λ { 0 → x ; (suc n) → sequence (a ∘ suc) x y n }

unzip-complete⇒LLPO : Complete → LLPO
unzip-complete⇒LLPO complete a true? = PT.map {! !} (Path→⟨,⟩≡⟨,⟩ $ complete {! !} {! !} {! !} {! !} {! !}) where
  longs₁ : ℕ → ωTree
  longs₁ = sequence a long-tree (long?-tree a)

  longs₂ : ℕ → ωTree
  longs₂ = sequence a (long?-tree a) long-tree

-- unzip : M ωTree → ωMTree
-- unzip = M.rec isSetωMTree ε* η* union* unit* assoc* comm* where
--   open Limit
-- 
--   open ChainLimit
-- 
--   isSetM' : ∀ {X} → isSet' (M X)
--   isSetM' = isSet→isSet' isSetM
-- 
--   ε* : ωMTree
--   ε* = lim (λ _ → ε) (λ _ → refl {x = ε})
-- 
--   η* : ωTree → ωMTree
--   η* (lim elements isChainLimit) = lim
--     (λ n → η (elements n))
--     λ n → cong η (isChainLimit n)
-- 
--   union* : ωMTree → ωMTree → ωMTree
--   union* (lim e₁ islim₁) (lim e₂ islim₂) = lim
--     (λ n → e₁ n ⊕ e₂ n)
--     (λ n → cong₂ _⊕_ (islim₁ n) (islim₂ n))
-- 
--   unit* : ∀ t → union* ε* t ≡ t
--   unit* t = ChainLimitPathP _ (unit-ext , funExt λ n → isSetM' _ _ _ _) where
--     unit-ext : (λ n → ε ⊕ t .elements n) ≡ t .elements
--     unit-ext = funExt λ n → unit _
-- 
--   assoc* : ∀ a b c → union* a (union* b c) ≡ union* (union* a b) c
--   assoc* a b c = ChainLimitPathP _ (assoc-ext , funExt λ n → isSetM' _ _ _ _) where
--     assoc-ext : (λ n → _ ⊕ (_ ⊕ _)) ≡ (λ n → (_ ⊕ _) ⊕ _)
--     assoc-ext = funExt λ n → assoc _ _ _
-- 
--   comm* : ∀ a b → union* a b ≡ union* b a
--   comm* a b = ChainLimitPathP _ (comm-ext , funExt (λ n → isSetM' _ _ _ _)) where
--     comm-ext : (union* a b) .elements ≡ (union* b a) .elements
--     comm-ext = funExt λ n → comm _ _
-- 
-- open Limit.ChainLimit
-- 
-- module _ where
--   open Limit using (lim)
--   unzip-ε : unzip ε ≡ lim (λ _ → ε) _
--   unzip-ε = refl
-- 
--   unzip-η : ∀ {t : ωTree} → unzip (η t) ≡ Limit.lim (η ∘ t .elements) _
--   unzip-η = refl
-- 
-- hasTrace : (xs₀ : M Unit) → (el : (n : ℕ) → M (UnorderedTree n)) → Type _
-- hasTrace xs₀ el = ∀ n → M.map !_ (el n) ≡ xs₀
-- 
-- isPropHasTrace : ∀ {xs₀} {el} → isProp (hasTrace xs₀ el)
-- isPropHasTrace = isPropΠ λ n → isSetM _ _
-- 
-- limitHasTrace : (lim : ωMTree) → hasTrace (lim .elements 0) (lim .elements)
-- limitHasTrace (Limit.lim el islim) zero = M.mapId (el 0)
-- limitHasTrace (Limit.lim el islim) (suc n) =
--     M.map (!_)               (el (suc n))   ≡⟨⟩
--     M.map (!_ ∘ !^ n)        (el (suc n))   ≡⟨ mapComp !_ (!^ n) ⟩
--     M.map (!_) (M.map (!^ n) (el (suc n)))  ≡⟨ cong (M.map !_) (islim n) ⟩
--     M.map (!_) (el n)                       ≡⟨ limitHasTrace _ n ⟩
--     el 0 ∎
-- 
-- contrFiberFromHasTrace : ∀ (xs₀ : M Unit) (lim : ωMTree) → Type _
-- contrFiberFromHasTrace xs₀ lim = hasTrace xs₀ (lim .elements) → isContr (fiber unzip lim)
-- 
-- isEquivToωMTree : isEquiv (unzip)
-- isEquivToωMTree .equiv-proof lim =
--   M.ind {P = λ xs → (lim : ωMTree) → contrFiberFromHasTrace xs lim}
--     (λ xs → isPropΠ2 λ lim tr → isPropIsContr)
--     empty* singl* union*
--     (lim .elements 0) lim (limitHasTrace lim) where
-- 
--     open Limit using (isSet→ChainLimitPathExt)
-- 
--     LimInMPath = isSet→ChainLimitPathExt _ (λ n → isSetM)
--     LimInMPath′ = isSet→ChainLimitPathExt (BagChain.iterated)
--       ( λ { 0 → Unit.isSetUnit
--           ; (suc n) → isSetM
--           })
-- 
--     _ = {! Σ≡Prop (λ xs → isSetωMTree (unzip xs) _) !}
-- 
--     empty* : ∀ lim → hasTrace ε (lim .elements) → isContr (fiber unzip lim)
--     empty* lim tr = (ε , LimInMPath (sym ∘ all-empty)) , contrFiber where
--       all-empty : ∀ n → lim .elements n ≡ ε
--       all-empty n = map-ε (lim .elements n) (tr n)
-- 
--       contrFiber : ∀ y → (ε , _) ≡ y
--       contrFiber (ys , unzip-ys≡lim) = Σ≡Prop (λ ys → isSetωMTree (unzip ys) lim) ε≡ys where
--         ε≡ys : ε ≡ ys
--         ε≡ys = M.ind {P = λ ys → unzip ys ≡ lim → ε ≡ ys}
--           (λ ys → isPropΠ λ h → isSetM _ _)
--           (λ h → refl {x = ε}) singl* union* ys unzip-ys≡lim where
--             singl* : ∀ x → unzip (η x) ≡ lim → ε ≡ η x
--             singl* x h = Empty.elim $ η≢ε contra where
--               contra : η _ ≡ ε
--               contra =
--                 η _             ≡⟨ cong (λ l → l .elements 0) h ⟩
--                 lim .elements 0 ≡⟨ all-empty 0 ⟩
--                 ε ∎
-- 
--             union* : ∀ {xs₁ xs₂}
--               → (unzip xs₁ ≡ lim → ε ≡ xs₁)
--               → (unzip xs₂ ≡ lim → ε ≡ xs₂)
--               → (unzip (xs₁ ⊕ xs₂) ≡ lim → ε ≡ (xs₁ ⊕ xs₂))
--             union* {xs₁} {xs₂} indH-xs₁ indH-xs₂ h =
--               sym $ subst-ε⊕ε≡ε (sym $ indH-xs₁ unzip-xs₁≡lim) (sym $ indH-xs₂ unzip-xs₂≡lim) where
--               ⊕-empty : ∀ n → (unzip xs₁ .elements n) ⊕ (unzip xs₂ .elements n) ≡ ε
--               ⊕-empty n = cong (λ l → l .elements n) h ∙ all-empty n
-- 
--               unzip-xs₁-empty : ∀ n → unzip xs₁ .elements n ≡ ε
--               unzip-xs₁-empty n = no-zero-divisorsˡ (⊕-empty n)
-- 
--               unzip-xs₂-empty : ∀ n → unzip xs₂ .elements n ≡ ε
--               unzip-xs₂-empty n = no-zero-divisorsʳ (⊕-empty n)
-- 
--               unzip-xs₁≡lim : unzip xs₁ ≡ lim
--               unzip-xs₁≡lim = LimInMPath λ n → unzip-xs₁-empty n ∙ (sym $ all-empty n)
-- 
--               unzip-xs₂≡lim : unzip xs₂ ≡ lim
--               unzip-xs₂≡lim = LimInMPath λ n → unzip-xs₂-empty n ∙ (sym $ all-empty n)
-- 
--     singl* : ∀ (⋆ : Unit) lim → hasTrace (η ⋆) (lim .elements) → isContr (fiber unzip lim)
--     singl* tt lim tr = (η extracted-tree , LimInMPath (snd ∘ all-singl)) , contrFiber where
--       all-singl : ∀ n → isSingleton (lim .elements n)
--       all-singl n = map⁻¹-isSingleton (lim .elements n) (tt , sym (tr n))
-- 
--       islim-singletons′ : ∀ n → η (!^ n $ all-singl (suc n) .fst) ≡ η (all-singl n .fst)
--       islim-singletons′ n =
--         η (!^ n $ all-singl (suc n) .fst)         ≡⟨⟩
--         (!^ (suc n)) (η $ all-singl (suc n) .fst) ≡⟨ cong (!^ (suc n)) (all-singl (suc n) .snd) ⟩
--         (!^ (suc n)) (lim .elements (suc n))      ≡⟨ lim .isChainLimit n ⟩
--         lim .elements n                           ≡⟨ sym $ all-singl n .snd ⟩
--         η (all-singl n .fst) ∎
-- 
--       islim-singletons : ∀ n → !^ n (all-singl (suc n) .fst) ≡ all-singl n .fst
--       islim-singletons = η-injective isSetUnorderedTree ∘ islim-singletons′
-- 
--       extracted-tree : ωTree
--       extracted-tree = Limit.lim (fst ∘ all-singl) (islim-singletons)
-- 
--       contrFiber : ∀ y → (η extracted-tree , _) ≡ y
--       contrFiber (ys , unzip-ys≡lim) = Σ≡Prop (λ ys → isSetωMTree (unzip ys) lim) ηt≡ys where
--         all-singl-subst : ∀ {lim′} → lim′ ≡ lim → ∀ n → isSingleton (lim′ .elements n)
--         all-singl-subst {lim′} p = subst (λ lim′ → ∀ n → isSingleton (lim′ .elements n)) (sym p) all-singl
-- 
--         ηt≡ys : η extracted-tree ≡ ys
--         ηt≡ys = ind {P = λ ys → unzip ys ≡ lim → η extracted-tree ≡ ys} (λ ys → isPropΠ λ _ → isSetM _ _)
--           empty** singl** {! !} ys unzip-ys≡lim where
--             empty** : unzip ε ≡ lim → η extracted-tree ≡ ε
--             empty** h = Empty.rec (¬isSingleton-ε contra) where
--               isSingleton-unzip₀ : isSingleton (unzip ε .elements 0)
--               isSingleton-unzip₀ = all-singl-subst h 0
--               
--               contra : isSingleton ε
--               contra = subst (λ ys → isSingleton (ys .elements 0)) unzip-ε isSingleton-unzip₀
-- 
--             singl** : ∀ (x : ωTree) → unzip (η x) ≡ lim → η extracted-tree ≡ η x
--             singl** x h = cong η extracted-tree≡x where
--               extracted-tree≡x : extracted-tree ≡ x
--               extracted-tree≡x = LimInMPath′ λ n →
--                 extracted-tree .elements n ≡⟨⟩
--                 isSingletonElement (all-singl n) ≡⟨ sym $ cong (isSingletonElement) {! subst-filler (λ l → ∀ n → isSingleton (l .elements n)) (sym h) all-singl !} ⟩
--                 isSingletonElement (all-singl-subst h n) ≡⟨ η-injective _ $ isSingletonProof (all-singl-subst h n) ⟩
--                 x .elements n ∎
-- 
--     union* : ∀ {xs₀ ys₀}
--       → (∀ lim-xs → contrFiberFromHasTrace xs₀ lim-xs)
--       → (∀ lim-ys → contrFiberFromHasTrace ys₀ lim-ys)
--       → ∀ lim → contrFiberFromHasTrace (xs₀ ⊕ ys₀) lim
--     union* indH-xs indH-ys lim tr = ({! !} , {! !}) , {! !} where
--       all-unions : ∀ n → {! exitence of a split !}
--       all-unions = {! !}
--       
-- to-MωTree : ωMTree → M ωTree
-- to-MωTree lim =
--   M.elim {A = λ xs → (lim : ωMTree) → hasTrace xs (lim .elements) → M ωTree}
--     (λ xs → isSetΠ2 λ lim h → isSetM)
--     empty* {! !} {! !}
--     {! !} {! !} {! !}
--     (lim .elements 0) lim (limitHasTrace lim) where
-- 
--     empty* : ∀ lim → hasTrace ε (lim .elements) → M ωTree
--     empty* lim tr = ε
-- 
--     singl* : ∀ x lim → hasTrace (η x) (lim .elements) → M ωTree
--     singl* x lim tr = η (Limit.lim (λ n → {! !}) {! !}) where
--       all-singl : ∀ n → _
--       all-singl = {! map-η !}
--       
-- 
-- 
-- preservesLimits : BagChain.isLimitPreserving
-- preservesLimits = unzip , is-equiv where
--   center : ∀ t → fiber unzip t
--   center t = {! !} , {! !}
-- 
--   contrFiber : ∀ t → isContr (fiber unzip t)
--   contrFiber t = {! !} , {! !}
-- 
--   is-equiv : isEquiv unzip
--   is-equiv .equiv-proof = contrFiber
