module Multiset.Inductive.Limit where

open import Multiset.Prelude
open import Multiset.Util using (!_ ; isInjective ; isSurjective)

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
open import Cubical.Data.Sum as Sum using (_⊎_ ; inl ; inr)
open import Cubical.Data.Nat.Base
open import Cubical.Data.Bool.Base as Bool
  using (Bool ; if_then_else_ ; true ; false ; _and_ ; not)

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

limitPath : ∀ {lim₁ lim₂} → (∀ n → lim₁ .ωTree.elements n ≡ lim₂ .ωTree.elements n) → lim₁ ≡ lim₂
limitPath = Limit.isSet→ChainLimitPathExt iterated (λ k → isSetUnorderedTree {k})

shiftedLimitPath : ∀ {shlim₁ shlim₂} → (∀ n → shlim₁ .shωTree.elements n ≡ shlim₂ .shωTree.elements n) → shlim₁ ≡ shlim₂
shiftedLimitPath = Limit.isSet→ChainLimitPathExt shifted (λ k → isSetM)

module _ {ℓ ℓ′ : Level} {A : Type ℓ} {B : A → Type ℓ′} where
  zipDep : M ((x : A) → B x) → (x : A) → M (B x)
  zipDep = M.rec (isSetΠ λ x → isSetM) ε* η* _⊕*_ unit* assoc* comm* where
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

  zip₁ : M ωTree → ∀ n → M (UnorderedTree n)
  zip₁ xs = zipDep (map elements xs)

  zip₁-islim : (xs : M ωTree) → IsChainLimit BagChain.shifted (zip₁ xs)
  zip₁-islim = ind {P = λ xs → IsChainLimit shifted (zip₁ xs)}
    (λ xs → isPropΠ λ n → isSetM _ _)
    empty* singl* union* where

    empty* : ∀ n → ε ≡ ε
    empty* _ = refl

    singl* : (x : ωTree) → ∀ n → map (!^ n) (zip₁ (η x) (suc n)) ≡ zip₁ (η x) n
    singl* x n = cong η (x .isChainLimit n)
    
    union*
      : ∀ {xs ys : M ωTree}
      → IsChainLimit shifted (zip₁ xs)
      → IsChainLimit shifted (zip₁ ys)
      → IsChainLimit shifted (zip₁ (xs ⊕ ys))
    union* indH-xs indH-ys n = cong₂ _⊕_ (indH-xs n) (indH-ys n)

zip : M ωTree → shωTree
zip xs .shωTree.elements = zip₁ xs
zip xs .shωTree.isChainLimit = zip₁-islim xs

isSurjectiveZip : isSurjective zip
isSurjectiveZip sh = unzipped , unzipped-proof where
  unzipped : M ωTree
  unzipped = {! !}

  unzipped-proof : zip unzipped ≡ sh
  unzipped-proof = {! !}

infixr 6 _⊎₁_
_⊎₁_ : ∀ {ℓ ℓ'} → (A : Type ℓ) → (B : Type ℓ') → Type (ℓ-max ℓ ℓ')
A ⊎₁ B = ∥ A ⊎ B ∥₁

module _ {ℓ} {X : Type ℓ} where
  ⟅_,_⟆ : X → X → M X
  ⟅ x , y ⟆ = η x ⊕ η y

  ⟅_,_⟆≡⟅_,_⟆ : (x y z w : X) → Type _
  ⟅ x , y ⟆≡⟅ z , w ⟆ = ∥ ((x ≡ z) × (y ≡ w)) ⊎ ((x ≡ w) × (y ≡ z)) ∥₁

  ⟅,⟆-comm : ∀ x y → ⟅ x , y ⟆ ≡ ⟅ y , x ⟆
  ⟅,⟆-comm x y = comm (η x) (η y)

diag : (ℕ → ωTree) → (n : ℕ) → UnorderedTree n
diag z n = cut n (z n)

Complete : Type _
Complete = {x y₁ y₂ : ωTree}
  → (ys : ℕ → ωTree)
  → (p : ∀ n → (ys n ≡ y₁) ⊎ (ys n ≡ y₂))
  → (q : ∀ n → cut n x ≡ diag ys n)
  → (x ≡ y₁) ⊎₁ (x ≡ y₂)

isPropComplete : isProp Complete
isPropComplete =
  isPropImplicitΠ2 λ _ _ → isPropImplicitΠ λ _ → isPropΠ3 λ _ _ _ → PT.isPropPropTrunc

open ωTree using (elements) renaming (isChainLimit to isωTree)

zip-inj⇒complete : isInjective zip → Complete
zip-inj⇒complete inj {x} {y₁} {y₂} ys p q = goal where

  ysᶜ : ℕ → ωTree
  ysᶜ n = Sum.elim (λ ysₙ≡y₁ → y₂) (λ ysₙ≡y₂ → y₁) (p n)

  pᶜ : ∀ n → (ysᶜ n ≡ y₂) ⊎ (ysᶜ n ≡ y₁)
  pᶜ n = Sum.elim inr inl (p n)

  p∧pᶜ : ∀ n → ⟅ ys n , ysᶜ n ⟆ ≡ ⟅ y₁ , y₂ ⟆
  p∧pᶜ n with p n
  ... | inl ysₙ≡y₁ = cong ⟅_, y₂ ⟆ ysₙ≡y₁
  ... | inr ysₙ≡y₂ = cong ⟅_, y₁ ⟆ ysₙ≡y₂ ∙ ⟅,⟆-comm y₂ y₁

  diag-ysᶜ-islim-alternating : ∀ {n} {a b : ωTree}
    → (ys n ≡ a)
    → (ys (suc n) ≡ b)
    → !^ n (cut (suc n) a) ≡ cut n b
  diag-ysᶜ-islim-alternating {n = n} {a} {b} ysₙ≡a ysₙ₊₁≡b =
    !^ n (cut (suc n) a)   ≡⟨ a .isωTree n ⟩
    cut n a                ≡⟨ cong (cut n) (sym ysₙ≡a) ⟩
    diag ys n              ≡⟨ sym (q n) ⟩
    cut n x                ≡⟨ sym (x .isωTree n) ⟩
    !^ n (cut (suc n) x)   ≡⟨ cong (!^ n) (q (suc n)) ⟩
    !^ n (diag ys (suc n)) ≡⟨ cong (!^ n ∘ cut (suc n)) ysₙ₊₁≡b ⟩
    !^ n (cut (suc n) b)   ≡⟨ b .isωTree n ⟩
    cut n b ∎

  diag-ysᶜ-islim : ∀ n → !^ n (diag ysᶜ (suc n)) ≡ diag ysᶜ n
  diag-ysᶜ-islim n with (p (suc n)) | (p n)
  ... | inl ysₙ₊₁≡y₁ | inl ysₙ≡y₁ = y₂ .isωTree n
  ... | inl ysₙ₊₁≡y₁ | inr ysₙ≡y₂ = diag-ysᶜ-islim-alternating ysₙ≡y₂ ysₙ₊₁≡y₁
  ... | inr ysₙ₊₁≡y₂ | inl ysₙ≡y₁ = diag-ysᶜ-islim-alternating ysₙ≡y₁ ysₙ₊₁≡y₂
  ... | inr ysₙ₊₁≡y₂ | inr ysₙ≡y₂ = y₁ .isωTree n

  xᶜ : ωTree
  xᶜ .ωTree.elements = diag ysᶜ
  xᶜ .ωTree.isChainLimit = diag-ysᶜ-islim

  qᶜ : ∀ n → cut n xᶜ ≡ diag ysᶜ n
  qᶜ n with p n
  ... | inl _ = refl
  ... | inr _ = refl

  zip-diags-pair-path : zip ⟅ x , xᶜ ⟆ ≡ zip ⟅ y₁ , y₂ ⟆
  zip-diags-pair-path = shiftedLimitPath λ n →
    zip₁ ⟅ x , xᶜ ⟆ n ≡⟨⟩
    ⟅ cut n x , cut n xᶜ ⟆ ≡⟨ cong₂ ⟅_,_⟆ (q n) (qᶜ n) ⟩
    ⟅ diag ys n , diag ysᶜ n ⟆ ≡⟨⟩
    zip₁ ⟅ ys n , ysᶜ n ⟆ n ≡⟨ cong (λ z → zip₁ z n) (p∧pᶜ n) ⟩
    zip₁ ⟅ y₁   , y₂    ⟆ n ∎

  diags-pair-path : ⟅ x , xᶜ ⟆ ≡ ⟅ y₁ , y₂ ⟆
  diags-pair-path = inj ⟅ x , xᶜ ⟆ ⟅ y₁ , y₂ ⟆ zip-diags-pair-path

  goal : ∥ (x ≡ y₁) ⊎ (x ≡ y₂) ∥₁
  goal = PT.rec PT.isPropPropTrunc (Sum.elim (PT.map inl) (PT.map inr)) x∈⟅y₁,y₂⟆ where
    x∈⟅x,xᶜ⟆ : x ∈ ⟅ x , xᶜ ⟆
    x∈⟅x,xᶜ⟆ = ∣ inl ∣ refl {x = x} ∣₁ ∣₁

    x∈⟅y₁,y₂⟆ : x ∈ ⟅ y₁ , y₂ ⟆
    x∈⟅y₁,y₂⟆ = subst (x ∈_) diags-pair-path x∈⟅x,xᶜ⟆

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

sequence′ : (a : ℕ → Bool) (x y : ωTree) → (even? : Bool) → ℕ → ωTree
sequence′ a x y even? with (a 0) and even?
... | true = λ n → y
... | false = λ { 0 → x ; (suc n) → sequence′ (a ∘ suc) x y (not even?) n }

sequence′-either : (a : ℕ → Bool) (x y : ωTree) (even? : Bool)
  → ∀ n → (sequence′ a x y even? n ≡ x) ⊎ (sequence′ a x y even? n ≡ y)
sequence′-either a x y even? with (a 0 and even?)
... | true = λ n → inr (refl {x = y})
... | false =
  λ { zero → inl (refl {x = x})
    ; (suc n) → sequence′-either (a ∘ suc) x y (not even?) n
    }

sequence : (a : ℕ → Bool) (x y : ωTree) → ℕ → ωTree
sequence a x y = sequence′ a x y true

sequence-either : (a : ℕ → Bool) (x y : ωTree)
  → ∀ n → (sequence a x y n ≡ x) ⊎ (sequence a x y n ≡ y)
sequence-either a x y = sequence′-either a x y true

sequence-odd : (a : ℕ → Bool) (x y : ωTree)
  → ∀ n → isOddT n → sequence a x y n ≡ x
sequence-odd a x y with a 0
... | true = {! !}
... | false = {! !}

zip-complete⇒LLPO : Complete → LLPO
zip-complete⇒LLPO complete a true? = PT.map (Sum.map-⊎ {! !} ?)
  (complete {x = longs-diag} {y₁ = long-tree} {y₂ = long?-tree a} longs (sequence-either a _ _) λ n → refl {x = diag longs n})
  where

  longs : ℕ → ωTree
  longs = sequence a long-tree (long?-tree a)

  longs-diag : ωTree
  longs-diag .elements = diag longs
  longs-diag .isωTree n = {! !}

  case₁ : longs-diag ≡ long-tree → ∀ n → isEvenT n → a n ≡ false
  case₁ p n with a n
  ... | false = λ _ → refl
  ... | true = {! cong (cut n) p!}
