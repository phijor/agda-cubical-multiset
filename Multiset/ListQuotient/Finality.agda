{-# OPTIONS --safe #-}

module Multiset.ListQuotient.Finality where

open import Multiset.Prelude hiding (_$_)
open import Multiset.ListQuotient.ListFinality
  using
    ( FunctorΣVec
    ; isSetΣVec^
    ; !^
    ; cut
    ; Tree
    ; isTree
    ; TreePath
    ; fix ; fix⁺ ; fix⁻
    ; pres ; pres⁺ ; pres⁻
    ; step
    ; unfold
    )
open import Multiset.ListQuotient.Bisimilarity as Bisimilarity
  using
    ( Bisim ; _≈_ ; bisim
    ; RelatorLim^
    ; isReflApprox
    ; isTransApprox
    ; isReflBisim
    ; isTransBisim
    ; isPropBisim
    ; ShBisim ; _≈ˢʰ_ ; shbisim
    ; Approx
    ; Approx-π
    ; Bisim→Approx
    )
open import Multiset.Util.BoolSequence as Seq using (latch-even)
open import Multiset.Util.Relation using (ReflectsRel;PreservesRel;isSymTot)
open import Multiset.Util.Vec as Vec 
open import Multiset.Util.BundledVec as BVec
  using
    ( ΣVec
    ; []
    ; _#∷_
    ; _∈_
    ; remove
    ; Relator∞ ; Relator
    ; rnil∞ ; rcons∞
    ; isReflRelator
    ; isTransRelator
    ; isPropRelator
    ; Relator-map
    ; Relator∞-map
    )
  renaming
    ( [_] to #[_]
    )
open import Multiset.Limit.Chain
  using
    ( lim
    ; Limit
    )
open import Multiset.Limit.TerminalChain as TerminalChain
  using
    ( Functor
    ; _^_
    )
open import Multiset.Omniscience using (LLPO)

open import Cubical.Foundations.Everything
open import Cubical.Data.Bool
  using
    ( Bool ; true ; false
    ; if_then_else_
    ; isSetBool
    ; dichotomyBool
    ; true≢false
    )
open import Cubical.Data.Empty as Empty using ()
open import Cubical.Data.Nat as Nat using (ℕ ; suc ; zero)
open import Cubical.Data.Nat.Order.Recursive as NatOrder using (_≤_)
open import Cubical.Data.Unit.Base using (tt*)
open import Cubical.Data.Sigma.Base using (∃-syntax ; _×_)
open import Cubical.Data.Sigma.Properties using (Σ≡Prop)
open import Cubical.Data.Sum as Sum using (_⊎_ ; inl ; inr)
open import Cubical.HITs.PropositionalTruncation as PT using (∥_∥₁)
open import Cubical.HITs.SetQuotients as SQ
  using ()
  renaming
    ( _/_ to _/₂_
    )
open import Cubical.Relation.Nullary.Base using (Dec ; yes ; no ; ¬_)
open import Cubical.Data.Vec hiding ([];map)
open BVec.ΣVec
open Limit using (elements ; is-lim)
open Iso
open Functor ⦃...⦄

UnorderedTree : Type _
UnorderedTree = Tree /₂ Bisim

module _ (a b : Tree) (cs : ΣVec Tree) where
  ∷-swap-approx : Relator Bisim (a #∷ b #∷ cs) (b #∷ a #∷ cs)
  ∷-swap-approx = BVec.Relator-∷-swap isReflBisim a b

private
  [_,_] : ∀ {ℓ} {A : Type ℓ} → A → A → ΣVec A
  [ a , b ] = a #∷ b #∷ []

  [,]-refl : (s t : Tree) → Relator Bisim [ s , t ] [ s , t ]
  [,]-refl s t = isReflRelator isReflBisim [ s , t ]

  [,]-swap : (s t : Tree) → Relator Bisim [ s , t ] [ t , s ]
  [,]-swap s t = ∷-swap-approx s t []

diag : (ℕ → Tree) → (n : ℕ) → ΣVec ^ n
diag = TerminalChain.diag ΣVec

Complete : Type _
Complete = {x y₁ y₂ : Tree}
  → (ys : ℕ → Tree)
  → (split : ∀ n → (ys n ≡ y₁) ⊎ (ys n ≡ y₂))
  → (approx : ∀ n → (cut n x) ≡ (diag ys n))
  → ∥ (x ≈ y₁) ⊎ (x ≈ y₂) ∥₁

pres-reflects-≈→Complete : ReflectsRel _≈ˢʰ_ (Relator _≈_) pres⁺ → Complete
pres-reflects-≈→Complete reflects {x = x} {y₁} {y₂} ys split approx = goal split where
  open import Cubical.Data.Sum.Base as Sum using (_⊎_ ; inl ; inr)
  open import Cubical.Foundations.Transport using (subst⁻)

  open BVec.Reasoning Bisim isReflBisim isTransBisim
    using (_Rel⟨_⟩_ ; _Rel∎)

  Split : ℕ → Type
  Split n = (ys n ≡ y₁) ⊎ (ys n ≡ y₂)

  ysᶜ : (n : ℕ) → Split n → Tree
  ysᶜ n (inl _) = y₂
  ysᶜ n (inr _) = y₁

  either-≈ : (n : ℕ) → (e : Split n) → Relator Bisim [ ys n , ysᶜ n e ] [ y₁ , y₂ ]
  either-≈ n (inl ysₙ≡y₁) =
    [ ys n , y₂ ] Rel⟨ BVec.Relator-cong-∷ isReflBisim ysₙ≡y₁ ⟩
    [ y₁ , y₂ ] Rel∎
  either-≈ n (inr ysₙ≡y₂) =
    [ ys n , y₁ ] Rel⟨ BVec.Relator-cong-∷ isReflBisim ysₙ≡y₂ ⟩
    [ y₂   , y₁ ] Rel⟨ [,]-swap y₂ y₁ ⟩
    [ y₁   , y₂ ] Rel∎

  module _ (e : ∀ n → Split n) where
    approx-xᶜ : (n : ℕ) → ΣVec ^ n
    approx-xᶜ n = cut n $ ysᶜ n (e n)

    approx-xᶜ-islim : ∀ n → !^ n (approx-xᶜ (suc n)) ≡ approx-xᶜ n
    approx-xᶜ-islim n with (e (suc n)) | (e n)
    ... | inl ysₙ₊₁≡y₁ | inl ysₙ≡y₁ = y₂ .is-lim n
    ... | inl ysₙ₊₁≡y₁ | inr ysₙ≡y₂ = TerminalChain.diag-islim-alternating _ y₂ y₁ x ys approx ysₙ≡y₂ ysₙ₊₁≡y₁
    ... | inr ysₙ₊₁≡y₂ | inl ysₙ≡y₁ = TerminalChain.diag-islim-alternating _ y₁ y₂ x ys approx ysₙ≡y₁ ysₙ₊₁≡y₂
    ... | inr ysₙ₊₁≡y₂ | inr ysₙ≡y₂ = y₁ .is-lim n

    xᶜ : Tree
    xᶜ .elements = approx-xᶜ
    xᶜ .is-lim = approx-xᶜ-islim

    approxᶜ : ∀ n → cut n xᶜ ≡ cut n (ysᶜ n (e n))
    approxᶜ n = refl

    pres-pairs : pres⁺ [ x , xᶜ ] ≈ˢʰ pres⁺ [ y₁ , y₂ ]
    pres-pairs = shbisim goal where module _ (n : ℕ) where
      step₁ : Relator (Approx n) [ cut n (ys n) , cut n (ysᶜ n (e n)) ] [ cut n y₁ , cut n y₂ ]
      step₁ = Relator-map _ (Approx n) (Bisim→Approx _ _ n) (either-≈ n (e n))

      goal : Relator (Approx n) [ cut n x , cut n (ysᶜ n (e n)) ] [ cut n y₁ , cut n y₂ ]
      goal = subst⁻ (λ · → Relator (Approx n) [ · , cut n (ysᶜ n (e n)) ] [ _ , _ ]) (approx n) step₁

    pairs : Relator Bisim [ x , xᶜ ] [ y₁ , y₂ ]
    pairs = reflects pres-pairs

    eq : ∀ {a b x y} → Relator Bisim [ x , y ] [ a , b ] → ∥ (x ≈ a) ⊎ (x ≈ b) ∥₁
    eq {x = x} = PT.map λ where
      (rcons∞ a x≈a Vec.here _) → inl x≈a
      (rcons∞ b x≈b (Vec.there Vec.here) _) → inr x≈b

    goal : ∥ (x ≈ y₁) ⊎ (x ≈ y₂) ∥₁
    goal = eq pairs

-- The sequence corresponding to the infinite tree in which each node
-- has exactly one subtree.
module long where
  node : ∀ n → ΣVec ^ n
  node zero = tt*
  node (suc n) = #[ node n ]

  is-tree : isTree node
  is-tree zero = refl
  is-tree (suc n) = cong #[_] (is-tree n)

  -- Anything that approximates node is already node, up to a path.
  --
  -- NOTE: This only works since (ΣVec ^ n) is a set and bisimilarity is Prop-valued.
  -- If instead we were to define bisimilarity in a proof-relevant vay (i.e. using Relator∞),
  -- this might not be necessary: Extracting the witness of being Relator∞-related to a singleton
  -- can be done without any assumtion of truncation on the relation being lifted.
  approx-node→≡node : ∀ n → (t : ΣVec ^ n) → Approx n t (node n) → t ≡ node n
  approx-node→≡node zero tt* _ = refl
  approx-node→≡node (suc n) t approx = t≡#[nodeₙ] where
    t-is-singleton : Σ[ (t′ , _) ∈ BVec.isSingleton t ] Approx n t′ (node n)
    t-is-singleton = BVec.isSet→Relator-singleton→isSingleton (isSetΣVec^ n) (Bisimilarity.isPropApprox n) approx

    t′ : ΣVec ^ n
    t′ = t-is-singleton .fst .fst

    approx-t′-node : Approx n t′ (node n)
    approx-t′-node = t-is-singleton .snd

    t≡#[nodeₙ] : t ≡ #[ node n ]
    t≡#[nodeₙ] =
      t           ≡⟨ t-is-singleton .fst .snd ⟩
      #[ t′ ]     ≡⟨ cong #[_] (approx-node→≡node n t′ approx-t′-node) ⟩
      #[ node n ] ∎


long : Tree
long .elements = long.node
long .is-lim = long.is-tree

-- Any tree that is bisimilar to the long tree is already the long tree, up to a path:
≈long→≡long : ∀ {t : Tree} → t ≈ long → t ≡ long
≈long→≡long {t} t≈long = TreePath λ n → long.approx-node→≡node n (cut n t) (t≈long .elements n)

-- Given a sequence a : ℕ → Bool, we define a variant (long? a) of long,
-- which is equal to long if the sequence a contains only value false,
-- but its height stop growing if there is n : ℕ such that (a n) is
-- the first true in a.

module long? where
  node₀ : (a₀ : Bool) → (a : ℕ → Bool) → ∀ n → ΣVec ^ n
  node₀ _ _ zero = tt*
  node₀ true a (suc n) = []
  node₀ false a (suc n) = #[ node₀ (Seq.head a) (Seq.tail a) n ]

  is-tree₀ : (a₀ : Bool) → (a : ℕ → Bool) → isTree (node₀ a₀ a)
  is-tree₀ a₀ a zero = refl
  is-tree₀ true a (suc n) = refl {x = []}
  is-tree₀ false a (suc n) = cong #[_] (is-tree₀ (Seq.head a) (Seq.tail a) n)

  node : (a : ℕ → Bool) → ∀ n → ΣVec ^ n
  node a = node₀ (Seq.head a) (Seq.tail a)

  is-tree : (a : ℕ → Bool) → isTree (node a)
  is-tree a = is-tree₀ (Seq.head a) (Seq.tail a)

  approx-node→≡node : (a : ℕ → Bool) → ∀ n → (t : ΣVec ^ n) → Approx n t (node a n) → t ≡ node a n
  approx-node→≡node a zero tt* _ = refl
  approx-node→≡node a (suc n) t approx with (a 0)
  ... | true = BVec.isSet→Relator-empty→isEmpty (isSetΣVec^ n) approx
  ... | false = t≡#[nodeₙ] where
    a′ = Seq.tail a

    t-is-singleton : Σ[ (t′ , _) ∈ BVec.isSingleton t ] Approx n t′ (node a′ n)
    t-is-singleton = BVec.isSet→Relator-singleton→isSingleton (isSetΣVec^ n) (Bisimilarity.isPropApprox n) approx

    t′ : ΣVec ^ n
    t′ = t-is-singleton .fst .fst

    approx-t′-node : Approx n t′ (node a′ n)
    approx-t′-node = t-is-singleton .snd

    t≡#[nodeₙ] : t ≡ #[ node a′ n ]
    t≡#[nodeₙ] =
      t               ≡⟨ t-is-singleton .fst .snd ⟩
      #[ t′ ]         ≡⟨ cong #[_] (approx-node→≡node a′ n t′ approx-t′-node) ⟩
      #[ node a′ n ]  ∎


long? : (a : ℕ → Bool) → Tree
long? a .elements = long?.node a
long? a .is-lim = long?.is-tree a

-- Like above: If a tree is bisimilar to the potentially finite singleton-tree,
-- they're already the same up to a path:
≈long?→≡long? : ∀ {t : Tree}
  → (as : ℕ → Bool)
  → t ≈ long? as
  → t ≡ long? as
≈long?→≡long? {t} as t≈long? = TreePath λ n → long?.approx-node→≡node as n (cut n t) (t≈long? .elements n)

long?≠long : (a : ℕ → Bool) (aP : isProp (Σ[ n ∈ ℕ ] a n ≡ true))
  → ∀ n → long? a .elements (suc n) ≡ long .elements (suc n) → a n ≡ false
long?≠long a aP zero p with a 0
... | false = refl
... | true = Empty.rec $ BVec.[]-#∷-disjoint p
long?≠long a aP (suc n) p with a 0
... | false = long?≠long (a ∘ suc) (λ { (x , q) (y , r) → Σ≡Prop (λ _ → isSetBool _ _) (Nat.injSuc (cong fst (aP (_ , q) (_ , r)))) }) n (BVec.isInjectiveCons p)
... | true = Empty.rec $ BVec.[]-#∷-disjoint p

long?-long-connect : (as : ℕ → Bool) (aP : isProp (Σ[ n ∈ ℕ ] as n ≡ true))
  → ∀ n → as (suc n) ≡ true
  → !^ n (long?.node as (suc n)) ≡ long.node n
long?-long-connect as aP zero _ = refl
long?-long-connect as aP (suc n) asₙ₊₁≡true with dichotomyBool (Seq.head as)
... | inl as₀≡true = Empty.rec (Nat.znots (cong fst (aP (_ , as₀≡true) (_ , asₙ₊₁≡true))))
... | inr as₀≡false =
  !^ (suc n) (long?.node₀ (Seq.head as) (Seq.tail as) (suc (suc n)))  ≡⟨ cong (λ · → !^ (suc n) (long?.node₀ · (Seq.tail as) (suc (suc n)))) as₀≡false ⟩
  !^ (suc n) #[ long?.node (Seq.tail as) (suc n) ]                    ≡⟨⟩
  #[ !^ n (long?.node (Seq.tail as) (suc n)) ]                        ≡⟨ cong #[_] (long?-long-connect (Seq.tail as) aP-tail n asₙ₊₁≡true) ⟩
  #[ long.node n ] ∎ where

  aP-tail : isProp (Σ[ k ∈ ℕ ] Seq.tail as k ≡ true)
  aP-tail (k , asₖ₊₁≡true) (l , asₗ₊₁≡true) = Σ≡Prop (λ n → isSetBool (Seq.tail as n) true) (Nat.injSuc goal) where
    goal : suc k ≡ suc l
    goal = cong fst (aP (suc k , asₖ₊₁≡true) (suc l , asₗ₊₁≡true))

complete→llpo : Complete → LLPO
complete→llpo complete as as-true-once = PT.map
  (Sum.map x≈l→as-evens-false x≈long?→as-odds-false)
  (complete {x = x} {y₁ = long} {y₂ = long? as} approx split is-approx)
  where

  approx : ℕ → Tree
  approx = latch-even as long (long? as)

  private
    ≤-suc : ∀ m {n} → m ≤ n → m ≤ suc n
    ≤-suc zero _ = _
    ≤-suc (suc m) {suc n} p = ≤-suc m p

  abstract
    module _ {n : ℕ} (¬≤n-true : ¬ (Σ[ k ∈ ℕ ] (k ≤ n) × (as k ≡ true))) where
      -- Praise be decidability: The assumtion ¬≤n-true implies
      -- that `as` is constantly `false` for all `k ≤ n`:
      all-≤n-false : ∀ k → k ≤ n → as k ≡ false
      all-≤n-false k k≤n with (dichotomyBool (as k))
      ... | inr asₖ≡false = asₖ≡false
      ... | inl asₖ≡true = Empty.rec (¬≤n-true (k , k≤n , asₖ≡true))

      -- This implies that `latch-even as ...` is `long` for all positions `k ≤ n`:
      latch-even-const-long : ∀ k → k ≤ n → latch-even as long (long? as) k ≡ long
      latch-even-const-long = Seq.latch-even-until as n all-≤n-false

      approxₙ≡long : approx n ≡ long
      approxₙ≡long = latch-even-const-long n (NatOrder.≤-refl n)

      -- We can extend the hypothesis one more step:
      ¬≤false-suc : as (suc n) ≡ false → ¬ (Σ[ k ∈ ℕ ] (k ≤ suc n) × (as k ≡ true))
      ¬≤false-suc asₙ₊₁≡false (k , k≤n+1 , asₖ≡true) with NatOrder.≤-split {m = k} {n = suc n} k≤n+1
      ... | inl k≤n = ¬≤n-true (k , k≤n , asₖ≡true)
      ... | inr k≡n+1 = true≢false (sym asₖ≡true ∙∙ cong as k≡n+1 ∙∙ asₙ₊₁≡false)

    -- The proof below (`diag-approx-is-tree`) is done by wild case-bashing,
    -- but all cases factor through the following line of reasoning:
    approx-flip-flop : {n : ℕ} → (flip flop : _)
      → (approx (suc n) ≡ flip)
      --^ The n+1ˢᵗ approximation is `flip`
      → (!^ n (cut (suc n) flip) ≡ cut n flop)
      --^ `flip` and `flop` are related by a triangle in the limit cone
      → (approx n ≡ flop)
      --^ The nᵗʰ approximation is `flop`
      → !^ n (diag approx (suc n)) ≡ diag approx n
    approx-flip-flop {n = n} flip flop step₁ step₂ step₃ =
      !^ n (cut (suc n) $ approx (suc n)) ≡⟨ cong (!^ n ∘ cut (suc n)) step₁ ⟩
      !^ n (cut (suc n) $ flip )          ≡⟨ step₂ ⟩
      cut n flop                          ≡⟨ sym (cong (cut n) step₃) ⟩
      cut n (approx n) ∎

    diag-approx-is-tree : isTree (diag approx)
    diag-approx-is-tree n with Seq.true-before? as n
    -- `as` is not true for any `k ≤ n`:
    ... | no ¬≤n-true with dichotomyBool (as (suc n))
    ... | inl asₙ₊₁≡true with Nat.evenOrOdd (suc n)
    ... | inl even-n+1 = approx-flip-flop (long? as) long
      (Seq.latch-even-at as (suc n) even-n+1 asₙ₊₁≡true)
      (long?-long-connect as as-true-once n asₙ₊₁≡true)
      (approxₙ≡long ¬≤n-true)
    ... | inr odd-n+1 = approx-flip-flop long long
      lemma
      (long .is-lim n)
      (approxₙ≡long ¬≤n-true)
      where
        force-odds-false-until-n+1 : ∀ k → k ≤ suc n → Seq.force-odds-false as k ≡ false
        force-odds-false-until-n+1 k k≤n+1 with NatOrder.≤-split {m = k} {n = suc n} k≤n+1
        ... | inl k≤n = Seq.force-odds-false-const-until as n (all-≤n-false ¬≤n-true) k k≤n
        ... | inr k≡n+1 =
          Seq.force-odds-false as k ≡⟨ cong (Seq.force-odds-false as) k≡n+1 ⟩
          Seq.force-odds-false as (suc n) ≡⟨ Seq.force-odds-false-at-odd as {suc n} odd-n+1 ⟩
          false ∎

        lemma : latch-even as long (long? as) (suc n) ≡ long
        lemma =
          (if as 0 then long? as else Seq.latch long (long? as) (Seq.tail (Seq.force-odds-false as)) n)
            ≡⟨ Seq.if-false (all-≤n-false ¬≤n-true 0 _) ⟩
          (Seq.latch long (long? as) (Seq.tail (Seq.force-odds-false as)) n)
            ≡⟨ Seq.latch-until _ n (Seq.UpTo-tail (_≡ false) n force-odds-false-until-n+1) n (NatOrder.≤-refl n) ⟩∎
          long ∎

    diag-approx-is-tree n | no ¬≤n-true | inr asₙ₊₁≡false = approx-flip-flop long long
      lemma
      (long .is-lim n)
      (approxₙ≡long ¬≤n-true)
      where
        -- `force-odds-false` is false for all `k ≤ n + 1`, since we assume `as k ≡ false` for all `k ≤ n` and `k = n + 1`.
        force-odds-false-until-n+1 : ∀ k → k ≤ suc n → Seq.force-odds-false as k ≡ false
        force-odds-false-until-n+1 = Seq.force-odds-false-const-until as (suc n) (all-≤n-false (¬≤false-suc ¬≤n-true asₙ₊₁≡false))

        -- A shorthand:
        long′ : Tree
        long′ = Seq.latch long (long? as) (Seq.tail (Seq.force-odds-false as)) n

        -- Knowing that `as₀ ≡ false`, expand the definition of `latch-even` and use the previous observation
        -- to rewrite it into `long`:
        lemma : latch-even as long (long? as) (suc n) ≡ long
        lemma =
          (if as 0 then long? as else long′) ≡⟨ Seq.if-false (all-≤n-false ¬≤n-true 0 _) ⟩
          long′                              ≡⟨ Seq.latch-until _ n (Seq.UpTo-tail (_≡ false) n force-odds-false-until-n+1) n (NatOrder.≤-refl n) ⟩∎
          long ∎

    -- There exists some `k ≤ n` such that `as` is true:
    diag-approx-is-tree n | yes (k , k≤n , asₖ≡true) with Nat.evenOrOdd k
    -- If that k is even, `diag approx` is `long? as` at both positions `n` and `suc n`:
    ... | inl even-k = approx-flip-flop (long? as) (long? as)
      (Seq.latch-even-after as (suc n) before-1+n)
      (long? as .is-lim n)
      (Seq.latch-even-after as n before-n)
      where
      before-1+n : Seq.Before as (suc n) (λ k aₖ → Nat.isEvenT k × (aₖ ≡ true))
      before-1+n = k , ≤-suc k k≤n , even-k , asₖ≡true

      before-n : Seq.Before as n (λ k aₖ → Nat.isEvenT k × (aₖ ≡ true))
      before-n = k , k≤n , even-k , asₖ≡true
    -- In case the `k` is odd, `diag approx` has to be `long` at every position:
    ... | inr odd-k = approx-flip-flop long long
      (latch-even-const-l (suc n))
      (long .is-lim n)
      (latch-even-const-l n)
      where

      -- latch-even has to be long:
      -- * `as` is true at most once
      -- * it is true at k
      -- * k is odd, and latch-even never returns (long? as) in that case.
      latch-even-const-l : ∀ n → latch-even as long (long? as) n ≡ long
      latch-even-const-l = Seq.latch-even-const-true-once as as-true-once (k , odd-k , asₖ≡true)

  x : Tree
  x .elements = diag approx
  x .is-lim = diag-approx-is-tree

  is-approx : ∀ n → x .elements n ≡ diag approx n
  is-approx n = refl

  split : ∀ n → (approx n ≡ long) ⊎ (approx n ≡ (long? as))
  split n = Seq.latch-even-dichotomy as long (long? as) n

  x≈l→as-evens-false : x ≈ long → ∀ n → Nat.isEvenT n → as n ≡ false
  x≈l→as-evens-false x≈l n even-n with dichotomyBool (as n)
  ... | inr asₙ≡false = asₙ≡false
  ... | inl asₙ≡true = long?≠long as as-true-once n bad where
    x≡l : x ≡ long
    x≡l = ≈long→≡long x≈l

    bad : long?.node as (suc n) ≡ long.node (suc n)
    bad =
      long?.node as (suc n)   ≡⟨ cong (cut (suc n)) (sym (Seq.latch-even-after as (suc n) (n , ≤-suc n (NatOrder.≤-refl n) , even-n , asₙ≡true))) ⟩
      cut (suc n) x           ≡⟨ cong (cut (suc n)) x≡l ⟩
      cut (suc n) long ∎

  x≈long?→as-odds-false : x ≈ long? as → ∀ n → Nat.isOddT n → as n ≡ false
  x≈long?→as-odds-false x≈long? n odd-n with dichotomyBool (as n)
  ... | inr asₙ≡false = asₙ≡false
  ... | inl asₙ≡true = long?≠long as as-true-once n (sym bad) where
    x≡long? : x ≡ long? as
    x≡long? = ≈long?→≡long? as x≈long?

    bad : long.node (suc n) ≡ long?.node as (suc n)
    bad =
      cut (suc n) long        ≡⟨ cong (cut (suc n)) (sym (Seq.latch-even-const-true-once as as-true-once (n , odd-n , asₙ≡true) (suc n))) ⟩
      cut (suc n) x           ≡⟨ cong (cut (suc n)) x≡long? ⟩
      cut (suc n) (long? as)  ∎

pres-reflects-≈→LLPO : ReflectsRel _≈ˢʰ_ (Relator _≈_) pres⁺ → LLPO
pres-reflects-≈→LLPO reflects = complete→llpo (pres-reflects-≈→Complete reflects)

FMSet : ∀ {ℓ} → Type ℓ → Type ℓ
FMSet X = ΣVec X /₂ (Relator _≡_)

Path→Approx : ∀ n {t u}
  → t ≡ u
  → Approx n t u
Path→Approx n {t} t≡u = subst (Approx n t) t≡u (isReflApprox n t)

Path→Bisim : ∀ {t u} → t ≡ u → t ≈ u
Path→Bisim {t} t≡u = subst (Bisim t) t≡u (isReflBisim t)

-- fix⁺ is a well-defined setoid morphism
fix⁺-preserves-≈' : ∀ n {t u}
  → Relator _≈_ t u
  → Approx n (!^ n (map (cut n) t)) (!^ n (map (cut n) u))
fix⁺-preserves-≈' zero _ = tt*
fix⁺-preserves-≈' (suc n) = PT.map λ r →
  BVec.Relator∞-trans (isTransApprox n)
 (BVec.Relator∞-trans (isTransApprox n)
                      (BVec.Path→Relator∞ (isReflApprox n) (sym (map-comp _ _ _)))                      
                      (Relator∞-map _ _ goal r))
                      (BVec.Path→Relator∞ (isReflApprox n) (map-comp _ _ _))
  where
    goal : ∀ {t u} → t ≈ u → Approx n (!^ n (cut (suc n) t)) (!^ n (cut (suc n) u))
    goal {t} {u} r = 
       isTransApprox n _ _ _
      (isTransApprox n _ _ _ (Path→Approx n (t .is-lim n))
                             (r .elements n))
                             (Path→Approx n (sym (u .is-lim n)))

fix⁺-preserves-≈ : PreservesRel (Relator _≈_) _≈_ fix⁺
fix⁺-preserves-≈ r = bisim λ n → fix⁺-preserves-≈' n r

module _ {C : Type} (R : C → C → Type)
         (γ : C → ΣVec C)
         (γ-preserves-R : PreservesRel R (Relator R) γ)
         where

-- unfold is a setoid morphism
  unfold-preserves-R' : ∀ n {x y} → R x y → Approx n (step γ n x) (step γ n y)
  unfold-preserves-R' zero r = tt*
  unfold-preserves-R' (suc n) r = PT.map (Relator∞-map R _ (unfold-preserves-R' n)) (γ-preserves-R r)

  unfold-preserves-R : PreservesRel R _≈_ (unfold γ)
  unfold-preserves-R r = bisim (λ n → unfold-preserves-R' n r)

-- uniqueness of unfold
  unfold-unique' : (f : C → Tree)
    → (∀ x → f x ≈ fix⁺ (map f (γ x)))
    → ∀ x n → Approx n (f x .elements n) (step γ n x)
  unfold-unique' f feq x zero = tt*
  unfold-unique' f feq x (suc n) =
    PT.map (λ r → BVec.Relator∞-trans (isTransApprox n)
                  (BVec.Relator∞-trans (isTransApprox n)
                                       r
                                       (BVec.Path→Relator∞ (isReflApprox n) path)) goal)
                                       (feq x .elements (suc n))
    where
      goal : Relator∞ (Approx n) (map (λ y → f y .elements n) (γ x)) (map (step γ n) (γ x))
      goal =
        Relator∞-map _≡_ _
                     (λ {y} → J (λ z eq → Approx n (f y .elements n) (step γ n z)) (unfold-unique' f feq y n))
                     (BVec.isReflRelator∞ (λ _ → refl) _)

      path : cut (suc n) (fix⁺ (map f (γ x))) ≡ map (λ y → f y .elements n) (γ x)
      path =
        cut (suc n) (fix⁺ (map f (γ x)))   ≡⟨ sym (map-comp _ _ _) ⟩
        _                                  ≡⟨ sym (map-comp _ _ _) ⟩
        _                                  ≡⟨ cong (λ g → map g (γ x)) (funExt (λ y → f y .is-lim n)) ⟩
        map (λ y → f y .elements n) (γ x) ∎

  unfold-unique : (f : C → Tree)
    → (∀ x → Relator _≈_ (fix⁻ (f x)) (map f (γ x)))
    → ∀ x → f x ≈ unfold γ x
  unfold-unique f feq x =
    bisim (unfold-unique' f (λ y → isTransBisim _ _ _ (Path→Bisim (sym (secEq fix (f y)))) (fix⁺-preserves-≈ (feq y))) x)


-- Tree/Bisim is a fixpoint of FMSet
Tree/Bisim : Type
Tree/Bisim = Tree /₂ Bisim

module _ {A : Type} (R : A → A → Type) where

  data ΣVecRel : ΣVec A → ΣVec A → Type where
    rnil∞ : ΣVecRel [] []
    rcons∞ : {a b : A} {as bs : ΣVec A} 
      → R a b
      → ΣVecRel as bs
      → ΣVecRel (a #∷ as) (b #∷ bs)
 
  isReflΣVecRel : (∀ x → R x x) → ∀ xs → ΣVecRel xs xs
  isReflΣVecRel reflR [] = rnil∞
  isReflΣVecRel reflR (BVec.# (x ∷ xs)) = rcons∞ (reflR x) (isReflΣVecRel reflR (BVec.# xs))

  ΣVecRel→Relator∞ : ∀{xs ys} → ΣVecRel xs ys → Relator∞ R xs ys
  ΣVecRel→Relator∞ rnil∞ = rnil∞
  ΣVecRel→Relator∞ (rcons∞ r rs) = rcons∞ _ r Vec.here (ΣVecRel→Relator∞ rs)

  ΣVecRel→Relator : ∀{xs ys} → ΣVecRel xs ys → Relator R xs ys
  ΣVecRel→Relator rs = PT.∣ ΣVecRel→Relator∞ rs ∣₁

  ΣVecRel-eq/ : ∀{xs ys} → ΣVecRel xs ys → Path (ΣVec (A /₂ R)) (map SQ.[_] xs) (map SQ.[_] ys)
  ΣVecRel-eq/ rnil∞ = refl
  ΣVecRel-eq/ (rcons∞ r rs) i = SQ.eq/ _ _ r i #∷ ΣVecRel-eq/ rs i

toΣVecRel : {X : Type} {R : X → X → Type}
  → (∀ x → R x x)
  → ΣVec (X /₂ R) → ΣVec X /₂ ΣVecRel R
toΣVecRel reflR [] = SQ.[ [] ]
toΣVecRel reflR (BVec.# (x ∷ xs)) =
  SQ.rec2 SQ.squash/
          (λ y ys → SQ.[ y #∷ ys ])
          (λ y y' ys r → SQ.eq/ _ _ (rcons∞ r (isReflΣVecRel _ reflR _)))
          (λ y ys ys' rs → SQ.eq/ _ _ (rcons∞ (reflR y) rs))
          x
          (toΣVecRel reflR (BVec.# xs))

fromΣVecRel : {X : Type} {R : X → X → Type}
  → ΣVec X /₂ ΣVecRel R → ΣVec (X /₂ R)
fromΣVecRel =
  SQ.rec (BVec.isSetΣVec SQ.squash/)
         (map SQ.[_])
         (λ _ _ → ΣVecRel-eq/ _)

toΣVecRelPath : {X : Type} {R : X → X → Type}
  → (reflR : ∀ x → R x x)
  → (xs : ΣVec X) → toΣVecRel {R = R} reflR (map SQ.[_] xs) ≡ SQ.[ xs ]
toΣVecRelPath reflR [] = refl
toΣVecRelPath reflR (BVec.# (x ∷ xs)) = 
  cong (SQ.rec2 SQ.squash/
              (λ y ys → SQ.[ y #∷ ys ])
              (λ y y' ys r → SQ.eq/ (y #∷ ys) (y' #∷ ys) (rcons∞ r (isReflΣVecRel _ reflR ys)))
              (λ y ys ys' rs → SQ.eq/ (y #∷ ys) (y #∷ ys') (rcons∞ (reflR y) rs))
              SQ.[ x ])
       (toΣVecRelPath reflR (BVec.# xs))

fromΣVecRel-toΣVecRel : {X : Type} {R : X → X → Type}
  → (reflR : ∀ x → R x x)
  → ∀ xs → fromΣVecRel {R = R} (toΣVecRel reflR xs) ≡ xs
fromΣVecRel-toΣVecRel reflR [] = refl
fromΣVecRel-toΣVecRel reflR (BVec.# (x ∷ xs)) =
   SQ.elimProp2 {P = λ y ys → fromΣVecRel (SQ.rec2 SQ.squash/
                                                (λ x xs → SQ.[ x #∷ xs ])
                                                (λ x x' xs r → SQ.eq/ (x #∷ xs) (x' #∷ xs) (rcons∞ r (isReflΣVecRel _ reflR xs)))
                                                (λ x xs xs' rs → SQ.eq/ (x #∷ xs) (x #∷ xs') (rcons∞ (reflR x) rs))
                                                y ys)
                              ≡ y #∷ fromΣVecRel ys}
              (λ _ _ → BVec.isSetΣVec SQ.squash/ _ _)
              (λ _ _ → refl)
              x (toΣVecRel reflR (BVec.# xs))
   ∙ cong (x #∷_) (fromΣVecRel-toΣVecRel reflR (BVec.# xs))


recΣVec : {X Y : Type} 
  → {R : X → X → Type}
  → isSet Y
  → (∀ x → R x x)
  → (f : ΣVec X → Y)
  → (∀ xs ys → ΣVecRel R xs ys → f xs ≡ f ys)
  → ΣVec (X /₂ R) → Y
recΣVec setY reflR f p xs = SQ.rec setY f p (toΣVecRel reflR xs)

recΣVecPath : {X Y : Type} 
  → {R : X → X → Type}
  → (setY : isSet Y)
  → (reflR : ∀ x → R x x)
  → (f : ΣVec X → Y)
  → (p : ∀ xs ys → ΣVecRel R xs ys → f xs ≡ f ys)
  → (xs : ΣVec X) → recΣVec setY reflR f p (map SQ.[_] xs) ≡ f xs
recΣVecPath setY reflR f p xs = cong (SQ.rec setY f p) (toΣVecRelPath reflR xs)

elimΣVecProp : {X : Type}
  → {R : X → X → Type}
  → (Y : ΣVec (X /₂ R) → Type)
  → (∀ xs → isProp (Y xs))
  → (∀ x → R x x)
  → (f : (xs : ΣVec X) → Y (map SQ.[_] xs))
  → (xs : ΣVec (X /₂ R)) → Y xs
elimΣVecProp Y propY reflR f xs =
  subst Y (fromΣVecRel-toΣVecRel reflR xs) (goal xs)
  where
    goal : (xs : ΣVec _) → Y (fromΣVecRel (toΣVecRel reflR xs))
    goal xs = SQ.elimProp {P = λ xs → Y (fromΣVecRel xs)}
                          (λ _ → propY _)
                          f
                          (toΣVecRel reflR xs) 

elimΣVecProp2 : {X : Type}
  → {R : X → X → Type}
  → (Y : ΣVec (X /₂ R) → ΣVec (X /₂ R) → Type)
  → (∀ xs ys → isProp (Y xs ys))
  → (∀ x → R x x)
  → (f : (xs ys : ΣVec X) → Y (map SQ.[_] xs) (map SQ.[_] ys))
  → (xs ys : ΣVec (X /₂ R)) → Y xs ys
elimΣVecProp2 {R} Y propY reflR f xs ys = 
  subst2 Y (fromΣVecRel-toΣVecRel reflR xs) (fromΣVecRel-toΣVecRel reflR ys) (goal xs ys)
  where
    goal : (xs ys : ΣVec _) → Y (fromΣVecRel (toΣVecRel reflR xs)) (fromΣVecRel (toΣVecRel reflR ys))
    goal xs ys = SQ.elimProp2 {P = λ xs ys → Y (fromΣVecRel xs) (fromΣVecRel ys)}
                              (λ _ _ → propY _ _)
                              f
                              (toΣVecRel reflR xs) (toΣVecRel reflR ys)

open import Cubical.Relation.Binary.Base
open BinaryRelation

Relator∞-remove : {A : Type} {R : A → A → Type}
  → ∀ {n x y xs ys} (mem : y Vec.∈ ys) (r : R y x)
  → Relator∞ R (BVec.# Vec.remove ys mem) xs
  → Relator∞ R (BVec.#_ {length = suc n} ys) (x #∷ xs)
Relator∞-remove {ys = y ∷ ys} here r rs = rcons∞ _ r here rs
Relator∞-remove {xs = BVec.# (x ∷ xs)} {ys = y ∷ y' ∷ ys} (there mem) r (rcons∞ _ r' ∈xs rs) = 
  rcons∞ _ r' (there ∈xs) (Relator∞-remove mem r rs )

isSymRelator∞ : {A : Type} {R : A → A → Type}
  → isSym R
  → ∀ xs ys → Relator∞ R xs ys → Relator∞ R ys xs
isSymRelator∞ symR _ _ rnil∞ = rnil∞
isSymRelator∞ symR _ (BVec.# (y ∷ ys)) (rcons∞ b r mem rs) =
  Relator∞-remove mem (symR _ _ r) (isSymRelator∞ symR _ _ rs)

isSymRelator : {A : Type} {R : A → A → Type}
  → isSym R → isSym (Relator R)
isSymRelator symR _ _ = PT.map (isSymRelator∞ symR _ _)

isSymApprox : ∀ n → isSym (Approx n)
isSymApprox zero = isSymTot
isSymApprox (suc n) = isSymRelator (isSymApprox n)

isSymBisim : isSym Bisim
isSymBisim s t s≈t = bisim λ n → isSymApprox n _ _ (s≈t .elements n)

isEquivRelRelator : {X : Type} {R : X → X → Type}
  → isEquivRel R 
  → isEquivRel (Relator R)
isEquivRelRelator eqR =
  equivRel (isReflRelator (isEquivRel.reflexive eqR))
           (isSymRelator (isEquivRel.symmetric eqR))
           (isTransRelator (isEquivRel.transitive eqR))  
  

isEquivRelBisim : isEquivRel Bisim
isEquivRelBisim =
  equivRel isReflBisim
           isSymBisim
           isTransBisim  

∈map : {A B : Type} {f : A → B} {a : A} {xs : ΣVec A}
  → a BVec.∈ xs → f a BVec.∈ map f xs
∈map {f = f} here = here
∈map (there m) = there (∈map m)

map∈ : {A B : Type} {f : A → B} {b : B} {xs : ΣVec A}
  → b BVec.∈ map f xs → Σ[ a ∈ A ] (a BVec.∈ xs) × (f a ≡ b)
map∈ {xs = BVec.# (x ∷ xs)} here = _ , here , refl
map∈ {xs = BVec.# (x ∷ xs)} (there mb) =
  map∈ mb .fst , there (map∈ mb .snd .fst) , map∈ mb .snd .snd

∈map-map∈ : {A B : Type} {f : A → B} {b : B} {xs : ΣVec A}
  → (m : b BVec.∈ map f xs)
  → PathP (λ i → map∈ m .snd .snd (~ i) BVec.∈ map f xs) m (∈map (map∈ m .snd .fst))
∈map-map∈ {xs = BVec.# (x ∷ xs)} here = refl
∈map-map∈ {xs = BVec.# (x ∷ xs)} (there m) = congP (λ _ → there) (∈map-map∈ m)

remove-map : {A B : Type} {f : A → B} {a : A} {xs : ΣVec A}
  → (m : a BVec.∈ xs) → map f (BVec.remove xs m) ≡ BVec.remove (map f xs) (∈map m)
remove-map here = refl
remove-map (there {as = x ∷ as} m) = cong (_ #∷_) (remove-map m)


effectiveRelator∞ : {X : Type} {R : X → X → Type}
  → isPropValued R
  → isEquivRel R 
  → {xs ys : ΣVec X}
  → Relator∞ _≡_ (map (SQ.[_] {R = R}) xs) (map SQ.[_] ys)
  → Relator∞ R xs ys
effectiveRelator∞ propR eqR {[]} {[]} rs = rnil∞
effectiveRelator∞ propR eqR {BVec.# (x ∷ xs)} (rcons∞ y r ∈ys rs) =
  let (x' , ∈ys' , r') = map∈ ∈ys
  in rcons∞ x' (SQ.effective propR eqR _ _ (r ∙ sym r')) ∈ys'
            (effectiveRelator∞ propR eqR
                               (subst (Relator∞ _≡_ (map SQ.[_] (BVec.# xs)))
                                      (sym (remove-map ∈ys' ∙ \ i -> BVec.remove _ (∈map-map∈ ∈ys (~ i))))
                                      rs))

effectiveRelator : {X : Type} {R : X → X → Type}
  → isPropValued R
  → isEquivRel R 
  → {xs ys : ΣVec X}
  → Relator _≡_ (map (SQ.[_] {R = R}) xs) (map SQ.[_] ys)
  → Relator R xs ys
effectiveRelator propR eqR = PT.map (effectiveRelator∞ propR eqR)

fixQ⁺ : FMSet Tree/Bisim → Tree/Bisim
fixQ⁺ =
  SQ.rec SQ.squash/ 
         (recΣVec SQ.squash/ (λ _ → isReflBisim _) f fR)
         (elimΣVecProp2 _ (λ _ _ → isPropΠ (λ _ → SQ.squash/ _ _) )
                        (λ _ → isReflBisim _)
                        λ ts us rs → recΣVecPath SQ.squash/ (λ _ → isReflBisim _) f fR ts
                                      ∙ SQ.eq/ _ _ (fix⁺-preserves-≈ (effectiveRelator isPropBisim isEquivRelBisim rs))
                                      ∙ sym (recΣVecPath SQ.squash/ (λ _ → isReflBisim _) f fR us))
  where
    f : ΣVec Tree → Tree/Bisim
    f ts = SQ.[ fix⁺ ts ] 

    fR : ∀ xs ys → ΣVecRel Bisim xs ys → f xs ≡ f ys
    fR ts us rs = SQ.eq/ _ _ (fix⁺-preserves-≈ (ΣVecRel→Relator _≈_ rs))

module _ (fix⁻-preserves-≈ : PreservesRel _≈_ (Relator _≈_) fix⁻) where
  fixQ⁻ : Tree/Bisim → FMSet Tree/Bisim
  fixQ⁻ =
    SQ.rec SQ.squash/
           (λ t → SQ.[ map SQ.[_] (fix⁻ t) ])
           λ t u t≈u → SQ.eq/ _ _ (Relator-map _ _ (SQ.eq/ _ _) (fix⁻-preserves-≈ t≈u))


  inj-fixQ⁻' : ∀ {t u} → Relator (Path Tree/Bisim) (map SQ.[_] (fix⁻ t)) (map SQ.[_] (fix⁻ u))
    → t ≈ u
  inj-fixQ⁻' {t}{u} rs = subst2 Bisim (secEq fix t) (secEq fix u)
    (fix⁺-preserves-≈ (effectiveRelator isPropBisim isEquivRelBisim rs))
  
  inj-fixQ⁻ : ∀ t u → fixQ⁻ t ≡ fixQ⁻ u → t ≡ u
  inj-fixQ⁻ =
    SQ.elimProp2 (λ _ _ → isPropΠ (λ _ → SQ.squash/ _ _))
      (λ t u r →
        SQ.eq/ _ _
          (inj-fixQ⁻' (SQ.effective (λ _ _ → isPropRelator _)
                                    (isEquivRelRelator (equivRel (λ _ → refl) (λ _ _ → sym) λ _ _ _ → _∙_))
                                    _
                                    _
                                    r)) )

  fixQ⁻fixQ⁺ : ∀ t → fixQ⁻ (fixQ⁺ t) ≡ t
  fixQ⁻fixQ⁺ =
    SQ.elimProp (λ _ → SQ.squash/ _ _)
      (elimΣVecProp _ (λ _ → SQ.squash/ _ _) isReflBisim
        (λ ts →
          fixQ⁻ (fixQ⁺ SQ.[ map SQ.[_] ts ])                           ≡⟨⟩
          fixQ⁻ (recΣVec SQ.squash/ isReflBisim f fR (map SQ.[_] ts))  ≡⟨ cong fixQ⁻ (recΣVecPath SQ.squash/ isReflBisim f fR ts) ⟩
          fixQ⁻ (SQ.[ fix⁺ ts ])                                       ≡⟨⟩
          SQ.[ map SQ.[_] (fix⁻ (fix⁺ ts)) ]                           ≡⟨ (λ i → SQ.[ map SQ.[_] (retEq fix ts i) ]) ⟩
          SQ.[ map SQ.[_] ts ]                                         ∎))
    where
      f : ΣVec Tree → Tree/Bisim
      f ts = SQ.[ fix⁺ ts ] 

      fR : ∀ xs ys → ΣVecRel Bisim xs ys → f xs ≡ f ys
      fR ts us rs = SQ.eq/ _ _ (fix⁺-preserves-≈ (ΣVecRel→Relator _≈_ rs))

  fixQ⁺fixQ⁻ : ∀ ts → fixQ⁺ (fixQ⁻ ts) ≡ ts
  fixQ⁺fixQ⁻ ts = inj-fixQ⁻ _ _ (fixQ⁻fixQ⁺ _)

  fixQ⁺-iso : Iso (FMSet Tree/Bisim) Tree/Bisim
  fixQ⁺-iso = iso fixQ⁺ fixQ⁻ fixQ⁺fixQ⁻ fixQ⁻fixQ⁺
