{-# OPTIONS --safe #-}

module Multiset.Util.BoolSequence where

open import Multiset.Prelude

open import Cubical.Foundations.Function using (_∘_ ; case_of_ ; case_return_of_)
open import Cubical.Foundations.Transport using (subst⁻)
open import Cubical.Data.Bool.Base as Bool using (Bool ; false ; true ; if_then_else_ ; _and_ ; dichotomyBool)
open import Cubical.Data.Bool.Properties using (true≢false)
open import Cubical.Data.Nat.Base using (ℕ ; zero ; suc ; _+_ ; isEvenT ; isOddT)
open import Cubical.Data.Nat.Properties as Nat using ()
open import Cubical.Data.Nat.Order.Recursive as NatOrder using (_≤_ ; _<_ ; _≤?_)
open import Cubical.Data.Sigma.Base as Sigma using (_×_)
open import Cubical.Data.Sum.Base as Sum using (_⊎_ ; inl ; inr)
open import Cubical.Data.Empty.Base as Empty using () renaming (rec to absurd)
open import Cubical.Relation.Nullary.Base using (Dec ; yes ; no)
open import Cubical.Relation.Nullary.Properties using (mapDec)

private
  variable
    ℓ : Level
    A B : Type ℓ

  and-falseˡ : ∀ b → false and b ≡ false
  and-falseˡ false = refl
  and-falseˡ true = refl

if-false : ∀ {f t : A} {b} → b ≡ false → (if b then t else f) ≡ f
if-false {f = f} {t} p = subst⁻ (λ b → (if b then t else f) ≡ f) p refl

if-true : ∀ {f t : A} {b} → b ≡ true → (if b then t else f) ≡ t
if-true {f = f} {t} p = subst⁻ (λ b → (if b then t else f) ≡ t) p refl

Seq : Type ℓ → Type ℓ
Seq A = ℕ → A

head : Seq A → A
head = _$ 0

tail : Seq A → Seq A
tail = _∘ suc

--- Given a sequence `as` of booleans, return a sequence
--- that is, at each position, either `f` or `t`:
---   * if for all k ≤ n, `as k ≡ false`, return `f`
---   * otherwise, return `t`.
---
--- The returned sequence is like a "latch": its values is
--- constantly `f` until the first `true` is encountered in
--- `as`, then it becomes `t`.
latch : (f t : A) → (as : Seq Bool) → Seq A
latch f t as zero =
  if head as
    then t
    else f
latch f t as (suc n) =
  if head as
    then t
    else latch f t (tail as) n

Dichotomy : (as : Seq A) (a b : A) → Type _
Dichotomy as a b = ∀ n → (as n ≡ a) ⊎ (as n ≡ b)

--- As claimed above, `latch` takes only values `f` and `t`.
latch-dichotomy : ∀ (as : Seq Bool) {f t : A} → Dichotomy (latch f t as) f t
latch-dichotomy as {f} {t} zero with head as
... | false = inl (refl {x = f})
... | true = inr (refl {x = t})
latch-dichotomy as {f} {t} (suc n) with head as
... | false = latch-dichotomy (tail as) n
... | true = inr (refl {x = t})

latch-const : ∀ (as : Seq Bool) {f t : A}
  → (∀ n → as n ≡ false)
  → ∀ n → latch f t as n ≡ f
latch-const as const-false zero with dichotomyBool (head as)
... | inl as₀≡true = absurd (true≢false (sym as₀≡true ∙ const-false 0))
... | inr as₀≡false = if-false as₀≡false
latch-const as const-false (suc n) with dichotomyBool (head as)
... | inl as₀≡true = absurd (true≢false (sym as₀≡true ∙ const-false 0))
... | inr as₀≡false = if-false as₀≡false ∙ latch-const (tail as) (const-false ∘ suc) n

UpTo : ∀ {ℓP} (as : Seq A) (n : ℕ) (P : {k : ℕ} → A → Type ℓP) → Type ℓP
UpTo as n P = ∀ k → k ≤ n → P {k} (as k)

_≤_⇒_ = UpTo

UpTo-tail : ∀ {ℓP} {as : Seq A} (P : A → Type ℓP)
  → ∀ n → (as ≤ suc n ⇒ P) → (tail as ≤ n ⇒ P)
UpTo-tail _ n up-to = λ { k k≤n → up-to (suc k) k≤n }

latch-until : (as : Seq Bool) {f t : A}
  → ∀ n → as ≤ n ⇒ (_≡ false) → (latch f t as) ≤ n ⇒ (_≡ f)
latch-until as n as≡false-until zero 0≤n = if-false (as≡false-until 0 0≤n)
latch-until as zero _ (suc k) k<0 = absurd k<0
latch-until as {f} {t} (suc n) as≡false-until (suc k) k+1≤n+1 =
  (if head as then t else latch f t (tail as) k)  ≡⟨ if-false (as≡false-until 0 _) ⟩
  latch f t (tail as) k                           ≡⟨ ind ⟩
  f ∎ where
    ind = latch-until (tail as) n (UpTo-tail (_≡ false) n as≡false-until) k k+1≤n+1

Before : ∀ {ℓP} (as : Seq Bool) (n : ℕ) (P : (k : ℕ) → (aₖ : Bool) → Type ℓP) → Type ℓP
Before as n P = Σ[ k ∈ ℕ ] (k ≤ n) × P k (as k)

Before-sytnax : ∀ {ℓP} (as : Seq Bool) (n : ℕ) (P : (k : ℕ) → (aₖ : Bool) → Type ℓP) → Type ℓP
Before-sytnax = Before

syntax Before-sytnax as n (λ k → P) = ∃[ k ≤ n of as ] P

TrueBefore : (as : Seq Bool) (n : ℕ) → Type _
TrueBefore as n = Before as n (λ k → _≡ true)

true-before? : (as : Seq Bool) (n : ℕ) → Dec (TrueBefore as n)
true-before? as zero with dichotomyBool (head as)
... | inl as₀≡true = yes (0 , _ , as₀≡true)
... | inr as₀≡false = no λ { (zero , _ , as₀≡true) → true≢false (sym as₀≡true ∙ as₀≡false) }
true-before? as (suc n) with true-before? as n
... | yes (k , k≤n , aₖ≡true) = yes (k , NatOrder.<-weaken {m = k} {n = suc n} k≤n , aₖ≡true)
... | no ¬true-before-n with dichotomyBool (as $ suc n)
... | inl asₙ₊₁≡true = yes (suc n , NatOrder.≤-refl n , asₙ₊₁≡true)
... | inr asₙ₊₁≡false = no λ where
  (k , k≤1+n , asₖ≡true) →
    Sum.rec {C = Empty.⊥}
      (λ k≤n → ¬true-before-n $ k , k≤n , asₖ≡true
      )
      (λ k≡1+n → true≢false $
        true ≡⟨ sym asₖ≡true ⟩
        as k ≡⟨ cong as k≡1+n ⟩
        as (1 + n) ≡⟨ asₙ₊₁≡false ⟩
        false ∎
      )
      (NatOrder.≤-split {m = k} {n = 1 + n} k≤1+n)

latch-after : (as : Seq Bool) → {f t : A}
  → ∀ n → TrueBefore as n → latch f t as n ≡ t
latch-after as zero (zero , _ , as₀≡true) = if-true as₀≡true
latch-after as (suc n) (zero , _ , as₀≡true) = if-true as₀≡true
latch-after as (suc n) (suc k , k≤n , asₖ₊₁≡true) with head as
... | false = latch-after (tail as) n (k , k≤n , asₖ₊₁≡true)
... | true = refl

force-odds-false : (as : Seq Bool) → Seq Bool
force-odds-false as n = Sum.rec (λ even → as n) (λ odd → false) (Nat.evenOrOdd n)

force-odds-false-at-odd : (as : Seq Bool) → {n : ℕ} → isOddT n → force-odds-false as n ≡ false
force-odds-false-at-odd as {n} odd-n with Nat.evenOrOdd n
... | inl even-n = absurd (Nat.¬evenAndOdd n (even-n , odd-n))
... | inr odd-n = refl

force-odds-false-at-true : (as : Seq Bool)
  → ∀ n → isEvenT n → force-odds-false as n ≡ as n
force-odds-false-at-true as n even-n with Nat.evenOrOdd n
... | inl _ = refl
... | inr odd-n = absurd (Nat.¬evenAndOdd n (even-n , odd-n))

force-odds-false-const : (as : Seq Bool)
  → (∀ n → as n ≡ false)
  → ∀ n → force-odds-false as n ≡ as n
force-odds-false-const as all-false n with Nat.evenOrOdd n
... | inl _ = refl
... | inr _ = sym (all-false n)

force-odds-false-const-until : (as : Seq Bool) (n : ℕ)
  → as ≤ n ⇒ (_≡ false)
  → force-odds-false as ≤ n ⇒ (_≡ false)
force-odds-false-const-until as n all-≤n-false k k≤n with Nat.evenOrOdd k
... | inl _ = all-≤n-false k k≤n
... | inr _ = refl

--- Like `latch`, but only flips to `t` on the first *even* position of `as` that is `true`.
latch-even : (as : Seq Bool) → (f t : A) → Seq A
latch-even as f t = latch f t $ force-odds-false as

latch-even-dichotomy : (as : Seq Bool) (f t : A) → Dichotomy (latch-even as f t) f t
latch-even-dichotomy as f t = latch-dichotomy _

latch-even-until' : (as : Seq Bool) → {f t : A} → ∀ n
  → (force-odds-false as) ≤ n ⇒ (_≡ false)
  → (latch-even as f t) ≤ n ⇒ (_≡ f)
latch-even-until' as = latch-until (force-odds-false as)

latch-even-until : (as : Seq Bool) → {f t : A} → ∀ n
  → as ≤ n ⇒ (_≡ false)
  → (latch-even as f t) ≤ n ⇒ (_≡ f)
latch-even-until as n all-≤n-false = latch-even-until' as n lem where
  lem : force-odds-false as ≤ n ⇒ (_≡ false)
  lem k k≤n with (Nat.evenOrOdd k)
  ... | inl _ = all-≤n-false k k≤n
  ... | inr _ = refl

force-odds-false-until : (as : Seq Bool) → (n : ℕ)
  → (∀ k → k ≤ n → isEvenT k → as k ≡ false)
  → force-odds-false as ≤ n ⇒ (_≡ false)
force-odds-false-until as n up-to k k≤n with Nat.evenOrOdd k
... | inl even-k = up-to k k≤n even-k
... | inr odd-k = refl {x = false}

--- `latch-even` is `f` up to position `n` if all even positions less than `n` are `false`.
latch-even-false-until : (as : Seq Bool) → {f t : A} → ∀ n
  → as ≤ n ⇒ (λ {k} aₖ → isEvenT k → aₖ ≡ false)
  → latch-even as f t ≤ n ⇒ (_≡ f)
latch-even-false-until as n up-to = latch-even-until' as n (force-odds-false-until as n up-to)

latch-even-at : (as : Seq Bool) → {f t : A}
  → ∀ k → isEvenT k → as k ≡ true → latch-even as f t k ≡ t
latch-even-at as k even-k asₖ≡true = latch-after (force-odds-false as) k
  (k , NatOrder.≤-refl k , (
      force-odds-false as k ≡⟨ force-odds-false-at-true as k even-k ⟩
      as k ≡⟨ asₖ≡true ⟩∎
      true ∎
    )
  )

latch-even-after : (as : Seq Bool) → {f t : A}
  → ∀ n → (∃[ k ≤ n of as ] λ aₖ → isEvenT k × (aₖ ≡ true)) → latch-even as f t n ≡ t
latch-even-after as n (k , k≤n , even-k , asₖ≡true) = latch-after (force-odds-false as) n h where
  h : TrueBefore (force-odds-false as) n
  h = k , k≤n , (
      force-odds-false as k ≡⟨ force-odds-false-at-true as k even-k ⟩
      as k                  ≡⟨ asₖ≡true ⟩∎
      true ∎
    )

--- `latch-even` is constantly `f` if any even position of `as` has value `false`.
latch-even-const : (as : Seq Bool) → {f t : A}
  → (∀ n → isEvenT n → as n ≡ false)
  → ∀ n → latch-even as f t n ≡ f
latch-even-const as evens-are-false = latch-const (force-odds-false as) lem where
  lem : ∀ n → force-odds-false as n ≡ false
  lem n with Nat.evenOrOdd n
  ... | inr odd-n = refl
  ... | inl even-n = evens-are-false n even-n

--- The same as above, but with the contrapositive of the assumption.
--- Yay, LEM 🎉🎉🎉
latch-even-const-contr : (as : Seq Bool) → {f t : A}
  → (∀ n → as n ≡ true → isOddT n)
  → ∀ n → latch-even as f t n ≡ f
latch-even-const-contr as trues-are-odd = latch-even-const as lem where
  lem : ∀ n → isEvenT n → as n ≡ false
  lem n even-n with dichotomyBool (as n)
  ... | inr asₙ≡false = asₙ≡false
  ... | inl asₙ≡true = absurd (Nat.¬evenAndOdd n (even-n , trues-are-odd n asₙ≡true))

--- If `as` is true at most once, and that happens at an odd position,
--- then `latch-even as` is constantly `f`.
latch-even-const-true-once : (as : Seq Bool) → {f t : A}
  → isProp (Σ[ k ∈ ℕ ] as k ≡ true)
  → (Σ[ k ∈ ℕ ] isOddT k × (as k ≡ true))
  → ∀ n → latch-even as f t n ≡ f
latch-even-const-true-once as prop-true (k , odd-k , asₖ≡true) = latch-even-const-contr as lem where
  lem : ∀ n → as n ≡ true → isOddT n
  lem n asₙ≡true = subst isOddT k≡n odd-k where
    k≡n : k ≡ n
    k≡n = cong fst (prop-true (k , asₖ≡true) (n , asₙ≡true))

module Old where
  data Parity : Type where
    even odd : Parity

  flip : Parity → Parity
  flip even = odd
  flip odd = even

  even? : Parity → Bool
  even? even = true
  even? odd = false

  latch-parity : Parity → (as : Seq Bool) → (f t : A) → Seq A
  latch-parity p as f t zero = if (even? p and head as) then t else f
  latch-parity p as f t (suc n) = if (even? p and head as) then t else latch-parity (flip p) (tail as) f t n

  latch-parity-dichotomy : (p : Parity) → (as : Seq Bool) (f t : A) (n : ℕ) → (latch-parity p as f t n ≡ f) ⊎ (latch-parity p as f t n ≡ t)
  latch-parity-dichotomy p as f t zero with (even? p and head as)
  ... | true = inr (refl {x = t})
  ... | false = inl (refl {x = f})
  latch-parity-dichotomy p as f t (suc n) with (even? p and head as)
  ... | true = inr (refl {x = t})
  ... | false = latch-parity-dichotomy (flip p) (tail as) f t n

  latch-unlatched : ∀ (p : Parity) (as : Seq Bool) (f t : A)
    → ∀ n → (∀ k → k ≤ n → as k ≡ false) → latch-parity p as f t n ≡ f
  latch-unlatched p as f t zero ≤n→≡false with (≤n→≡false 0 _)
  ... | r with (as 0) | p
  ... | false | odd = refl {x = f}
  ... | false | even = refl {x = f}
  ... | true | odd = refl {x = f}
  ... | true | even = absurd (true≢false r)
  latch-unlatched p as f t (suc n) ≤n→≡false with (≤n→≡false 0 _)
  ... | r with (as 0) | p
  ... | false | odd = latch-unlatched even (as ∘ suc) f t n (λ k le → ≤n→≡false (suc k) le)
  ... | false | even = latch-unlatched odd (as ∘ suc) f t n (λ k le → ≤n→≡false (suc k) le)
  ... | true | odd = latch-unlatched even (as ∘ suc) f t n (λ k le → ≤n→≡false (suc k) le)
  ... | true | even = Empty.rec (true≢false r)

  latch-even' : (as : ℕ → Bool) → (f t : A) → Seq A
  latch-even' = latch-parity even

  latch-odd : (as : ℕ → Bool) → (f t : A) → Seq A
  latch-odd = latch-parity odd

  latch-even'≡latch-even : (as : Seq Bool) (f t : A) → latch-even' as f t ≡ latch-even as f t
  latch-even'≡latch-even as f t = funExt (ptwise as) where
    ptwise : ∀ as n → latch-even' as f t n ≡ latch-even as f t n
    ptwise as zero with head as
    ... | false = refl
    ... | true = refl
    ptwise as (suc 0) with head as
    ... | false = subst⁻ (λ b → (if b then t else f) ≡ f) (and-falseˡ (as 1)) (refl {x = f})
    ... | true = refl
    ptwise as (suc (suc n)) with head as
    ... | false =
      (if false and as 1 then t else _) ≡⟨ if-false (and-falseˡ (as 1)) ⟩
      latch-even' (as ∘ suc ∘ suc) f t n ≡⟨ ptwise (as ∘ suc ∘ suc) n ⟩
      latch-even (as ∘ suc ∘ suc) f t n ∎
    ... | true = refl
