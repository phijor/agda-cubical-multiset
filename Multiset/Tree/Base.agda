module Multiset.Tree.Base where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Data.Nat
open import Cubical.Data.Unit
open import Cubical.Data.Sigma

open import Multiset.Inductive.Base renaming (map to mapM)
open import Multiset.Limits

-- Iterated application of the Multiset functor.
--
-- We introduce a syntax notation for this where
-- `M[ n ] X = iterM n X`, which mimics the functorial
-- action Mⁿ(X) on some set X.
iterM : {ℓ : Level} → ℕ → Type ℓ → Type ℓ
iterM zero X = X
iterM (suc n) X = M (iterM n X)

syntax iterM n X = M[ n ] X

-- Assuming `X` is a set, iterated multisets over `X` are sets, too.
isSet-iterM : {X : Type} → (isSet X)
  → (n : ℕ) → isSet (M[ n ] X)
isSet-iterM isSetX zero = isSetX
isSet-iterM {X} isSetX (suc n) =
  let isSetIterM : isSet (M (M[ n ] X))
      isSetIterM = trunc in
  isSetIterM

-- In particular, Mⁿ(∗) is a set for the singleton set ∗ (called Unit here).
isSet-iterMUnit : (n : ℕ) → isSet (iterM n Unit)
isSet-iterMUnit = isSet-iterM isSetUnit

-- Repeated functorial action of M on the terminal map !∶ X → ∗.
-- Here, `iter! n` is Mⁿ(!).
iter! : (n : ℕ) → iterM (suc n) Unit → iterM n Unit
iter! zero x = tt
iter! (suc n) x = mapM (iter! n) x

-- Iterating ! yields an ω-cochain
--
--  ⋆ ← M(⋆) ← M²(∗) ← ...
!-ωCochain : ωCochain
!-ωCochain = record
  { ob = λ n → M[ n ] Unit
  ; ∂ = iter!
  }

-- The type of well founded, finitely branching (?) trees.
--
-- An element T of this type is a family { T(n) }ₙ of nested
-- multisets of depth n for each n : ℕ, together with a proof
-- that cutting the leaves of T(n+1) results in T(n).
--
-- We will show later that this type is a limit over the above cochain.
ωTree : Type
ωTree =
  Σ[ level ∈ ((n : ℕ) → iterM n Unit) ]
    ((n : ℕ) → iter! n (level (suc n)) ≡ level n)

-- Nice names for the levels T(n) of a tree T, and the cutting properties.
level : ωTree → (n : ℕ) → iterM n Unit
level = fst

cut : (t : ωTree) → (n : ℕ) → (iter! n (level t (suc n)) ≡ level t n)
cut = snd

-- For some tree T, each level T(n) is a set...
isSet-ωTree-level : isSet ((n : ℕ) → iterM n Unit)
isSet-ωTree-level = isSetΠ isSet-iterMUnit

-- ...and the cutting property is a propostion.
isProp-ωTree-cut : (level : (n : ℕ) → iterM n Unit) → isProp ((n : ℕ) → iter! n (level (suc n)) ≡ level n)
isProp-ωTree-cut level = isPropΠ (λ n → isSet-iterMUnit n (iter! n (level (suc n))) (level n))

-- This means that in total, any such tree is a set.
isSet-ωTree : isSet ωTree
isSet-ωTree = isSetΣ
  (isSet-ωTree-level)
  λ level → isProp→isOfHLevelSuc 1 (
    isProp-ωTree-cut level
  )
