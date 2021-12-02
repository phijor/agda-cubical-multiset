-- Define the finite multiset functor M (HITs)
-- Define the ω-chain 1 <- M 1 <- M (M 1) <- ...
-- Construct the limit L
-- Prove that L is the final coalgebra of M
-- Look at other ways of constructing the final coalgebra (coinductive types)

module Multiset.Multiset where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Data.Nat
open import Cubical.Data.Unit
open import Cubical.Data.Sigma

open import Multiset.Base renaming (map to mapM)
open import Multiset.Limits

-- Iterated application of the Multiset functor.
--
-- We introduce a syntax notation for this where
-- `M[ n ] X = iterM n X`, which mimics the functorial
-- action Mⁿ(X) on some set X.
iterM : ℕ → Type → Type
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


open module MCone = Multiset.Limits.ωCone !-ωCochain

-- To show that ωTree is a limit of the !-cochain,
-- we must construct a cone with it at the apex...
Lim : ωCone
Lim = record
  { Apex = ωTree
  ; leg = λ n (level , _) → level n
  ; cond = λ n (_ , cut) → cut n
  }

-- ...and show that this cone is terminal.
-- We get a function into ωTree for free for any other cone V:
Lim-map : (V : ωCone) → V .Apex → ωTree
Lim-map V v = (λ n → V .leg n v) , λ n → V .cond n v


-- This map is trivially a cone map.
Lim-up-∃ : (V : ωCone) → ωConeMap V Lim
Lim-up-∃ V = record
  { map = Lim-map V
  ; commutes = λ n v → refl
  }

-- Indeed, it is also equal to any other map into the limit.
Lim-up-!-map : (V : ωCone) (f : ωConeMap V Lim)
  → Lim-map V ≡ f .map
Lim-up-!-map V f = funExt (λ v → Σ≡Prop isProp-ωTree-cut (funExt λ n → sym (f .commutes n v)))

-- Since equality of cone maps is a proposition when the chain
-- consists of sets, we can show that this extends to an equality
-- of cone maps proper. 
Lim-up-! : (V : ωCone) (f : ωConeMap V Lim)
  → Lim-up-∃ V ≡ f
Lim-up-! V f = ωConeMap≡Prop (isSet-iterM isSetUnit) (Lim-up-!-map V f)

-- Since we have both existence and uniqueness of a final cone map,
-- this concludes the proof that ω-Trees form a limit over the !-chain.
Lim-is-Limit : is-Limit Lim
Lim-is-Limit V = (Lim-up-∃ V) , (Lim-up-! V)
   