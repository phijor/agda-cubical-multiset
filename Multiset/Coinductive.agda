{-# OPTIONS --sized-types #-}

module Multiset.Coinductive where

open import Multiset.Prelude
open import Multiset.Coinductive.Setoid using (anaMSEq ; anaMSUniq)

private
  open import Cubical.Foundations.Equiv using (_≃_)
  open import Cubical.HITs.PropositionalTruncation using (∥_∥₁)

  open import Multiset.ListQuotient.Base using () renaming (M to List[_]/Relator≡ ; mapM to List/Relator≡-map)
  open import Multiset.Coinductive.Trees as Trees
    using  (M-νM-FixpointEquiv ; νM→MνM)
    renaming (νM to LimList/Bisim)

  -- (LimList , Bisim) has a final FMSetoid coalgebra in setoids.
  Theorem5ExistsAna = anaMSEq
  Theorem5Uniqeness = anaMSUniq

  -- LimList/Bisim is a fixed point
  Theorem6 : List[ LimList/Bisim ]/Relator≡ ≃ LimList/Bisim
  Theorem6 = Trees.M-νM-FixpointEquiv

  -- Assuming choice, LimList/Bisim is a final coalgebra.
  module Theorem7
    (ac : {A : Type} {B : A → Type}
      → (R : (a : A) → B a → Type)
      → isSet A → (∀ a → isSet (B a)) → (∀ a b → isProp (R a b))
      → ((a : A) → ∥ (Σ[ b ∈ B a ] R a b ) ∥₁)
      → ∥ Σ[ f ∈ ((a : A) → B a) ] ((a : A) → R a (f a)) ∥₁)
    (X : Type)
    (setX : isSet X)
    where
    isFinalCoalgebraLimList/Bisim : (c : X → List[ X ]/Relator≡)
      → isContr (Σ[ f ∈ (X → LimList/Bisim) ] (∀ x → νM→MνM (f x) ≡ List/Relator≡-map f (c x)))
    isFinalCoalgebraLimList/Bisim = Trees.isContrAna ac X setX
