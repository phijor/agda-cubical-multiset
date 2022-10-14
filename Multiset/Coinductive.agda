{-# OPTIONS --sized-types #-}

module Multiset.Coinductive where

open import Multiset.Coinductive.FinCoalg
open import Multiset.Coinductive.Trees
open import Multiset.Coinductive.Setoid

private
  open import Cubical.Foundations.Equiv using (_≃_)
  open import Multiset.ListQuotient.Base using () renaming (M to FMSet)
  open import Multiset.Coinductive.Trees as Trees
    using  (M-νM-FixpointEquiv)
    renaming (νM to LimList/Bisim)

  -- (LimList , Bisim) has a final FMSetoid coalgebra in setoids.
  Theorem5ExistsAna = anaMSEq
  Theorem5Uniqeness = anaMSUniq

  -- LimList/Bisim is a fixed point
  Theorem6 : FMSet LimList/Bisim ≃ LimList/Bisim
  Theorem6 = Trees.M-νM-FixpointEquiv

  -- Assuming choice, LimList/Bisim is a final coalgebra.
  Theorem7 = Trees.anaM
