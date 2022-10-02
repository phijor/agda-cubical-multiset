------------------------------------------------------------------------
-- The Agda standard library
--
-- Sizes for Agda's sized types
------------------------------------------------------------------------

{-# OPTIONS --without-K --sized-types #-}

module Multiset.Coinductive.Size where


------------------------------------------------------------------------
-- Re-export builtins

open import Agda.Builtin.Size public using
  ( SizeUniv  --  sort SizeUniv
  ; Size      --  : SizeUniv
  ; Size<_    --  : Size → SizeUniv
  ; ↑_        --  : Size → Size
  ; _⊔ˢ_      --  : Size → Size → Size
  ; ∞         --  : Size
  )

------------------------------------------------------------------------
-- Concept of sized type

SizedSet : ∀ ℓ → Set _
SizedSet ℓ = Size → Set ℓ
