{-# OPTIONS --safe #-}

module Multiset.FMSet.Base where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv as Equiv
  using
    ( _≃_
    )
open import Cubical.Foundations.Univalence as Univalence
  using
    ( ua
    )
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Function
  using
    ( _∘_
    )

open import Cubical.Data.Sigma as Σ
  using
    ( ΣPathP
    ; ∃
    ; ∃-syntax
    )
open import Cubical.Data.Nat as ℕ
  using
    ( ℕ
    ; suc
    ; _+_
    )
open import Cubical.Data.SumFin as Fin

open import Cubical.HITs.SetQuotients as SQ
  renaming
    ( _/_ to _/₂_
    ; eq/ to eq/₂
    ; [_] to [_]₂
    )
import Cubical.HITs.PropositionalTruncation as PT
open import Cubical.Relation.Binary as BinRel
  using
    ( Rel
    )

open import Multiset.Util using (Path→cong)

private
  variable
    ℓ ℓ' : Level
    X : Type ℓ

SymmetricAction : (n : ℕ) → Rel (Fin n → X) (Fin n → X) _
SymmetricAction {X = X} n v w = ∃[ σ ∈ (Fin n ≃ Fin n) ] PathP (λ i → (ua σ i → X)) v w

_∼_ : {n : ℕ} → (v w : Fin n → X) → Type _
v ∼ w = SymmetricAction _ v w

infix 4 _∼_

∼cong : ∀ {ℓ''} {Y : Type ℓ''}  {n : ℕ} {v w : Fin n → X}
  → (f : X → Y)
  → (v ∼ w)
  → (f ∘ v) ∼ (f ∘ w)
∼cong f = PT.map (λ (σ , v∼w) → σ , (Path→cong f v∼w))

PVect : Type ℓ → ℕ → Type ℓ
PVect X n = (Fin n → X) /₂ SymmetricAction n

FMSet : Type ℓ → Type ℓ
FMSet X = Σ[ n ∈ ℕ ] PVect X n

⟅_⟆ : ∀ {sz} → PVect X sz → FMSet X
⟅_⟆ {sz = sz} v = sz , v

open Σ.Σ renaming (fst to size ; snd to members) public
