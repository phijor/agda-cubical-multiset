module Multiset.Util where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.GroupoidLaws
open import Cubical.Foundations.Structure

private
  variable
    ℓ : Level
    A : Type ℓ

-- Square t b l r

-- A square
-- a ==== a
-- ∥      |
-- ∥      v p
-- a ---> b
--    p
⌜_ : {a b : A} (p : a ≡ b) → Square refl p refl p
⌜_ p i j = p (i ∧ j)

⌜~_ : {a b : A} (p : a ≡ b) → Square refl (sym p) refl (sym p)
⌜~_ p = ⌜ (sym p)

square-comp-horizontal : {aₗ aₘ aᵣ bₗ bₘ bᵣ : A}
  {vₗ : aₗ ≡ bₗ} {vₘ : aₘ ≡ bₘ} {vᵣ : aᵣ ≡ bᵣ}
  {pₗ : aₗ ≡ aₘ} {pᵣ : aₘ ≡ aᵣ}
  {qₗ : bₗ ≡ bₘ} {qᵣ : bₘ ≡ bᵣ}
  (left  : Square pₗ qₗ vₗ vₘ)
  (right : Square pᵣ qᵣ vₘ vᵣ)
  → Square (pₗ ∙ pᵣ) (qₗ ∙ qᵣ) vₗ vᵣ
square-comp-horizontal
  {A = A}
  {vₗ = vₗ} {vₘ = vₘ} {vᵣ = vᵣ}
  {pₗ = pₗ} {pᵣ = pᵣ}
  {qₗ = qₗ} {qᵣ = qᵣ}
  left right j i = hcomp (λ k → faces k j i) (base j i) where
  base = left

  face-bot : Square pₗ (pₗ ∙ pᵣ) refl pᵣ
  face-bot = compPath-filler pₗ pᵣ

  face-top : Square qₗ (qₗ ∙ qᵣ) refl qᵣ
  face-top = compPath-filler qₗ qᵣ

  face-left : Square vₗ vₗ refl refl
  face-left j i = vₗ i

  face-right : Square vₘ vᵣ pᵣ qᵣ
  face-right j i = right i j

  faces : (k j i : I) → Partial (~ j ∨ j ∨ ~ i ∨ i) A
  faces k j i (j = i0) = face-bot k i -- bottom
  faces k j i (j = i1) = face-top k i -- top
  faces k j i (i = i0) = face-left k j -- left
  faces k j i (i = i1) = face-right k j -- right

-- Filler for the square
--
--  a ∙∙∙∙∙ A
--  ∥       |
--  ∥       p
--  ∥       v
--  a --r-> c
comp-filler' : {a b c : A} (r : a ≡ c) (p : b ≡ c)
  → Square {A = A} r (r ∙ sym p) refl (sym p)
comp-filler' r p = compPath-filler r (sym p)

-- Filler for the square
--
--  a ===== A
--  |       |
--  r       |
--  |       r
-- ~p       |
--  |       |
--  b --p-- c
comp-filler : {a b c : A} (r : a ≡ c) (p : b ≡ c)
  → Square {A = A} refl p (r ∙ sym p) r
comp-filler {A = A} {a = a} r p = λ j i → comp-filler' r p (~ i) (j)

filler-comp-refl-top = comp-filler

square-comp-vertical : {aₗ aᵣ bₗ bᵣ cₗ cᵣ : A}
  {pₗ : aₗ ≡ bₗ} {pᵣ : aᵣ ≡ bᵣ}
  {qₗ : bₗ ≡ cₗ} {qᵣ : bᵣ ≡ cᵣ}
  {hₜ : aₗ ≡ aᵣ} {hₘ : bₗ ≡ bᵣ} {hₛ : cₗ ≡ cᵣ}
  (top : Square hₜ hₘ pₗ pᵣ)
  (bot : Square hₘ hₛ qₗ qᵣ)
  → Square hₜ hₛ (pₗ ∙ qₗ) (pᵣ ∙ qᵣ)
square-comp-vertical top bot i j = {!  bot ∙ top !}

private
  variable
    ℓ' ℓX ℓY : Level

MapOfStr : (S : {ℓ : Level} → Type ℓ → Type ℓ') → (X : TypeWithStr ℓX S) → (Y : TypeWithStr ℓY S) → Type (ℓ-max ℓX ℓY)
MapOfStr _ X Y = ⟨ X ⟩ → ⟨ Y ⟩

map-syntax : (S : {ℓ : Level} → Type ℓ → Type ℓ') → (X : TypeWithStr ℓX S) → (Y : TypeWithStr ℓY S) → Type (ℓ-max ℓX ℓY)
map-syntax = MapOfStr

_→ₛ_ : {S : {ℓ : Level} → Type ℓ → Type ℓ'} (X : TypeWithStr ℓX S) → (Y : TypeWithStr ℓY S) → Type (ℓ-max ℓX ℓY)
X →ₛ Y = ⟨ X ⟩ → ⟨ Y ⟩

infixr 6 _→ₛ_

syntax map-syntax S X Y = X →ₛ[ S ] Y
