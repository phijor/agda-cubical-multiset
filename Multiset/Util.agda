module Multiset.Util where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.GroupoidLaws hiding (_⁻¹)
open import Cubical.Foundations.Structure
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Function
open import Cubical.Foundations.Univalence using (ua)

open import Cubical.Data.Empty as Empty using (⊥)

private
  variable
    ℓ : Level
    A : Type ℓ


ua→cong : ∀ {ℓ ℓ' ℓ''} {A₀ A₁ : Type ℓ} {e : A₀ ≃ A₁}
  {B : (i : I) → Type ℓ'}
  {C : (i : I) → Type ℓ''}
  {f₀ : A₀ → B i0} {f₁ : A₁ → B i1}
  (F : {i : I} → B i → C i)
  (p : PathP (λ i → ua e i → B i) f₀ f₁)
  → PathP (λ i → ua e i → C i) (F {i0} ∘ f₀) (F {i1} ∘ f₁)
ua→cong F p = λ i x → F (p i x)

module _ {ℓ' : Level} {Y : ⊥ → Type ℓ'} where
  isPropΠ⊥ : isProp ((k : ⊥) → Y k)
  isPropΠ⊥ = isContr→isProp Empty.isContrΠ⊥

  Π⊥≡elim : (v : (k : ⊥) → Y k) → Empty.elim ≡ v
  Π⊥≡elim v _ ()

module _ {X Y : Type ℓ} (p : X ≡ Y) where abstract
  open import Cubical.Foundations.Equiv
    using
      ( invEquiv
      ; idEquiv
      ; invEquivIdEquiv
      ; compEquivEquivId
      )
    renaming
      (compEquiv to _∘≃_)
  open import Cubical.Foundations.Univalence
    using
      ( pathToEquiv
      ; pathToEquivRefl
      )
  import Cubical.Foundations.GroupoidLaws as GpdLaws

  -- TODO: This is not needed anymore, but keep it for later.
  -- It's a useful lemma.
  pathToEquivSymRefl : pathToEquiv (sym (refl {x = X})) ≡ invEquiv (pathToEquiv refl)
  pathToEquivSymRefl =
    pathToEquiv (sym refl)
      ≡⟨ pathToEquivRefl ⟩
    idEquiv _
      ≡⟨ sym (invEquivIdEquiv _) ⟩
    invEquiv (idEquiv _)
      ≡⟨ sym (cong invEquiv pathToEquivRefl) ⟩
    invEquiv (pathToEquiv refl)
      ∎

  pathToEquivSym : pathToEquiv (sym p) ≡ invEquiv (pathToEquiv p)
  pathToEquivSym = J (λ Y' p' → pathToEquiv (sym p') ≡ invEquiv (pathToEquiv p')) pathToEquivSymRefl p

  pathToEquivCompRefl : pathToEquiv (p ∙ refl) ≡ (pathToEquiv p ∘≃ pathToEquiv refl)
  pathToEquivCompRefl =
    pathToEquiv (p ∙ refl)
      ≡⟨ cong pathToEquiv (sym (GpdLaws.rUnit p)) ⟩
    pathToEquiv p
      ≡⟨ sym (compEquivEquivId (pathToEquiv p)) ⟩
    (pathToEquiv p ∘≃ idEquiv Y)
      ≡⟨ cong (pathToEquiv p ∘≃_) (sym pathToEquivRefl) ⟩
    (pathToEquiv p ∘≃ pathToEquiv refl)
      ∎

  pathToEquivComp : {Z : Type ℓ} (q : Y ≡ Z) → pathToEquiv (p ∙ q) ≡ pathToEquiv p ∘≃ pathToEquiv q
  pathToEquivComp = J (λ Z' q' → pathToEquiv (p ∙ q') ≡ pathToEquiv p ∘≃ pathToEquiv q') pathToEquivCompRefl

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

module Conjugate {ℓ' : Level} {K : Type ℓ'} (isSetK≃K : isSet (K ≃ K)) where
  open import Cubical.Foundations.Univalence
  import Cubical.HITs.PropositionalTruncation as Prop
  open import Cubical.Foundations.Equiv
    renaming
      ( compEquiv to infixl 4 _∙≃_
      ; invEquiv to infix 40 _⁻¹
      )

  open Prop

  conjugate′ : A ≃ K → A ≃ A → K ≃ K
  conjugate′ ε α = (ε ⁻¹) ∙≃ α ∙≃ ε

  is2ConstantConjugate : (α : A ≃ A) (ε η : A ≃ K) → conjugate′ ε α ≡ conjugate′ η α
  is2ConstantConjugate α ε η = {!   !}

  conjugate : ∥ A ≃ K ∥₁ → A ≃ A → K ≃ K
  conjugate ∣ε∣ α = rec→Set isSetK≃K (λ ε → conjugate′ ε α) (is2ConstantConjugate α) ∣ε∣

open Conjugate public

module CounterExample where
  open import Cubical.Foundations.Isomorphism
  open import Cubical.Data.SumFin
  open import Cubical.Data.Empty
  open import Cubical.Algebra.SymmetricGroup
  open import Cubical.Relation.Nullary.Base

  open Conjugate {K = Fin 3} (isOfHLevel≃ 2 isSetFin isSetFin) renaming (conjugate′ to conj)



  -- ⎛ 0 1 2 ⎞
  -- ⎝ 0 2 1 ⎠
  α-fun : Fin 3 → Fin 3
  α-fun fzero = fzero
  α-fun (fsuc fzero) = fsuc (fsuc fzero)
  α-fun (fsuc (fsuc fzero)) = fsuc fzero

  α : Fin 3 ≃ Fin 3
  α = isoToEquiv (iso α-fun α-fun α-inv α-inv) where
    α-inv : ∀ k → α-fun (α-fun k) ≡ k
    α-inv (inl x) = refl
    α-inv (fsuc (inl x)) = refl
    α-inv (fsuc (fsuc (inl x))) = refl

  -- ⎛ 0 1 2 ⎞
  -- ⎝ 1 0 2 ⎠
  η-fun : Fin 3 → Fin 3
  η-fun fzero = fsuc fzero
  η-fun (fsuc fzero) = fzero
  η-fun (fsuc (fsuc fzero)) = (fsuc (fsuc fzero))

  η : Fin 3 ≃ Fin 3
  η = isoToEquiv (iso η-fun η-fun η-inv η-inv) where
    η-inv : ∀ k → η-fun (η-fun k) ≡ k
    η-inv fzero = refl
    η-inv (fsuc fzero) = refl
    η-inv (fsuc (fsuc fzero)) = refl

  counterExample : ¬ (conj α (idEquiv _) ≡ conj α η)
  counterExample ch = not-that that where
    that : fzero ≡ fsuc (fsuc fzero)
    that = funExt⁻ (cong fst ch) ((fzero))

    not-that : ¬ (fzero ≡ fsuc (fsuc fzero))
    not-that = SumFin≡≃ 3 fzero (fsuc (fsuc fzero)) .fst
