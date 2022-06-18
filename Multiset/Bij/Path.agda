module Multiset.Bij.Path where

open import Multiset.Bij.Base as Bij

open import Multiset.Util.Square
  using
    ( ΣSquareP
    ; ΣSquarePProp
    )
open import Multiset.Util.Equiv
  using
    ( postComp
    ; postCompIdEquiv
    ; postCompCompEquiv
    )

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Equiv.Properties
open import Cubical.Foundations.Path using (PathP≡doubleCompPathʳ)
open import Cubical.Foundations.Univalence
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.GroupoidLaws using (cong-∙)
open import Cubical.Foundations.Function using (_∘_ ; flip ; idfun)

open import Cubical.Foundations.Structure
open import Cubical.Syntax.⟨⟩

open import Cubical.Functions.FunExtEquiv
  using (funExtDep)

open import Cubical.Data.Sigma as Sigma
  using (Σ≡Prop ; ΣPathP ; ΣPathPProp)
open import Cubical.Data.Nat as ℕ
  using (ℕ)
open import Cubical.Data.SumFin as Fin
  using (Fin)

hSet₀ : Type₁
hSet₀ = hSet ℓ-zero

module _ (s t : ℕ) where
  isSetFin≃ : isSet (Fin s ≃ Fin t)
  isSetFin≃ = isOfHLevel≃ 2 (Fin.isSetFin) (Fin.isSetFin)

  Fin≃ : hSet₀
  Fin≃ = (Fin s ≃ Fin t) , isSetFin≃

Fin≃Path : ∀ {s t : ℕ} (m : ℕ) → Fin s ≃ Fin t → Fin≃ s m ≡ Fin≃ t m
Fin≃Path {s} {t} m α = TypeOfHLevel≡ 2 path where
  path : (Fin s ≃ Fin m) ≡ (Fin t ≃ Fin m)
  path = cong (_≃ Fin m) (ua α)

Fin≃PathId : (m n : ℕ) → Fin≃Path m (idEquiv (Fin n)) ≡ refl {x = Fin≃ n m}
Fin≃PathId m n = ΣSquarePProp (λ _ → isPropΠ2 (λ _ _ → isPropIsProp)) (cong (cong (_≃ Fin m)) uaIdEquiv)

Fin≃PathComp : ∀ {m n o : ℕ} (k : ℕ)
  → (α : Fin m ≃ Fin n)
  → (β : Fin n ≃ Fin o) →
      Fin≃Path k (α ∙ₑ β) ≡ Fin≃Path k α ∙ Fin≃Path k β
Fin≃PathComp k α β = ΣSquarePProp ((λ _ → isPropΠ2 (λ _ _ → isPropIsProp)))
  ( cong (_≃ Fin k) (ua (α ∙ₑ β)) ≡⟨ cong (cong (_≃ Fin k)) (uaCompEquiv α β) ⟩
    cong (_≃ Fin k) (ua α ∙ ua β) ≡⟨ cong-∙ (_≃ Fin k) (ua α) (ua β) ⟩
    cong (_≃ Fin k) (ua α) ∙ cong (_≃ Fin k) (ua β) ∎
  )

Code : ℕ → Bij → hSet₀
Code m = rec (isOfHLevelTypeOfHLevel 2)
  (flip Fin≃ m)
  (Fin≃Path m)
  (Fin≃PathId m)
  (Fin≃PathComp m)

isSetCode : ∀ {m} {x} → isSet ⟨ Code m x ⟩
isSetCode {m = m} {x} = str (Code m x)

encode : {n : ℕ} → {x : Bij} → obj n ≡ x → ⟨ Code n x ⟩
encode {n = n} p = subst (λ x → ⟨ Code n x ⟩) p (idEquiv (Fin n))

encodeRefl : ∀ {n} → encode {x = obj n} refl ≡ idEquiv (Fin n)
encodeRefl {n = n} = substRefl {B = λ x → ⟨ Code n x ⟩} {x = obj n} (idEquiv (Fin n))

decode : {m : ℕ} → (x : Bij) → ⟨ Code m x ⟩ → obj m ≡ x
decode {m = m} = elimSet (λ _ → isOfHLevelΠ 2 λ _ → isSetBijPath) (obj* m) (hom* m) where
  -- NOTE: This is contravariant so that
  --    PathP (λ i → ⟨ Code m (hom α i) ⟩) β₀ β₁
  -- reduces to a path of equivalences with ua in their domain.
  -- This way, we can use `ua→` to extract a commutative
  -- triangle of equivalences (see `commutesPointwise`).
  obj* : (m n : ℕ) → Fin n ≃ Fin m → obj m ≡ obj n
  obj* m n α = sym (hom α)

  hom* : ∀ {n₀ n₁ : ℕ} (m : ℕ)
    → (α : Fin n₀ ≃ Fin n₁)
    → PathP (λ j → ⟨ Code m (hom α j) ⟩ → obj m ≡ hom α j) (obj* m n₀) (obj* m n₁)
  hom* {n₀ = n₀} {n₁ = n₁} m α = funExtDep goal where
    module _ {β₀ : Fin n₀ ≃ Fin m} {β₁ : Fin n₁ ≃ Fin m} (p : PathP (λ i → ⟨ Code m (hom α i) ⟩) β₀ β₁) where abstract

      -- From `p`, we can deduce that there is a commutative triangle of equivalences:
      --
      --            α
      --  Fin n₀ -------> Fin n₁
      --    |               |
      -- β₀ |               | β₁
      --    |               |
      --    '---> Fin m <---'
      commutesPointwise : ∀ (k : Fin n₀) → equivFun β₀ k ≡ equivFun β₁ (equivFun α k)
      commutesPointwise = ua→⁻ (congP (λ _ → equivFun) p)

      commutes : β₀ ≡ α ∙ₑ β₁
      commutes = equivEq (funExt commutesPointwise)

      -- Using `comp-coh`, this lifts to `hom`s in `Bij`.
      -- NOTE: We use (_∙'_) here so that the following
      -- steps become easier.
      coh-commutes : hom β₀ ≡ hom α ∙' hom β₁
      coh-commutes =
        hom β₀                  ≡⟨ cong hom commutes ⟩
        hom (α ∙ₑ β₁)           ≡⟨ comp-coh α β₁ ⟩
        hom α ∙ hom β₁          ≡⟨ compPath≡compPath' _ _ ⟩
        hom α ∙' hom β₁         ≡⟨⟩
        hom α ∙∙ hom β₁ ∙∙ refl ∎

      -- The above coherence law can be translated back into
      -- a Square, as required by the goal.
      coh-sq : Square (hom β₀) (hom β₁) (hom α) (refl {x = obj m})
      coh-sq = transport (sym (PathP≡doubleCompPathʳ (hom α) (hom β₀) (hom β₁) refl)) coh-commutes

      -- Since `obj*` is defined contravariantly, the goal is
      -- `coh-sq`, but mirrored horizontally.  This way, the
      -- top and bottom of the square become
      --   (obj* _ _ βₓ) ≡ sym (hom βₓ)
      -- for βₓ ∈ { β₀, β₁ }.
      goal : Square (obj* _ _ β₀) (obj* _ _ β₁) (refl {x = obj m}) (hom α)
      goal = λ i j → coh-sq i (~ j)

decodeIdEquiv : ∀ {n} → decode (obj n) (idEquiv (Fin n)) ≡ refl
decodeIdEquiv {n = n} =
  decode (obj n) (idEquiv (Fin n)) ≡⟨⟩
  sym (hom (idEquiv (Fin n)))      ≡⟨ cong sym (id-coh n) ⟩
  sym refl                         ≡⟨⟩
  refl ∎

decode∘encodeRefl : ∀ {n} → decode (obj n) (encode refl) ≡ refl
decode∘encodeRefl {n = n} =
  decode (obj n) (encode refl) ≡⟨ cong (decode (obj n)) encodeRefl ⟩
  decode (obj n) (idEquiv _)   ≡⟨ decodeIdEquiv ⟩
  refl ∎

decode∘encode : ∀ {n} {x : Bij} (p : obj n ≡ x) → decode x (encode p) ≡ p
decode∘encode {n} {x = x} = elimProp {P = λ x → (p : obj n ≡ x) → decode x (encode p) ≡ p} propP obj* x where
  propP : ∀ x → isProp ((p : obj n ≡ x) → decode x (encode p) ≡ p)
  propP x = isPropΠ (λ p → isGroupoidBij _ _ (decode x (encode p)) p)

  obj* : ∀ m (p : obj n ≡ obj m) → decode (obj m) (encode p) ≡ p
  obj* m = J (λ x (p : obj n ≡ x) → decode x (encode p) ≡ p) decode∘encodeRefl

encode∘decodeIdEquiv : ∀ {m} → encode (decode (obj m) (idEquiv (Fin m))) ≡ idEquiv (Fin m)
encode∘decodeIdEquiv {m = m} =
  encode (decode (obj m) (idEquiv (Fin m))) ≡⟨ cong encode decodeIdEquiv ⟩
  encode refl                               ≡⟨ encodeRefl ⟩
  idEquiv (Fin m)                           ∎

encode∘decode : ∀ {m} {x}
  → (α : ⟨ Code m x ⟩)
  → encode (decode x α) ≡ α
encode∘decode {m = m} {x = x} = elimProp {P = λ x → (α : ⟨ Code m x ⟩) → encode (decode x α) ≡ α} propP obj* x where
  propP : ∀ x → isProp ((α : ⟨ Code m x ⟩) → encode (decode x α) ≡ α)
  propP x = isPropΠ λ α → isSetCode {m = m} {x = x} (encode (decode x α)) α

  module _ (n : ℕ) (α : Fin n ≃ Fin m) where
    equivFunPath : PathP (λ j → ua α j → Fin m) (equivFun α) (idfun _)
    equivFunPath = ua→ (λ k → refl)

    equivPath : PathP (λ j → ua α j ≃ Fin m) α (idEquiv (Fin m))
    equivPath = ΣPathPProp (λ _ → isPropIsEquiv _) equivFunPath

    obj* : encode (decode (obj n) α) ≡ α
    obj* =
      encode (decode (obj n) α) ≡⟨⟩
      transport (λ j → ua α (~ j) ≃ Fin m) (idEquiv (Fin m)) ≡⟨ fromPathP (symP {A = λ j → ua α (~ j) ≃ Fin m} equivPath) ⟩
      α ∎

open Iso

BijPathFin≃Iso : ∀ {m n} → Iso (obj m ≡ obj n) (Fin n ≃ Fin m)
BijPathFin≃Iso {m = m} {n = n} = iso′ where
  iso′ : Iso _ _
  iso′ .fun = encode
  iso′ .inv = decode {m = m} (obj n)
  iso′ .rightInv = encode∘decode {m = m} {x = obj n}
  iso′ .leftInv = decode∘encode

BijPath≃Fin≃ : ∀ {m n} → (obj m ≡ obj n) ≃ (Fin n ≃ Fin m)
BijPath≃Fin≃ = isoToEquiv BijPathFin≃Iso
