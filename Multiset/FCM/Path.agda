module Multiset.FCM.Path where

open import Multiset.Prelude
open import Multiset.FCM.Base as M

open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Function using (_∘_)
open import Cubical.Foundations.HLevels
open import Cubical.HITs.PropositionalTruncation as PT
  using
    ( ∥_∥₁
    ; ∣_∣₁
    )

open import Cubical.Functions.Logic as Logic

infix 4 _≈′_ _≈_

data _≈′_ {ℓ} {X : Type ℓ} : M X → M X → Type ℓ where
  ε-refl : ε ≈′ ε
  η-refl : ∀ x → η x ≈′ η x
  ⊕-congʳ : ∀ xs {ys zs}
    → (ys ≈′ zs)
    → (xs ⊕ ys) ≈′ (xs ⊕ zs)
  ⊕-split : ∀ {xs ys zs ws as bs cs ds}
    → xs ≈′ as ⊕ bs
    → ys ≈′ cs ⊕ ds
    → zs ≈′ as ⊕ cs
    → ws ≈′ bs ⊕ ds
    → xs ⊕ ys ≈′ zs ⊕ ws

≈′-elim : ∀ {ℓ ℓ'} {X : Type ℓ} {B : ∀ {xs ys : M X} → xs ≈′ ys → Type ℓ'}
  → (B ε-refl)
  → (∀ x → B (η-refl x))
  → (∀ xs {ys zs} → (p : ys ≈′ zs) → B (⊕-congʳ xs p))
  → ( ∀ {xs ys zs ws as bs cs ds}
    → (p₁ : xs ≈′ as ⊕ bs)
    → (p₂ : ys ≈′ cs ⊕ ds)
    → (p₃ : zs ≈′ as ⊕ cs)
    → (p₄ : ws ≈′ bs ⊕ ds)
    → B (⊕-split p₁ p₂ p₃ p₄)
    )
  → ∀ {xs ys} → (p : xs ≈′ ys) → B p
≈′-elim {B = B} ε-refl* η-refl* ⊕-congʳ* ⊕-split* = go where
  go : ∀ {xs ys} → (p : xs ≈′ ys) → B p
  go ε-refl = ε-refl*
  go (η-refl x) = η-refl* x
  go (⊕-congʳ xs p) = ⊕-congʳ* xs p
  go (⊕-split p₁ p₂ p₃ p₄) = ⊕-split* p₁ p₂ p₃ p₄

_≈_ : ∀ {ℓ} {X : Type ℓ} → M X → M X → Type ℓ
xs ≈ ys = ∥ xs ≈′ ys ∥₁

private
  variable
    ℓ : Level
    X : Type ℓ

≈-refl : ∀ {xs : M X} → xs ≈ xs
≈-refl {xs = xs} = M.ind {P = λ xs → xs ≈ xs} (λ xs → PT.isPropPropTrunc) (∣ ε-refl ∣₁)  (∣_∣₁ ∘ η-refl) ⊕-refl xs where
  ⊕-refl : ∀ {xs ys} → xs ≈ xs → ys ≈ ys → xs ⊕ ys ≈ xs ⊕ ys
  ⊕-refl = PT.map2 λ xs-refl ys-refl → ⊕-congʳ _ ys-refl

encode : {xs ys : M X} → xs ≡ ys → xs ≈ ys
encode {X = _} {xs} {ys} = J (λ ys p → xs ≈ ys) ≈-refl

assoc₄ : ∀ {xs ys zs ws : M X}
  → (xs ⊕ ys) ⊕ (zs ⊕ ws) ≡ xs ⊕ (ys ⊕ zs) ⊕ ws
assoc₄ {xs = xs} = sym (assoc _ _ _) ∙ (cong (xs ⊕_) (assoc _ _ _))

middle-four-interchange : ∀ {xs ys zs ws : M X}
  → (xs ⊕ ys) ⊕ (zs ⊕ ws) ≡ (xs ⊕ zs) ⊕ (ys ⊕ ws)
middle-four-interchange {X = X} {xs} {ys} {zs} {ws} =
  assoc₄ ∙∙ (cong (λ as → xs ⊕ as ⊕ ws) (comm ys zs)) ∙∙ (sym assoc₄)

decode′ : {xs ys : M X} → xs ≈′ ys → xs ≡ ys
decode′ ε-refl = refl {x = ε}
decode′ (η-refl x) = refl {x = η x}
decode′ (⊕-congʳ xs p) = cong (xs ⊕_) (decode′ p)
decode′ (⊕-split {xs} {ys} {zs} {ws} {as} {bs} {cs} {ds} p₁ p₂ p₃ p₄) = goal where
  p₁′ : xs ≡ as ⊕ bs
  p₁′ = decode′ p₁

  p₂′ : ys ≡ cs ⊕ ds
  p₂′ = decode′ p₂

  p₃′ : zs ≡ as ⊕ cs
  p₃′ = decode′ p₃

  p₄′ : ws ≡ bs ⊕ ds
  p₄′ = decode′ p₄

  goal : xs ⊕ ys ≡ zs ⊕ ws
  goal =
    xs ⊕ ys ≡⟨ cong₂ _⊕_ p₁′ p₂′ ⟩
    (as ⊕ bs) ⊕ (cs ⊕ ds) ≡⟨ middle-four-interchange ⟩
    (as ⊕ cs) ⊕ (bs ⊕ ds) ≡⟨ cong₂ _⊕_ (sym p₃′) (sym p₄′) ⟩
    zs ⊕ ws ∎

decode : {xs ys : M X} → xs ≈ ys → xs ≡ ys
decode = PT.rec (isSetM _ _) decode′

MPathEquiv : ∀ {xs ys : M X} → (xs ≡ ys) ≃ (xs ≈ ys)
MPathEquiv {X = _} {xs} {ys} = propBiimpl→Equiv (isSetM xs ys) PT.isPropPropTrunc encode decode

isSingl≈′ : ∀ {ℓ} {X : Type ℓ} (xs : M X) → Type ℓ
isSingl≈′ {X = X} xs = Σ[ x ∈ X ] (xs ≈′ η x)

η≈′ToPath : ∀ {x y : X} → η x ≈′ η y → x ≡ y
η≈′ToPath {X = X} {x = x} {y = y} p = {! !}
 
η≈ToPath : ∀ {x y : X} → η x ≈ η y → x ≡ y
η≈ToPath {X = _} {x = x} {y = y} p = {! !}

-- inj-η : ∀ {x y : X} → η x ≡ η y → x ≡ y
-- inj-η {x = x} {y = y} p = η≈ToPath $ equivFun MPathEquiv p where
