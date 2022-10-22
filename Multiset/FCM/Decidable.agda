module Multiset.FCM.Decidable where

open import Multiset.Prelude
open import Multiset.FCM.Base as M

open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Function
open import Cubical.Foundations.Structure

open import Cubical.Data.Nat as ℕ
  using
    ( ℕ
    ; _+_
    )
import Cubical.Data.Unit as Unit
import Cubical.Data.Empty as Empty
open import Cubical.Data.Sum as Sum
  using
    ( _⊎_
    )

open import Cubical.Functions.Logic as Logic
  renaming (¬_ to ¬ₚ_)

open import Cubical.Relation.Nullary.Base
  using
  ( Dec
  ; Discrete
  ; ¬_
  ; yes
  ; no
  )
open import Cubical.Relation.Nullary.Properties
  using
    ( isPropDec
    )
open import Cubical.Relation.Nullary.DecidablePropositions
  using
    ( DecProp
    )
open import Cubical.HITs.PropositionalTruncation as PT
  using
    ( ∣_∣₁
    ; ∥_∥₁
    ; isPropPropTrunc
    )



infix 4 _∼_ _∼ₚ_

data _∼_ {ℓ} {X : Type ℓ}: M X → M X → Type ℓ where
  ε∼ : ε ∼ ε
  ∷∼ : ∀ {x y} {xs ys}
    → x ≡ y
    → xs ∼ ys
    → x ∷ xs ∼ y ∷ ys
  ⊕∼ : ∀ {x y} {xs ys zs}
    → (xs ∼ y ∷ zs)
    → (x ∷ zs ∼ ys)
    → (x ∷ xs ∼ y ∷ ys)

private
  variable
    ℓ : Level
    X :  Type ℓ

module _ {p : X → hProp ℓ} (p? : ∀ x → Dec ⟨ p x ⟩) where
  open import Multiset.FCM.Properties

  any? : ∀ xs → Dec ⟨ any p xs ⟩
  any? = M.ind (λ xs → isPropDec (str (any p xs))) dec-ε dec-η dec-⊕ where
    dec-ε : Dec ⟨ any p ε ⟩
    dec-ε = no (¬any-ε p)

    dec-η : ∀ (x : X) → Dec ⟨ any p (η x) ⟩
    dec-η = p?

    dec-⊕ : ∀ {xs ys}
      → Dec ⟨ any p xs ⟩
      → Dec ⟨ any p ys ⟩
      → Dec ⟨ any p (xs ⊕ ys) ⟩
    dec-⊕ {xs} {ys} (yes r) _       = yes (any-⊕ˡ p xs ys r)
    dec-⊕ {xs} {ys} (no ¬r) (yes s) = yes (any-⊕ʳ p xs ys s)
    dec-⊕ {xs} {ys} (no ¬r) (no ¬s) = no (¬any-⊕ p ¬r ¬s)

  all? : ∀ xs → Dec ⟨ all p xs ⟩
  all? = M.ind (λ xs → isPropDec (str (all p xs))) dec-ε dec-η dec-⊕ where
    dec-ε : Dec ⟨ all p ε ⟩
    dec-ε = yes (all-ε p)

    dec-η : ∀ (x : X) → Dec ⟨ all p (η x) ⟩
    dec-η = p?

    dec-⊕ : ∀ {xs ys}
      → Dec ⟨ all p xs ⟩
      → Dec ⟨ all p ys ⟩
      → Dec ⟨ all p (xs ⊕ ys) ⟩
    dec-⊕ (yes r) (yes s) = yes (all-⊕ p r s)
    dec-⊕ (yes r) (no ¬s) = no (¬all-⊕ʳ p ¬s)
    dec-⊕ (no ¬r) _       = no (¬all-⊕ˡ p ¬r)

η-inj : ∀ {x y : X} → η x ≡ η y → x ≡ y
η-inj {x} {y} p = {!J (λ y → η x ≡ y → ) !}

-- ε≁η : (x : X) → ¬ (ε ∼ η x)
-- ε≁η x ε∼ = {! !}
-- ε≁η x _ = {! !}

_∼ₚ_ : (xs ys : M {ℓ = ℓ} X) → hProp ℓ
xs ∼ₚ ys = ∥ xs ∼ ys ∥₁ , isPropPropTrunc

decode : ∀ {xs ys}
  → xs ∼ ys
  → xs ≡ ys
decode ε∼ = refl
decode (∷∼ x≡y r) = cong₂ _∷_ x≡y (decode r)
decode (⊕∼ {x} {y} {xs} {ys} {zs} r s) = ∷-swap-split≡ r' s' where
  r' : xs ≡ y ∷ zs
  r' = decode r

  s' : x ∷ zs ≡ ys
  s' = decode s

decodeₚ : ∀ {xs ys}
  → ⟨ xs ∼ₚ ys ⟩
  → ⟨ xs ≡ₚ ys ⟩
decodeₚ = PT.map decode

module _ (_≡?_ : Discrete X) where
  dec∼ₚ : ∀ xs ys → DecProp {! !}
  dec∼ₚ xs ys = {! !}

  _∼?_ : ∀ xs ys → Dec ⟨ xs ∼ₚ ys ⟩
  xs ∼? ys = M.ind {P = λ xs → ∀ ys → Dec ⟨ xs ∼ₚ ys ⟩} (λ xs → isPropΠ λ ys → isPropDec isPropPropTrunc)
    empty* {! !} {! !} xs ys where

    empty* : ∀ ys → Dec ∥ ε ∼ ys ∥₁
    empty* = M.ind (λ ys → isPropDec isPropPropTrunc) (yes ∣ ε∼ ∣₁) (λ x → no {! !}) ({! !})

module _ (_≡?_ : Discrete X) where
  private
    χ : (x y : X) → ℕ
    χ x y with x ≡? y
    ... | yes _ = 1
    ... | no _ = 0

    χ-sym : ∀ x → χ x x ≡ 1
    χ-sym x with x ≡? x
    ... | yes _  = refl {x = 1}
    ... | no x≢x = Empty.elim (x≢x refl)

  -- Multiplicity
  _♯_ : X → M X → ℕ
  _♯_ x = count (χ x)

  infix 7 _♯_

  ♯-ε : ∀ x → x ♯ ε ≡ 0
  ♯-ε x = refl

  ♯-η : ∀ x → x ♯ η x ≡ 1
  ♯-η x = χ-sym x

  ¬♯-η : ∀ {x y} → ¬ x ≡ y → x ♯ η y ≡ 0
  ¬♯-η {x} {y} x≢y with x ≡? y
  ... | yes x≡y = Empty.elim $ x≢y x≡y
  ... | no ¬p = refl {x = 0}

  dec-♯-η : ∀ x y → (x ♯ η y ≡ 0) ⊎ (x ♯ η y ≡ 1)
  dec-♯-η x y with x ≡? y
  ... | yes p = Sum.inr refl
  ... | no ¬p = Sum.inl refl

  ♯-⊕-+-comm : ∀ x {xs ys} → x ♯ xs ⊕ ys ≡ x ♯ xs + x ♯ ys
  ♯-⊕-+-comm x {xs = xs} {ys = ys} = refl

  _≡♯_ : (xs ys : M X) → Type _
  xs ≡♯ ys = (x : X) → (x ♯ xs) ≡ (x ♯ ys)
  
  infix 4 _≡♯_

  _≢♯_ : (xs ys : M X) → Type _
  xs ≢♯ ys = ¬ xs ≡♯ ys

  ≡♯-refl : ∀ {xs} → xs ≡♯ xs
  ≡♯-refl = λ x → refl {x = x ♯ _}

  ε≢♯η : ∀ x → ε ≢♯ η x
  ε≢♯η x = λ ε≡♯η → ℕ.znots $
    0       ≡⟨ ♯-ε x ⟩
    x ♯ ε   ≡⟨ ε≡♯η x ⟩
    x ♯ η x ≡⟨ ♯-η x ⟩
    1 ∎

  ε≡♯⊕ : ∀ {xs ys}
    → ε ≡♯ xs
    → ε ≡♯ ys
    → ε ≡♯ xs ⊕ ys
  ε≡♯⊕ {xs = xs} {ys = ys} ε≡♯xs ε≡♯ys = λ x →
    x ♯ ε           ≡⟨⟩
    0               ≡⟨ cong₂ _+_ (ε≡♯xs x) (ε≡♯ys x) ⟩
    x ♯ xs + x ♯ ys ≡⟨⟩
    x ♯ xs ⊕ ys     ∎

  ε≡♯⊕→ε≡♯ʳ : ∀ {xs ys} → ε ≡♯ xs ⊕ ys → ε ≡♯ ys
  ε≡♯⊕→ε≡♯ʳ {xs = xs} {ys = ys} = M.ind
    {P = λ xs → ∀ ys → ε ≡♯ xs ⊕ ys → ε ≡♯ ys}
    (λ _ → isPropΠ3 (λ _ _ _ → ℕ.isSetℕ _ _))
    empty* singl* union* xs ys where
    empty* : ∀ ys → ε ≡♯ ε ⊕ ys → ε ≡♯ ys
    empty* ys = subst (ε ≡♯_) (unit ys)

    singl* : ∀ x ys → ε ≡♯ η x ⊕ ys → ε ≡♯ ys
    singl* x ys indH z with x ≡? z
    ... | yes x≡z = Empty.elim $ ℕ.znots contra where
      contra : 0 ≡ ℕ.suc _
      contra =
        0                 ≡⟨⟩
        z ♯ ε             ≡⟨ cong (_♯ ε) x≡z ⟩
        x ♯ ε             ≡⟨ indH x ⟩
        x ♯ η x ⊕ ys      ≡⟨⟩
        x ♯ η x + x ♯ ys  ≡⟨ cong (_+ (x ♯ ys)) (♯-η x) ⟩
        1       + x ♯ ys  ≡⟨⟩
        ℕ.suc (x ♯ ys) ∎
    ... | no ¬x≡z =
      z ♯ ε ≡⟨ indH z ⟩
      z ♯ η x + z ♯ ys ≡⟨ cong (_+ z ♯ ys) z♯ηx≡0 ⟩
      z ♯ ys ∎ where

      z♯ηx≡0 : z ♯ η x ≡ 0
      z♯ηx≡0 = ¬♯-η (¬x≡z ∘ sym)

    union* : ∀ {xs ys}
      → (∀ zs → ε ≡♯ xs ⊕ zs → ε ≡♯ zs)
      → (∀ zs → ε ≡♯ ys ⊕ zs → ε ≡♯ zs)
      → ∀ zs → ε ≡♯ (xs ⊕ ys) → ε ≡♯ zs
    union* {xs = xs} {ys} p-xs p-ys zs indH z =
      z ♯ ε ≡⟨ indH z ⟩
      z ♯ (xs ⊕ ys) ≡⟨⟩
      z ♯ xs + z ♯ ys ≡⟨ {! indH  !} ⟩
      z ♯ zs ∎ where

      p : ε ≡♯ ys
      p = p-xs ys indH

      q : ε ≡♯ xs
      q = p-ys xs (subst (ε ≡♯_) (comm xs ys) indH)

      r = {! ε≡♯⊕ p q z !}

  ε≡♯⊕→ε≡♯ˡ : ∀ {xs ys} → ε ≡♯ xs ⊕ ys → ε ≡♯ xs
  ε≡♯⊕→ε≡♯ˡ {xs = xs} {ys = ys} = ε≡♯⊕→ε≡♯ʳ {xs = ys} {ys = xs} ∘ subst (ε ≡♯_) (comm xs ys)

  -- ♯≡0→is-ε : ()

  isProp-≡♯ : ∀ {xs ys} → isProp (xs ≡♯ ys)
  isProp-≡♯ {xs = xs} {ys = ys} = isPropΠ λ x → ℕ.isSetℕ (x ♯ xs) (x ♯ ys)


  dec-≡♯ : ∀ xs ys → Dec (xs ≡♯ ys)
  dec-≡♯ = M.ind (λ xs → isPropΠ (propDec xs)) dec-ε≡♯ {! !} {! !} where
    propDec : ∀ xs ys → isProp (Dec (xs ≡♯ ys))
    propDec xs ys = isPropDec isProp-≡♯

    dec-ε≡♯ε : Dec (ε ≡♯ ε)
    dec-ε≡♯ε = yes ≡♯-refl

    dec-ε≡♯η : ∀ x → Dec (ε ≡♯ η x)
    dec-ε≡♯η x = no (ε≢♯η x)

    dec-ε≡♯⊕ : ∀ {xs ys}
      → Dec (ε ≡♯ xs)
      → Dec (ε ≡♯ ys)
      → Dec (ε ≡♯ (xs ⊕ ys))
    dec-ε≡♯⊕ {xs} {ys} (yes p-xs) (yes p-ys) = yes $ ε≡♯⊕ {xs} {ys} p-xs p-ys
    dec-ε≡♯⊕ {xs} {ys} (yes p-xs) (no ¬p-ys) = no (¬p-ys ∘ ε≡♯⊕→ε≡♯ʳ {xs} {ys})
    dec-ε≡♯⊕ (no ¬p-xs) _ = no (¬p-xs ∘ ε≡♯⊕→ε≡♯ˡ)

    dec-ε≡♯ : ∀ ys → Dec (ε ≡♯ ys)
    dec-ε≡♯ = M.ind (λ ys → propDec ε ys) dec-ε≡♯ε dec-ε≡♯η dec-ε≡♯⊕

    dec-η≡♯ : ∀ x ys → Dec (η x ≡♯ ys)
    dec-η≡♯ x ys = ?

-- module _ (_≡X?_ : Discrete X) where
--   open import Cubical.Relation.Nullary.Base
--     using
--       ( Dec
--       ; Discrete
--       )

--   open import Cubical.Relation.Nullary.Properties
--     using
--       ( isPropDec
--       ; mapDec
--       ; ¬→¬∥∥
--       ; Dec∥∥
--       )

--   private
--     dec-⊓ : {p q : hProp ℓ}
--       → Dec ⟨ p ⟩
--       → Dec ⟨ q ⟩
--       → Dec ⟨ p ⊓ q ⟩
--     dec-⊓ (yes p) (yes q) = yes (p , q)
--     dec-⊓ (yes p) (no ¬q) = no (¬q ∘ snd)
--     dec-⊓ (no ¬p) _       = no (¬p ∘ fst)

--   _∈?_ : ∀ z xs → Dec (z ∈ xs)
--   z ∈? xs = any? {p = z ≡ₚ_} dec-≡ₚ xs where
--     dec-≡ₚ : ∀ x → Dec ∥ z ≡ x ∥₁
--     dec-≡ₚ x = Dec∥∥ (z ≡X? x)

--   _⊆?_ : (xs ys : M X) → Dec (xs ⊆ ys)
--   xs ⊆? ys = all? (_∈? ys) xs

--   ⟦_≡?_⟧ : (xs ys : M X) → Dec ⟦ xs ≡ ys ⟧
--   ⟦ xs ≡? ys ⟧ = dec-⟦≡⟧ where
--     dec-⊆ : Dec (xs ⊆ ys)
--     dec-⊆ = xs ⊆? ys

--     dec-⊇ : Dec (xs ⊇ ys)
--     dec-⊇ = ys ⊆? xs

--     dec-⟦≡⟧ : Dec ⟨ xs ⊆ₚ ys ⊓ xs ⊇ₚ ys ⟩
--     dec-⟦≡⟧ = dec-⊓ dec-⊆ dec-⊇

--   ⟦≡⟧→Path : ∀ {xs ys} → ⟦ xs ≡ ys ⟧ → xs ≡ ys
--   ⟦≡⟧→Path {xs = xs} {ys = ys} = M.ind
--     {P = λ xs → ∀ ys → ⟦ xs ≡ ys ⟧ → xs ≡ ys}
--     (λ _ → isPropΠ2 λ _ _ → isSetM _ _)
--     empty* {! !} {! !} xs ys where

--     ¬ε-η : ∀ x → ⟦ ε ≡ η x ⟧ → ε ≡ η x
--     ¬ε-η x ()

--     ¬ε-⊕ : ∀ {xs ys}
--       → ⟦ ε ≡ xs ⊕ ys ⟧ → ε ≡ xs ⊕ ys
--     ¬ε-⊕ (ε⊆xs⊕ys , ε⊇xs⊕ys) = sym (⊆-ε-minimal ε⊇xs⊕ys)

--     empty* : ∀ ys → ⟦ ε ≡ ys ⟧ → ε ≡ ys
--     empty* = M.ind (λ _ → isPropΠ λ _ → isSetM _ _) (λ _ → refl) ¬ε-η (λ _ _ → ¬ε-⊕)

--     singl* : ∀ x ys → ⟦ η x ≡ ys ⟧ → η x ≡ ys
--     singl* x = M.ind (λ _ → isPropΠ λ _ → isSetM _ _) (sym ∘ ¬ε-η x ∘ ⟦≡⟧-sym) (λ _ _ → refl {x = η x}) {! !}

--   ⟦≡?⟧→DecPath : ∀ {xs ys} → Dec ⟦ xs ≡ ys ⟧ → Dec (xs ≡ ys)
--   ⟦≡?⟧→DecPath (yes p) = {! yes!}
--   ⟦≡?⟧→DecPath (no ¬p) = {! !}

--   discreteM : Discrete (M X)
--   discreteM xs ys = decMPath where
--     decMPath : Dec (xs ≡ ys)
--     decMPath = {! ⟦≡?⟧→DecPath ⟦ xs ≡? ys ⟧ !}
