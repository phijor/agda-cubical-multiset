{-# OPTIONS --safe #-}

module Multiset.FCM.Properties where

open import Multiset.Prelude
open import Multiset.Util using (!_)
open import Multiset.FCM.Base as M

-- open import Multiset.Util.Logic using
--   ( _xor_
--   ; xorl
--   ; xorr
--   ; isPropXor
--   )

open import Cubical.Foundations.Id using (ap)
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Structure
open import Cubical.Foundations.Path
open import Cubical.Foundations.GroupoidLaws hiding (assoc)
open import Cubical.Foundations.Function using (_∘_ ; flip)
open import Cubical.Foundations.Structure
open import Cubical.Functions.Logic as Logic
  renaming
    (¬_ to ¬ₚ_)
open import Cubical.Functions.FunExtEquiv

open import Cubical.HITs.PropositionalTruncation as PT
  using
    ( ∣_∣₁
    ; ∥_∥₁
    ; isPropPropTrunc
    )
open import Cubical.Data.Nat as ℕ
  using
    ( ℕ
    ; zero
    ; suc
    )
open import Cubical.Data.Unit as Unit
  using (Unit)
import Cubical.Data.Empty as Empty
open import Cubical.Data.Sigma as Sigma

open import Cubical.Relation.Nullary.Base
  using
  (¬_)

record M-Dalg {ℓ : Level} {X : Type} : Type (ℓ-suc ℓ) where
  field
    Carrier : M X → Type ℓ
    Cε : Carrier ε
    _C⊕_ : {m n : M X} → Carrier m → Carrier n → Carrier (m ⊕ n)
    Cunit : {m : M X} → (x : Carrier m) → PathP (λ i → Carrier (unit m i)) (Cε C⊕ x) x
    -- continue for the rest of the path constructors

private
  variable
    ℓ ℓX ℓY : Level
    X : Type ℓX
    Y : Type ℓY

flatten : M (M X) → M X
flatten = rec isSetM ε (λ m → m) _⊕_ unit assoc comm

-- -- Size
sizeof : M X → ℕ
sizeof = count (λ _ → 1)

subst-unitl : ∀ {xs ys zs : M X}
  → xs ≡ ε
  → zs ≡ xs ⊕ ys
  → zs ≡ ys
subst-unitl {ys = ys} {zs = zs} p q = subst (zs ≡_) (cong (_⊕ ys) p ∙ unit ys) q

subst-unitr : ∀ {xs ys zs : M X}
  → ys ≡ ε
  → zs ≡ xs ⊕ ys
  → zs ≡ xs
subst-unitr {xs = xs} {zs = zs} p q = subst (zs ≡_) (cong (xs ⊕_) p ∙ unit' xs) q

subst-ε⊕ε≡ε : ∀ {xs ys : M X}
  → xs ≡ ε
  → ys ≡ ε
  → xs ⊕ ys ≡ ε
subst-ε⊕ε≡ε {xs = xs} {ys = ys} p q =
  (xs ⊕ ys) ≡⟨ cong₂ _⊕_ p q ⟩
  (ε ⊕ ε)   ≡⟨ unit ε ⟩∎
  ε ∎
  

η≢ε : {x : X} → ¬ (η x ≡ ε)
η≢ε ηx≡ε = Empty.rec (ℕ.snotz (cong sizeof ηx≡ε))

η⊕≢ε : ∀ {x : X} {ys : M X} → ¬ (η x ⊕ ys ≡ ε)
η⊕≢ε {x = x} {ys = ys} ηx⊕ys≡ε = Empty.rec (ℕ.snotz contra) where
  contra : suc (sizeof ys) ≡ 0
  contra = cong sizeof ηx⊕ys≡ε

¬η-unitl : ∀ {x : X} {ys : M X} → ¬ (η x ⊕ ys ≡ ys)
¬η-unitl {x = x} {ys = ys} ηx⊕ys≡ys = Empty.rec (snot-self _ contra) where
  contra : suc (sizeof ys) ≡ sizeof ys
  contra = cong sizeof ηx⊕ys≡ys

  snot-self : ∀ n → ¬ (suc n ≡ n)
  snot-self zero = ℕ.snotz
  snot-self (suc n) = snot-self n ∘ ℕ.injSuc

¬η-unitr : ∀ {x : X} {ys : M X} → ¬ (ys ⊕ η x ≡ ys)
¬η-unitr {ys = ys} = ¬η-unitl ∘ subst (_≡ ys) (comm _ _)

no-zero-divisorsˡ : ∀ {xs ys : M X} → xs ⊕ ys ≡ ε → xs ≡ ε
no-zero-divisorsˡ {xs = xs} {ys = ys} = M.ind {P = λ xs → ∀ ys → xs ⊕ ys ≡ ε → xs ≡ ε}
  (λ xs → isPropΠ2 λ ys h → isSetM xs ε)
  empty* singl* union* xs ys where

  empty* : ∀ ys → _ → ε ≡ ε
  empty* ys _ = refl

  singl* : ∀ x ys → η x ⊕ ys ≡ ε → η x ≡ ε
  singl* x ys h = Empty.rec (η⊕≢ε h)

  union* : ∀ {xs₁ xs₂}
    → (∀ ys → xs₁ ⊕ ys ≡ ε → xs₁ ≡ ε)
    → (∀ ys → xs₂ ⊕ ys ≡ ε → xs₂ ≡ ε)
    → (∀ ys → (xs₁ ⊕ xs₂) ⊕ ys ≡ ε → (xs₁ ⊕ xs₂) ≡ ε)
  union* {xs₁} {xs₂} indH-xs₁ indH-xs₂ ys h =
    subst-ε⊕ε≡ε (indH-xs₁ _ h₁) (indH-xs₂ _ h₂) where

    h₁ : xs₁ ⊕ xs₂ ⊕ ys ≡ ε
    h₁ = subst (_≡ ε) (sym (assoc _ _ _)) h

    h₂ : xs₂ ⊕ xs₁ ⊕ ys ≡ ε
    h₂ = subst (_≡ ε) (
        (xs₁ ⊕ xs₂) ⊕ ys ≡⟨ cong (_⊕ ys) (comm xs₁ xs₂) ⟩
        (xs₂ ⊕ xs₁) ⊕ ys ≡⟨ sym (assoc _ _ _) ⟩
        xs₂ ⊕ xs₁ ⊕ ys ∎
      ) h

no-zero-divisorsʳ : ∀ {xs ys : M X} → xs ⊕ ys ≡ ε → ys ≡ ε
no-zero-divisorsʳ {xs = xs} {ys = ys} = no-zero-divisorsˡ ∘ subst (_≡ ε) (comm xs ys)

no-zero-divisors : ∀ {xs ys : M X} → xs ⊕ ys ≡ ε → (xs ≡ ε) × (ys ≡ ε)
no-zero-divisors h = (no-zero-divisorsˡ h) , (no-zero-divisorsʳ h)

sizeof-ε : sizeof {X = X} ε ≡ 0
sizeof-ε = refl

sizeof-η : {x : X} → sizeof (η x) ≡ 1
sizeof-η = refl

sizeof-∷ : ∀ {x : X} {xs} → sizeof (x ∷ xs) ≡ suc (sizeof xs)
sizeof-∷ {x = x} {xs = xs} = refl

sizeof-⊕ : (m n : M X) → sizeof (m ⊕ n) ≡ sizeof m ℕ.+ sizeof n
sizeof-⊕ _ _ = refl

sizeof≡0→ε : (m : M X) → sizeof m ≡ 0 → m ≡ ε
sizeof≡0→ε {X = X} = M.ind (λ m → isPropΠ (λ _ → isSetM m ε)) Pε Pη P+ where
  Pε : sizeof {X = X} ε ≡ 0 → ε ≡ ε
  Pε _ = refl

  Pη : (x : X) → sizeof (η x) ≡ 0 → η x ≡ ε
  Pη _ 1≡0 = Empty.rec (ℕ.snotz 1≡0)

  P+ : {m n : M X}
      → (sizeof m ≡ 0 → m ≡ ε)
      → (sizeof n ≡ 0 → n ≡ ε)
      → sizeof (m ⊕ n) ≡ 0 → m ⊕ n ≡ ε
  P+ {m = m} {n = n} IHm IHn sz-m⊕n≡0 =
    let sz-m≡0 , sz-n≡0 = ℕ.m+n≡0→m≡0×n≡0 {sizeof m} {sizeof n} sz-m⊕n≡0 in
    m ⊕ n
      ≡⟨ cong (_⊕ n) (IHm sz-m≡0) ⟩
    ε ⊕ n
      ≡⟨ unit n ⟩
      n
      ≡⟨ IHn sz-n≡0 ⟩
    ε ∎

unitl-universal : ∀ {xs ys : M X}
  → xs ≡ ys ⊕ xs
  → ys ≡ ε
unitl-universal {xs = xs} {ys = ys} p = sizeof≡0→ε ys sizeof-ys≡0 where
  sizeof-≡ : sizeof xs ≡ sizeof ys ℕ.+ sizeof xs
  sizeof-≡ = cong sizeof p

  sizeof-ys≡0 : sizeof ys ≡ 0
  sizeof-ys≡0 = ℕ.m+n≡n→m≡0 (sym sizeof-≡)

unitr-universal : ∀ {xs ys : M X}
  → xs ≡ xs ⊕ ys
  → ys ≡ ε
unitr-universal {xs = xs} = unitl-universal ∘ subst (xs ≡_) (comm _ _)

private
  open import Cubical.Data.Sum as Sum
    using (_⊎_)

  sumOf1-subsplit : ∀ {m n : ℕ}
    → m ℕ.+ n ≡ 1
    → ((m ≡ 1) × (n ≡ 0)) ⊎ ((n ≡ 1) × (m ≡ 0))
  sumOf1-subsplit {m = 0} p = Sum.inr (p , refl)
  sumOf1-subsplit {m = 1} p = Sum.inl (refl , ℕ.injSuc p)
  sumOf1-subsplit {m = suc (suc m)} p = Empty.rec (ℕ.snotz $ ℕ.injSuc p)

sizeof≡1→∥η≡∥₁ : (xs : M X) → sizeof xs ≡ 1 → ∃[ x ∈ X ] (η x ≡ xs)
sizeof≡1→∥η≡∥₁ {X = X} = M.ind (λ xs → isPropΠ λ _ → PT.isPropPropTrunc)
  (Empty.rec ∘ ℕ.znots)
  (λ x 1≡1 → ∣ x , refl ∣₁)
  union* where
  union* : ∀ {xs ys : M X}
    → (sizeof xs ≡ 1 → ∃[ x ∈ X ] η x ≡ xs)
    → (sizeof ys ≡ 1 → ∃[ y ∈ X ] η y ≡ ys)
    → sizeof (xs ⊕ ys) ≡ 1 → ∃[ z ∈ X ] η z ≡ xs ⊕ ys
  union* {xs = xs} {ys = ys} indH-xs indH-ys p = Sum.elim left right size-split where
    size-split : ((sizeof xs ≡ 1) × (sizeof ys ≡ 0)) ⊎ ((sizeof ys ≡ 1) × (sizeof xs ≡ 0))
    size-split = sumOf1-subsplit p

    left : ((sizeof xs ≡ 1) × (sizeof ys ≡ 0)) → ∃[ x ∈ X ] η x ≡ (xs ⊕ ys)
    left (singl-xs , empty-ys) = subst (λ zs → ∃[ x ∈ X ] η x ≡ zs) (sym p') (indH-xs singl-xs) where
      p' : xs ⊕ ys ≡ xs
      p' = cong (xs ⊕_) (sizeof≡0→ε _ empty-ys) ∙ unit' _

    right : ((sizeof ys ≡ 1) × (sizeof xs ≡ 0)) → ∃[ y ∈ X ] η y ≡ (xs ⊕ ys)
    right (singl-ys , empty-xs) = subst (λ zs → ∃[ x ∈ X ] η x ≡ zs) (sym q') (indH-ys singl-ys) where
      q' : xs ⊕ ys ≡ ys
      q' = cong (_⊕ ys) (sizeof≡0→ε _ empty-xs) ∙ unit _

-- Parity
open import Cubical.Data.Bool as Bool
  using (Bool ; true ; false)
parity : M X → Bool
parity xs = rec Bool.isSetBool false (λ _ → true) Bool._⊕_ (λ b → refl) Bool.⊕-assoc Bool.⊕-comm xs

repeat : X → ℕ → M X
repeat x 0 = ε
repeat x (suc n) = x ∷ repeat x n

sizeof-repeat : {x : X} → ∀ n → sizeof (repeat x n) ≡ n
sizeof-repeat {X = X} zero = sizeof-ε {X = X}
sizeof-repeat (suc n) = cong suc $ sizeof-repeat n

section-sizeof : ∀ {x : X} → section sizeof (repeat x)
section-sizeof = sizeof-repeat

repeat-+-⊕ : ∀ {x : X} (m n : ℕ) → repeat x (m ℕ.+ n) ≡ (repeat x m) ⊕ (repeat x n)
repeat-+-⊕ zero n = sym (unit _)
repeat-+-⊕ {x = x} (suc m) n = cong (x ∷_) (repeat-+-⊕ m n) ∙ (assoc _ _ _)

module _ (contrX : isContr X) where
  open Iso
  private
    x₀ : X
    x₀ = contrX .fst

    x₀≡_ : ∀ x → x₀ ≡ x
    x₀≡ x = contrX .snd x

  retract-sizeof : retract sizeof (repeat x₀)
  retract-sizeof = M.ind (λ xs → isSetM _ xs) refl singl* union* where
    singl* : ∀ x → x₀ ∷ ε ≡ η x
    singl* x = unit' (η x₀) ∙ cong η (x₀≡ x)

    union* : ∀ {xs ys}
      → repeat x₀ (sizeof xs) ≡ xs
      → repeat x₀ (sizeof ys) ≡ ys
      → repeat x₀ (sizeof (xs ⊕ ys)) ≡ xs ⊕ ys
    union* {xs} {ys} indH-xs indH-ys =
      repeat x₀ (sizeof (xs ⊕ ys)) ≡⟨⟩
      repeat x₀ (sizeof xs ℕ.+ sizeof ys) ≡⟨ repeat-+-⊕ _ _ ⟩
      (repeat x₀ $ sizeof xs) ⊕ (repeat x₀ $ sizeof ys) ≡⟨ cong₂ _⊕_ indH-xs indH-ys ⟩
      xs ⊕ ys ∎

  MContrℕIso : Iso (M X) ℕ
  MContrℕIso .fun = sizeof
  MContrℕIso .inv = repeat x₀
  MContrℕIso .rightInv = sizeof-repeat {x = x₀}
  MContrℕIso .leftInv = retract-sizeof

  MContr≃ℕ : M X ≃ ℕ
  MContr≃ℕ = isoToEquiv MContrℕIso

mapSizeof : ∀ {f : X → Y} xs
  → sizeof (map f xs) ≡ sizeof xs
mapSizeof {f = f} = M.ind (λ _ → ℕ.isSetℕ _ _) refl (λ _ → refl)
  λ {xs ys} p q →
    sizeof (map f (xs ⊕ ys)) ≡⟨⟩
    sizeof (map f xs ⊕ map f ys) ≡⟨⟩
    sizeof (map f xs) ℕ.+ sizeof (map f ys) ≡⟨ cong₂ (ℕ._+_) p q ⟩
    sizeof xs ℕ.+ sizeof ys ≡⟨⟩
    sizeof (xs ⊕ ys) ∎

map-ε : ∀ {f : X → Y}
  → (xs : M X)
  → map f xs ≡ ε
  → xs ≡ ε
map-ε {f = f} = ind (λ xs → isPropΠ λ h → isSetM xs ε) empty* singl* union* where
  empty* : map f ε ≡ ε → ε ≡ ε
  empty* _ = refl

  singl* : ∀ x → map f (η x) ≡ ε → η x ≡ ε
  singl* x mapH = Empty.rec (η≢ε mapH)

  union* : ∀ {xs₁ xs₂}
    → (map f xs₁ ≡ ε → xs₁ ≡ ε)
    → (map f xs₂ ≡ ε → xs₂ ≡ ε)
    → map f (xs₁ ⊕ xs₂) ≡ ε
    → xs₁ ⊕ xs₂ ≡ ε
  union* {xs₁} {xs₂} indH-xs₁ indH-xs₂ mapH =
    xs₁ ⊕ xs₂ ≡⟨ cong₂ _⊕_ (indH-xs₁ map-xs₁) (indH-xs₂ map-xs₂) ⟩
    ε   ⊕ ε   ≡⟨ unit ε ⟩
    ε ∎
    where
    _ : map f xs₁ ⊕ map f xs₂ ≡ ε
    _ = mapH

    map-xs₁ : map f xs₁ ≡ ε
    map-xs₁ = no-zero-divisorsˡ mapH

    map-xs₂ : map f xs₂ ≡ ε
    map-xs₂ = no-zero-divisorsʳ mapH

-- module _ {ℓ} {X : Type ℓ} where
--   open import Cubical.Relation.Nullary

--   open import Cubical.Data.Sum.Base using (_⊎_)

--   isEmpty : M X → Type ℓ
--   isEmpty xs = xs ≡ ε

--   isPropIsEmpty : ∀ {xs} → isProp (isEmpty xs)
--   isPropIsEmpty = isSetM _ _

--   isSingleton' : M X → Type
--   isSingleton' xs = sizeof xs ≡ 1

--   isPropIsSingleton' : ∀ {xs} → isProp (isSingleton' xs)
--   isPropIsSingleton' {xs = xs} = ℕ.isSetℕ (sizeof xs) 1

--   isSingleton : M X → Type ℓ
--   isSingleton = fiber η

--   isSingleton₁ : M X → Type ℓ
--   isSingleton₁ xs = ∃[ x ∈ X ] (η x ≡ xs)

--   isSingletonElement : ∀ {xs} → isSingleton xs → X
--   isSingletonElement = fst

--   isSingletonProof : ∀ {xs} → (p : isSingleton xs) → η (isSingletonElement p) ≡ xs
--   isSingletonProof = snd

--   isSingleton'→isSingleton : ∀ {xs} → isSingleton' xs → isSingleton xs
--   isSingleton'→isSingleton {xs = xs} = M.ind {! !} {! !} {! !} {! !} xs

--   isSingleton→isSingleton' : ∀ {xs} → isSingleton xs → isSingleton' xs
--   isSingleton→isSingleton' {xs = xs} (x , p) = cong sizeof (sym p)

--   isSingleton-η : ∀ x → isSingleton (η x)
--   isSingleton-η x = x , refl

--   ¬isSingleton-ε : ¬ (isSingleton ε)
--   ¬isSingleton-ε = η≢ε ∘ isSingletonProof

--   isContr-η-Path : ∀ {x y : X} → x ≡ y → isContr (η x ≡ η y)
--   isContr-η-Path p = cong η p , isSetM _ _ (cong η p)

--   isSet→isSetIsSingleton : (isSet X) → ∀ {xs} → isSet (isSingleton xs)
--   isSet→isSetIsSingleton setX {xs = xs} = isSetΣ setX λ x → isProp→isSet (isSetM (η x) xs)

--   isSet→isPropIsSingleton : (isSet X) → ∀ {xs} → isProp (isSingleton xs)
--   isSet→isPropIsSingleton setX {xs = xs} (x , p) (y , q) = ΣPathP ({! !} , isSet→SquareP (λ i j → isSetM) p q (p ∙ sym q) refl)
--     -- M.ind {P = λ xs → isProp (isSingleton xs)}
--     -- (λ xs → isPropIsProp) (λ { (x , p) (y , q) → {! !} }) (λ { z (x , p) (y , q) → {! !} }) {! !} xs

--   isSet→isSingleton₁≃isSingleton : (isSet X) → ∀ {xs} → isSingleton₁ xs ≃ isSingleton xs
--   isSet→isSingleton₁≃isSingleton setX = {! Σ-cong-equiv!} -- Σ-cong-equiv-snd λ x → PT.propTruncIdempotent≃ {! !}

--   isSubSingleton : M X → Type ℓ
--   isSubSingleton xs = isEmpty xs ⊎ isSingleton xs

--   isSingleton-⊕-xor : ∀ xs ys
--     → isSingleton (xs ⊕ ys)
--     → (isSingleton xs) xor (isSingleton ys)
--   isSingleton-⊕-xor xs ys h = {! !}

--   isPropIsSingleton : ∀ {xs} → isProp (isSingleton xs)
--   isPropIsSingleton {xs = xs} = {! !}

--   -- isPropIsSingleton : ∀ {xs} → isProp (isSingleton xs)
--   -- isPropIsSingleton {xs = xs} = isPropRetract isSingleton→isSingleton' isSingleton'→isSingleton {! !} (isPropIsSingleton' {xs = xs})
--     -- ind {P = λ xs → isProp (isSingleton xs)}
--     -- (λ xs → isPropIsProp) empty* {! !} {! !} xs where

--     -- empty* : isProp (isSingleton ε)
--     -- empty* (x , ηx≡ε) (y , _) = Empty.rec (η≢ε ηx≡ε)

--     -- singl* : ∀ x → isProp (isSingleton (η x))
--     -- singl* x = {! !}
  
--   decEmpty : ∀ xs → Dec (isEmpty xs)
--   decEmpty = ind (λ xs → isPropDec isPropIsEmpty) dec-ε dec-η dec-⊕ where
--     dec-ε : Dec (isEmpty ε)
--     dec-ε = yes refl

--     dec-η : ∀ x → Dec (isEmpty (η x))
--     dec-η x = no η≢ε

--     dec-⊕ : ∀ {xs ys}
--       → Dec (isEmpty xs)
--       → Dec (isEmpty ys)
--       → Dec (isEmpty (xs ⊕ ys))
--     dec-⊕ (yes xs≡ε) (yes ys≡ε) = yes (subst-ε⊕ε≡ε xs≡ε ys≡ε)
--     dec-⊕ (yes _) (no ys≢ε) = no $ ys≢ε ∘ no-zero-divisorsʳ
--     dec-⊕ (no xs≢ε) _ = no $ xs≢ε ∘ no-zero-divisorsˡ
  
--   decIsSingleton : ∀ xs → Dec (isSingleton xs)
--   decIsSingleton = ind (λ xs → isPropDec isPropIsSingleton) dec-ε dec-η dec-⊕ where
--     dec-ε : Dec (isSingleton ε)
--     dec-ε = no (η≢ε ∘ snd)

--     dec-η : ∀ x → Dec (isSingleton (η x))
--     dec-η x = yes $ isSingleton-η x

--     dec-⊕ : ∀ {xs ys}
--       → Dec (isSingleton xs)
--       → Dec (isSingleton ys)
--       → Dec (isSingleton (xs ⊕ ys))
--     dec-⊕ (yes (x , ηx≡⊕)) (yes q) = no {!  !}
--     dec-⊕ (yes (x , ηx≡⊕)) (no ¬q) = yes {! !}
--     dec-⊕ (no ¬p) (yes q) = yes {! !}
--     dec-⊕ (no ¬p) (no ¬q) = no {! !}


-- map⁻¹-isSingleton : ∀ {f : X → Y}
--   → (xs : M X)
--   → isSingleton (map f xs)
--   → isSingleton xs
-- map⁻¹-isSingleton {X = X} {f = f} = M.ind {P = λ xs → isSingleton (map f xs) → isSingleton xs}
--   (λ xs → isPropΠ λ _ → isPropIsSingleton) empty* singl* {! !} where
--     empty* : isSingleton (map f ε) → _
--     empty* (_ , ηx≡ε) = Empty.elim (η≢ε ηx≡ε)

--     singl* : ∀ x → isSingleton (map f (η x)) → isSingleton (η x)
--     singl* x _ = x , refl

--     union* : ∀ {xs ys}
--       → (isSingleton (map f xs) → isSingleton xs)
--       → (isSingleton (map f ys) → isSingleton ys)
--       → isSingleton (map f (xs ⊕ ys)) → isSingleton (xs ⊕ ys)
--     union* {xs} {ys} indH-xs indH-ys h = {!h !} where
--       _ = {! isSingleton-⊕-xor (map f xs) (map f ys) h !}

--       p : isSingleton (map f xs) xor isSingleton (map f ys)
--         → isSingleton (xs ⊕ ys)
--       p (xorl (singl-xs , ¬singl-ys)) = indH-xs singl-xs .fst , {! indH-xs singl-xs .snd!}
--       p (xorr x) = {! !}

-- ofSizeOne : ∀ {ℓ} (X : Type ℓ) → Type ℓ
-- ofSizeOne X = Σ[ xs ∈ M X ] (sizeof xs ≡ 1)

-- η-merely-injective : ∀ {x y : X}
--   → η x ≡ η y
--   → ∥ x ≡ y ∥₁
-- η-merely-injective {x = x} {y = y} p = {! !}

-- module _ {ℓ} {X : Type ℓ} (setX : isSet X) where

--   ofSizeOne→isSingleton : ∀ {xs : M X}
--     → sizeof xs ≡ 1 → isSingleton xs
--   ofSizeOne→isSingleton {xs = xs} = M.elim {A = λ xs → sizeof xs ≡ 1 → isSingleton xs}
--     (λ xs → isSetΠ λ _ → isSet→isSetIsSingleton setX)
--     (Empty.rec ∘ ℕ.znots) (λ x _ → x , refl) union*
--     {! !} {! !} {! λ _ _ → transportRefl !} xs
--     where
--     module _ {xs ys : M X}
--       (indH-xs : sizeof xs ≡ 1 → Σ[ x ∈ X ] η x ≡ xs)
--       (indH-ys : sizeof ys ≡ 1 → Σ[ y ∈ X ] η y ≡ ys)
--       (p : sizeof (xs ⊕ ys) ≡ 1) where

--       size-split : ((sizeof xs ≡ 1) × (sizeof ys ≡ 0)) ⊎ ((sizeof ys ≡ 1) × (sizeof xs ≡ 0))
--       size-split = sumOf1-subsplit p

--       left : ((sizeof xs ≡ 1) × (sizeof ys ≡ 0)) → Σ[ x ∈ X ] η x ≡ (xs ⊕ ys)
--       left (singl-xs , empty-ys) = subst (λ zs → Σ[ x ∈ X ] η x ≡ zs) (sym p') (indH-xs singl-xs) where
--         p' : xs ⊕ ys ≡ xs
--         p' = cong (xs ⊕_) (sizeof≡0→ε _ empty-ys) ∙ unit' _

--       right : ((sizeof ys ≡ 1) × (sizeof xs ≡ 0)) → Σ[ y ∈ X ] η y ≡ (xs ⊕ ys)
--       right (singl-ys , empty-xs) = subst (λ zs → Σ[ x ∈ X ] η x ≡ zs) (sym q') (indH-ys singl-ys) where
--         q' : xs ⊕ ys ≡ ys
--         q' = cong (_⊕ ys) (sizeof≡0→ε _ empty-xs) ∙ unit _

--       union* : Σ[ z ∈ X ] η z ≡ xs ⊕ ys
--       union* = Sum.elim left right size-split


--     unit* : ∀ {xs : M X}
--       → (P : sizeof xs ≡ 1 → isSingleton xs)
--       → PathP (λ i → sizeof (unit xs i) ≡ 1 → isSingleton (unit xs i)) (union* (λ x → Empty.rec (ℕ.znots x)) P) P
--     unit* {xs = xs} P = symP {A = λ i → sizeof (unit xs i) ≡ 1 → isSingleton (unit xs i)} (subst-filler (λ xs → sizeof xs ≡ 1 → isSingleton xs) (sym $ unit xs) P ▷ {! (sym $ funExt step) !}) where
--       module _ (q : sizeof xs ≡ 1) where
--         bar : sumOf1-subsplit q ≡ Sum.inr (q , refl)
--         bar = refl

--         foo : union* (Empty.rec ∘ ℕ.znots) P q ≡ subst (λ zs → Σ[ x ∈ X ] η x ≡ zs) (sym (refl ∙ unit _)) (P q)
--         foo = refl

--         step : _ ≡ _
--         step =
--           union* (Empty.rec ∘ ℕ.znots) P q ≡⟨⟩
--           subst (λ zs → Σ[ x ∈ X ] η x ≡ zs) (sym (refl ∙ unit _)) (P q) ≡⟨ cong (λ r → subst (λ zs → Σ[ x ∈ X ] η x ≡ zs) (sym r) (P q)) (sym $ lUnit (unit _)) ⟩
--           subst (λ zs → Σ[ x ∈ X ] η x ≡ zs) (sym (unit _)) (P q) ∎

--   η-injective : ∀ {x y : X}
--     → η x ≡ η y
--     → x ≡ y
--   η-injective p =
--     {! !}

-- map-η′ : ∀ {f : X → Y}
--   → (xs : M X)
--   → (y : Y)
--   → map f xs ≡ η y
--   → ∃[ x ∈ X ] (xs ≡ η x)
-- map-η′ {X = X} {f = f} = M.ind {P = P} isPropP
--   empty* singl* {! !} where
--   P : M X → Type _
--   P xs = ∀ y → map f xs ≡ η y → ∃[ x ∈ X ] xs ≡ η x

--   isPropP = λ xs → isPropΠ2 λ y h → isPropPropTrunc

--   empty* : ∀ y → ε ≡ η y → _
--   empty* y = Empty.elim ∘ η≢ε ∘ sym

--   singl* : ∀ x y → map f (η x) ≡ η y → ∃[ x′ ∈ X ] η x ≡ η x′
--   singl* x y h = ∣ x , refl ∣₁

--   union* : ∀ {xs₁ xs₂}
--     → P xs₁
--     → P xs₂
--     → ∀ y → map f (xs₁ ⊕ xs₂) ≡ η y → ∃[ x ∈ X ] xs₁ ⊕ xs₂ ≡ η x
--   union* indH-xs₁ indH-xs₂ y h = PT.map2 {! !} {! !} {! !} where

--     _ = {! PT.rec ?  !}

module _ where
  open import Cubical.Data.Vec.Base as Vec
  open import Cubical.Data.List.Base as List

  fromVec : ∀ {n} → Vec X n → M X
  fromVec = Vec.foldr M._∷_ ε

  to∥Vec∥₁ : (xs : M X) → ∥ Vec X (sizeof xs) ∥₁
  to∥Vec∥₁ = ind (λ xs → isPropPropTrunc) (∣ [] ∣₁) (λ x → ∣ x Vec.∷ Vec.[] ∣₁) (PT.map2 Vec._++_)

  fromList : List X → M X
  fromList = List.foldr M._∷_ ε

-- module _ where
--   open import Multiset.FMSet as FMSet
--     using (FMSet)

--   toFMSet : M X → FMSet X
--   toFMSet = M.elim (λ xs → FMSet.isSetFMSet) FMSet.[] FMSet.[_] FMSet._++_ {! !} {! !} {! !}

--   fromFMSet : FMSet X → M X
--   fromFMSet = FMSet.∷-elim (λ xs → isSetM) ε (λ x → x ∷_) λ x y {_} {xs} → ∷-swap x y xs

map-id : ∀ {ℓ} {X : Type ℓ} (s : M X)
  → map (λ x → x) s ≡ s
map-id =
  ind (λ _ → isSetM _ _)
      refl
      (λ _ → refl)
      (λ ih1 ih2 → cong₂ _⊕_ ih1 ih2)

map-comp : ∀ {ℓ ℓ' ℓ''} {X : Type ℓ} {Y : Type ℓ'} {Z : Type ℓ''}
  → (g : Y → Z) (f : X → Y) (s : M X)
  → map g (map f s) ≡ map (λ x → g (f x)) s
map-comp g f =
  ind (λ _ → isSetM _ _)
      refl
      (λ _ → refl)
      (λ ih1 ih2 → cong₂ _⊕_ ih1 ih2)
