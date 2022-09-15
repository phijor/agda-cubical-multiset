module Multiset.OverSet.Properties where

open import Multiset.Prelude
open import Multiset.Util.Path using (subst⁻Domain)

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Function
  using
    ( _∘_
    )
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Univalence
open import Cubical.Foundations.Path
open import Cubical.Foundations.Transport

open import Cubical.Data.Unit as ⊤
  using
    ( Unit
    ; tt
    )

open import Cubical.Data.Empty as Empty
  using
    ( ⊥
    )
open import Cubical.Data.Nat as ℕ
  using
    ( ℕ
    ; zero
    ; suc
    ; _+_
    )
open import Cubical.Data.Sum as Sum
  using
    ( _⊎_
    )
open import Cubical.Data.Sigma as Sigma
  using
    ( ΣPathP
    ; ∃-syntax
    )
open import Cubical.Data.SumFin as Fin
  using
    ( Fin
    ; fsuc
    ; fzero
    )

open import Cubical.HITs.SetQuotients as SQ
  using ()
  renaming
    ( _/_ to _/₂_
    ; eq/ to eq/₂
    ; [_] to [_]₂
    ; squash/ to squash/₂
    )
open import Cubical.HITs.PropositionalTruncation as PT
  using
    ( ∣_∣₁
    )

open import Cubical.Relation.Binary.Base using (module BinaryRelation)

open import Multiset.Util
  using
    ( Path→cong
    ; Π⊥≡elim
    )
open import Multiset.OverSet.Base

open BinaryRelation

private
  variable
    ℓ ℓ' : Level
    X : Type ℓ

private
  isSetSetQuotient : {R : X → X → Type ℓ'} → isSet (X /₂ R)
  isSetSetQuotient = squash/₂

isSetSymmQuot : ∀ {n} → isSet ((Fin n → X) /₂ SymmetricAction n)
isSetSymmQuot = squash/₂

private
  [_]∼ : {n : ℕ} → (v : Fin n → X) → (Fin n → X) /₂ SymmetricAction n
  [_]∼ = [_]₂ {R = SymmetricAction _}

eq/∼ : ∀ {sz} {v w : Fin sz → X} → v ∼ w → [ v ]∼ ≡ [ w ]∼
eq/∼ rel = eq/₂ _ _ rel


module _ {ℓ} {X : Type ℓ} (n : ℕ) where
  _∼ₙ_ = SymmetricAction {X = X} n

  isRefl-∼ : isRefl _∼ₙ_
  isRefl-∼ v = ∣ idEquiv _ , ua→ (λ k → refl {x = v k}) ∣₁

  isSym-∼ : isSym _∼ₙ_
  isSym-∼ v w = PT.map λ { (σ , rel) → invEquiv σ , ua→ λ k → inv-rel σ (ua→⁻ rel) k } where
    inv-rel : ∀ (σ : Fin n ≃ Fin n)
      → (∀ k → v k ≡ w (equivFun σ k))
      → ∀ k → w k ≡ v (invEq σ k)
    inv-rel σ rel k = cong w (sym $ secEq σ k) ∙ (sym $ rel _)

  isTrans-∼ : isTrans _∼ₙ_
  isTrans-∼ u v w = PT.map2 λ { (σ , u∼v) (ψ , v∼w) → trans-rel σ ψ u∼v v∼w } where
    module _
      (σ ψ : Fin n ≃ Fin n)
      (u∼v : PathP (λ i → ua σ i → X) u v)
      (v∼w : PathP (λ i → ua ψ i → X) v w) where

      trans-rel : Σ[ φ ∈ (Fin n ≃ Fin n) ] PathP (λ i → ua φ i → X) u w
      trans-rel = σ ∙ₑ ψ , ua→ λ k → ua→⁻ u∼v k ∙ ua→⁻ v∼w (equivFun σ k)

  open isEquivRel

  isEquivRel-∼ : isEquivRel _∼ₙ_
  reflexive isEquivRel-∼ = isRefl-∼
  symmetric isEquivRel-∼ = isSym-∼
  transitive isEquivRel-∼ = isTrans-∼

  isPropValued-∼ : isPropValued _∼ₙ_
  isPropValued-∼ v w = PT.isPropPropTrunc

  isEffective-∼ : isEffective _∼ₙ_
  isEffective-∼ = SQ.isEquivRel→isEffective isPropValued-∼ isEquivRel-∼

  effective : ∀ {v w : Fin n → X} → [ v ]∼ ≡ [ w ]∼ → v ∼ₙ w
  effective {v} {w} = invIsEq (isEffective-∼ v w)

isPermutationInvariantˡ : ∀ {n : ℕ}
  → (v : Fin n → X)
  → (σ : Fin n ≃ Fin n)
  → [ v ∘ equivFun σ ]∼ ≡ [ v ]∼
isPermutationInvariantˡ {X = X} {n = n} v σ = eq/₂ (v ∘ equivFun σ) v ∣ σ , ua→ rel ∣₁ where
  rel : (k : Fin n) → v (equivFun σ k) ≡ v (equivFun σ k)
  rel k = refl

isPermutationInvariant : ∀ {m n : ℕ}
  → {v w : Fin m → X}
  → (e : Fin n ≃ Fin m)
  → [ v ]∼ ≡ [ w ]∼
  → [ v ∘ equivFun e ]∼ ≡ [ w ∘ equivFun e ]∼
isPermutationInvariant {X = X} {m = m} {n = n} {v} {w} e [v]≡[w] = eq/₂ (v ∘ equivFun e) (w ∘ equivFun e) rel' where
  rel : v ∼ w
  rel = effective m [v]≡[w]

  module _ (σ : Fin m ≃ Fin m) (p : PathP (λ i → ua σ i → X) v w) where

    σ' : Fin n ≃ Fin n
    σ' = e ∙ₑ σ ∙ₑ invEquiv e

    lift-rel : Σ[ σ' ∈ (Fin n ≃ Fin n) ] (PathP (λ i → ua σ' i → X) (v ∘ equivFun e) (w ∘ equivFun e))
    lift-rel = σ' , ua→ λ (k : Fin n) →
      (v $ equivFun e k) ≡⟨ ua→⁻ p (equivFun e k) ⟩
      (w $ equivFun σ $ equivFun e k) ≡⟨ cong w (sym $ secEq e _) ⟩
      (w $ equivFun e $ (invEq e) $ (equivFun σ) $ (equivFun e) $ k) ≡⟨⟩
      (w $ equivFun e $ equivFun σ' k) ∎

  rel' : (v ∘ equivFun e) ∼ (w ∘ equivFun e)
  rel' = PT.map (λ { (σ , p) → lift-rel σ p }) rel

private
  substCommSlice′ : ∀ {ℓ ℓ′ ℓ″} {A : Type ℓ}
                    → (B : A → Type ℓ′)
                    → (C : A → Type ℓ″)
                    → (F : ∀ a → B a → C a)
                    → {x y : A} (p : x ≡ y) (u : B x)
                    → subst C p (F x u) ≡ F y (subst B p u)
  substCommSlice′ B C F p Bx a =
    transport-fillerExt⁻ (cong C p) a (F _ (transport-fillerExt (cong B p) a Bx))

substComm[] : ∀ {m n : ℕ}
  → (p : m ≡ n)
  → (v : Fin m → X)
  → subst (PVect X) p [ v ]∼ ≡ [ v ∘ subst⁻ Fin p ]∼
substComm[] {X = X} p v = step₁ ∙ step₂ where
  step₁ : subst (PVect X) p [ v ]∼ ≡ [ subst (λ sz → Fin sz → X) p v ]∼
  step₁ = substCommSlice′ {A = ℕ} (λ sz → Fin sz → X) (PVect X) (λ _ → [_]∼) p v

  step₂ : [ subst (λ sz → Fin sz → X) p v ]∼ ≡ [ v ∘ subst⁻ Fin p ]∼
  step₂ = cong [_]∼ (subst⁻Domain v (sym p))

fromPathP[] : ∀ {m n : ℕ}
  → (p : m ≡ n)
  → (v : Fin m → X)
  → (w : Fin n → X)
  → PathP (λ i → PVect X (p i)) [ v ]∼ [ w ]∼
  → [ v ]∼ ≡ [ w ∘ (subst Fin p) ]∼
fromPathP[] p v w q = fromPathP⁻ q ∙ substComm[] (sym p) w
  
effectiveDep : ∀ {m n : ℕ}
  → (p : m ≡ n)
  → (v : Fin m → X)
  → (w : Fin n → X)
  → PathP (λ i → PVect X (p i)) [ v ]∼ [ w ]∼
  → v ∼ (w ∘ (subst Fin p))
effectiveDep {m = m} p v w q = effective m (fromPathP[] p v w q)


isSetFMSet : isSet (FMSet X)
isSetFMSet = isSetΣ ℕ.isSetℕ (λ _ → isSetSymmQuot)

FMSetPath : ∀ {n}
  → (v w : Fin n → X)
  → (∃[ σ ∈ (Fin n ≃ Fin n) ] PathP (λ i → (ua σ i → X)) v w)
  → Path (FMSet X) (n , [ v ]₂) (n , [ w ]₂)
FMSetPath v w = PT.elim (λ _ → isSetFMSet _ _)
  λ (σ , p) → ΣPathP (refl , (eq/₂ v w ∣ σ , p ∣₁))

FMSetPathP : ∀ {n m}
  → {v : (Fin m → X) /₂ SymmetricAction m}
  → {w : (Fin n → X) /₂ SymmetricAction n}
  → (p : m ≡ n)
  → (q : PathP (λ i → (Fin (p i) → X) /₂ SymmetricAction (p i)) v w)
  → Path (FMSet X) (m , v) (n , w)
FMSetPathP {n = n} {v} {w} p q = λ i → p i , q i

elimSet : ∀ {ℓ'} {B : FMSet X → Type ℓ'}
  → (∀ xs → isSet (B xs))
  → (bs : ∀ {sz} → (v : Fin sz → X) → B (sz , [ v ]₂))
  → (∀ {sz} (v w : Fin sz → X) → (r : v ∼ w) → PathP (λ i → B (sz , eq/₂ v w r i)) (bs v) (bs w))
  → (xs : FMSet X) → B xs
elimSet {B = B} setB bs bs-rel (sz , v) = SQ.elim {P = λ v → B (sz , v)} (setB ∘ (sz ,_)) bs bs-rel v

elimProp : ∀ {ℓ'} {P : FMSet X → Type ℓ'}
  → (∀ xs → isProp (P xs))
  → (ps : ∀ {sz} → (xs : Fin sz → X) → P (sz , [ xs ]₂))
  → (xs : FMSet X) → P xs
elimProp {P = P} propP ps = elimSet {B = P} (isProp→isSet ∘ propP) ps (λ {sz} v w r → isProp→PathP (λ i → propP (sz , eq/₂ v w r i)) (ps v) (ps w))

-- elimProp2 : ∀ {ℓ'} {P : (xs ys : FMSet X) → Type ℓ'}
--   → (∀ xs ys → isProp (P xs ys))
--   → (ps : ∀ {sz₁ sz₂} → (xs : Fin sz₁ → X) (ys : Fin sz₂ → X) → P (sz₁ , [ xs ]₂) (sz₂ , [ ys ]₂))
--   → (xs ys : FMSet X) → P xs ys
-- elimProp2 {P = P} propP ps = elimProp {P = λ xs → ∀ ys → P xs ys} (λ xs → isPropΠ λ ys → propP xs ys) λ {sz} xs → elimProp {P = λ ys → P (sz , [ xs ]₂) ys} (λ ys → propP _ ys) {! !}

rec : ∀ {ℓ'} {A : Type ℓ'}
  → isSet A
  → (as : ∀ {sz} → (Fin sz → X) → A)
  → (∀ {sz} (v w : Fin sz → X) → v ∼ w → as v ≡ as w)
  → FMSet X → A
rec setA as as-rel (n , v) = SQ.rec setA as as-rel v

module _ {ℓx ℓy} {X : Type ℓx} {Y : Type ℓy} where
  map-members : ∀ {sz} → (f : X → Y) → PVect X sz → PVect Y sz
  map-members {sz = sz} f = SQ.rec isSetSetQuotient (λ v → [ f ∘ v ]₂) well-defined where
    well-defined : ∀ v w → _
    well-defined v w =
      PT.elim (λ _ → isSetSetQuotient [ f ∘ v ]₂ [ f ∘ w ]₂)
        ((λ { (σ , p) → eq/₂ _ _ ∣ σ , Path→cong f p ∣₁ }))

  map : (f : X → Y) → FMSet X → FMSet Y
  map f (sz , v) = sz , map-members f v

  map-β : ∀ {n} f (v : Fin n → X) → map f (n , [ v ]₂) ≡ (n , [ f ∘ v ]₂)
  map-β v f = refl

mapId : (xs : FMSet {ℓ = ℓ} X) → map (λ x → x) xs ≡ xs
mapId = elimProp (λ xs → isSetFMSet (map (λ x → x) xs) xs) (λ v → refl {x = _ , [ v ]₂})

mapComp : ∀ {ℓx ℓy ℓz} {X : Type ℓx} {Y : Type ℓy} {Z : Type ℓz}
  → (g : Y → Z)
  → (f : X → Y)
  → ∀ xs → map g (map f xs) ≡ map (g ∘ f) xs
mapComp g f = elimProp (λ xs → isSetFMSet _ _) (λ xs → refl)

[] : FMSet X
[] = 0 , [ Empty.elim ]₂

[_] : X → FMSet X
[ x ] = 1 , [ (λ _ → x) ]∼

private
  _∷ᶠ_ : ∀ {n} → (x : X) → (xs : Fin n → X) → Fin (suc n) → X
  x ∷ᶠ xs = Sum.rec (λ _ → x) xs

  ∷ᶠ-β : ∀ {n} → (xs : Fin (suc n) → X) → (xs fzero) ∷ᶠ (xs ∘ fsuc) ≡ xs
  ∷ᶠ-β {n = n} xs =
    funExt (
      Sum.elim
        (λ { tt → refl {x = xs fzero} })
        (λ (k : Fin n) → refl {x = xs (fsuc k)})
    )

  fsuc≃ : ∀ {n} → Fin n ≃ Fin n → Fin (suc n) ≃ Fin (suc n)
  fsuc≃ σ = Sum.⊎-equiv (idEquiv Unit) σ

  infixr 5 _∷ᶠ_

  module _ {n : ℕ} where
    [_]∷_ : (x : X) → (v : Fin n → X) → (Fin (suc n) → X) /₂ SymmetricAction (suc n)
    [ x ]∷ v = [ x ∷ᶠ v ]₂

    []∷-well-defined : {x : X} → (v w : Fin n → X) → (v ∼ w) → [ x ]∷ v ≡ [ x ]∷ w
    []∷-well-defined {x = x} v w v∼w = eq/₂ (x ∷ᶠ v) (x ∷ᶠ w) rel
      where
        rel : SymmetricAction (suc n) (x ∷ᶠ v) (x ∷ᶠ w)
        rel = PT.map (λ (σ , p) → (fsuc≃ σ) , (ua→ (Sum.elim (λ (_ : Unit) → refl) (ua→⁻ p)))) v∼w

_∷_ : X → FMSet X → FMSet X
_∷_ {X = X} x (n , [v]) = (suc n) , x∷v where
  x∷v : (Fin (suc n) → X) /₂ SymmetricAction (suc n)
  x∷v = SQ.elim (λ _ → isSetSymmQuot {n = suc n}) [ x ]∷_ []∷-well-defined [v]

infixr 5 _∷_

∷-comm : ∀ x y → (xs : FMSet X)
  → x ∷ y ∷ xs ≡ y ∷ x ∷ xs
∷-comm {X = X} x y (n , v) = SQ.elimProp
  {P = λ [v] → x ∷ y ∷ (n , [v]) ≡ y ∷ x ∷ (n , [v])}
  (λ _ → isSetFMSet _ _)
  (λ v → FMSetPath _ _ ∣ swap₀₁ , (ua→ (comm v)) ∣₁)
  v
  where
    open Sum

    swap₀₁ : (Fin (2 + n)) ≃ (Fin (2 + n))
    swap₀₁ = invEquiv ⊎-assoc-≃ ∙ₑ ⊎-equiv ⊎-swap-≃ (idEquiv (Fin n)) ∙ₑ ⊎-assoc-≃

    module _ (v : Fin n → X) where
      comm : (k : Fin (2 + n))
        → (x ∷ᶠ y ∷ᶠ v) k ≡ (y ∷ᶠ x ∷ᶠ v) ((equivFun swap₀₁) k)
      comm (inl x) = refl
      comm (fsuc (inl x)) = refl
      comm (fsuc (fsuc x)) = refl

isContrFMSet₀ : ([v] : (Fin 0 → X) /₂ SymmetricAction 0) → [] ≡ (0 , [v])
isContrFMSet₀ [v] = ΣPathP
  ( refl
  , ( SQ.elimProp {P = λ [v] → [ Empty.elim ]₂ ≡ [v]}
      (λ _ → isSetSymmQuot _ _)
      (λ v → cong [_]₂ (Π⊥≡elim v))
      [v]
    )
  )

FMSetContr≃ℕ : (isContr X) → FMSet X ≃ ℕ
FMSetContr≃ℕ {X = X} contrX = Sigma.Σ-contractSnd contrMembers/∼ where
  module _ (sz : ℕ) where
    contrMembers : isContr (Fin sz → X)
    contrMembers = isContrΠ (λ _ → contrX)

    contrMembers/∼ : isContr ((Fin sz → X) /₂ SymmetricAction sz)
    contrMembers/∼ = center , contraction where
      center : (Fin sz → X) /₂ SymmetricAction sz
      center = [ contrMembers .fst ]₂

      contraction : ∀ (y : (Fin sz → X) /₂ SymmetricAction sz) → center ≡ y
      contraction = SQ.elimProp
        (λ _ → isSetSetQuotient _ _)
        λ (y : Fin sz → X) → cong [_]₂ (contrMembers .snd y)

∷-elim : {B : FMSet X → Type ℓ'}
  → (setB : ∀ m → isSet (B m))
  → (nil : B [])
  → (cons : (x : X) → {xs : FMSet X} → B xs → B (x ∷ xs))
  → (comm : (x y : X) → {xs : FMSet X} → {b : B xs} → PathP (λ i → B (∷-comm x y xs i)) (cons x (cons y b)) (cons y (cons x b)))
  → (m : FMSet X) → B m
∷-elim {X = X} {B = B} setB nil cons comm = elimSet {B = B} setB fun well-defined where
  fun : ∀ {sz} (v : Fin sz → X) → B (sz , [ v ]₂)
  fun {zero} v = subst (λ v → B (0 , [ v ]₂)) (Π⊥≡elim v) nil
  fun {suc sz} v = subst (λ v → B (suc sz , [ v ]₂)) p rec₂ where
    rec₁ : B (sz , [ v ∘ fsuc ]₂)
    rec₁ = fun (v ∘ fsuc)

    rec₂ : B (v fzero ∷ (sz , [ v ∘ fsuc ]₂))
    rec₂ = cons (v fzero) rec₁

    p : (v fzero ∷ᶠ v ∘ fsuc) ≡ v
    p = ∷ᶠ-β v

  well-defined : ∀ {sz} (v w : Fin sz → X) (r : v ∼ w)
    → PathP (λ i → B (sz , eq/₂ v w r i)) (fun v) (fun w)
  well-defined {zero} v w = PT.elim (λ r p q → isSet→SquareP (λ i j → setB _) p q _ _) {! subst-filler (λ v → B (0 , [ v ]₂)) (Π⊥≡elim v) nil !}
  well-defined {suc sz} v w = PT.elim (λ r p q → isSet→SquareP (λ i j → setB _) p q _ _) {! !}

∷-elimProp : ∀ {P : FMSet X → Type ℓ'}
  → (propP : ∀ xs → isProp (P xs))
  → (nil : P [])
  → (cons : (x : X) → {xs : FMSet X} → P xs → P (x ∷ xs))
  → (m : FMSet X) → P m
∷-elimProp {P = P} propP nil cons = ∷-elim {B = P} (isProp→isSet ∘ propP) nil cons comm where
  comm = λ x y {xs} {p} → isProp→PathP (λ i → propP _) (cons x (cons y p)) (cons y (cons x p))

_++_ : FMSet X → FMSet X → FMSet X
_++_ = ∷-elim (λ xs → isSetΠ λ ys → isSetFMSet)
  (λ ys → ys)
  (λ x xs++_ ys → x ∷ (xs++ ys))
  λ x y {xs} {xs++_} → funExt (∷-comm x y ∘ xs++_)


map-head : ∀ {ℓ'} {Y : Type ℓ'} {x} {xs}
  → (f : X → Y)
  → map f (x ∷ xs) ≡ f x ∷ map f xs
map-head {x = x} {xs = xs} f = FMSetPathP (refl {x = suc (size xs)}) {! !}
  -- ∷-elimProp {P = λ xs → map f (x ∷ xs) ≡ f x ∷ map f xs} (λ xs → isSetFMSet _ _) nil* {! !} xs where
  -- nil* : ⟅ [ f ∘ Sum.rec (λ _ → x) Empty.elim ]₂ ⟆ ≡ ⟅ [ Sum.rec (λ _ → f x) (f ∘ Empty.elim) ]₂ ⟆
  -- nil* = FMSetPath _ _ ∣ idEquiv _ , ua→ (Sum.elim (λ _ → refl {x = f x}) Empty.elim) ∣₁

  -- cons* : ∀ y {ys}
  --   → map f (y ∷ ys) ≡ f y ∷ map f ys
  --   → map f (x ∷ y ∷ ys) ≡ f x ∷ map f (y ∷ ys)
  -- cons* y {ys} indH-ys = {! !}
