module Multiset.Ordering.Perm where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Function

open import Cubical.Data.List as List hiding ([_] ; elim ; rec)
open import Cubical.HITs.SetQuotients as SQ using (_/_)

private
  variable
    ℓ : Level
    A : Type ℓ
    x y : A
    xs ys zs : List A

data Swap {A : Type ℓ} : List A → List A → Type ℓ where
  swap-head : (x y : A) {xs : List A} → Swap (x ∷ y ∷ xs) (y ∷ x ∷ xs)
  swap-tail : {x : A} {xs ys : List A}
    → Swap xs ys
    → Swap (x ∷ xs) (x ∷ ys)

data Perm {A : Type ℓ} : List A → List A → Type ℓ where
  stop : ∀ {xs} → Perm xs xs
  swap : ∀ {xs ys zs}
    → (s : Swap xs ys)
    → (p : Perm ys zs)
    → Perm xs zs

transP : Perm xs ys → Perm ys zs → Perm xs zs
transP stop q = q
transP (swap s p) q = swap s (transP p q)

infixr 30 _∙ₚ_
_∙ₚ_ = transP


substP : xs ≡ ys → Perm xs ys
substP {xs = xs} eq = subst (Perm xs) eq stop

congPerm : Perm xs ys → Perm (x ∷ xs) (x ∷ ys)
congPerm stop = stop
congPerm (swap s p) = swap (swap-tail s) (congPerm p)

congPerm′ : (x : A) → Perm xs ys → Perm (x ∷ xs) (x ∷ ys)
congPerm′ x = congPerm

prependP : (xs : List A) {ys zs : List A}
  → Perm ys zs
  → Perm (xs ++ ys) (xs ++ zs)
prependP [] ps = ps
prependP (x ∷ xs) ps = congPerm (prependP xs ps)

invS : Swap xs ys → Swap ys xs
invS (swap-head x y) = swap-head y x
invS (swap-tail s) = swap-tail (invS s)

invP : Perm xs ys → Perm ys xs
invP stop = stop
invP {xs = xs} {ys = ys} (swap {ys = ys′} s p) = goal where
  q : Perm ys ys′
  q = invP p

  goal : Perm ys xs
  goal = q ∙ₚ swap (invS s) stop

infix 40 _⁻ᵖ
_⁻ᵖ = invP

moveHeadP : (x : A) (xs : List A) {ys : List A}
  → Perm (x ∷ xs ++ ys) (xs ++ x ∷ ys)
moveHeadP x [] = stop
moveHeadP x (y ∷ xs) = swap (swap-head x y) (congPerm′ y (moveHeadP x xs))

commP : (xs ys : List A) → Perm (xs ++ ys) (ys ++ xs)
commP xs [] = substP (++-unit-r xs)
commP xs (y ∷ ys) = goal where
  comm : Perm (xs ++ ys) (ys ++ xs)
  comm = commP xs ys

  goal : Perm (xs ++ y ∷ ys) (y ∷ ys ++ xs)
  goal = invP (moveHeadP y xs) ∙ₚ congPerm {x = y} comm

appendP : {xs ys zs : List A}
  → Perm xs ys
  → Perm (xs ++ zs) (ys ++ zs)
appendP {xs = xs} {ys = ys} {zs = zs} p = commP xs zs ∙ₚ prependP zs p ∙ₚ commP zs ys

module _ {ℓ} (A : Type ℓ) where
  MSet : Type ℓ
  MSet = List A / Perm {A = A}

  [_] : List A → MSet
  [_] = SQ.[_]

  perm≡ : {xs ys : List A} → (p : Perm xs ys) → [ xs ] ≡ [ ys ]
  perm≡ p = SQ.eq/ _ _ p

  isSetMSet : isSet MSet
  isSetMSet = SQ.squash/

  elim : ∀ {ℓ} {B : MSet → Type ℓ}
    → (∀ xs → isSet (B xs))
    → ([_]* : (as : List A) → B [ as ])
    → (∀ xs ys → (p : Perm xs ys) → PathP (λ i → B (perm≡ p i)) [ xs ]* [ ys ]*)
    → (xs : MSet) → B xs
  elim {B = B} setB [_]* well-defined = go where
    setB' : isOfHLevelDep 2 B
    setB' = isOfHLevel→isOfHLevelDep 2 setB

    go : (xs : MSet) → B xs
    go SQ.[ as ] = [ as ]*
    go (SQ.eq/ xs ys r i) = well-defined xs ys r i
    go (SQ.squash/ xs ys p q i j) = setB' (go xs) (go ys) (cong go p) (cong go q) (SQ.squash/ xs ys p q) i j

  rec : ∀ {ℓ} {B : Type ℓ}
    → (isSet B)
    → ([_]* : List A → B)
    → (∀ xs ys → (p : Perm xs ys) → [ xs ]* ≡ [ ys ]*)
    → MSet → B
  rec is-set-B [_]* well-defined = SQ.rec is-set-B [_]* well-defined

  rec2 : ∀ {ℓ} {B : Type ℓ}
    → (isSet B)
    → (f : List A → List A → B)
    → (f-left : ∀ xs ys zs → (p : Perm xs ys) → f xs zs ≡ f ys zs)
    → (f-right : ∀ xs ys zs → (p : Perm ys zs) → f xs ys ≡ f xs zs)
    → MSet → MSet → B
  rec2 is-set-B f f-left f-right = SQ.rec2 is-set-B f f-left f-right

  ∅ : MSet
  ∅ = SQ.[ [] ]

  _⊍_ : MSet → MSet → MSet
  _⊍_ = rec2 isSetMSet (λ xs ys → [ xs ++ ys ])
    (λ xs ys zs p → perm≡ (appendP p))
    (λ xs ys zs p → perm≡ (prependP xs p))
