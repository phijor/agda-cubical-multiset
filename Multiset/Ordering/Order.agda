{-# OPTIONS --safe --lossy-unification #-}

module Multiset.Ordering.Order where


open import Cubical.Core.Everything
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Everything
open import Cubical.Data.List as List hiding ([_])
open import Cubical.Data.Nat using (zero ; suc ; _+_ ; +-zero ; +-suc)
open import Cubical.Data.Sigma
open import Cubical.HITs.SetQuotients as SQ
open import Cubical.Relation.Binary
open BinaryRelation
open isEquivRel
open import Cubical.Data.Empty as Empty
open import Cubical.Data.Sum as Sum
open import Multiset.ListQuotient.Base hiding (M)

-- ====================================================================

-- Linear orders

record isLinOrder {A : Type} (R : A → A → Type) : Type where
  field
    asymR  : {x y : A} → R x y → R y x → ⊥
    transR : {x y z : A} → R x y → R y z → R x z
    propR  : {x y : A} → isProp (R x y)
    totR   : (x y : A) → R x y ⊎ (R y x ⊎ (x ≡ y))

  irreflR : {x : A} → R x x → ⊥
  irreflR r = asymR r r

  totR-case1 : (x y : A) (r : R x y) → totR x y ≡ inl r
  totR-case1 x y r with totR x y
  ... | inl r' = cong inl (propR _ _)
  ... | inr (inl r') = Empty.rec (asymR r r')
  ... | inr (inr eq) = Empty.rec (irreflR (subst (R x) (sym eq) r))

  totR-case2 : (x y : A) (r : R x y) → totR y x ≡ inr (inl r)
  totR-case2 x y r with totR y x
  ... | inl r' = Empty.rec (asymR r' r)
  ... | inr (inl r') = cong inr (cong inl (propR _ _))
  ... | inr (inr eq) = Empty.rec (irreflR (subst (R x) eq r))

  totR-case3 : isSet A → (x y : A) (r : x ≡ y) → totR x y ≡ inr (inr r)
  totR-case3 setA x y eq with totR x y
  ... | inl r = Empty.rec (irreflR (subst (R x) (sym eq) r))
  ... | inr (inl r) = Empty.rec (irreflR (subst (R y) eq r))
  ... | inr (inr eq') = cong inr (cong inr (setA _ _ _ _))

-- Induction principle to prove stuff involving the trichotomy
elimTotR : ∀{ℓ ℓ' ℓ''} {A : Type ℓ} {x y : A}
  → (R : A → A → Type ℓ'')
  → (B : (R x y ⊎ (R y x ⊎ (x ≡ y))) → Type ℓ')
  → ((r : R x y) → B (inl r))
  → ((r : R y x) → B (inr (inl r)))
  → ((eq : x ≡ y) → B (inr (inr eq)))
  → (r : R x y ⊎ (R y x ⊎ (x ≡ y))) → B r
elimTotR R B f g h (inl r) = f r
elimTotR R B f g h (inr (inl r)) = g r
elimTotR R B f g h (inr (inr r)) = h r

recTotR : ∀{ℓ ℓ' ℓ''} {A : Type ℓ} {B : Type ℓ'}
  → (R : A → A → Type ℓ'')
  → {x y : A}
  → (R x y → B)
  → (R y x → B)
  → (x ≡ y → B)
  → R x y ⊎ (R y x ⊎ (x ≡ y)) → B
recTotR R f g h = elimTotR R _ f g h

casesTotR : ∀{ℓ ℓ' ℓ''} {A : Type ℓ} {B : Type ℓ'}
  → (R : A → A → Type ℓ'')
  → {x y : A}
  → B → B → B
  → R x y ⊎ (R y x ⊎ (x ≡ y)) → B
casesTotR R f g h = recTotR R (λ _ → f) (λ _ → g) (λ _ → h)

-- ====================================================================

-- Permutations on lists (there are of course other possible
-- definitions, possibly already in the cubical library, but this one
-- is pretty convenient here)

data Perm {A : Type} : List A → List A → Type where
  stop : ∀ {xs} → Perm xs xs
  perm : ∀ {x y xs ys zs} → Perm (xs ++ y ∷ x ∷ ys) zs
    → Perm (xs ++ x ∷ y ∷ ys) zs

transP : {A : Type} {xs ys zs : List A}
  → Perm xs ys → Perm ys zs → Perm xs zs
transP stop qs = qs
transP (perm ps) qs = perm (transP ps qs)

infixr 30 _∙ₚ_
_∙ₚ_ = transP

invP : {A : Type} {xs ys : List A}
  → Perm xs ys → Perm ys xs
invP stop = stop
invP (perm ps) = transP (invP ps) (perm stop)

infix 40 _⁻ᵖ
_⁻ᵖ = invP

substP : {A : Type} {xs ys : List A} → xs ≡ ys → Perm xs ys
substP {xs = xs} eq = subst (Perm xs) eq stop

congPerm : {A : Type} {x : A} {xs ys : List A}
  → Perm xs ys → Perm (x ∷ xs) (x ∷ ys)
congPerm stop = stop
congPerm {x = x} (perm {xs = xs} ps) = perm {xs = x ∷ xs} (congPerm ps)

reflP : {A : Type} → (xs : List A) → Perm xs xs
reflP [] = stop
reflP (x ∷ xs) = congPerm {x = x} (reflP xs)

prependP : {A : Type} (xs : List A) {ys zs : List A}
  → Perm ys zs → Perm (xs ++ ys) (xs ++ zs)
prependP [] ps = ps
prependP (x ∷ xs) ps = congPerm (prependP xs ps)

appendP : {A : Type} {xs ys zs : List A}
  → Perm xs ys → Perm (xs ++ zs) (ys ++ zs)
appendP stop = stop
appendP {zs = zs} (perm {xs = xs}{ys} ps) =
  transP (substP (++-assoc xs _ _))
         (perm {ys = ys ++ zs} (transP (substP (sym (++-assoc xs _ _)))
                                       (appendP ps)))

moveHeadP : {A : Type} (x : A) (xs : List A) {ys : List A}
  → Perm (x ∷ xs ++ ys) (xs ++ x ∷ ys)
moveHeadP x [] = stop
moveHeadP x (y ∷ xs) = perm {xs = []} (congPerm (moveHeadP x xs))

commP : {A : Type} → (xs ys : List A)
  → Perm (xs ++ ys) (ys ++ xs)
commP xs [] = substP (++-unit-r xs)
commP xs (y ∷ ys) = goal where
  indH : Perm (xs ++ ys) (ys ++ xs)
  indH = commP xs ys

  lem : Perm (y ∷ xs ++ ys) (y ∷ ys ++ xs)
  lem = congPerm indH

  goal : Perm (xs ++ y ∷ ys) (y ∷ ys ++ xs)
  goal = (moveHeadP y xs {ys = ys} ⁻ᵖ) ∙ₚ lem

mapP : {A B : Type} (f : A → B) {xs ys : List A}
  → Perm xs ys → Perm (List.map f xs) (List.map f ys)
mapP f stop = stop
mapP f {ys = zs} (perm {xs = xs} ps) =
  transP (substP (mapList++ xs))
         (perm (transP (substP (sym (mapList++ xs)))
                       (mapP f ps)))

-- ====================================================================

-- Yet another definition of finite bags, as quotients of lists

Mset : Type → Type
Mset A = List A / Perm

isSetMset : ∀ {A} → isSet (Mset A)
isSetMset = squash/

elimMset : ∀ {ℓ} {A : Type} {B : Mset A → Type ℓ}
  → (∀ xs → isSet (B xs))
  → ([_]* : (as : List A) → B [ as ])
  → (∀ xs ys → (p : Perm xs ys) → PathP (λ i → B (eq/ xs ys p i)) [ xs ]* [ ys ]*)
  → (xs : Mset A) → B xs
elimMset {A = A} {B = B} setB [_]* well-defined = go where
  setB' : isOfHLevelDep 2 B
  setB' = isOfHLevel→isOfHLevelDep 2 setB

  go : (xs : Mset A) → B xs
  go [ as ] = [ as ]*
  go (eq/ xs ys r i) = well-defined xs ys r i
  go (squash/ xs ys p q i j) = setB' (go xs) (go ys) (cong go p) (cong go q) (squash/ xs ys p q) i j

elimPropMset : ∀ {ℓ} {A : Type} {P : Mset A → Type ℓ}
  → (∀ xs → isProp (P xs))
  → (P[_] : (as : List A) → P [ as ])
  → (xs : Mset A) → P xs
elimPropMset {P = P} propP P[_] = elimMset {B = P}
  (λ xs → isProp→isSet (propP xs))
  P[_]
  (λ as bs p → isProp→PathP (λ i → propP (eq/ as bs p i)) P[ as ] P[ bs ])

elimProp2Mset : ∀ {ℓ} {A A' : Type} {P : Mset A → Mset A' → Type ℓ}
  → (∀ xs ys → isProp (P xs ys))
  → (P[_,_] : (as : List A) → (bs : List A') → P [ as ] [ bs ])
  → (xs : Mset A) → (ys : Mset A') → P xs ys
elimProp2Mset propP P[_,_] = elimPropMset
  (λ xs → isPropΠ λ ys → propP xs ys)
  (λ as → elimPropMset (λ bs → propP [ as ] bs) P[ as ,_])

recMset : ∀ {ℓ} {A : Type} {B : Type ℓ}
  → (isSet B)
  → ([_]* : List A → B)
  → (∀ xs ys → (p : Perm xs ys) → [ xs ]* ≡ [ ys ]*)
  → Mset A → B
recMset setB = elimMset (λ _ → setB)

rec2Mset : ∀ {ℓ} {A A' : Type} {B : Type ℓ}
  → (isSet B)
  → (_*_ : List A → List A' → B)
  → (∀ {zs} xs ys → (p : Perm xs ys) → xs * zs ≡ ys * zs)
  → (∀ {zs} xs ys → (p : Perm xs ys) → zs * xs ≡ zs * ys)
  → Mset A → Mset A' → B
rec2Mset {A = A} {A' = A'} {B = B} setB _*_ wd₁ wd₂ = recMset (isSetΠ (λ _ → setB)) rec' well-defined where
  rec' : List A → Mset A' → B
  rec' = λ as → recMset setB (as *_) wd₂

  well-defined : (as bs : List A) → Perm as bs → rec' as ≡ rec' bs
  well-defined as bs p = funExt (elimPropMset (λ xs → setB (rec' as xs) (rec' bs xs)) λ _ → wd₁ as bs p)

mapMset : {A B : Type} (f : A → B) → Mset A → Mset B
mapMset f = recMset
  isSetMset
  ([_] ∘ List.map f)
  (λ xs ys p → eq/ _ _ (mapP f p))

-- ====================================================================
--
-- Mset forms a commutative monoid under concatenation.
--
-- Unitality and associativity of concatenation are lifted from Lists,
-- commutativity follows the permutation of (xs ++ ys) into (ys ++ xs).
module _ {A : Type} where
  emptyMset : Mset A
  emptyMset = [ [] ]

  singleton : A → Mset A
  singleton x = [ x ∷ [] ]

  concat : Mset A → Mset A → Mset A
  concat = rec2Mset isSetMset (λ as bs → [ as ++ bs ]) wd₁ wd₂ where
    wd₁ : ∀ {cs} as bs → Perm as bs → [ as ++ cs ] ≡ [ bs ++ cs ]
    wd₁ as bs p = eq/ _ _ (appendP p)

    wd₂ : ∀ {cs} as bs → Perm as bs → [ cs ++ as ] ≡ [ cs ++ bs ]
    wd₂ {cs} as bs p = eq/ _ _ (prependP cs p)

  concat-unitˡ : (xs : Mset A) → concat emptyMset xs ≡ xs
  concat-unitˡ = elimPropMset (λ xs → isSetMset _ xs) (λ as → refl {x = [ as ]})

  concat-comm : (xs ys : Mset A) → concat xs ys ≡ concat ys xs
  concat-comm = elimProp2Mset (λ xs ys → isSetMset _ _) comm where
    comm : (as bs : List A) → [ as ++ bs ] ≡ [ bs ++ as ]
    comm as bs = eq/ _ _ (commP as bs)

  concat-assoc : (xs ys zs : Mset A) → concat xs (concat ys zs) ≡ concat (concat xs ys) zs
  concat-assoc = elimPropMset (λ xs → isPropΠ2 λ ys zs → isSetMset _ _)
    λ as → elimProp2Mset (λ _ _ → isSetMset _ _) λ bs cs → cong [_] (sym (++-assoc as bs cs))

-- ====================================================================

-- Insertion-sort for lists, assuming the carrier is a linear
-- order. This allows to define a section for [_] : List A → Mset A.

module Sorting {A : Type} (setA : isSet A)
  (R : A → A → Type)
  (linR : isLinOrder R) where

  open isLinOrder linR


  insert : A → (xs : List A) → List A
  insert x [] = x ∷ [] 
  insert x (y ∷ xs) =
    casesTotR R
              (x ∷ y ∷ xs)
              (y ∷ insert x xs)
              (x ∷ y ∷ xs)
              (totR x y)

  lengthInsert : (x : A) (xs : List A) → length (insert x xs) ≡ suc (length xs)
  lengthInsert x [] = refl
  lengthInsert x (y ∷ xs) =
    elimTotR R
             (λ z → length (casesTotR R (x ∷ y ∷ xs) (y ∷ insert x xs) (x ∷ y ∷ xs) z)
                      ≡ suc (suc (length xs)))
             (λ _ → refl)
             (λ _ → cong suc (lengthInsert x xs))
             (λ _ → refl)
             (totR x y)

  insert-insert : ∀ x y xs
    → insert y (insert x xs) ≡ insert x (insert y xs)
  insert-insert x y [] =
    elimTotR R
             (λ z → casesTotR R (y ∷ x ∷ []) (x ∷ y ∷ []) (y ∷ x ∷ []) (totR y x)
                  ≡ casesTotR R (x ∷ y ∷ []) (y ∷ x ∷ []) (x ∷ y ∷ []) z)
             (λ r → cong (casesTotR R (y ∷ x ∷ []) (x ∷ y ∷ []) (y ∷ x ∷ [])) (totR-case2 x y r))
             (λ r → cong (casesTotR R (y ∷ x ∷ []) (x ∷ y ∷ []) (y ∷ x ∷ [])) (totR-case1 y x r))
             (λ eq → cong (casesTotR R (y ∷ x ∷ []) (x ∷ y ∷ []) (y ∷ x ∷ [])) (totR-case3 setA y x (sym eq)) ∙ λ i → eq (~ i) ∷ eq i ∷ [])
             (totR x y)
  insert-insert x y (z ∷ xs) =
    elimTotR R
       (λ l → insert y (casesTotR R (x ∷ z ∷ xs) (z ∷ insert x xs) (x ∷ z ∷ xs) l)
          ≡ insert x (casesTotR R (y ∷ z ∷ xs) (z ∷ insert y xs) (y ∷ z ∷ xs) (totR y z)))
       (λ r → elimTotR R
           (λ l → casesTotR R (y ∷ x ∷ z ∷ xs) (x ∷ casesTotR R (y ∷ z ∷ xs) (z ∷ insert y xs) (y ∷ z ∷ xs) (totR y z)) (y ∷ x ∷ z ∷ xs) (totR y x)
              ≡ insert x (casesTotR R (y ∷ z ∷ xs) (z ∷ insert y xs) (y ∷ z ∷ xs) l))
           (λ r' → elimTotR R
                (λ l → casesTotR R (y ∷ x ∷ z ∷ xs) (x ∷ casesTotR R (y ∷ z ∷ xs) (z ∷ insert y xs) (y ∷ z ∷ xs) (totR y z)) (y ∷ x ∷ z ∷ xs) (totR y x)
                  ≡ casesTotR R (x ∷ y ∷ z ∷ xs) (y ∷ casesTotR R (x ∷ z ∷ xs) (z ∷ insert x xs) (x ∷ z ∷ xs) (totR x z)) (x ∷ y ∷ z ∷ xs) l)
                (λ r'' → cong (casesTotR R (y ∷ x ∷ z ∷ xs) (x ∷ casesTotR R (y ∷ z ∷ xs) (z ∷ insert y xs) (y ∷ z ∷ xs) (totR y z)) (y ∷ x ∷ z ∷ xs)) (totR-case2 x y r'')
                          ∙ cong (λ l → x ∷ casesTotR R (y ∷ z ∷ xs) (z ∷ insert y xs) (y ∷ z ∷ xs) l) (totR-case1 y z r'))
                (λ r'' → cong (casesTotR R (y ∷ x ∷ z ∷ xs) (x ∷ casesTotR R (y ∷ z ∷ xs) (z ∷ insert y xs) (y ∷ z ∷ xs) (totR y z)) (y ∷ x ∷ z ∷ xs)) (totR-case1 y x r'')
                          ∙ sym (cong (λ l → y ∷ casesTotR R (x ∷ z ∷ xs) (z ∷ insert x xs) (x ∷ z ∷ xs) l) (totR-case1 x z r)))
                (λ eq → cong (casesTotR R (y ∷ x ∷ z ∷ xs) (x ∷ casesTotR R (y ∷ z ∷ xs) (z ∷ insert y xs) (y ∷ z ∷ xs) (totR y z)) (y ∷ x ∷ z ∷ xs)) (totR-case3 setA y x (sym eq))
                        ∙ λ i → eq (~ i) ∷ eq i ∷ z ∷ xs)
                (totR x y))
           (λ r' → cong (casesTotR R (y ∷ x ∷ z ∷ xs) (x ∷ casesTotR R (y ∷ z ∷ xs) (z ∷ insert y xs) (y ∷ z ∷ xs) (totR y z)) (y ∷ x ∷ z ∷ xs)) (totR-case2 x y (transR r r')) 
                ∙ cong (λ l → x ∷ casesTotR R (y ∷ z ∷ xs) (z ∷ insert y xs) (y ∷ z ∷ xs) l) (totR-case2 z y r')
                ∙ sym (cong (casesTotR R (x ∷ z ∷ insert y xs) (z ∷ insert x (insert y xs)) (x ∷ z ∷ insert y xs)) (totR-case1 x z r)))
           (λ eq → cong (casesTotR R (y ∷ x ∷ z ∷ xs) (x ∷ casesTotR R (y ∷ z ∷ xs) (z ∷ insert y xs) (y ∷ z ∷ xs) (totR y z)) (y ∷ x ∷ z ∷ xs)) (totR-case2 x y (subst (R x) (sym eq) r))
                ∙ cong (λ l → x ∷ casesTotR R (y ∷ z ∷ xs) (z ∷ insert y xs) (y ∷ z ∷ xs) l) (totR-case3 setA y z eq)
                ∙ sym (cong (casesTotR R (x ∷ y ∷ z ∷ xs) (y ∷ casesTotR R (x ∷ z ∷ xs) (z ∷ insert x xs) (x ∷ z ∷ xs) (totR x z)) (x ∷ y ∷ z ∷ xs)) (totR-case1 x y (subst (R x) (sym eq) r))))
           (totR y z))
       (λ r → elimTotR R
          (λ l → casesTotR R (y ∷ z ∷ insert x xs) (z ∷ insert y (insert x xs)) (y ∷ z ∷ insert x xs) l
              ≡ insert x (casesTotR R (y ∷ z ∷ xs) (z ∷ insert y xs) (y ∷ z ∷ xs) l))
          (λ r' → sym (cong (casesTotR R (x ∷ y ∷ z ∷ xs) (y ∷ casesTotR R (x ∷ z ∷ xs) (z ∷ insert x xs) (x ∷ z ∷ xs) (totR x z)) (x ∷ y ∷ z ∷ xs)) (totR-case2 y x (transR r' r))
                       ∙ cong (λ l → y ∷ casesTotR R (x ∷ z ∷ xs) (z ∷ insert x xs) (x ∷ z ∷ xs) l) (totR-case2 z x r)))
          (λ r' → sym (cong (casesTotR R (x ∷ z ∷ insert y xs) (z ∷ insert x (insert y xs)) (x ∷ z ∷ insert y xs)) (totR-case2 z x r)
                       ∙ λ i → z ∷ insert-insert y x xs i))
          (λ eq → sym (cong (casesTotR R (x ∷ y ∷ z ∷ xs) (y ∷ casesTotR R (x ∷ z ∷ xs) (z ∷ insert x xs) (x ∷ z ∷ xs) (totR x z)) (x ∷ y ∷ z ∷ xs)) (totR-case2 y x (subst (λ l → R l x) (sym eq) r))
                       ∙ cong (λ l → y ∷ casesTotR R (x ∷ z ∷ xs) (z ∷ insert x xs) (x ∷ z ∷ xs) l) (totR-case2 z x r)))
          (totR y z))
       (J (λ z eq → casesTotR R (y ∷ x ∷ z ∷ xs) (x ∷ casesTotR R (y ∷ z ∷ xs) (z ∷ insert y xs) (y ∷ z ∷ xs) (totR y z)) (y ∷ x ∷ z ∷ xs) (totR y x)
             ≡ insert x (casesTotR R (y ∷ z ∷ xs) (z ∷ insert y xs) (y ∷ z ∷ xs) (totR y z)))
          (elimTotR R
             (λ l →  casesTotR R (y ∷ x ∷ x ∷ xs) (x ∷ casesTotR R (y ∷ x ∷ xs) (x ∷ insert y xs) (y ∷ x ∷ xs) l) (y ∷ x ∷ x ∷ xs) l
               ≡ insert x (casesTotR R (y ∷ x ∷ xs) (x ∷ insert y xs) (y ∷ x ∷ xs) l))
             (λ r → sym (cong (casesTotR R (x ∷ y ∷ x ∷ xs) (y ∷ casesTotR R (x ∷ x ∷ xs) (x ∷ insert x xs) (x ∷ x ∷ xs) (totR x x)) (x ∷ y ∷ x ∷ xs)) (totR-case2 y x r)
                         ∙ cong (λ l → y ∷ casesTotR R (x ∷ x ∷ xs) (x ∷ insert x xs) (x ∷ x ∷ xs) l) (totR-case3 setA x x refl)))
             (λ r → sym (cong (casesTotR R (x ∷ x ∷ insert y xs) (x ∷ insert x (insert y xs)) (x ∷ x ∷ insert y xs)) (totR-case3 setA x x refl)))
             (λ eq → sym (cong (casesTotR R (x ∷ y ∷ x ∷ xs) (y ∷ casesTotR R (x ∷ x ∷ xs) (x ∷ insert x xs) (x ∷ x ∷ xs) (totR x x)) (x ∷ y ∷ x ∷ xs)) (totR-case3 setA x y (sym eq))
                          ∙ λ i → eq (~ i) ∷ eq i ∷ x ∷ xs))
             (totR y x)))
       (totR x z)


  insertP : (x : A) (xs : List A) → Perm (x ∷ xs) (insert x xs)
  insertP x [] = stop
  insertP x (y ∷ xs) =
    elimTotR R
             (λ l → Perm (x ∷ y ∷ xs) (casesTotR R (x ∷ y ∷ xs) (y ∷ insert x xs) (x ∷ y ∷ xs) l))
             (λ _ → stop)
             (λ _ →  perm {xs = []} (congPerm (insertP x xs)))
             (λ _ → stop)
             (totR x y)

  sort-acc : List A → List A → List A
  sort-acc [] acc = acc
  sort-acc (x ∷ xs) acc = sort-acc xs (insert x acc)

  sort : List A → List A
  sort xs = sort-acc xs []

  lengthSortAcc : (xs acc : List A) → length (sort-acc xs acc) ≡ length xs + length acc
  lengthSortAcc [] acc = refl
  lengthSortAcc (x ∷ xs) acc =
    length (sort-acc (x ∷ xs) acc)    ≡⟨ lengthSortAcc xs (insert x acc) ⟩
    length xs + length (insert x acc) ≡⟨ congS (length xs +_) (lengthInsert x acc) ⟩
    (length xs + suc (length acc))    ≡⟨ +-suc _ _ ⟩
    suc (length xs + length acc)      ∎

  lengthSort : (xs : List A) → length (sort xs) ≡ length xs
  lengthSort xs =
    length (sort-acc xs []) ≡⟨ lengthSortAcc xs [] ⟩
    length xs + 0           ≡⟨ +-zero (length xs) ⟩
    length xs ∎


  sort-eq/-acc : ∀ {xs ys acc}
    → Perm xs ys → sort-acc xs acc ≡ sort-acc ys acc
  sort-eq/-acc stop = refl
  sort-eq/-acc (perm {xs = xs} ps) = perm-eq/ xs ∙ sort-eq/-acc ps where
    perm-eq/ : ∀ xs {ys acc x y}
      → sort-acc (xs ++ x ∷ y ∷ ys) acc ≡ sort-acc (xs ++ y ∷ x ∷ ys) acc
    perm-eq/ [] {ys} {acc} = cong (sort-acc ys) (insert-insert _ _ acc)
    perm-eq/ (x ∷ xs) = perm-eq/ xs

  sort-eq/ : ∀ {xs ys}
    → Perm xs ys → sort xs ≡ sort ys
  sort-eq/ p = sort-eq/-acc {acc = []} p

  sortMset : Mset A → List A
  sortMset = SQ.rec (isOfHLevelList 0 setA) sort well-defined where
    well-defined : ∀ xs ys → Perm xs ys → sort xs ≡ sort ys
    well-defined _ _ = sort-eq/

  sortP : (xs : List A) → Perm xs (sort xs)
  sortP xs = sortP-acc xs [] where
    sortP-acc : (xs acc : List A) → Perm (acc ++ xs) (sort-acc xs acc)
    sortP-acc [] acc = substP (++-unit-r acc)
    sortP-acc (x ∷ xs) acc =
      (moveHeadP x acc) ⁻ᵖ
        ∙ₚ ((appendP {zs = xs} (insertP x acc))
        ∙ₚ (sortP-acc xs (insert x acc)))

  sortMset-section : ∀ xs → [ sortMset xs ] ≡ xs
  sortMset-section =
    SQ.elimProp (λ _ → squash/ _ _)
      (λ xs → eq/ _ _ (invP (sortP xs)))

  -- Knowing a permutation between xs and ys, we build another one by
  -- first sorting xs and then un-sorting ys. This is a constant function.
  canonPerm : (xs ys : List A) → Perm xs ys → Perm xs ys
  canonPerm xs ys σ = (sortP xs) ∙ₚ substP (sort-eq/ σ) ∙ₚ (sortP ys ⁻ᵖ)


  canonPerm-const : (xs ys : List A) (σ τ : Perm xs ys)
    → canonPerm xs ys σ ≡ canonPerm xs ys τ
  canonPerm-const xs ys σ τ =
    canonPerm xs ys σ                                   ≡⟨⟩
    (sortP xs) ∙ₚ substP (sort-eq/ σ) ∙ₚ (sortP ys ⁻ᵖ)  ≡⟨ cong (λ p → (sortP xs) ∙ₚ substP p ∙ₚ (sortP ys ⁻ᵖ)) lem ⟩
    (sortP xs) ∙ₚ substP (sort-eq/ τ) ∙ₚ (sortP ys ⁻ᵖ)  ≡⟨⟩
    canonPerm xs ys τ ∎ where
      -- Since A is a set, equality of lists is a proposition.
      isPropSorted≡ : isProp (sort xs ≡ sort ys)
      isPropSorted≡ = isOfHLevelList 0 setA (sort xs) (sort ys)

      lem : sort-eq/ σ ≡ sort-eq/ τ
      lem = isPropSorted≡ (sort-eq/ σ) (sort-eq/ τ)


module Example where
  -- =======================================================================
  --
  --  Example: Computing the canonical permutation on lists of units.
  --
  --  For any `p : Perm [ tt , tt ] [ tt , tt ]`, we show that `canonPerm p`
  --  computes to a double braid-like permutation
  --
  --        [ tt , tt ]
  --           \  /
  --            '/
  --            /.
  --           /  \
  --        [ tt , tt ]
  --           \  /
  --            '/
  --            /.
  --           /  \
  --        [ tt , tt ]
  --
  --  This suggests that `Perm [ tt , tt ] [ tt , tt ]` is equivalent to the
  --  braid group on two strands (B₂), which is in turn equivalent to ℤ.
  open import Cubical.Data.Unit

  -- The unit type comes with a trivial linear order — the empty relation:
  _<_ : Unit → Unit → Type
  _<_ tt tt = ⊥

  isLinOrderUnit : isLinOrder {A = Unit} _<_
  isLinOrderUnit .isLinOrder.asymR ()
  isLinOrderUnit .isLinOrder.transR ()
  isLinOrderUnit .isLinOrder.propR ()
  isLinOrderUnit .isLinOrder.totR tt tt = inr (inr refl)

  -- Abbreviation for the unique two-element list of units:
  𝟚 : List Unit
  𝟚 = tt ∷ tt ∷ []

  -- The permutations on 𝟚 are less permutations, more braidings.
  -- In analogy to the braid group on two strands, call them B₂:
  B₂ : Type
  B₂ = Perm 𝟚 𝟚

  -- We have terms for braiding once...
  --
  --          [ tt , tt ]
  --             \  /
  --              '/
  --              /.
  --             /  \
  --          [ tt , tt ]
  --
  braid : B₂
  braid = perm {x = tt} {y = tt} {xs = []} {ys = []} stop

  -- ...and twice:
  braid² : B₂
  braid² = perm {xs = []} braid
  -- Notice that since B₂ is generated freely, braid² ≢ stop.

  module S = Sorting isSetUnit _<_ isLinOrderUnit

  canonPerm𝟚 : B₂ → B₂
  canonPerm𝟚 = S.canonPerm _ _

  -- After getting rid of some substitutions over `refl`, we see
  -- that `canonPerm𝟚` computes to `braid²` on `braid`...
  canonPerm𝟚-braid : canonPerm𝟚 braid ≡ braid²
  canonPerm𝟚-braid =
    canonPerm𝟚 braid ≡⟨⟩
    perm (p ∙ₚ (p ∙ₚ ((p ⁻ᵖ) ∙ₚ braid))) ≡⟨ cong (λ p → perm {xs = []} (p ∙ₚ (p ∙ₚ ((p ⁻ᵖ) ∙ₚ braid)))) p≡stop ⟩
    perm (stop ∙ₚ (stop ∙ₚ ((stop ⁻ᵖ) ∙ₚ braid))) ≡⟨⟩
    braid² ∎
    where
      p : B₂
      p = subst (Perm 𝟚) refl stop

      p≡stop : p ≡ stop
      p≡stop = substRefl {B = Perm 𝟚} {x = 𝟚} stop

  -- ... and of course on any other value:
  canonPerm𝟚-const-braid² : (p : B₂) → canonPerm𝟚 p ≡ braid²
  canonPerm𝟚-const-braid² p = S.canonPerm-const _ _ p braid ∙ canonPerm𝟚-braid

-- ====================================================================

-- Lexicographic order on list, i.e. how to lift a linear order on A
-- to a linear order on List A

module ListLinOrder {A : Type} (setA : isSet A)
  (R : A → A → Type)
  (linR : isLinOrder R) where

  open isLinOrder linR

  data Lex : List A → List A → Type where
    []< : ∀ {y ys} → Lex [] (y ∷ ys)
    R< : ∀ {x y xs ys} (r : R x y) → Lex (x ∷ xs) (y ∷ ys)
    ≡< : ∀ {x y xs ys} (eq : x ≡ y) (ls : Lex xs ys) → Lex (x ∷ xs) (y ∷ ys)

  asymLex : ∀ {xs ys} → Lex xs ys → Lex ys xs → ⊥
  asymLex (R< r) (R< r') = asymR r r'
  asymLex (R< r) (≡< eq ls') = irreflR (subst (R _) eq r)
  asymLex (≡< eq ls) (R< r) = irreflR (subst (R _) eq r)
  asymLex (≡< eq ls) (≡< eq' ls') = asymLex ls ls'

  transLex : ∀ {xs ys zs} → Lex xs ys → Lex ys zs → Lex xs zs
  transLex []< (R< r) = []<
  transLex []< (≡< eq ls') = []<
  transLex (R< r) (R< r') = R< (transR r r')
  transLex (R< r) (≡< eq ls') = R< (subst (R _) eq r)
  transLex (≡< eq ls) (R< r) = R< (subst (λ x → R x _) (sym eq) r)
  transLex (≡< eq ls) (≡< eq' ls') = ≡< (eq ∙ eq') (transLex ls ls')

  propLex : ∀ {xs ys} → isProp (Lex xs ys)
  propLex []< []< = refl
  propLex (R< r) (R< r') = cong R< (propR r r')
  propLex (R< r) (≡< eq ls') = Empty.rec (irreflR (subst (R _) (sym eq) r))
  propLex (≡< eq ls) (R< r) = Empty.rec (irreflR (subst (R _) (sym eq) r))
  propLex (≡< eq ls) (≡< eq' ls') i = ≡< (setA _ _ eq eq' i) (propLex ls ls' i)

  totLex : ∀ xs ys → Lex xs ys ⊎ (Lex ys xs ⊎ (xs ≡ ys))
  totLex [] [] = inr (inr refl)
  totLex [] (x ∷ ys) = inl []<
  totLex (x ∷ xs) [] = inr (inl []<)
  totLex (x ∷ xs) (y ∷ ys) =
    recTotR R
            (λ r → inl (R< r))
            (λ r → inr (inl (R< r)))
            (λ eq → Sum.map (≡< eq)
                    (Sum.map (≡< (sym eq))
                          (λ eq' i → eq i ∷ eq' i))
                          (totLex xs ys))
            (totR x y)

  linLex : isLinOrder Lex
  linLex =
    record { asymR = asymLex
           ; transR = transLex
           ; propR = propLex
           ; totR = totLex
           }

-- ====================================================================

-- The lexicographic order extends to multisets.

module MsetLinOrder {A : Type} (setA : isSet A)
  (R : A → A → Type)
  (linR : isLinOrder R) where

  open isLinOrder linR
  open ListLinOrder setA R linR
  open Sorting setA R linR

  LexMset : Mset A → Mset A → Type
  LexMset xs ys = Lex (sortMset xs) (sortMset ys)

  totLexMset : ∀ xs ys → LexMset xs ys ⊎ (LexMset ys xs ⊎ (xs ≡ ys))
  totLexMset xs ys = Sum.map (idfun _) (Sum.map (idfun _) lem) (totLex (sortMset xs) (sortMset ys))
    where
      lem : sortMset xs ≡ sortMset ys → xs ≡ ys
      lem eq =
        xs ≡⟨ sym (sortMset-section xs) ⟩
        [ sortMset xs ] ≡⟨ cong [_] eq ⟩
        [ sortMset ys ] ≡⟨ sortMset-section ys ⟩
        ys ∎

  linLexMset : isLinOrder LexMset
  linLexMset =
    record { asymR = asymLex
           ; transR = transLex
           ; propR = propLex
           ; totR = totLexMset
           }


