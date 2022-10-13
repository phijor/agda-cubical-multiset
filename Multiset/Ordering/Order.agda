{-# OPTIONS --safe #-}

module Multiset.Ordering.Order where


open import Cubical.Core.Everything
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Everything
open import Cubical.Data.List as List hiding ([_])
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

  sort : List A → List A → List A
  sort [] acc = acc
  sort (x ∷ xs) acc = sort xs (insert x acc)

  sort-eq/' : ∀ xs {ys acc x y}
    → sort (xs ++ x ∷ y ∷ ys) acc ≡ sort (xs ++ y ∷ x ∷ ys) acc
  sort-eq/' [] {ys} {acc} = cong (sort ys) (insert-insert _ _ acc)
  sort-eq/' (x ∷ xs) = sort-eq/' xs


  sort-eq/ : ∀ {xs ys acc}
    → Perm xs ys → sort xs acc ≡ sort ys acc
  sort-eq/ stop = refl
  sort-eq/ (perm {xs = xs} ps) = sort-eq/' xs ∙ sort-eq/ ps

  sortMset : Mset A → List A
  sortMset =
    SQ.rec (isOfHLevelList 0 setA)
      (λ xs → sort xs [])
      (λ _ _ → sort-eq/)

  sortP : (xs acc : List A) → Perm (acc ++ xs) (sort xs acc)
  sortP [] acc = substP (++-unit-r acc)
  sortP (x ∷ xs) acc =
    transP (invP (moveHeadP x acc))
            (transP (appendP {zs = xs} (insertP x acc))
                     (sortP xs (insert x acc)))

  sortMset-section : ∀ xs → [ sortMset xs ] ≡ xs
  sortMset-section =
    SQ.elimProp (λ _ → squash/ _ _)
      (λ xs → eq/ _ _ (invP (sortP xs [])))

-- Knowing a permutation between xs and ys, we build another one by
-- first sorting xs and then un-sorting ys. This is a constant function.

  canonicalP : (xs ys : List A) → Perm xs ys → Perm xs ys
  canonicalP xs ys σ =
    transP (sortP xs [])
            (transP (substP (sort-eq/ σ))
                    (invP (sortP ys [])))

  canonicalP-const : (xs ys : List A) (σ Φ : Perm xs ys)
    → canonicalP xs ys σ ≡ canonicalP xs ys Φ
  canonicalP-const xs ys σ Φ =
    cong (transP (sortP xs []))
         (cong (λ z → transP z (invP (sortP ys [])))
               (cong substP (isOfHLevelList 0 setA _ _ _ _)))


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


