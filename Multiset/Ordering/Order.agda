
module Multiset.Ordering.Order where


open import Cubical.Core.Everything
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Everything
open import Cubical.Data.List hiding ([_]) renaming (map to mapList)
open import Cubical.Data.Sigma
open import Cubical.Data.Nat
--open import Cubical.Data.SumFin as Fin
--open import Cubical.Data.Fin
--  hiding (_/_)
open import Cubical.HITs.PropositionalTruncation as PropTrunc
  renaming (rec to ∥rec∥; map to ∥map∥)
open import Cubical.HITs.SetQuotients
  renaming (rec to recQ; rec2 to recQ2; elimProp2 to elimPropQ2; elimProp to elimPropQ)
open import Cubical.Relation.Binary
open BinaryRelation
open isEquivRel
--open import Multiset.OverSet.Base
--open import Multiset.OverSet.Properties
open import Cubical.Data.Empty as Empty
open import Cubical.Data.Unit
open import Cubical.Data.Sum renaming (map to map⊎; rec to rec⊎)

open import Multiset.Coinductive.ListStuff

recTotR : ∀{ℓ ℓ' ℓ''} {A : Type ℓ} {B : Type ℓ'}
  → (R : A → A → Type ℓ'')
  → {x y : A}
  → (R x y → B)
  → (R y x → B)
  → (x ≡ y → B)
  → R x y ⊎ (R y x ⊎ (x ≡ y)) → B
recTotR R f g h (inl r) = f r
recTotR R f g h (inr (inl r)) = g r
recTotR R f g h (inr (inr r)) = h r

casesTotR : ∀{ℓ ℓ' ℓ''} {A : Type ℓ} {B : Type ℓ'}
  → (R : A → A → Type ℓ'')
  → {x y : A}
  → B → B → B
  → R x y ⊎ (R y x ⊎ (x ≡ y)) → B
casesTotR R f g h (inl r) = f
casesTotR R f g h (inr (inl r)) = g 
casesTotR R f g h (inr (inr r)) = h 


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

record isStrictOrder {A : Type} (R : A → A → Type) : Type where
  field
    asymR  : {x y : A} → R x y → R y x → ⊥
    transR : {x y z : A} → R x y → R y z → R x z
    propR  : {x y : A} → isProp (R x y)

  irreflR : {x : A} → R x x → ⊥
  irreflR r = asymR r r

record isLinOrder {A : Type} (R : A → A → Type) : Type where
  field
    strictR : isStrictOrder R
    totR    : (x y : A) → R x y ⊎ (R y x ⊎ (x ≡ y))

  open isStrictOrder strictR

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

module ListLinOrder {A : Type} (setA : isSet A)
  (R : A → A → Type)
  (linR : isLinOrder R) where

  open isLinOrder linR
  open isStrictOrder strictR

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

  strictLex : isStrictOrder Lex
  strictLex = 
    record { asymR = asymLex
           ; transR = transLex
           ; propR = propLex
           }

  totLex : ∀ xs ys → Lex xs ys ⊎ (Lex ys xs ⊎ (xs ≡ ys))
  totLex [] [] = inr (inr refl)
  totLex [] (x ∷ ys) = inl []<
  totLex (x ∷ xs) [] = inr (inl []<)
  totLex (x ∷ xs) (y ∷ ys) =
    recTotR R
            (λ r → inl (R< r))
            (λ r → inr (inl (R< r)))
            (λ eq → map⊎ (≡< eq) (map⊎ (≡< (sym eq)) (λ eq' i → eq i ∷ eq' i)) (totLex xs ys))
            (totR x y)

  linLex : isLinOrder Lex
  linLex =
    record { strictR = strictLex
           ; totR = totLex
           }

{-
module VectLinOrder {A : Type} (setA : isSet A)
  (R : A → A → Type)
  (linR : isLinOrder R) where

  open isLinOrder linR
  open isStrictOrder strictR

  RV : (n : ℕ) → (xs ys : Fin n → A) → Type
  RV zero xs ys = ⊥
  RV (suc n) xs ys =
    recTotR R
      (λ _ → Unit)
      (λ _ → ⊥)
      (λ eq → RV n (xs ∘ fsuc) (ys ∘ fsuc))
      (totR (xs fzero) (ys fzero))

  asymRV : ∀ n {xs ys} → RV n xs ys → RV n ys xs → ⊥
  asymRV (suc n) {xs}{ys} rv rv' =
    elimTotR R (λ r → K xs ys r → ⊥)
             (λ r _ → subst (K ys xs) (totR-case2 _ _ r) rv')
             (λ r x → x)
             (λ eq rv → asymRV n rv (subst (K ys xs) (totR-case3 setA _ _ (sym eq)) rv'))
             (totR (xs fzero) (ys fzero))
             rv
    where
      K : ∀ xs ys → (r : R (xs fzero) (ys fzero) ⊎ (R (ys fzero) (xs fzero) ⊎ (xs fzero ≡ ys fzero))) → Type
      K xs ys = recTotR R (λ _ → Unit) (λ _ → ⊥) (λ eq → RV n (xs ∘ fsuc) (ys ∘ fsuc))

  transRV : ∀ n {xs ys zs} → RV n xs ys → RV n ys zs → RV n xs zs
  transRV (suc n) {xs}{ys}{zs} rv rv' =
    elimTotR R (K' xs zs)
             (λ _ → tt)
             (λ r → {!!})
             {!!}
             (totR (xs fzero) (zs fzero))
--     recTotR R --(λ r → K xs ys zs r → RV (suc n) xs zs)
--              (λ r _ → recTotR R
--                               (λ r' → subst (K' xs zs) (sym (totR-case1 (xs fzero) (zs fzero) (transR r r')) ) tt)
--                               (λ r' → elimTotR R (K' xs zs) (λ _ → tt)
--                                                              {!!}
--                                                              {!!}
--                                                              (totR (xs fzero) (zs fzero)))
--                               {!!}
--                               (totR (ys fzero) (zs fzero)) )
--              (λ _ → Empty.rec)
--              {!!}
--              (totR (xs fzero) (ys fzero))
--             {!rv!}
    where
--      K : ∀ xs ys zs → (r : R (xs fzero) (ys fzero) ⊎ (R (ys fzero) (xs fzero) ⊎ (xs fzero ≡ ys fzero))) → Type
--      K xs ys zs = recTotR R (λ _ → Unit) (λ _ → ⊥) (λ eq → RV n (ys ∘ fsuc) (zs ∘ fsuc))

      K' : ∀ xs zs → (r : R (xs fzero) (zs fzero) ⊎ (R (zs fzero) (xs fzero) ⊎ (xs fzero ≡ zs fzero))) → Type
      K' xs zs = recTotR R (λ _ → Unit) (λ _ → ⊥) (λ eq → RV n (xs ∘ fsuc) (zs ∘ fsuc))

  propRV : ∀ n {x y} → isProp (RV n x y)
  propRV zero = isProp⊥
  propRV (suc n) {xs}{ys} =
    elimTotR R
             (λ r → isProp (recTotR R (λ _ → Unit) (λ _ → ⊥) (λ eq → RV n (xs ∘ fsuc) (ys ∘ fsuc)) r))
             (λ _ → isPropUnit)
             (λ _ → isProp⊥)
             (λ eq → propRV n)
             (totR (xs fzero) (ys fzero))

  isStrictOrderRV : ∀ n → isStrictOrder (RV n)
  isStrictOrderRV n =
    record { asymR = asymRV n
           ; transR = transRV n
           ; propR = propRV n }

-}


{-
module Sorting {A : Type} (setA : isSet A)
  (R : A → A → Type)
  (linR : isLinOrder R) where

  open isLinOrder linR
  open isStrictOrder strictR
  
  insert : ∀ n → A → (Fin n → A) → Fin (suc n) → A
  insert n x xs fzero = x
  insert (suc n) x xs (fsuc k) =
    casesTotR R
              (xs k)
              (insert n x (xs ∘ fsuc) k)
              (xs k)
              (totR x (xs fzero))

  sort : ∀ n {m} (xs : Fin n → A) (acc : Fin m → A) → Fin (n + m) → A
  sort zero xs acc = acc
  sort (suc n) {m} xs acc k =
    sort n (xs ∘ fsuc) (insert m (xs fzero) acc) (subst Fin (sym (+-suc n m)) k) 

  rmv : ∀ {B : Type} {n} → (Fin (suc n) → B) → Fin (suc n) → Fin n → B
  rmv {n = suc n} xs fzero = xs ∘ fsuc
  rmv {n = suc n} xs (fsuc k) fzero = xs fzero
  rmv {n = suc n} xs (fsuc k) (fsuc j) = rmv (xs ∘ fsuc) k j


  sort-eq/' : ∀ n {m} xs (acc : Fin m → A)
    → (σ : Fin n ≃ Fin n) -- ] (∀ k → xs k ≡ ys (equivFun σ k))) --PathP (λ i → (ua σ i → A)) xs ys)
    → ∀ k → sort n xs acc k ≡ sort n (λ j → xs (equivFun σ j)) acc k
  sort-eq/' zero xs acc σ k = refl
  sort-eq/' (suc n) {m} xs acc σ k =
    sort-eq/' n (xs ∘ fsuc) _ ({!!} , {!!}) _
    ∙ {!!}
-}



{-
  sort-eq/ : ∀ n {m} xs ys (acc : Fin m → A)
    → (Σ[ σ ∈ (Fin n ≃ Fin n) ] (∀ k → xs k ≡ ys (equivFun σ k))) --PathP (λ i → (ua σ i → A)) xs ys)
    → ∀ k → sort n xs acc k ≡ sort n ys acc k
  sort-eq/ zero xs ys acc (σ , eq) k = refl
  sort-eq/ (suc n) {m} xs ys acc (σ , eq) k =
    sort n (xs ∘ fsuc) (insert m (xs fzero) acc) p
    ≡⟨ {!!} ⟩
    sort n (xs ∘ fsuc) (insert m (ys (equivFun σ fzero)) acc) p
    ≡⟨ {!!} ⟩
    sort n (rmv ys (equivFun σ fzero)) (insert m (ys (equivFun σ fzero)) acc) p
    ≡⟨ {!!} ⟩
    sort n (ys ∘ fsuc) (insert m (ys fzero) acc) p
    ∎
    where
      p = subst Fin (λ i → +-suc n m (~ i)) k
-}



-- open import Cubical.Core.Everything
-- open import Cubical.Foundations.Prelude
-- open import Cubical.Foundations.Everything
-- open import Cubical.Functions.Logic renaming (⊥ to ⊥ₚ)
-- open import Cubical.Relation.Everything
-- open import Cubical.HITs.PropositionalTruncation as PropTrunc
--   renaming (rec to ∥rec∥; map to ∥map∥)
-- open import Cubical.HITs.SetQuotients
--   renaming (rec to recQ; rec2 to recQ2; elim to elimQ)
-- open import Cubical.Data.Sigma
-- open import Cubical.Data.Nat 
-- open import Cubical.Data.Bool
-- open import Cubical.Data.List renaming (map to mapList) hiding ([_])
-- open import Cubical.Data.Sum renaming (map to map⊎; inl to inj₁; inr to inj₂; rec to rec⊎)
-- open import Cubical.Data.Empty renaming (elim to ⊥-elim; rec to ⊥-rec)
-- open import Cubical.Relation.Binary
-- open import Cubical.Relation.Nullary
-- open import Basics
-- open import ListStuff
-- open import ListRelations
-- open import Trees
-- open import Mset.AsFreeCommMonoid
-- open import Cubical.Data.Nat.Order hiding (eq) renaming (_≤_ to _≤N_)


-- -- Permutation on lists
data Perm {A : Type} : List A → List A → Type where
  swapp : {x y : A} (xs : List A) {ys : List A}
    → Perm (xs ++ x ∷ y ∷ ys) (xs ++ y ∷ x ∷ ys)

congPerm : {A : Type} {x : A}{xs ys : List A} → Perm xs ys → Perm (x ∷ xs) (x ∷ ys)
congPerm (swapp xs) = swapp (_ ∷ xs)

mapPerm : {A B : Type} (f : A → B) {xs ys : List A}
  → Perm xs ys → Perm (mapList f xs) (mapList f ys)
mapPerm f (swapp xs) =
  subst2 Perm (sym (mapList++ xs)) (sym (mapList++ xs)) (swapp (mapList f xs))

data Perm* {A : Type} : List A → List A → Type where
  stop : ∀ {xs} → Perm* xs xs
  perm : ∀ {xs ys zs} → Perm xs ys → Perm* ys zs → Perm* xs zs

transP* : {A : Type} {xs ys zs : List A}
  → Perm* xs ys → Perm* ys zs → Perm* xs zs
transP* stop qs = qs
transP* (perm p ps) qs = perm p (transP* ps qs)

revP : {A : Type} {xs ys : List A}
  → Perm xs ys → Perm ys xs 
revP (swapp xs) = swapp xs

revP* : {A : Type} {xs ys : List A}
  → Perm* xs ys → Perm* ys xs 
revP* stop = stop
revP* (perm p ps) = transP* (revP* ps) (perm (revP p) stop)

substP* : {A : Type} {xs ys : List A} → xs ≡ ys → Perm* xs ys
substP* {xs = xs} eq = subst (Perm* xs) eq stop

congPerm* : {A : Type} {x : A} {xs ys : List A} → Perm* xs ys → Perm* (x ∷ xs) (x ∷ ys)
congPerm* stop = stop
congPerm* (perm p ps) = perm (congPerm p) (congPerm* ps)

appendP* : {A : Type} (xs : List A) {ys zs : List A} → Perm* ys zs → Perm* (xs ++ ys) (xs ++ zs)
appendP* [] ps = ps
appendP* (x ∷ xs) ps = congPerm* (appendP* xs ps)

appendP : {A : Type} (xs : List A) {ys zs : List A} → Perm ys zs → Perm (xs ++ ys) (xs ++ zs)
appendP [] p = p
appendP (x ∷ xs) p = congPerm (appendP xs p)

append2P : {A : Type} {xs ys zs : List A} → Perm xs ys → Perm (xs ++ zs) (ys ++ zs)
append2P {zs = zs} (swapp xs {ys}) =
  subst2 Perm (sym (++-assoc xs (_ ∷ _ ∷ ys) zs))
              (sym (++-assoc xs (_ ∷ _ ∷ ys) zs))
              (swapp xs)

append2P* : {A : Type} {xs ys zs : List A} → Perm* xs ys → Perm* (xs ++ zs) (ys ++ zs)
append2P* stop = stop
append2P* (perm p ps) = perm (append2P p) (append2P* ps)

moveHeadP* : {A : Type} (x : A) (xs : List A) {ys : List A} → Perm* (x ∷ xs ++ ys) (xs ++ x ∷ ys)
moveHeadP* x [] = stop
moveHeadP* x (y ∷ xs) = perm (swapp []) (congPerm* (moveHeadP* x xs))

MsetQ : Type → Type
MsetQ A = List A / Perm

mapMsetQ : {A B : Type} (f : A → B) → MsetQ A → MsetQ B
mapMsetQ f [ xs ] = [ mapList f xs ]
mapMsetQ f (eq/ xs ys r i) =
  eq/ (mapList f xs) (mapList f ys) (mapPerm f r) i
mapMsetQ f (squash/ xs ys p q i j) =
  squash/ (mapMsetQ f xs) (mapMsetQ f ys)
          (λ k → mapMsetQ f (p k)) (λ k → mapMsetQ f (q k))
          i j

_∷Q_ : ∀ {A} → A → MsetQ A → MsetQ A
_∷Q_ a = recQ squash/ (λ xs → [ a ∷ xs ])
  λ { ._ ._ (swapp xs) → eq/ _ _ (swapp (a ∷ xs))}

_++Q_ : ∀ {A} → MsetQ A → MsetQ A → MsetQ A
_++Q_ = recQ2 squash/ (λ xs ys → [ xs ++ ys ])
  (λ { ._ ._ zs (swapp xs) →
    eq/ _ _ (subst2 Perm (sym (++-assoc xs _ _)) (sym (++-assoc xs _ _)) (swapp xs)) })
  λ { zs ._ ._ (swapp xs {ys = ys} ) →
    eq/ _ _ (subst2 Perm (++-assoc zs _ _) (++-assoc zs _ _) (swapp (zs ++ xs))) }

[moveHead] : {A : Type} (x : A) (xs : List A) {ys : List A} → _≡_ {A = MsetQ A} [ x ∷ xs ++ ys ] [ xs ++ x ∷ ys ]
[moveHead] x [] = refl
[moveHead] x (y ∷ xs) = eq/ _ _ (swapp []) ∙ cong (y ∷Q_) ([moveHead] x xs)


MsetQ' : Type → Type
MsetQ' A = List A / Perm*

toMsetQ : ∀{A} → MsetQ' A → MsetQ A
toMsetQ = recQ squash/ [_] lem
  where
    lem : ∀ xs ys → Perm* xs ys → [ xs ] ≡ [ ys ]
    lem xs .xs stop = refl
    lem xs ys (perm p ps) = eq/ xs _ p ∙ lem _ ys ps

fromMsetQ : ∀{A} → MsetQ A → MsetQ' A
fromMsetQ = recQ squash/ [_] (λ _ _ p → eq/ _ _ (perm p stop))

toFromMsetQ : ∀{A} (xs : MsetQ A) → toMsetQ (fromMsetQ xs) ≡ xs
toFromMsetQ = elimPropQ (λ _ → squash/ _ _) λ _ → refl 

fromToMsetQ : ∀{A} (xs : MsetQ' A) → fromMsetQ (toMsetQ xs) ≡ xs
fromToMsetQ = elimPropQ (λ _ → squash/ _ _) λ _ → refl 


module Sorting {A : Type} (setA : isSet A)
  (R : A → A → Type)
  (linR : isLinOrder R) where

  open isLinOrder linR
  open isStrictOrder strictR


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


  insert-eq/ : ∀ x acc 
    → _≡_ {A = MsetQ A} [ insert x acc ] [ x ∷ acc ]
  insert-eq/ x [] = refl
  insert-eq/ x (y ∷ acc) with totR x y
  ... | inl Rxy = refl
  ... | inr (inl Ryx) = cong (y ∷Q_) (insert-eq/ x acc) ∙ eq/ _ _ (swapp [])
  ... | inr (inr x≡y) = refl

  sort : List A → List A → List A
  sort [] acc = acc
  sort (x ∷ xs) acc = sort xs (insert x acc)

  sortPerm : ∀ xs ys acc
    → Perm xs ys → sort xs acc ≡ sort ys acc
  sortPerm .([] ++ _ ∷ _ ∷ ys) .([] ++ _ ∷ _ ∷ ys) acc (swapp [] {ys}) =
    cong (sort ys) (insert-insert _ _ acc)
  sortPerm ._ ._ acc (swapp (x ∷ xs)) = sortPerm _ _ _ (swapp xs)

  sort-eq/ : ∀ {xs ys acc}
    → Perm* xs ys → sort xs acc ≡ sort ys acc
  sort-eq/ stop = refl
  sort-eq/ (perm p ps) = sortPerm _ _ _ p ∙ sort-eq/ ps

  sortM : MsetQ A → List A
  sortM =
    recQ (isOfHLevelList 0 setA)
      (λ xs → sort xs [])
      λ xs ys p → sortPerm xs ys _ p

  sortM-sec' : ∀ xs acc
    → _≡_ {A = MsetQ A} [ sort xs acc ] [ xs ++ acc ]
  sortM-sec' [] acc = refl
  sortM-sec' (x ∷ xs) acc =
    sortM-sec' xs (insert x acc)
    ∙ (λ i → [ xs ] ++Q (insert-eq/ x acc i))
    ∙ sym ([moveHead] x xs) 

  sortM-sec : ∀ xs → [ sortM xs ] ≡ xs
  sortM-sec =
    elimPropQ (λ _ → squash/ _ _)
      (λ xs → sortM-sec' xs []
              ∙ λ i → [ ++-unit-r xs i ])


  insertP* : (x : A) (xs : List A) → Perm* (x ∷ xs) (insert x xs)
  insertP* x [] = stop
  insertP* x (y ∷ xs) with totR x y
  ... | inl p = stop
  ... | inr (inl p) = perm (swapp []) (congPerm* (insertP* x xs))
  ... | inr (inr p) = stop

--   sortP*' : (xs acc : List A) → Perm* (rev xs ++ acc) (sort xs acc)
--   sortP*' [] acc = stop
--   sortP*' (x ∷ xs) acc =
--     transP* (substP* (++-assoc (rev xs) _ _))
--             (transP* (appendP* (rev xs) (insertP* x acc)) (sortP*' xs (insert x acc)))

  sortP* : (xs acc : List A) → Perm* (acc ++ xs) (sort xs acc)
  sortP* [] acc = substP* (++-unit-r acc)
  sortP* (x ∷ xs) acc =
    transP* (revP* (moveHeadP* x acc))
            (transP* (append2P* {zs = xs} (insertP* x acc))
                     (sortP* xs (insert x acc)))

  canonicalPerm* : (xs ys : List A) → Perm* xs ys → Perm* xs ys
  canonicalPerm* xs ys σ =
    transP* (sortP* xs [])
            (transP* (substP* (sort-eq/ σ))
                     (revP* (sortP* ys [])))

  canonicalPerm*-const : (xs ys : List A) (σ Φ : Perm* xs ys)
    → canonicalPerm* xs ys σ ≡ canonicalPerm* xs ys Φ
  canonicalPerm*-const xs ys σ Φ =
    cong (transP* (sortP* xs []))
         (cong (λ z → transP* z (revP* (sortP* ys [])))
               (cong substP* (isOfHLevelList 0 setA _ _ _ _)))



module MsetLinOrder {A : Type} (setA : isSet A)
  (R : A → A → Type)
  (linR : isLinOrder R) where

  open isLinOrder linR
  open isStrictOrder strictR
  open ListLinOrder setA R linR
  open Sorting setA R linR

  LexQ : MsetQ A → MsetQ A → Type
  LexQ xs ys = Lex (sortM xs) (sortM ys)

  strictLexQ : isStrictOrder LexQ
  strictLexQ = 
    record { asymR = asymLex
           ; transR = transLex
           ; propR = propLex
           }

  totLexQ : ∀ xs ys → LexQ xs ys ⊎ (LexQ ys xs ⊎ (xs ≡ ys))
  totLexQ xs ys = map⊎ (idfun _) (map⊎ (idfun _) lem) (totLex (sortM xs) (sortM ys))
    where
      lem : sortM xs ≡ sortM ys → xs ≡ ys
      lem eq =
        xs ≡⟨ sym (sortM-sec xs) ⟩
        [ sortM xs ] ≡⟨ cong [_] eq ⟩
        [ sortM ys ] ≡⟨ sortM-sec ys ⟩
        ys ∎

  linLexQ : isLinOrder LexQ
  linLexQ =
    record { strictR = strictLexQ
           ; totR = totLexQ
           }


-- Perm-com : {A : Type} (xs ys : List A) → _≡_ {A = MsetQ A} [ xs ++ ys ] [ ys ++ xs ]
-- Perm-com [] ys = sym (cong [_] (++-unit-r ys))
-- Perm-com (x ∷ xs) ys = [moveHead]  x xs ∙ Perm-com xs (x ∷ ys) ∙ [moveHead] x ys

-- -- turning a list into a finite multisubset
-- List→Mset : ∀{A : Type} → List A → Mset A
-- List→Mset [] = ø
-- List→Mset (x ∷ xs) = η x ∪ List→Mset xs

-- -- this functions is a monoid morphism (turns ++ into ∪)
-- List→Mset++ : {A : Type}(xs ys : List A)
--   → List→Mset (xs ++ ys) ≡ List→Mset xs ∪ List→Mset ys
-- List→Mset++ [] ys = sym (com _ _ ∙ nr _)
-- List→Mset++ (x ∷ xs) ys = cong (η x ∪_) (List→Mset++ xs ys) ∙ ass _ _ _

-- MsetQ→MsetEq : ∀{A} {xs ys : List A} → Perm xs ys → List→Mset xs ≡ List→Mset ys
-- MsetQ→MsetEq (swapp xs {ys}) =
--   List→Mset++ xs _
--   ∙ cong (List→Mset xs ∪_) (ass _ _ _ ∙ cong (_∪ List→Mset ys) (com _ _) ∙ sym (ass _ _ _))
--   ∙ sym (List→Mset++ xs _)

-- MsetQ→Mset : ∀{A} → MsetQ A → Mset A
-- MsetQ→Mset = recQ trunc List→Mset (λ _ _ → MsetQ→MsetEq)

-- Mset→MsetQ : ∀{A} → Mset A → MsetQ A
-- Mset→MsetQ =
--   recMset squash/
--     [ [] ]
--     (λ a → [ a ∷ [] ])
--     (recQ2 squash/ (λ xs ys → [ xs ++ ys ])
--       (λ xs ys zs p → eq/ _ _ (append2P p))
--       (λ xs ys zs p → eq/ _ _ (appendP xs p)))
--     (elimProp2 (λ _ _ → squash/ _ _) (λ xs ys → Perm-com xs ys))
--     (elimProp3 (λ _ _ _ → squash/ _ _) (λ xs ys zs → cong [_] (sym (++-assoc xs ys zs))))
--     (elimProp (λ _ → squash/ _ _) (λ xs → cong [_] (++-unit-r xs)))

-- MsetQ→Mset→MsetQ' : ∀{A} (xs : List A)
--   → Mset→MsetQ (List→Mset xs) ≡ [ xs ]
-- MsetQ→Mset→MsetQ' [] = refl
-- MsetQ→Mset→MsetQ' (x ∷ xs) =
--   cong (recQ squash/ (λ ys → [ x ∷ ys ]) _) (MsetQ→Mset→MsetQ' xs)

-- MsetQ→Mset→MsetQ : ∀{A} (s : MsetQ A) → Mset→MsetQ (MsetQ→Mset s) ≡ s
-- MsetQ→Mset→MsetQ = elimProp (λ _ → squash/ _ _) MsetQ→Mset→MsetQ'

-- Mset→MsetQ→Mset : ∀{A} (s : Mset A) → MsetQ→Mset (Mset→MsetQ s) ≡ s
-- Mset→MsetQ→Mset {A} =
--   elimMsetProp (λ _ → _ , trunc _ _) refl (λ _ → nr _)
--     λ {s₁}{s₂} p q →
--       lem (Mset→MsetQ s₁) (Mset→MsetQ s₂) ∙ cong₂ _∪_ p q
--   where
--     lem : (s₁ s₂ : MsetQ A)
--       → MsetQ→Mset (recQ2 squash/ (λ xs ys → [ xs ++ ys ]) _ _ s₁ s₂) ≡
--          MsetQ→Mset s₁ ∪ MsetQ→Mset s₂
--     lem = elimProp2 (λ _ _ → trunc _ _) List→Mset++

-- Mset≡MsetQ : ∀{A} → Mset A ≡ MsetQ A
-- Mset≡MsetQ =
--   isoToPath (iso Mset→MsetQ MsetQ→Mset MsetQ→Mset→MsetQ Mset→MsetQ→Mset)

{-
  data Sorted : List A → Type where
    [] : Sorted []
    _∷_ : ∀{x xs} → (∀ y → y ∈ xs → R x y ⊎ (x ≡ y)) → Sorted xs → Sorted (x ∷ xs)

  propSorted : ∀ xs → isProp (Sorted xs)
  propSorted [] [] [] = refl
  propSorted (x ∷ xs) (r ∷ p) (r' ∷ p') i =
    (λ y y∈ → {!r y y∈!}) ∷ propSorted xs p p' i
    --propR (r y y∈) (r' y y∈) i) 

  sorted++1 : ∀ xs {ys} → Sorted (xs ++ ys) → Sorted xs
  sorted++1 [] std = []
  sorted++1 (x ∷ xs) (r ∷ std) = (λ y y∈ → r y {!!}) ∷ (sorted++1 xs std) --(∈++₁ y∈)

  sorted++2 : ∀ xs {ys} → Sorted (xs ++ ys) → Sorted ys
  sorted++2 [] std = std
  sorted++2 (x ∷ xs) (r ∷ std) = sorted++2 xs std

--   sorted++3 : ∀ {x xs ys} → Sorted (xs ++ x ∷ ys)
--     → ∀{z} → z ∈ xs → R z x
--   sorted++3 (r ∷ std) here = {!!} --r _ {!!} --(∈++₂ here)
--   sorted++3 (r ∷ std) (there z∈) = sorted++3 std z∈

  SList : Type
  SList = Σ[ xs ∈ List A ] Sorted xs

  setSList : isSet SList
  setSList =
    isSetΣ (isOfHLevelList 0 setA)
           λ _ → isProp→isSet (propSorted _)

  ∈insert : ∀ x z acc 
    → z ∈ insert x acc → (z ≡ x) ⊎ z ∈ acc
  ∈insert x .x [] here = inl refl
  ∈insert x z (y ∷ acc) z∈ with totR x y
  ∈insert x .x (y ∷ acc) here | inl Rxy = inl refl
  ∈insert x z (y ∷ acc) (there z∈) | inl Rxy = inr z∈
  ∈insert x .y (y ∷ acc) here | inr (inl Ryx) = inr here
  ∈insert x z (y ∷ acc) (there z∈) | inr (inl Ryx) =
    map⊎ (idfun _) there (∈insert x z acc z∈)
  ∈insert x .x (y ∷ acc) here | inr (inr x≡y) = inl refl
  ∈insert x z (y ∷ acc) (there z∈) | inr (inr x≡y) = inr z∈

  sinsert : ∀ x acc (std : Sorted acc) → Sorted (insert x acc)
  sinsert x [] [] = (λ y ()) ∷ []
  sinsert x (y ∷ acc) (r ∷ std) with totR x y
  ... | inl Rxy =
    (λ { z here → inl Rxy ; z (there z∈) → inl (rec⊎ (transR Rxy) (λ eq → subst (R x) eq Rxy ) (r z z∈)) }) 
      ∷ r ∷ std
  ... | inr (inl Ryx) =
    (λ z z∈ → rec⊎ (λ eq → inl (subst (R y) (sym eq) Ryx)) (r z) (∈insert x z acc z∈)) 
      ∷ (sinsert x acc std)
  ... | inr (inr x≡y) =
    (λ { z here → inr x≡y ; z (there z∈) → J (λ x eq → R x z ⊎ (x ≡ z)) (r z z∈) (sym x≡y) })
      ∷ r ∷ std
      
  sort : List A → SList → SList
  sort [] sacc = sacc
  sort (x ∷ xs) (acc , std) =
    sort xs (insert x acc , sinsert x acc std)

  sort-perm : ∀ xs ys (acc : SList)
    → Perm xs ys → sort xs acc .fst ≡ sort ys acc .fst
  sort-perm .([] ++ _ ∷ _ ∷ ys) .([] ++ _ ∷ _ ∷ ys) (acc , std) (swapp [] {ys}) =
    cong (λ z → sort ys z .fst) (Σ≡Prop propSorted (insert-insert _ _ acc))
  sort-perm ._ ._ acc (swapp (x ∷ xs)) = sort-perm _ _ _ (swapp xs)

  MsetQ→SList : MsetQ A → SList
  MsetQ→SList =
    recQ setSList
      (λ xs → sort xs ([] , []))
      λ xs ys p → Σ≡Prop propSorted (sort-perm xs ys _ p)

  SList→MsetQ : SList → MsetQ A
  SList→MsetQ (xs , _) = [ xs ]

  MsetQ→SList→MsetQ' : ∀ xs ((acc , std) : SList)
    → _≡_ {A = MsetQ A} [ sort xs (acc , std) .fst ] [ xs ++ acc ]
  MsetQ→SList→MsetQ' [] sacc = refl
  MsetQ→SList→MsetQ' (x ∷ xs) (acc , std) =
    MsetQ→SList→MsetQ' xs (insert x acc , sinsert x acc std)
    ∙ (λ i → [ xs ] ++Q (insert-eq/ x acc i))
    ∙ sym ([moveHead] x xs) 

  MsetQ→SList→MsetQ : ∀ xs
    → SList→MsetQ (MsetQ→SList xs) ≡ xs
  MsetQ→SList→MsetQ =
    elimPropQ (λ _ → squash/ _ _)
      (λ xs → MsetQ→SList→MsetQ' xs ([] , [])
              ∙ λ i → [ ++-unit-r xs i ])
-}

--   insert-last : ∀ x xs (std : Sorted xs)
--     → (∀ y → y ∈ xs → R y x ⊎ (y ≡ x))
--     → insert x xs ≡ xs ++ x ∷ []
--   insert-last x [] [] p = refl
--   insert-last x (y ∷ xs) (r ∷ rs) p with totR x y
--   ... | inl Rxy = rec (rec⊎ (asymR Rxy) (λ eq → irreflR (subst (R x) eq Rxy)) (p y here))
--   ... | inr (inl Ryx) =
--     cong (y ∷_) (insert-last x xs {!!} (λ z z∈ → p z (there z∈)))
--   ... | inr (inr x≡y) = {!!}

  --(irreflR (subst (R y) x≡y {!!})) --(p y here)
 
--   sort-sorted : ∀ xs acc (std : Sorted (acc ++ xs))
--     → sort xs (acc , sorted++1 acc std) .fst ≡ acc ++ xs
--   sort-sorted [] acc std = sym (++-unit-r acc)
--   sort-sorted (x ∷ xs) acc std =
--     cong (λ z → sort xs z .fst) (Σ≡Prop propSorted (insert-last x acc {!!}))
--     ∙ sort-sorted xs (acc ++ x ∷ []) (subst Sorted (sym (++-assoc acc (x ∷ []) xs)) std) 
--     ∙ ++-assoc acc (x ∷ []) xs

--   SList→MsetQ→SList : (xs : SList)
--     → MsetQ→SList (SList→MsetQ xs) ≡ xs
--   SList→MsetQ→SList (xs , std) =
--     Σ≡Prop propSorted (sort-sorted xs [] std)

-- module SortedListProperties
--   (A : hSet ℓ-zero) {R : ⟨ A ⟩ → ⟨ A ⟩ → Type} (linR : isLinOrder R)
--   (B : hSet ℓ-zero) {S : ⟨ B ⟩ → ⟨ B ⟩ → Type} (linS : isLinOrder S)
--   (f : ⟨ A ⟩ → ⟨ B ⟩) (monf : ∀{x y} → R x y → S (f x) (f y)) where

--   open isLinOrder
--   open SortedLists
--   open isStrictOrder (strictR linS)

--   mapSorted : ∀{xs} → Sorted A linR xs → Sorted B linS (mapList f xs)
--   mapSorted [] = []
--   mapSorted (r ∷ std) =
--     (λ y y∈ → let (x , x∈ , fx≡y) = pre∈mapList y∈ in subst (S (f _)) fx≡y (monf (r x x∈)))
--       ∷ mapSorted std

--   mapSList : SList A linR → SList B linS
--   mapSList (xs , std) = mapList f xs , mapSorted std

--   insert-nat : ∀ x acc (std : Sorted A linR acc)
--     → insert B linS (f x) (mapList f acc) (mapSorted std) ≡
--              mapList f (insert A linR x acc std)
--   insert-nat x [] [] = refl
--   insert-nat x (y ∷ acc) (r ∷ std) with totR linR x y | totR linS (f x) (f y)
--   ... | inj₁ r | inj₁ s = refl
--   ... | inj₁ r | inj₂ s = ⊥-rec (asymR s (monf r))
--   ... | inj₂ r | inj₁ s = ⊥-rec (asymR s (monf r))
--   ... | inj₂ r | inj₂ s = cong (f y ∷_) (insert-nat x acc std)

--   sort-nat : ∀ xs (acc : SList A linR)
--     → sort B linS (mapList f xs) (mapSList acc) .fst
--              ≡ mapList f (sort A linR xs acc .fst)
--   sort-nat [] acc = refl
--   sort-nat (x ∷ xs) (acc , std) =
--     cong (λ z → sort B linS (mapList f xs) z .fst) 
--          (Σ≡Prop (propSorted B linS) (insert-nat x acc std))
--     ∙ sort-nat xs _

--   MsetQ→SList-nat : ∀ xs
--     → MsetQ→SList B linS (mapMsetQ f xs) ≡ mapSList (MsetQ→SList A linR xs)
--   MsetQ→SList-nat =
--     elimProp (λ _ → setSList B linS _ _)
--       λ xs → Σ≡Prop (propSorted B linS) (sort-nat xs ([] , [])) 


-- {-
-- module Lexicographic (A : hSet ℓ-zero) {R : ⟨ A ⟩ → ⟨ A ⟩ → Type}
--   (strictR : isStrictOrder R) where
-- --(decR : ∀ x y → Dec (R x y)) 

--   open isStrictOrder strictR

--   data LexL' : (xs ys : List ⟨ A ⟩) → length xs ≡ length ys → Type where
--     [] : LexL' [] [] refl
--     R∷ : ∀{x y xs ys sl} → R x y → LexL' (x ∷ xs) (y ∷ ys) (cong suc sl)
--     ≡∷ : ∀{x y xs ys sl} → x ≡ y → LexL' xs ys sl
--       → LexL' (x ∷ xs) (y ∷ ys) (cong suc sl)
    
--   data LexL (xs ys : List ⟨ A ⟩) : Type where
--     <l : length xs < length ys → LexL xs ys
--     ≡l : (sl : length xs ≡ length ys) → LexL' xs ys sl → LexL xs ys

--   data Lex : List ⟨ A ⟩ → List ⟨ A ⟩ → Type where
--     [] : ∀{y ys} → Lex [] (y ∷ ys)
--     R∷ : ∀{x y xs ys} → R x y → Lex (x ∷ xs) (y ∷ ys)
--     ≡∷ : ∀{x y xs ys} → x ≡ y → Lex xs ys → Lex (x ∷ xs) (y ∷ ys)

--   asymLex : ∀ {xs ys} → Lex xs ys → Lex ys xs → ⊥
--   asymLex (R∷ x) (R∷ x₁) = asymR x x₁
--   asymLex (R∷ x) (≡∷ x₁ q) = irreflR (subst (R _) x₁ x)
--   asymLex (≡∷ x p) (R∷ x₁) = irreflR (subst (R _) x x₁)
--   asymLex (≡∷ x p) (≡∷ x₁ q) = asymLex p q

--   transLex : ∀ {xs ys zs} → Lex xs ys → Lex ys zs → Lex xs zs
--   transLex [] (R∷ x) = []
--   transLex [] (≡∷ x q) = []
--   transLex (R∷ x) (R∷ x₁) = R∷ (transR x x₁)
--   transLex (R∷ x) (≡∷ x₁ q) = R∷ (subst (R _) x₁ x)
--   transLex (≡∷ x p) (R∷ x₁) = R∷ (subst (λ z → R z _) (sym x) x₁)
--   transLex (≡∷ x p) (≡∷ x₁ q) = ≡∷ (x ∙ x₁) (transLex p q)

--   propLex : ∀ {xs ys} → isProp (Lex xs ys)
--   propLex [] [] = refl
--   propLex (R∷ x) (R∷ x₁) = cong R∷ (propR x x₁)
--   propLex (R∷ x) (≡∷ x₁ q) = ⊥-rec (irreflR (subst (R _) (sym x₁) x))
--   propLex (≡∷ x p) (R∷ x₁) = ⊥-rec (irreflR (subst (R _) (sym x) x₁))
--   propLex (≡∷ x p) (≡∷ x₁ q) = cong₂ ≡∷ (A .snd _ _ _ _) (propLex p q)

--   -- TODO: add equality possibility to totR
--   totLex : ∀ xs ys → Lex xs ys ⊎ Lex ys xs
--   totLex [] [] = {!!}
--   totLex [] (x ∷ ys) = inj₁ []
--   totLex (x ∷ xs) [] = inj₂ []
--   totLex (x ∷ xs) (y ∷ ys) = {!!}

--   LexStrictOrder : isStrictOrder Lex
--   LexStrictOrder = record {
--     asymR = asymLex ;
--     transR = transLex ;
--     propR = propLex }

--   LexLinOrder : isLinOrder Lex
--   LexLinOrder = record { strictR = {!!} ; totR = {!!} }
-- -}

-- Pull : {A B C : Type} (f : A → C) (g : B → C) → Type
-- Pull {A}{B} f g = Σ (A × B) λ x → f (x .fst) ≡ g (x .snd)

-- module ListPullback {A B C : Type} (f : A → C) (g : B → C) where

--   ListPull : Type
--   ListPull =
--     Σ (List A × List B) λ xs → mapList f (xs .fst) ≡ mapList g (xs .snd)

--   w : List (Pull f g) → ListPull
--   w xs =
--     (mapList (λ x → x .fst .fst) xs ,
--      mapList (λ x → x .fst .snd) xs) ,
--      mapListComp xs ∙ (λ i → mapList (λ x → x .snd i) xs) ∙ sym (mapListComp xs)

--   w-1' : ∀ xs ys → mapList f xs ≡ mapList g ys → List (Pull f g)
--   w-1' [] [] p = []
--   w-1' [] (y ∷ ys) p = ⊥-rec (¬nil≡cons p)
--   w-1' (x ∷ xs) [] p = ⊥-rec (¬cons≡nil p)
--   w-1' (x ∷ xs) (y ∷ ys) p =
--     ((x , y) , cons-inj₁ p) ∷ w-1' xs ys (cons-inj₂ p)

--   w-1 : ListPull → List (Pull f g)
--   w-1 ((xs , ys) , p) = w-1' xs ys p

--   w-iso1' : ∀ xs ys (p : mapList f xs ≡ mapList g ys)
--     → w (w-1' xs ys p) .fst ≡ (xs , ys)
--   w-iso1' [] [] p = refl
--   w-iso1' [] (y ∷ ys) p = ⊥-rec (¬nil≡cons p)
--   w-iso1' (x ∷ xs) [] p = ⊥-rec (¬cons≡nil p)
--   w-iso1' (x ∷ xs) (y ∷ ys) p with w-iso1' xs ys (cons-inj₂ p)
--   ... | ih =
--     cong₂ _,_ (cong (x ∷_) (cong fst ih)) (cong (y ∷_) (cong snd ih))

--   w-iso1 : ∀ xs  → w (w-1 xs) ≡ xs
--   w-iso1 ((xs , ys) , p) = Σ≡Prop {!!} (w-iso1' xs ys p)

--   w-iso2 : ∀ xs → w-1 (w xs) ≡ xs
--   w-iso2 [] = refl
--   w-iso2 (x ∷ xs) =
--     {!!}
--     ∙ λ i → x ∷ w-iso2 xs i
-- --    cong₂ _∷_ (cong (λ z → (x .fst .fst , x .fst .snd) , z) {!!})
-- --              ((cong (w-1' (mapList (λ z → z .fst .fst) xs)
-- --      (mapList (λ z → z .fst .snd) xs)) {!!}) ∙ (w-iso2 xs))

-- module MsetQPullback {A B C : Type} (f : A → C) (g : B → C) where

--   open ListPullback f g

--   MsetQPull : Type
--   MsetQPull =
--     Σ (MsetQ A × MsetQ B) λ xs → mapMsetQ f (xs .fst) ≡ mapMsetQ g (xs .snd)

--   v : MsetQ (Pull f g) → MsetQPull
--   v = recQ {!!}
--     (λ xs → ([ w xs .fst .fst ] , [ w xs .fst .snd ]) , cong [_] (w xs .snd))
--     λ s s' p → Σ≡Prop {!!}
--       (λ i → (eq/ _ _ (mapPerm (λ x → x .fst .fst) p) i) ,
--               eq/ _ _ (mapPerm (λ x → x .fst .snd) p) i)

--   v-1'' : ∀ xs ys → Perm (mapList f xs) (mapList g ys)
--     → MsetQ (Pull f g)
--   v-1'' [] [] p = [ [] ]
--   v-1'' [] (x ∷ ys) p = {!!}
--   v-1'' (x ∷ xs) [] p = {!effective ? ? (f x ∷ mapList f xs) [] p!}
--   v-1'' (x ∷ xs) (y ∷ ys) p = ((x , y) , {!!}) ∷Q {!!}

--   v-1' : ∀ xs ys → mapMsetQ f xs ≡ mapMsetQ g ys → MsetQ (Pull f g)
--   v-1' = elimQ {!!}
--     (λ xs → elimQ {!!}
--       (λ ys p → {!!})
--       {!!})
--     {!!}

--   v-1 : MsetQPull → MsetQ (Pull f g)
--   v-1 ((xs , ys) , p) = {!!}

-- -- -- MsetQ action on functions 
-- -- DRelatorMapList : {A B : Type} (f : A → B) {xs ys : List A}
-- --   → DRelator _≡_ xs ys → DRelator _≡_ (mapList f xs) (mapList f ys)
-- -- DRelatorMapList f p x mx with pre∈mapList mx
-- -- ... | y , my , eq =
-- --   ∥map∥ (λ { (z , mz , eq') → _ , ∈mapList mz , sym eq ∙ cong f eq'}) (p y my)

-- -- mapMsetQ : ∀{A (f : A → B) (monf : ∀{x y} → R x y → S (f x) (f y))B} (f : A → B) → MsetQ A → MsetQ B
-- -- mapMsetQ f = recQ squash/ (λ xs → [ mapList f xs ])
-- --   λ xs ys p → eq/ _ _ (DRelatorMapList f (p .fst) , DRelatorMapList f (p .snd))

-- -- mapMsetQComp : ∀{A B C} {g : B → C} {f : A → B} (x : MsetQ A)
-- --   → mapMsetQ g (mapMsetQ f x) ≡ mapMsetQ (g ∘ f) x
-- -- mapMsetQComp = elimProp (λ _ → squash/ _ _)
-- --   (λ xs → cong [_] (mapListComp xs))

-- -- pre∈mapMsetQ : {A B : Type} {f : A → B} {b : B} (s : MsetQ A)
-- --   → ⟨ b ∈Q mapMsetQ f s ⟩ → ∃[ a ∈ A ] ⟨ a ∈Q s ⟩ × (f a ≡ b)
-- -- pre∈mapMsetQ = elimProp (λ _ → isPropΠ (λ _ → propTruncIsProp))
-- --   λ xs → ∥map∥ (λ m → _ , ∣ pre∈mapList m .snd .fst ∣ , pre∈mapList m .snd .snd) 

-- -- -- the size of a finite subset, which we can define if the carrier
-- -- -- type has decidable equality
-- -- size : {A : Type} (decA : (x y : A) → Dec (x ≡ y))
-- --   → MsetQ A → ℕ
-- -- size decA = recQ isSetℕ
-- --   (λ xs → length (removeDups decA xs))
-- --   λ xs ys r → ≤-antisym (lengthDupFree (removeDups decA xs) (removeDups decA ys)
-- --                                         (dupFreeRemoveDups decA xs) (dupFreeRemoveDups decA ys)
-- --                                         λ x m → ∥map∥ (λ { (y , m , eq) → y , ∈removeDups decA ys m , eq}) (r .fst _ (removeDups∈ decA xs m)))
-- --                          (lengthDupFree (removeDups decA ys) (removeDups decA xs)
-- --                                         (dupFreeRemoveDups decA ys) (dupFreeRemoveDups decA xs)
-- --                                         λ x m → ∥map∥ (λ { (y , m , eq) → y , ∈removeDups decA xs m , eq}) (r .snd _ (removeDups∈ decA ys m)))

-- -- -- the size of (x ∷Q s)
-- -- size∷Q' : {A : Type} (decA : (x y : A) → Dec (x ≡ y))
-- --   → {x : A} (xs : List A) → (∥ x ∈ xs ∥ → ⊥)
-- --   → size decA (x ∷Q [ xs ]) ≡ suc (size decA [ xs ])
-- -- size∷Q' decA {x} xs m with decMem decA x xs
-- -- ... | yes (x' , m' , eq) = ⊥-rec (m ∣ subst (_∈ xs) (sym eq) m' ∣)
-- -- ... | no ¬p = refl

-- -- size∷Q : {A : Type} (decA : (x y : A) → Dec (x ≡ y))
-- --   → {x : A} (s : MsetQ A) → (⟨ x ∈Q s ⟩ → ⊥)
-- --   → size decA (x ∷Q s) ≡ suc (size decA s)
-- -- size∷Q decA = elimProp (λ _ → isPropΠ (λ _ → isSetℕ _ _)) (size∷Q' decA)

-- -- -- the size of (mapMsetQ f s)
-- -- sizeMapMsetQ : {A B : Type} (decA : (x y : A) → Dec (x ≡ y))
-- --   → (decB : (x y : B) → Dec (x ≡ y))
-- --   → {f : A → B} (injf : ∀ x y → f x ≡ f y → x ≡ y) (s : MsetQ A)
-- --   → size decB (mapMsetQ f s) ≡ size decA s
-- -- sizeMapMsetQ decA decB injf = elimProp (λ _ → isSetℕ _ _)
-- --   (λ xs → cong length (removeDupMapList decA decB injf xs)
-- --           ∙ lengthMapList (removeDups decA xs))



-- -- -- if path equality on A is decidable, then also path equality on MsetQ A
-- -- -- is decidable
-- -- MsetQDecEq' : {A : Type}
-- --   → ((x y : A) → Dec (x ≡ y))
-- --   → (xs ys : List A) → Dec (_≡_ {A = MsetQ A} [ xs ] [ ys ])
-- -- MsetQDecEq'  decA xs ys with decRelator decA xs ys
-- -- ... | yes p = yes (eq/ _ _ p)
-- -- ... | no ¬p = no (λ p → ¬p (effective isPropSameEls isEquivRelSameEls _ _ p))

-- -- MsetQDecEq : {A : Type}
-- --   → ((x y : A) → Dec (x ≡ y))
-- --   → (x y : MsetQ A) → Dec (x ≡ y)
-- -- MsetQDecEq decA =
-- --   elimProp2 (λ _ _ → isPropDec (squash/ _ _))
-- --              (MsetQDecEq' decA)




