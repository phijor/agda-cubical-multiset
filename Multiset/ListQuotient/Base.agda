{-# OPTIONS --safe #-}

module Multiset.ListQuotient.Base where

open import Cubical.Core.Everything
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Everything
open import Cubical.Data.List hiding ([_]) renaming (map to mapList)
open import Cubical.Data.Sigma
open import Cubical.Data.Empty
open import Cubical.Data.Nat
open import Cubical.Data.Sum as Sum
open import Cubical.Data.Fin
  hiding (_/_)
open import Cubical.HITs.PropositionalTruncation as PropTrunc
  renaming (rec to ∥rec∥; map to ∥map∥)
open import Cubical.HITs.SetQuotients
  renaming (rec to recQ; rec2 to recQ2; elimProp2 to elimPropQ2; elimProp to elimPropQ)
open import Cubical.Relation.Binary
open BinaryRelation
open isEquivRel

open import Cubical.Relation.Nullary

-- Stuff about lists

-- mapList preserves identity and composition
mapListId : ∀{ℓ}{X : Type ℓ} (xs : List X)
  → mapList (λ x → x) xs ≡ xs
mapListId [] = refl
mapListId (x ∷ xs) = cong (_ ∷_) (mapListId xs)

mapListComp : ∀{ℓ}{X Y Z : Type ℓ}{g : Y → Z}{f : X → Y} (xs : List X)
  → mapList g (mapList f xs) ≡ mapList (g ∘ f) xs
mapListComp [] = refl
mapListComp (x ∷ xs) = cong (_ ∷_) (mapListComp xs)

mapList++ : ∀{ℓ}{X Y : Type ℓ} {f : X → Y} (xs : List X) {ys : List X}
  → mapList f (xs ++ ys) ≡ mapList f xs ++ mapList f ys
mapList++ [] = refl
mapList++ (x ∷ xs) = cong (_ ∷_) (mapList++ xs)

-- list membership
infix 21 _∈_
data _∈_ {ℓ}{X : Type ℓ} (x : X) : List X → Type ℓ where
  here : ∀{y xs} → x ≡ y → x ∈ (y ∷ xs)
  there : ∀{y xs} → x ∈ xs → x ∈ (y ∷ xs)

inv∈ : ∀ {ℓ}{X : Type ℓ} {x y : X} {xs : List X}
  → (m : x ∈ (y ∷ xs)) → (Σ (x ≡ y) λ p → m ≡ here p) ⊎ (Σ (x ∈ xs) λ m' → m ≡ there m')
inv∈ (here eq) = inl (eq , refl)
inv∈ (there m) = inr (m , refl)

-- removing an element from a list
remove : ∀{ℓ}{A : Type ℓ} {x : A} xs → x ∈ xs → List A
remove (x ∷ xs) (here eq) = xs
remove (y ∷ xs) (there m) = y ∷ remove xs m

-- interaction between ∈ and remove
remove∈ : ∀{ℓ}{A : Type ℓ} {x y : A} {xs} (m : x ∈ xs)
  → y ∈ remove xs m → y ∈ xs
remove∈ (here eq) m' = there m'
remove∈ (there m) (here eq) = here eq
remove∈ (there m) (there m') = there (remove∈ m m')

removeremove∈ : ∀{ℓ}{A : Type ℓ} {x y : A} {xs}
  → (m : x ∈ xs) (m' : y ∈ remove xs m)
  → x ∈ remove xs (remove∈ m m')
removeremove∈ (here eq) m' = here eq
removeremove∈ (there m) (here _) = m
removeremove∈ (there m) (there m') = there (removeremove∈ m m')

remove-par : ∀{ℓ}{A : Type ℓ} {x y : A} {xs}
  → (m : x ∈ xs) (m' : y ∈ remove xs m)
  → remove (remove xs m) m' ≡ remove (remove xs (remove∈ m m')) (removeremove∈ m m')
remove-par (here eq) m' = refl
remove-par (there m) (here eq) = refl
remove-par (there m) (there m') = cong (_ ∷_) (remove-par m m')

-- canonical relation lifting on trees
data ListRel {ℓ}{X Y : Type ℓ} (R : X → Y → Type ℓ)
     : List X → List Y → Type ℓ where
  [] : ListRel R [] []
  _∷_ : ∀{x y xs ys} → R x y → ListRel R xs ys
    → ListRel R (x ∷ xs) (y ∷ ys)

reflListRel : ∀{ℓ}{X : Type ℓ} {R : X → X → Type ℓ}
  → (∀ x → R x x)
  → ∀ xs → ListRel R xs xs
reflListRel reflR [] = []
reflListRel reflR (x ∷ xs) = reflR x ∷ reflListRel reflR xs

symListRel : ∀{ℓ}{X : Type ℓ} {R : X → X → Type ℓ}
  → (∀ {x y} → R x y → R y x)
  → ∀ {xs ys} → ListRel R xs ys → ListRel R ys xs
symListRel symR [] = []
symListRel symR (r ∷ rs) = symR r ∷ symListRel symR rs

ListRel-mapList : ∀{ℓ}{X : Type ℓ} {R : X → X → Type ℓ}
  → {xs ys : List X}
  → ListRel R xs ys
  → mapList ([_] {R = R}) xs ≡ mapList [_] ys
ListRel-mapList [] = refl
ListRel-mapList (r ∷ rs) i = eq/ _ _ r i ∷ ListRel-mapList rs i

data DRelator {ℓ}{X Y : Type ℓ} (R : X → Y → Type ℓ)
     : List X → List Y → Type ℓ where
  nil  : ∀{ys} → DRelator R [] ys
  cons : ∀{x xs ys} (p : ∃[ y ∈ Y ] R x y × (Σ[ m ∈ (y ∈ ys) ] DRelator R xs (remove ys m)))
    → DRelator R (x ∷ xs) ys

  --(r : R x y) (m : y ∈ ys) (p : Relator R xs (remove ys m))

Relator : ∀ {ℓ}{X : Type ℓ} (R : X → X → Type ℓ)
  → List X → List X → Type ℓ
Relator R xs ys = DRelator R xs ys × DRelator R ys xs

isPropDRelator : ∀{ℓ}{X : Type ℓ} (R : X → X → Type ℓ)
  → ∀ xs ys → isProp (DRelator R xs ys)
isPropDRelator R _ _ nil nil = refl
isPropDRelator R _ _ (cons r) (cons r') = cong cons (isPropPropTrunc r r')

isPropRelator : ∀{ℓ}{X : Type ℓ} (R : X → X → Type ℓ)
  → ∀ xs ys → isProp (Relator R xs ys)
isPropRelator R xs ys =
  isProp× (isPropDRelator _ _ _) (isPropDRelator _ _ _)

reflDRelator : ∀{ℓ}{X : Type ℓ} {R : X → X → Type ℓ}
  → (∀ x → R x x)
  → ∀ xs → DRelator R xs xs
reflDRelator reflR [] = nil
reflDRelator reflR (x ∷ xs) = cons ∣ x , reflR x , here refl , reflDRelator reflR xs ∣₁

reflRelator : ∀{ℓ}{X : Type ℓ} {R : X → X → Type ℓ}
  → (∀ x → R x x)
  → ∀ xs → Relator R xs xs
reflRelator reflR xs = (reflDRelator reflR xs) , (reflDRelator reflR xs)

symRelator : ∀{ℓ}{X : Type ℓ} {R : X → X → Type ℓ}
  → ∀ {xs ys} → Relator R xs ys → Relator R ys xs
symRelator (p , q) = (q , p)

memDRelator : ∀{ℓ}{X : Type ℓ} {R : X → X → Type ℓ}
  → ∀ {x xs ys} (m : x ∈ xs) → DRelator R xs ys
  → ∃[ y ∈ X ] R x y × (Σ[ m' ∈ (y ∈ ys) ] DRelator R (remove xs m) (remove ys m'))
memDRelator {X = X}{R} {ys = ys} (here eq) (cons {xs = xs} p) = ∥map∥ (λ r → r)
  (J (λ z _ → ∃[ y ∈ X ] R z y × (Σ[ m' ∈ (y ∈ ys) ] DRelator R xs (remove ys m'))) p (sym eq))
memDRelator (there m) (cons {x = z} p) =
  ∥rec∥ isPropPropTrunc
        (λ { (y , r , m' , p') →
          ∥map∥ (λ { (y' , r' , m'' , p'') →
                     y' , r' , remove∈ m' m'' , cons ∣ y , r , removeremove∈ m' m'' , subst (DRelator _ (remove _ m)) (remove-par m' m'') p'' ∣₁ })
                (memDRelator m p') })
        p

transDRelator : ∀{ℓ}{X : Type ℓ} {R : X → X → Type ℓ}
  → (∀ {x y z} → R x y → R y z → R x z)
  → ∀ {xs ys zs} → DRelator R xs ys → DRelator R ys zs → DRelator R xs zs
transDRelator transR nil q = nil
transDRelator transR (cons p) q =
  ∥rec∥ (isPropDRelator _ _ _)
        (λ { (y , r , m , p') →
          ∥rec∥ (isPropDRelator _ _ _)
                (λ { (z , r' , m' , q') → cons ∣ z , transR r r' , m' , transDRelator transR p' q' ∣₁ })
                (memDRelator m q) })
        p

transRelator : ∀{ℓ}{X : Type ℓ} {R : X → X → Type ℓ}
  → (∀ {x y z} → R x y → R y z → R x z)
  → ∀ {xs ys zs} → Relator R xs ys → Relator R ys zs → Relator R xs zs
transRelator transR p q =
  (transDRelator transR (p .fst) (q .fst)) ,
  (transDRelator transR (q .snd) (p .snd))

isEquivRelRelator : ∀{ℓ}{X : Type ℓ} {R : X → X → Type ℓ}
  → isEquivRel R → isEquivRel (Relator R)
isEquivRelRelator (equivRel reflR _ transR) =
  equivRel (reflRelator reflR)
           (λ _ _ r → r .snd , r .fst)
           λ _ _ _ → transRelator (transR _ _ _)

consInvDRelator : ∀{ℓ}{X Y : Type ℓ} {R : X → Y → Type ℓ}
  → ∀{x xs ys} → DRelator R (x ∷ xs) ys
  → ∃[ y ∈ Y ] R x y × (Σ[ m ∈ (y ∈ ys) ] DRelator R xs (remove ys m))
consInvDRelator (cons p) = p
  

pre∈mapList : ∀{ℓ} {A B : Type ℓ} {f : A → B} {b : B} {xs : List A}
  → b ∈ mapList f xs → Σ[ a ∈ A ] (a ∈ xs) × (f a ≡ b)
pre∈mapList {xs = x ∷ xs} (here eq) = _ , here refl , sym eq
pre∈mapList {xs = x ∷ xs} (there mb) =
  pre∈mapList mb .fst , there (pre∈mapList mb .snd .fst) , pre∈mapList mb .snd .snd


∈mapList : ∀{ℓ}{A B : Type ℓ} {f : A → B} {a : A} {xs : List A}
  → a ∈ xs → f a ∈ mapList f xs
∈mapList {f = f} (here eq) = here (cong f eq)
∈mapList (there m) = there (∈mapList m)

remove-mapList : ∀{ℓ} {A B : Type ℓ} {f : A → B} {a : A} {xs : List A}
  → (m : a ∈ xs) → mapList f (remove xs m) ≡ remove (mapList f xs) (∈mapList m)
remove-mapList (here eq) = refl
remove-mapList (there m) = cong (_ ∷_) (remove-mapList m)

∈mapList-lem' : ∀{ℓ} {A B : Type ℓ} {f : A → B} {b : B} {xs : List A}
  → (m : b ∈ mapList f xs)
  → PathP (λ i → pre∈mapList m .snd .snd (~ i) ∈ mapList f xs) m (∈mapList (pre∈mapList m .snd .fst))
∈mapList-lem' {f = f} {xs = x ∷ xs} (here eq) = J (λ z p → PathP (λ i → p i ∈ (z ∷ mapList f xs)) (here p) (here (λ i → z))) refl eq
∈mapList-lem' {xs = x ∷ xs} (there m) = congP (λ _ → there) (∈mapList-lem' m)

∈mapList-lem : ∀{ℓ} {A B : Type ℓ} {f : A → B} {b : B} {xs : List A}
  → (m : b ∈ mapList f xs)
  → subst (λ x → x ∈ mapList f xs) (sym (pre∈mapList m .snd .snd)) m
          ≡ ∈mapList (pre∈mapList m .snd .fst)
∈mapList-lem m = fromPathP (∈mapList-lem' m)

remove-eq : ∀{ℓ} {A : Type ℓ} {a b : A} {xs : List A}
  → (m : a ∈ xs) (m' : b ∈ xs) (e : a ≡ b) (e' : subst (λ x → x ∈ xs) e m ≡ m')
  → remove xs m ≡ remove xs m'
remove-eq {xs = xs} m m' e e' =
  J (λ b e → (m' : b ∈ xs) (e' : subst (λ x → x ∈ xs) e m ≡ m') → remove xs m ≡ remove xs m')
    (λ m' e' → cong (remove xs) (sym (substRefl {B = λ x → x ∈ xs} m) ∙ e'))
    e m' e'

effectiveDRelator : ∀{ℓ}{X : Type ℓ} {R : X → X → Type ℓ}
  → isPropValued R
  → isEquivRel R
  → ∀ {xs ys}
  → DRelator {X = X / R} _≡_ (mapList [_] xs) (mapList [_] ys)
  → DRelator R xs ys
effectiveDRelator _ _ {xs = []} nil = nil
effectiveDRelator propR eqR {xs = x ∷ xs} (cons p) =
  cons (∥rec∥ squash₁
              (λ { (x , e , m , p')
                → let (x' , m' , e') = pre∈mapList m
                   in ∣ x' ,
                       effective propR eqR _ _ (e ∙ sym e') ,
                       m' ,
                       effectiveDRelator propR eqR
                         (subst (DRelator _≡_ (mapList [_] xs)) (sym (remove-mapList m' ∙ sym (remove-eq m (∈mapList m') (sym e') (∈mapList-lem m)))) p') ∣₁ })
              p)

effectiveRelator : ∀{ℓ}{X : Type ℓ} {R : X → X → Type ℓ}
  → isPropValued R
  → isEquivRel R
  → ∀ {xs ys}
  → Relator {X = X / R} _≡_ (mapList [_] xs) (mapList [_] ys)
  → Relator R xs ys
effectiveRelator propR eqR (p , q) =
  effectiveDRelator propR eqR p , effectiveDRelator propR eqR q

eq/DRelator : ∀{ℓ}{X : Type ℓ} {R : X → X → Type ℓ}
  → ∀ {xs ys}
  → DRelator R xs ys
  → DRelator {X = X / R} _≡_ (mapList [_] xs) (mapList [_] ys)
eq/DRelator nil = nil
eq/DRelator (cons p) =
  cons (∥map∥ (λ { (t , e , m , p')
                     → [ t ] , eq/ _ _ e , ∈mapList m , subst (DRelator _≡_ (mapList [_] _)) (remove-mapList m) (eq/DRelator p')
                })
              p)

eq/Relator : ∀{ℓ}{X : Type ℓ} {R : X → X → Type ℓ}
  → ∀ {xs ys}
  → Relator R xs ys
  → Relator {X = X / R} _≡_ (mapList [_] xs) (mapList [_] ys)
eq/Relator (p , q) = eq/DRelator p , eq/DRelator q

M : Type → Type
M X = List X / Relator _≡_

mapDRelator' : ∀{ℓ}{X Y : Type ℓ}
  → {R : X → X → Type ℓ} {S : Y → Y → Type ℓ}
  → {f : X → Y}
  → (∀ {x x'} → R x x' → S (f x) (f x'))
  → ∀ {xs xs'}
  → DRelator R xs xs'
  → DRelator S (mapList f xs) (mapList f xs')
mapDRelator' fRel nil = nil
mapDRelator' fRel (cons p) =
  cons (∥map∥ (λ { (x , r , m , p')
                     → _ , fRel r , ∈mapList m , subst (DRelator _ _) (remove-mapList m) (mapDRelator' fRel p')
                })
              p)

mapDRelator : {X : Type} {R S : X → X → Type} {xs ys : List X}
  → (∀ {x y} → R x y → S x y) 
  → DRelator R xs ys → DRelator S xs ys
mapDRelator rs p =
  subst2 (DRelator _) (mapListId _) (mapListId _) (mapDRelator' {f = λ x → x} rs p)

mapListRel-fun : ∀{ℓ}{X Y : Type ℓ}
  → {R : Y → Y → Type ℓ} 
  → {f g : X → Y}
  → (∀ x → R (f x) (g x))
  → ∀ xs
  → ListRel R (mapList f xs) (mapList g xs)
mapListRel-fun rfg [] = []
mapListRel-fun rfg (x ∷ xs) = rfg x ∷ mapListRel-fun rfg xs
mapRelator' : ∀{ℓ}{X Y : Type ℓ}
  → {R : X → X → Type ℓ} {S : Y → Y → Type ℓ}
  → {f : X → Y}
  → (∀ {x x'} → R x x' → S (f x) (f x'))
  → ∀ {xs xs'}
  → Relator R xs xs'
  → Relator S (mapList f xs) (mapList f xs')
mapRelator' fRel (p , q) = mapDRelator' fRel p , mapDRelator' fRel q

removeDRelator' : ∀{ℓ}{X : Type ℓ}
  → {R : X → X → Type ℓ}
  → (∀ x → R x x)
  → ∀ {xs} {x : X} (m : x ∈ xs)
  → DRelator R xs (x ∷ remove xs m)
removeDRelator' {R = R} reflR (here eq) = cons ∣ _ , subst (R _) (sym eq) (reflR _) , here refl , reflDRelator reflR _ ∣₁
removeDRelator' reflR (there m) = cons ∣ _ , reflR _ , there (here refl) , removeDRelator' reflR m ∣₁

removeDRelator : ∀{ℓ}{X : Type ℓ}
  → {R : X → X → Type ℓ}
  → (∀ x → R x x)
  → ∀ {xs} {x : X} (m m' : x ∈ xs)
  → DRelator R (remove xs m) (remove xs m')
removeDRelator reflR (here eq) (here _) = reflDRelator reflR _
removeDRelator {R = R} reflR (here {xs = xs} eq) (there m) = J (λ z _ → DRelator R xs (z ∷ remove xs m)) (removeDRelator' reflR m) eq
removeDRelator {R = R} reflR (there m) (here {y = y} eq) = cons ∣ _ , subst (R y) (sym eq) (reflR y) , m , reflDRelator reflR _ ∣₁
removeDRelator reflR (there m) (there m') = cons ∣ _ , reflR _ , here refl , removeDRelator reflR m m' ∣₁


ListRel→DRelator : ∀ {ℓ}{X : Type ℓ} {R : X → X → Type ℓ}
  → {xs ys : List X} → ListRel R xs ys → DRelator R xs ys
ListRel→DRelator [] = nil
ListRel→DRelator (r ∷ p) = cons ∣ _ , r , here refl , ListRel→DRelator p ∣₁

ListRel→Relator : ∀ {ℓ}{X : Type ℓ} {R : X → X → Type ℓ}
  → (∀ {x y} → R x y → R y x)
  → {xs ys : List X} → ListRel R xs ys → Relator R xs ys
ListRel→Relator symR r = (ListRel→DRelator r) , ListRel→DRelator (symListRel symR r)

mapRelator-fun : ∀{ℓ}{X Y : Type ℓ}
  → {R : Y → Y → Type ℓ}
  → (∀{x y} → R x y → R y x)
  → {f g : X → Y}
  → (∀ x → R (f x) (g x))
  → ∀ xs
  → Relator R (mapList f xs) (mapList g xs)
mapRelator-fun symR rfg xs = ListRel→Relator symR (mapListRel-fun rfg xs)

mapM : ∀{X Y} (f : X → Y) → M X → M Y
mapM f = recQ squash/ (λ xs → [ mapList f xs ])
  λ xs ys rs → eq/ _ _ (mapRelator' (cong f) rs)

mapM-id : ∀ {X} (x : M X) → mapM (idfun X) x ≡ x
mapM-id = elimPropQ (λ _ → squash/ _ _) λ xs → cong [_] (mapListId xs)

mapM-comp : ∀ {X Y Z} (g : Y → Z) (f : X → Y) (x : M X) →
      mapM (g ∘ f) x ≡ mapM g (mapM f x)
mapM-comp g f = elimPropQ (λ _ → squash/ _ _) λ xs → cong [_] (sym (mapListComp xs))

isSetM : ∀{X} → isSet (M X)
isSetM = squash/



isEquivRel≡ : ∀{ℓ} {X : Type ℓ} → isEquivRel (_≡_ {A = X})
isEquivRel≡ = equivRel (λ _ → refl) (λ _ _ → sym) (λ _ _ _ → _∙_)

dec∈ : ∀{ℓ}{X : Type ℓ} {R : X → X → Type ℓ} 
  → (∀ x y → Dec (R x y)) → ∀ x ys
  → Dec (Σ[ y ∈ _ ] (y ∈ ys) × R x y)
dec∈ decR x [] = no (λ { () })
dec∈ {R = R} decR x (y ∷ ys) with decR x y
... | yes p = yes (y , here refl , p)
... | no ¬p with dec∈ decR x ys
... | yes (z , m , r) = yes (z , there m , r)
... | no ¬q = no (λ { (._ , here p , r') → ¬p (subst (R x) p r')
                    ; (w , there m' , r') → ¬q (w , m' , r') })

decDRelator : {X : Type} 
  → Discrete X
  → (xs ys : List X) → Dec (DRelator _≡_ xs ys)
decDRelator decEq [] ys = yes nil
decDRelator decEq (x ∷ xs) ys with dec∈ decEq x ys
... | no ¬p = no (λ { (cons p) →
  ∥rec∥ isProp⊥
        (λ { (y , q , m , rs) → ¬p (y , m , q) })
        p })
... | yes (y , m , r) with decDRelator decEq xs (remove ys m)
... | yes p = yes (cons ∣ y , r , m , p ∣₁)
... | no ¬p = no (λ { (cons p) →
  ∥rec∥ isProp⊥
        (λ { (y' , q , m' , rs) → ¬p (transDRelator _∙_ rs
          (J (λ z _ → (m'' : z ∈ ys) → DRelator _≡_ (remove ys m'') (remove ys m))
             (λ m'' → removeDRelator (λ _ → refl) m'' m)
             (sym r ∙ q)
             m')) })
        p })

decRelator : {X : Type} 
  → Discrete X
  → (xs ys : List X) → Dec (Relator _≡_ xs ys)
decRelator decEq xs ys with decDRelator decEq xs ys
... | no ¬d = no (¬d ∘ fst)
... | yes d with decDRelator decEq ys xs
... | no ¬d = no (¬d ∘ snd)
... | yes d' = yes (d , d')

decEqM : ∀ {X} (decEq : Discrete X) → Discrete (M X)
decEqM decEq =
  discreteSetQuotients
    (isEquivRelRelator isEquivRel≡)
    (decRelator decEq)

