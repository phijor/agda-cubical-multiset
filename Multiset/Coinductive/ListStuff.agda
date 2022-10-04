
module Multiset.Coinductive.ListStuff where

open import Cubical.Core.Everything
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Everything
open import Cubical.Data.List hiding ([_]) renaming (map to mapList)
open import Cubical.Data.Sigma
open import Cubical.Data.Nat
open import Cubical.Data.Fin
  hiding (_/_)
open import Cubical.HITs.PropositionalTruncation as PropTrunc
  renaming (rec to ∥rec∥; map to ∥map∥)
open import Cubical.HITs.SetQuotients
  renaming (rec to recQ; rec2 to recQ2; elimProp2 to elimPropQ2; elimProp to elimPropQ)
open import Cubical.Relation.Binary
open BinaryRelation
open isEquivRel

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
  here : ∀{xs} → x ∈ (x ∷ xs)
  there : ∀{y xs} → x ∈ xs → x ∈ (y ∷ xs)

-- removing an element from a list
remove : ∀{ℓ}{A : Type ℓ} {x : A} xs → x ∈ xs → List A
remove (x ∷ xs) here = xs
remove (y ∷ xs) (there m) = y ∷ remove xs m

-- interaction between ∈ and remove
remove∈ : ∀{ℓ}{A : Type ℓ} {x y : A} {xs} (m : x ∈ xs)
  → y ∈ remove xs m → y ∈ xs
remove∈ here m' = there m'
remove∈ (there m) here = here
remove∈ (there m) (there m') = there (remove∈ m m')

removeremove∈ : ∀{ℓ}{A : Type ℓ} {x y : A} {xs}
  → (m : x ∈ xs) (m' : y ∈ remove xs m)
  → x ∈ remove xs (remove∈ m m')
removeremove∈ here m' = here
removeremove∈ (there m) here = m
removeremove∈ (there m) (there m') = there (removeremove∈ m m')

remove-par : ∀{ℓ}{A : Type ℓ} {x y : A} {xs}
  → (m : x ∈ xs) (m' : y ∈ remove xs m)
  → remove (remove xs m) m' ≡ remove (remove xs (remove∈ m m')) (removeremove∈ m m')
remove-par here m' = refl
remove-par (there m) here = refl
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
reflDRelator reflR (x ∷ xs) = cons ∣ x , reflR x , here , reflDRelator reflR xs ∣₁

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
memDRelator here (cons p) = ∥map∥ (λ r → r) p
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

pre∈mapList : ∀{ℓ} {A B : Type ℓ} {f : A → B} {b : B} {xs : List A}
  → b ∈ mapList f xs → Σ[ a ∈ A ] (a ∈ xs) × (f a ≡ b)
pre∈mapList {xs = x ∷ xs} here = _ , here , refl
pre∈mapList {xs = x ∷ xs} (there mb) =
  pre∈mapList mb .fst , there (pre∈mapList mb .snd .fst) , pre∈mapList mb .snd .snd


∈mapList : ∀{ℓ}{A B : Type ℓ} {f : A → B} {a : A} {xs : List A}
  → a ∈ xs → f a ∈ mapList f xs
∈mapList here = here
∈mapList (there m) = there (∈mapList m)

remove-mapList : ∀{ℓ} {A B : Type ℓ} {f : A → B} {a : A} {xs : List A}
  → (m : a ∈ xs) → mapList f (remove xs m) ≡ remove (mapList f xs) (∈mapList m)
remove-mapList here = refl
remove-mapList (there m) = cong (_ ∷_) (remove-mapList m)

∈mapList-lem' : ∀{ℓ} {A B : Type ℓ} {f : A → B} {b : B} {xs : List A}
  → (m : b ∈ mapList f xs)
  → PathP (λ i → pre∈mapList m .snd .snd (~ i) ∈ mapList f xs) m (∈mapList (pre∈mapList m .snd .fst))
∈mapList-lem' {xs = x ∷ xs} here = refl
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

ListRel→DRelator : ∀ {ℓ}{X : Type ℓ} {R : X → X → Type ℓ}
  → {xs ys : List X} → ListRel R xs ys → DRelator R xs ys
ListRel→DRelator [] = nil
ListRel→DRelator (r ∷ p) = cons ∣ _ , r , here , ListRel→DRelator p ∣₁

ListRel→Relator : ∀ {ℓ}{X : Type ℓ} {R : X → X → Type ℓ}
  → (∀ {x y} → R x y → R y x)
  → {xs ys : List X} → ListRel R xs ys → Relator R xs ys
ListRel→Relator symR r = (ListRel→DRelator r) , ListRel→DRelator (symListRel symR r)

