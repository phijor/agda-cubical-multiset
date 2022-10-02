{-# OPTIONS --sized-types #-}

module Multiset.Coinductive.Trees where

open import Multiset.Coinductive.Size

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

-- non-wellfounded trees with finite ordered branching
record Tree (i : Size) : Type where
  constructor thunk
  coinductive
  field
    subtrees : {j : Size< i} → List (Tree j)
open Tree public

subtrees-1 : List (Tree ∞) → Tree ∞
subtrees-1 xs = thunk xs

-- tree bisimilarity
record Bisim (i : Size) (xs ys : Tree i) : Type where
  constructor thunkEq
  coinductive
  field
    subtreesB : {j : Size< i}
      → ListRel (Bisim j) (subtrees xs) (subtrees ys)
open Bisim public

reflBisim : ∀ {i} (xs : Tree i) → Bisim i xs xs
subtreesB (reflBisim xs) = reflListRel reflBisim (subtrees xs)

-- coinduction principle: tree bisimilarity implies path equality
bisim : (i : Size) {t₁ t₂ : Tree i} → Bisim i t₁ t₂ → t₁ ≡ t₂
bisimL : (i : Size) {t₁ t₂ : List (Tree i)}
  → ListRel (Bisim i) t₁ t₂ → t₁ ≡ t₂
  
subtrees (bisim s b i) {s'} = bisimL s' (subtreesB b) i 

bisimL s [] i = []
bisimL s (b ∷ bs) i = bisim s b i ∷ bisimL s bs i

-- existence of anamorphism
anaTree : {X : Type} (c : X → List X) → (i : Size) → X → Tree i
subtrees (anaTree c s x) {s'} = mapList (anaTree c s') (c x)

-- the anamorphism is a coalgebra morphism (the corresponding square
-- commutes on the nose)
anaTreeEq : {X : Type} (c : X → List X) (x : X)
  → subtrees (anaTree c ∞ x) ≡ mapList (anaTree c ∞) (c x)
anaTreeEq c x = refl

-- the anamorphism is unique
anaTreeUniqB : {X : Type} (c : X → List X)
  → (f : (s : Size) → X → Tree s)
  → (eq : ∀ (s : Size) (s' : Size< s) x
    → subtrees (f s x) {s'} ≡ mapList (f s') (c x))
  → ∀ (s : Size) x → Bisim s (f s x) (anaTree c s x)
anaTreeUniqB' : {X : Type} (c : X → List X)
  → (f : (s : Size) → X → Tree s)
  → (eq : ∀ (s : Size) (s' : Size< s) x
    → subtrees (f s x) {s'} ≡ mapList (f s') (c x))
  → (s : Size)
  → ∀ xs → ListRel (Bisim s) (mapList (f s) xs) (mapList (anaTree c s) xs)

subtreesB (anaTreeUniqB c f eq s x) {s'} =
  subst (λ z → ListRel (Bisim s') z (mapList (anaTree c s') (c x)))
        (sym (eq s s' x))
        (anaTreeUniqB' c f eq s' (c x))

anaTreeUniqB' c f eq s [] = []
anaTreeUniqB' c f eq s (x ∷ xs) =
  anaTreeUniqB c f eq s x ∷ anaTreeUniqB' c f eq s xs

anaTreeUniq : {X : Type} (c : X → List X)
  → (f : X → Tree ∞)
  → (eq : ∀ (s : Size) x → subtrees (f x) {s} ≡ mapList f (c x))
  → f ≡ anaTree c ∞
anaTreeUniq c f eq =
  funExt (λ x →
    bisim ∞ (anaTreeUniqB c (λ _ → f) (λ {_ _ → eq _}) ∞ x))

{- ================================================================ -}

-- coinductive closure of the relator, which gives a notion of
-- extensional equality of trees
record ExtEq (i : Size) (t₁ t₂ : Tree ∞) : Type where
  coinductive
  field
    subtreesE : {j : Size< i} → Relator (ExtEq j) (subtrees t₁) (subtrees t₂)
open ExtEq public

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

subtreesE-1 : ∀ {ts ts'} → Relator (ExtEq ∞) ts ts' → ExtEq ∞ (subtrees-1 ts) (subtrees-1 ts')
subtreesE (subtreesE-1 r) = (mapDRelator (λ x → x) (r .fst)) , mapDRelator (λ x → x) (r .snd)

isPropExtEq : ∀ t₁ t₂ → isProp (ExtEq ∞ t₁ t₂)
subtreesE (isPropExtEq t₁ t₂ p q i) =
  isPropRelator (ExtEq _) (subtrees t₁) (subtrees t₂)
                (subtreesE p) (subtreesE q) i

-- reflexivity, symmetry and transitivity of ExtEqS
reflExtEq : ∀ j t → ExtEq j t t
subtreesE (reflExtEq j t) {k} =
  reflRelator (reflExtEq k) (subtrees t)

symExtEq : ∀{t t'} (j : Size) → ExtEq j t t' → ExtEq j t' t
subtreesE (symExtEq j p) = subtreesE p .snd , subtreesE p .fst

transExtEq : ∀{t t₁ t₂}(j : Size)
  → ExtEq j t t₁ → ExtEq j t₁ t₂ → ExtEq j t t₂
subtreesE (transExtEq j p q) {k} =
  transRelator (transExtEq k) (subtreesE p) (subtreesE q)

isEquivRelExtEq : isEquivRel (ExtEq ∞)
isEquivRelExtEq =
  equivRel (reflExtEq ∞)
           (λ _ _ → symExtEq ∞)
           (λ _ _ _ → transExtEq ∞)
           
-- the final coalgebra of the bag functor as quotient of trees
νM : Type
νM = Tree ∞ / ExtEq ∞



toListRel : {X : Type} {R : X → X → Type}
  → (∀ x → R x x)
  → List (X / R) → List X / ListRel R
toListRel _ [] = [ [] ]
toListRel reflR (y ∷ ys) =
  recQ2 squash/
        (λ x xs → [ x ∷  xs ])
        (λ x x' xs r → eq/ _ _ (r ∷ reflListRel reflR xs))
        (λ x xs xs' rs → eq/ _ _ (reflR x ∷ rs))
        y
        (toListRel reflR ys)

fromListRel : {X : Type} {R : X → X → Type}
  → List X / ListRel R → List (X / R)
fromListRel = recQ (isOfHLevelList 0 squash/) (mapList [_]) (λ _ _ → ListRel-mapList)

fromListRel-toListRel : {X : Type} {R : X → X → Type}
  → (reflR : ∀ x → R x x)
  → ∀ xs → fromListRel {R = R} (toListRel reflR xs) ≡ xs
fromListRel-toListRel reflR [] = refl
fromListRel-toListRel reflR (y ∷ ys) =
   elimPropQ2 {P = λ y ys → fromListRel (recQ2 squash/
                                                (λ x xs → [ x ∷ xs ])
                                                (λ x x' xs r → eq/ (x ∷ xs) (x' ∷ xs) (r ∷ reflListRel reflR xs))
                                                (λ x xs xs' rs → eq/ (x ∷ xs) (x ∷ xs') (reflR x ∷ rs))
                                                y ys)
                              ≡ y ∷ fromListRel ys}
              (λ _ _ → isOfHLevelList 0 squash/ _ _)
              (λ _ _ → refl)
              y (toListRel reflR ys)
   ∙ cong (y ∷_) (fromListRel-toListRel reflR ys)

toListRel-mapList : {X : Type} {R : X → X → Type}
  → (reflR : ∀ x → R x x)
  → (xs : List X) → toListRel {R = R} reflR (mapList [_] xs) ≡ [ xs ]
toListRel-mapList reflR [] = refl
toListRel-mapList reflR (x ∷ xs) =
  cong (recQ2 squash/
              (λ x₁ xs₁ → [ x₁ ∷ xs₁ ])
              (λ x₁ x' xs₁ r → eq/ (x₁ ∷ xs₁) (x' ∷ xs₁) (r ∷ reflListRel reflR xs₁))
              (λ x₁ xs₁ xs' rs → eq/ (x₁ ∷ xs₁) (x₁ ∷ xs') (reflR x₁ ∷ rs))
              [ x ])
       (toListRel-mapList reflR xs)

recQList : {X Y : Type} 
  → {R : X → X → Type}
  → isSet Y
  → (∀ x → R x x)
  → (f : List X → Y)
  → (∀ xs ys → ListRel R xs ys → f xs ≡ f ys)
  → List (X / R) → Y
recQList setY reflR f p xs = recQ setY f p (toListRel reflR xs)

recQListEq : {X Y : Type} 
  → {R : X → X → Type}
  → (setY : isSet Y)
  → (reflR : ∀ x → R x x)
  → (f : List X → Y)
  → (p : ∀ xs ys → ListRel R xs ys → f xs ≡ f ys)
  → (xs : List X) → recQList setY reflR f p (mapList [_] xs) ≡ f xs
recQListEq setY reflR f p xs = cong (recQ setY f p) (toListRel-mapList reflR xs)

elimQListProp : {X : Type}
  → {R : X → X → Type}
  → (Y : List (X / R) → Type)
  → (∀ xs → isProp (Y xs))
  → (∀ x → R x x)
  → (f : (xs : List X) → Y (mapList [_] xs))
  → (xs : List (X / R)) → Y xs
elimQListProp Y propY reflR f xs = 
  subst Y (fromListRel-toListRel reflR xs) (goal xs)
  where
    goal : (xs : List _) → Y (fromListRel (toListRel reflR xs))
    goal xs = elimPropQ {P = λ xs → Y (fromListRel xs)}
                        (λ _ → propY _)
                        f
                        (toListRel reflR xs) 

elimQListProp2 : {X : Type}
  → {R : X → X → Type}
  → (Y : List (X / R) → List (X / R) → Type)
  → (∀ xs ys → isProp (Y xs ys))
  → (∀ x → R x x)
  → (f : (xs ys : List X) → Y (mapList [_] xs) (mapList [_] ys))
  → (xs ys : List (X / R)) → Y xs ys
elimQListProp2 {R = R} Y propY reflR f xs ys =
  subst2 Y (fromListRel-toListRel reflR xs) (fromListRel-toListRel reflR ys) (goal xs ys)
  where
    goal : (xs ys : List _) → Y (fromListRel (toListRel reflR xs)) (fromListRel (toListRel reflR ys))
    goal xs ys = elimPropQ2 {P = λ xs ys → Y (fromListRel xs) (fromListRel ys)}
                            (λ _ _ → propY _ _)
                            f
                            (toListRel reflR xs) (toListRel reflR ys)

-- Tree/ExtEq -> List (Tree/ExtEq) / Relator _≡_
νM→MνM : νM → M νM
νM→MνM = recQ squash/ f f-rel
  where
    f : Tree ∞ → M νM
    f t = [ (mapList [_] (subtrees t)) ]

    f-rel : ∀ t t' → ExtEq ∞ t t' → f t ≡ f t'
    f-rel _ _ p = eq/ _ _ (eq/DRelator (subtreesE p .fst) , eq/DRelator (subtreesE p .snd))

MνM→νM : M νM → νM
MνM→νM = recQ squash/ f f-rel
  where
    g : List (Tree ∞) → νM
    g ts =  [ subtrees-1 ts ]

    g-rel : ∀ ts ts' → ListRel (ExtEq ∞) ts ts' → g ts ≡ g ts'
    g-rel _ _ rs = eq/ _ _ (subtreesE-1 (ListRel→Relator (symExtEq _) rs))

    f : List νM → νM
    f = recQList squash/ (reflExtEq _) g g-rel

    f-rel : ∀ ts ts' → Relator _≡_ ts ts' → f ts ≡ f ts'
    f-rel =
      elimQListProp2 _
                     (λ _ _ → isPropΠ (λ _ → squash/ _ _))
                     (reflExtEq _)
                     (λ xs ys rs →
                         recQListEq squash/ (reflExtEq _) _ _ xs
                         ∙ eq/ _ _ (subtreesE-1 (effectiveRelator isPropExtEq isEquivRelExtEq rs))
                         ∙ sym (recQListEq squash/ (reflExtEq _) _ _ ys))


inj-νM→MνM' : ∀{t t'}
  → Relator {X = νM} _≡_ (mapList [_] (subtrees t)) (mapList [_] (subtrees t'))
  → ExtEq ∞ t t'
subtreesE (inj-νM→MνM' p) = lem (p .fst) , lem (p .snd) 
  where
    lem : ∀ {ts ts'}
      → DRelator {X = νM} _≡_ (mapList [_] ts) (mapList [_] ts')
      → DRelator (ExtEq ∞) ts ts'
    lem = effectiveDRelator isPropExtEq isEquivRelExtEq
  
inj-νM→MνM : ∀ t t' → νM→MνM t ≡ νM→MνM t' → t ≡ t'
inj-νM→MνM =
  elimPropQ2 (λ _ _ → isPropΠ (λ _ → squash/ _ _))
             (λ _ _ r →
               eq/ _ _ (inj-νM→MνM' (effective (isPropRelator _≡_)
                                                (isEquivRelRelator (equivRel (λ _ → refl) (λ _ _ → sym) (λ _ _ _ → _∙_)))
                                                _ _ r)))


νM→MνM→νM : ∀ t → νM→MνM (MνM→νM t) ≡ t
νM→MνM→νM =
  elimPropQ (λ _ → squash/ _ _)
            (elimQListProp (λ a → νM→MνM (MνM→νM [ a ]) ≡ [ a ])
                           (λ _ → squash/ _ _)
                           (reflExtEq _)
                           (λ ts → cong (λ x → recQ squash/
                                                      (λ t → [ mapList [_] (subtrees t) ])
                                                      (λ t t' p → eq/ _ _ (eq/Relator (subtreesE p)))
                                                      (recQ squash/
                                                            (λ xs → [ subtrees-1 xs ])
                                                            (λ xs ys rs →
                                                               eq/ _ _
                                                                   (subtreesE-1 (ListRel→Relator (symExtEq _) rs))) x))
                                          (toListRel-mapList (reflExtEq ∞) ts))) 

MνM→νM→MνM : ∀ t → MνM→νM (νM→MνM t) ≡ t
MνM→νM→MνM t = inj-νM→MνM _ _ (νM→MνM→νM _)


-- pointwise lifting of a relation to a function space
PW : {X A B : Type} (R : A → B → Type) → (X → A) → (X → B) → Type
PW R f g = ∀ x → R (f x) (g x)

-- the quotient a function space by the pointwise lifted relation
[_⇒_]/_ : (A B : Type) (R : B → B → Type) → Type
[ A ⇒ B ]/ R = (A → B) / PW R

-- a function sending equivalence classes of function wrt. pointwise
-- lifted relation and functions into equivalence classes
θ : ∀ A {B} (R : B → B → Type) → [ A ⇒ B ]/ R → A → B / R
θ A R = recQ (isSetΠ (λ _ → squash/)) (λ c x → [ c x ])
  λ c c' r → funExt (λ x → eq/ _ _ (r x))


-- two quotients of function spaces
[_⇒M_] : (A B : Type) → Type
[ A ⇒M B ] = [ A ⇒ (List B) ]/ Relator _≡_

[_⇒νM] : (A : Type) → Type
[ A ⇒νM] = [ A ⇒ Tree ∞ ]/ ExtEq ∞

-- towards the construction of the anamorphism: there exists a map
-- from X to νM, provided that X comes with a "coalgebra"
-- c : [ X ⇒M X ]

anaTreeRelCoalg : ∀{X}(c c' : X → List X)
  → (∀ x → Relator _≡_ (c x) (c' x)) → (j : Size) (x : X)
  → ExtEq j (anaTree c ∞ x) (anaTree c' ∞ x)
anaTreeRelCoalg' : ∀{X}(c c' : X → List X)
  → (∀ x → Relator _≡_ (c x) (c' x)) → (j : Size)
  → ∀ {xs xs'} → DRelator _≡_ xs xs'
  → DRelator (ExtEq j) (mapList (anaTree c ∞) xs)
                        (mapList (anaTree c' ∞) xs')

subtreesE (anaTreeRelCoalg c c' rc j x) {k} =
  anaTreeRelCoalg' c c' rc k (rc x .fst) ,
  anaTreeRelCoalg' c' c (λ z → symRelator (rc z)) k (rc x .snd)

anaTreeRelCoalg' c c' cr j nil = nil
anaTreeRelCoalg' c c' cr j {xs' = xs'} (cons {x = x} {xs = xs} p) =
 ∥rec∥ (isPropDRelator _ _ _)
       (λ { (y , eq , m , p') →
         J (λ y eq → (m : y ∈ xs') → DRelator _≡_ xs (remove xs' m) → DRelator (ExtEq j) (anaTree c ∞ x ∷ mapList (anaTree c ∞) xs) (mapList (anaTree c' ∞) xs'))
           (λ m p' → cons ∣ _ , anaTreeRelCoalg c c' cr j x , ∈mapList m , subst (DRelator (ExtEq j) (mapList (anaTree c ∞) _)) (remove-mapList m) (anaTreeRelCoalg' c c' cr j p') ∣₁)
           eq m p' })
       p

anaM' : {X : Type} (c : [ X ⇒M X ])
  → X → νM
anaM' =
  recQ (isSetΠ (λ _ → squash/))
       (λ c x → [ anaTree c ∞ x ])
       (λ c c' rc → funExt (λ x → eq/ _ _ (anaTreeRelCoalg c c' rc ∞ x)))

-- the construction of the anamorphism;
-- for this to work, we assume that θ has a section, i.e. it is a
-- split epimorphism; this is equivalent to full axiom of choice (the
-- equivalence is proved in the end of the file AxiomChoice.agda)

module _ (θInv : ∀ A {B} (R : B → B → Type) → (A → B / R) → [ A ⇒ B ]/ R)
         (sectionθ : ∀ A {B} (R : B → B → Type) → section (θ A R) (θInv A R)) where

  θ1 : ∀{X} → [ X ⇒M X ] → X → M X
  θ1 = θ _ _

  θ1Inv : ∀ {X} → (X → M X) → [ X ⇒M X ]
  θ1Inv = θInv _ _

  sectionθ1 : ∀{X} (f : X → M X) → θ1 (θ1Inv f) ≡ f
  sectionθ1 = sectionθ _ _

  θ2 : ∀{X} → [ X ⇒νM] → X → νM
  θ2 = θ _ _

  θ2-ns : ∀{X} → [ X ⇒νM] → X → νM
  θ2-ns = θ _ _

  θ2Inv : ∀ {X} → (X → νM) → [ X ⇒νM]
  θ2Inv = θInv _ _ 

  θ2Inv-ns : ∀ {X} → (X → νM) → [ X ⇒νM]
  θ2Inv-ns = θInv _ _ 

  sectionθ2 : ∀{X} (f : X → νM) → θ2 (θ2Inv f) ≡ f
  sectionθ2 = sectionθ _ _

  sectionθ2-ns : ∀{X} (f : X → νM) → θ2-ns (θ2Inv-ns f) ≡ f
  sectionθ2-ns = sectionθ _ _

  anaM : {X : Type} (c : X → M X)
    → X → νM
  anaM c = anaM' (θ1Inv c)


-- the anamorphism is a coalgebra morphism
  anaMEq' : {X : Type} (c : [ X ⇒M X ])
    → ∀ x → νM→MνM (anaM' c x) ≡ mapM (anaM' c) (θ1 c x)
  anaMEq' = elimPropQ (λ _ → isPropΠ (λ _ → squash/ _ _)) 
     (λ c x → cong [_] (mapListComp (c x)))

  anaMEq : {X : Type} (c : X → M X)
    → ∀ x → νM→MνM (anaM c x) ≡ mapM (anaM c) (c x)
  anaMEq c x =
    anaMEq' (θ1Inv c) x ∙ cong (λ f → mapM (anaM c) (f x)) (sectionθ1 c)

  anaTreeRel : ∀ {X} {R : X → X → Type}
    → (c : X → List X) (cRel : ∀ {x y} → R x y → Relator R (c x) (c y))
    → (j : Size)
    → ∀ {x y} → R x y
    → ExtEq j (anaTree c ∞ x) (anaTree c ∞ y)
  subtreesE (anaTreeRel c cRel j r) {k} = mapRelator' (anaTreeRel c cRel k) (cRel r)


  anaMUniq''' : {X : Type} (Xset : isSet X) (c : X → List X)
    → (f : X → Tree ∞) 
    → (feq : ∀ x → Relator (ExtEq ∞) (subtrees (f x)) (mapList f (c x)))
    → ∀ s x → ExtEq s (f x) (anaTree c ∞ x)
  subtreesE (anaMUniq''' Xset c f feq s x) {s'} =
    transDRelator (transExtEq s') (feq x .fst) (mapRelator-fun (symExtEq s') (anaMUniq''' Xset c f feq s') (c x) .fst) ,
    transDRelator (transExtEq s') (mapRelator-fun (symExtEq s') (anaMUniq''' Xset c f feq s') (c x) .snd) (feq x .snd)

  anaMUniq'' : {X : Type} (Xset : isSet X) (c : X → List X)
    → (f : [ X ⇒νM]) (feq : ∀ x → νM→MνM (θ2 f x) ≡ mapM (θ2 f) [ c x ])
    → ∀ x → θ2 f x ≡ anaM' [ c ] x
  anaMUniq'' Xset c =
    elimPropQ
      (λ _ → isPropΠ (λ _ → isPropΠ (λ _ → squash/ _ _)))
      (λ f feq x → eq/ _ _
        (anaMUniq''' Xset c f
                     (λ y → effectiveRelator isPropExtEq isEquivRelExtEq
                       (subst (Relator _≡_ (mapList [_] (subtrees (f y))))
                              (sym (mapListComp (c y)))
                              (effective (isPropRelator _) (isEquivRelRelator (equivRel (λ _ → refl) (λ _ _ → sym) (λ _ _ _ → _∙_))) _ _ (feq y))))
                     _ x))
          
  anaMUniq' : {X : Type} (Xset : isSet X) (c : [ X ⇒M X ])
    → (f : X → νM) (feq : ∀ x → νM→MνM (f x) ≡ mapM f (θ1 c x))
    → ∀ x → f x ≡ anaM' c x
  anaMUniq' Xset =
    elimPropQ
      (λ _ → isPropΠ (λ _ → isPropΠ (λ _ → isPropΠ (λ _ → squash/ _ _))))
      (λ c f feq x →
         (λ i → sym (sectionθ2 f) i x)
         ∙ anaMUniq'' Xset c (θ2Inv f)
                          (λ y → (λ i → νM→MνM (sectionθ2 f i y) )
                                  ∙ feq y
                                  ∙ cong (λ g → [ mapList g (c y) ]) (sym (sectionθ2 f)))
                          x)

  anaMUniq : {X : Type} (Xset : isSet X) (c : X → M X)
    → (f : X → νM) (feq : ∀ x → νM→MνM (f x) ≡ mapM f (c x))
    → f ≡ anaM c
  anaMUniq Xset c f feq = funExt λ x → 
    anaMUniq' Xset (θ1Inv c) f
      (λ y → feq y ∙ λ i → mapM f (sectionθ1 c (~ i) y))
      x
