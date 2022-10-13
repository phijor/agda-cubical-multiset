{-# OPTIONS --sized-types #-}

module Multiset.Coinductive.Trees where

open import Multiset.Coinductive.Size

open import Cubical.Core.Everything
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Everything
open import Cubical.Foundations.Isomorphism
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

open import Multiset.ListQuotient.Base

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

M-νM-FixpointIso : Iso (M νM) νM
M-νM-FixpointIso .Iso.fun = MνM→νM
M-νM-FixpointIso .Iso.inv = νM→MνM
M-νM-FixpointIso .Iso.rightInv = MνM→νM→MνM
M-νM-FixpointIso .Iso.leftInv = νM→MνM→νM

M-νM-FixpointEquiv : M νM ≃ νM
M-νM-FixpointEquiv = isoToEquiv M-νM-FixpointIso

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

anaTreeRel : ∀ {X} {R : X → X → Type}
  → (c : X → List X) (cRel : ∀ {x y} → R x y → Relator R (c x) (c y))
  → (j : Size)
  → ∀ {x y} → R x y
  → ExtEq j (anaTree c ∞ x) (anaTree c ∞ y)
subtreesE (anaTreeRel c cRel j r) {k} = mapRelator' (anaTreeRel c cRel k) (cRel r)

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
