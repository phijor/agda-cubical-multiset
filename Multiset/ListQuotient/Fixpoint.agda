{-# OPTIONS --safe #-}

module Multiset.ListQuotient.Fixpoint where

open import Multiset.Prelude
open import Multiset.ListQuotient.Finality
  using
    ( fix⁺-preserves-≈
    ; unfold-unique
    )
open import Multiset.ListQuotient.ListFinality
  using
    ( FunctorΣVec
    ; !^
    ; cut
    ; Tree
    ; fix ; fix⁺ ; fix⁻
    ; step
    ; unfold
    ; isSetTree
    ; isCoalgebraMorphismUnfold
    )
open import Multiset.ListQuotient.Bisimilarity as Bisimilarity
  using
    ( Bisim ; _≈_ ; bisim
    ; isTransApprox
    ; isReflBisim
    ; isTransBisim
    ; isEquivRelBisim
    ; isPropBisim
    ; Approx
    )
open import Multiset.Relation.Base using (PathRelation)
open import Multiset.Util.Relation using (ReflectsRel ; PreservesRel ; isSymTot ; isEquivRelPath)
open import Multiset.Util.Vec as Vec using ()
open import Multiset.Util.BundledVec as BVec
  using
    ( ΣVec
    ; []
    ; _#∷_
    ; Relator∞
    ; Relator
    ; rnil∞ ; rcons∞
    ; isReflRelator
    ; isSymRelator
    ; isTransRelator
    ; isEquivRelRelator
    ; isPropRelator
    ; Relator-map
    )
open import Multiset.Limit.Chain
  using
    ( lim
    ; Limit
    )
open import Multiset.Limit.TerminalChain as TerminalChain
  using
    ( Functor
    ; _^_
    )
open import Multiset.Categories.Coalgebra

open import Cubical.Foundations.Equiv using (_≃_ ; secEq ; retEq)
open import Cubical.Foundations.Function using (_∘_)
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism using (Iso ; isoToEquiv)
open import Cubical.Data.Nat as Nat using (ℕ ; suc ; zero)
open import Cubical.Data.Unit.Base using (tt*)
open import Cubical.Data.Vec using (_∷_)
open import Cubical.HITs.PropositionalTruncation as PT using (∥_∥₁)
open import Cubical.HITs.SetQuotients as SQ
  using ()
  renaming
    ( _/_ to _/₂_
    )
open import Cubical.Relation.Binary.Base using (module BinaryRelation)

import Cubical.Categories.Functor as Cat
open import Cubical.Categories.Instances.Sets


open BVec.ΣVec
open Limit using (elements ; is-lim)
open Iso
open Functor ⦃...⦄

FMSet : ∀ {ℓ} → Type ℓ → Type ℓ
FMSet X = ΣVec X /₂ (Relator _≡_)

mapFMSet : {X Y : Type} 
  → (X → Y) → FMSet X → FMSet Y
mapFMSet f =
  SQ.rec SQ.squash/
         (λ x → SQ.[ map f x ])
         λ x y r → SQ.eq/ _ _ (Relator-map _≡_ _ (cong f) r)  

isSetFMSet : ∀ {ℓ} {X : Type ℓ} → isSet (FMSet X)
isSetFMSet = SQ.squash/

-- Unordered trees are a fixpoint of FMSet
UnorderedTree : Type _
UnorderedTree = Tree /₂ Bisim

module _ {A : Type} (R : A → A → Type) where

  data ΣVecRel : ΣVec A → ΣVec A → Type where
    rnil∞ : ΣVecRel [] []
    rcons∞ : {a b : A} {as bs : ΣVec A}
      → R a b
      → ΣVecRel as bs
      → ΣVecRel (a #∷ as) (b #∷ bs)

  isReflΣVecRel : (∀ x → R x x) → ∀ xs → ΣVecRel xs xs
  isReflΣVecRel reflR [] = rnil∞
  isReflΣVecRel reflR (BVec.# (x ∷ xs)) = rcons∞ (reflR x) (isReflΣVecRel reflR (BVec.# xs))

  ΣVecRel→Relator∞ : ∀{xs ys} → ΣVecRel xs ys → Relator∞ R xs ys
  ΣVecRel→Relator∞ rnil∞ = rnil∞
  ΣVecRel→Relator∞ (rcons∞ r rs) = rcons∞ _ r Vec.here (ΣVecRel→Relator∞ rs)

  ΣVecRel→Relator : ∀{xs ys} → ΣVecRel xs ys → Relator R xs ys
  ΣVecRel→Relator rs = PT.∣ ΣVecRel→Relator∞ rs ∣₁

  ΣVecRel-eq/ : ∀{xs ys} → ΣVecRel xs ys → Path (ΣVec (A /₂ R)) (map SQ.[_] xs) (map SQ.[_] ys)
  ΣVecRel-eq/ rnil∞ = refl
  ΣVecRel-eq/ (rcons∞ r rs) i = SQ.eq/ _ _ r i #∷ ΣVecRel-eq/ rs i

toΣVecRel : {X : Type} {R : X → X → Type}
  → (∀ x → R x x)
  → ΣVec (X /₂ R) → ΣVec X /₂ ΣVecRel R
toΣVecRel reflR [] = SQ.[ [] ]
toΣVecRel reflR (BVec.# (x ∷ xs)) =
  SQ.rec2 SQ.squash/
          (λ y ys → SQ.[ y #∷ ys ])
          (λ y y' ys r → SQ.eq/ _ _ (rcons∞ r (isReflΣVecRel _ reflR _)))
          (λ y ys ys' rs → SQ.eq/ _ _ (rcons∞ (reflR y) rs))
          x
          (toΣVecRel reflR (BVec.# xs))

fromΣVecRel : {X : Type} {R : X → X → Type}
  → ΣVec X /₂ ΣVecRel R → ΣVec (X /₂ R)
fromΣVecRel =
  SQ.rec (BVec.isSetΣVec SQ.squash/)
         (map SQ.[_])
         (λ _ _ → ΣVecRel-eq/ _)

toΣVecRelPath : {X : Type} {R : X → X → Type}
  → (reflR : ∀ x → R x x)
  → (xs : ΣVec X) → toΣVecRel {R = R} reflR (map SQ.[_] xs) ≡ SQ.[ xs ]
toΣVecRelPath reflR [] = refl
toΣVecRelPath reflR (BVec.# (x ∷ xs)) =
  cong (SQ.rec2 SQ.squash/
              (λ y ys → SQ.[ y #∷ ys ])
              (λ y y' ys r → SQ.eq/ (y #∷ ys) (y' #∷ ys) (rcons∞ r (isReflΣVecRel _ reflR ys)))
              (λ y ys ys' rs → SQ.eq/ (y #∷ ys) (y #∷ ys') (rcons∞ (reflR y) rs))
              SQ.[ x ])
       (toΣVecRelPath reflR (BVec.# xs))

fromΣVecRel-toΣVecRel : {X : Type} {R : X → X → Type}
  → (reflR : ∀ x → R x x)
  → ∀ xs → fromΣVecRel {R = R} (toΣVecRel reflR xs) ≡ xs
fromΣVecRel-toΣVecRel reflR [] = refl
fromΣVecRel-toΣVecRel reflR (BVec.# (x ∷ xs)) =
   SQ.elimProp2 {P = λ y ys → fromΣVecRel (SQ.rec2 SQ.squash/
                                                (λ x xs → SQ.[ x #∷ xs ])
                                                (λ x x' xs r → SQ.eq/ (x #∷ xs) (x' #∷ xs) (rcons∞ r (isReflΣVecRel _ reflR xs)))
                                                (λ x xs xs' rs → SQ.eq/ (x #∷ xs) (x #∷ xs') (rcons∞ (reflR x) rs))
                                                y ys)
                              ≡ y #∷ fromΣVecRel ys}
              (λ _ _ → BVec.isSetΣVec SQ.squash/ _ _)
              (λ _ _ → refl)
              x (toΣVecRel reflR (BVec.# xs))
   ∙ cong (x #∷_) (fromΣVecRel-toΣVecRel reflR (BVec.# xs))


recΣVec : {X Y : Type}
  → {R : X → X → Type}
  → isSet Y
  → (∀ x → R x x)
  → (f : ΣVec X → Y)
  → (∀ xs ys → ΣVecRel R xs ys → f xs ≡ f ys)
  → ΣVec (X /₂ R) → Y
recΣVec setY reflR f p xs = SQ.rec setY f p (toΣVecRel reflR xs)

recΣVecPath : {X Y : Type}
  → {R : X → X → Type}
  → (setY : isSet Y)
  → (reflR : ∀ x → R x x)
  → (f : ΣVec X → Y)
  → (p : ∀ xs ys → ΣVecRel R xs ys → f xs ≡ f ys)
  → (xs : ΣVec X) → recΣVec setY reflR f p (map SQ.[_] xs) ≡ f xs
recΣVecPath setY reflR f p xs = cong (SQ.rec setY f p) (toΣVecRelPath reflR xs)

elimΣVecProp : {X : Type}
  → {R : X → X → Type}
  → (Y : ΣVec (X /₂ R) → Type)
  → (∀ xs → isProp (Y xs))
  → (∀ x → R x x)
  → (f : (xs : ΣVec X) → Y (map SQ.[_] xs))
  → (xs : ΣVec (X /₂ R)) → Y xs
elimΣVecProp Y propY reflR f xs =
  subst Y (fromΣVecRel-toΣVecRel reflR xs) (goal xs)
  where
    goal : (xs : ΣVec _) → Y (fromΣVecRel (toΣVecRel reflR xs))
    goal xs = SQ.elimProp {P = λ xs → Y (fromΣVecRel xs)}
                          (λ _ → propY _)
                          f
                          (toΣVecRel reflR xs)

elimΣVecProp2 : {X : Type}
  → {R : X → X → Type}
  → (Y : ΣVec (X /₂ R) → ΣVec (X /₂ R) → Type)
  → (∀ xs ys → isProp (Y xs ys))
  → (∀ x → R x x)
  → (f : (xs ys : ΣVec X) → Y (map SQ.[_] xs) (map SQ.[_] ys))
  → (xs ys : ΣVec (X /₂ R)) → Y xs ys
elimΣVecProp2 {R} Y propY reflR f xs ys =
  subst2 Y (fromΣVecRel-toΣVecRel reflR xs) (fromΣVecRel-toΣVecRel reflR ys) (goal xs ys)
  where
    goal : (xs ys : ΣVec _) → Y (fromΣVecRel (toΣVecRel reflR xs)) (fromΣVecRel (toΣVecRel reflR ys))
    goal xs ys = SQ.elimProp2 {P = λ xs ys → Y (fromΣVecRel xs) (fromΣVecRel ys)}
                              (λ _ _ → propY _ _)
                              f
                              (toΣVecRel reflR xs) (toΣVecRel reflR ys)

fixQ⁺ : FMSet UnorderedTree → UnorderedTree
fixQ⁺ =
  SQ.rec SQ.squash/
         (recΣVec SQ.squash/ (λ _ → isReflBisim _) f fR)
         (elimΣVecProp2 _ (λ _ _ → isPropΠ (λ _ → SQ.squash/ _ _) )
                        (λ _ → isReflBisim _)
                        λ ts us rs → recΣVecPath SQ.squash/ (λ _ → isReflBisim _) f fR ts
                                      ∙ SQ.eq/ _ _ (fix⁺-preserves-≈ (BVec.effectiveRelator isPropBisim isEquivRelBisim rs))
                                      ∙ sym (recΣVecPath SQ.squash/ (λ _ → isReflBisim _) f fR us))
  where
    f : ΣVec Tree → UnorderedTree
    f ts = SQ.[ fix⁺ ts ]

    fR : ∀ xs ys → ΣVecRel Bisim xs ys → f xs ≡ f ys
    fR ts us rs = SQ.eq/ _ _ (fix⁺-preserves-≈ (ΣVecRel→Relator _≈_ rs))

FMSetFunctor : Cat.Functor (SET ℓ-zero) (SET ℓ-zero)
FMSetFunctor .Cat.Functor.F-ob (X , _) = FMSet X , isSetFMSet
FMSetFunctor .Cat.Functor.F-hom f = mapFMSet f
FMSetFunctor .Cat.Functor.F-id = funExt (SQ.elimProp (λ x → isSetFMSet _ x) λ xs → cong _/₂_.[_] (BVec.map-id xs))
FMSetFunctor .Cat.Functor.F-seq f g = funExt (SQ.elimProp (λ _ → isSetFMSet _ _) λ xs → cong _/₂_.[_] (BVec.map-comp g f xs))

module _ (fix⁻-preserves-≈ : PreservesRel _≈_ (Relator _≈_) fix⁻) where
  fixQ⁻ : UnorderedTree → FMSet UnorderedTree
  fixQ⁻ =
    SQ.rec SQ.squash/
           (λ t → SQ.[ map SQ.[_] (fix⁻ t) ])
           λ t u t≈u → SQ.eq/ _ _ (Relator-map _ _ (SQ.eq/ _ _) (fix⁻-preserves-≈ t≈u))


  inj-fixQ⁻' : ∀ {t u} → Relator (Path UnorderedTree) (map SQ.[_] (fix⁻ t)) (map SQ.[_] (fix⁻ u))
    → t ≈ u
  inj-fixQ⁻' {t}{u} rs = subst2 Bisim (secEq fix t) (secEq fix u)
    (fix⁺-preserves-≈ (BVec.effectiveRelator isPropBisim isEquivRelBisim rs))

  inj-fixQ⁻ : ∀ t u → fixQ⁻ t ≡ fixQ⁻ u → t ≡ u
  inj-fixQ⁻ = SQ.elimProp2 (λ _ _ → isPropΠ (λ _ → SQ.squash/ _ _)) goal where
    module _ (t u : Tree) (p : fixQ⁻ SQ.[ t ] ≡ fixQ⁻ SQ.[ u ]) where

      t≈u : t ≈ u
      t≈u = inj-fixQ⁻' (BVec.effective (λ _ _ → isPropRelator _) (isEquivRelRelator isEquivRelPath) p)

      goal : SQ.[ t ] ≡ SQ.[ u ]
      goal = SQ.eq/ _ _ t≈u

  fixQ⁻fixQ⁺ : ∀ t → fixQ⁻ (fixQ⁺ t) ≡ t
  fixQ⁻fixQ⁺ =
    SQ.elimProp (λ _ → SQ.squash/ _ _)
      (elimΣVecProp _ (λ _ → SQ.squash/ _ _) isReflBisim
        (λ ts →
          fixQ⁻ (fixQ⁺ SQ.[ map SQ.[_] ts ])                           ≡⟨⟩
          fixQ⁻ (recΣVec SQ.squash/ isReflBisim f fR (map SQ.[_] ts))  ≡⟨ cong fixQ⁻ (recΣVecPath SQ.squash/ isReflBisim f fR ts) ⟩
          fixQ⁻ (SQ.[ fix⁺ ts ])                                       ≡⟨⟩
          SQ.[ map SQ.[_] (fix⁻ (fix⁺ ts)) ]                           ≡⟨ (λ i → SQ.[ map SQ.[_] (retEq fix ts i) ]) ⟩
          SQ.[ map SQ.[_] ts ]                                         ∎))
    where
      f : ΣVec Tree → UnorderedTree
      f ts = SQ.[ fix⁺ ts ]

      fR : ∀ xs ys → ΣVecRel Bisim xs ys → f xs ≡ f ys
      fR ts us rs = SQ.eq/ _ _ (fix⁺-preserves-≈ (ΣVecRel→Relator _≈_ rs))

  fixQ⁺fixQ⁻ : ∀ ts → fixQ⁺ (fixQ⁻ ts) ≡ ts
  fixQ⁺fixQ⁻ ts = inj-fixQ⁻ _ _ (fixQ⁻fixQ⁺ _)

  fixQ⁺-iso : Iso (FMSet UnorderedTree) UnorderedTree
  fixQ⁺-iso .fun = fixQ⁺
  fixQ⁺-iso .inv = fixQ⁻
  fixQ⁺-iso .rightInv = fixQ⁺fixQ⁻
  fixQ⁺-iso .leftInv = fixQ⁻fixQ⁺

  FMSetFixpointTree/Bisim : (FMSet (Tree /₂ Bisim)) ≃ Tree /₂ Bisim
  FMSetFixpointTree/Bisim = isoToEquiv fixQ⁺-iso

  open import Multiset.Axioms.Choice using (AC)
  open import Multiset.Axioms.PointwiseChoice using ([_⇒_]/_ ; AC→PointwiseChoice ; module PWC)

  [_⇒FMSet_] : (A B : Type) → Type
  [ A ⇒FMSet B ] = [ A ⇒ (ΣVec B) ]/ Relator _≡_

  [_⇒UTree] : (A : Type) → Type
  [ A ⇒UTree] = [ A ⇒ Tree ]/ Bisim
  
  unfold-preserves-coalg-rel' : {X : Type} {γ γ' : X → ΣVec X}
    → (∀ x → Relator _≡_ (γ x) (γ' x))
    → ∀ x n → Approx n (step γ n x) (step γ' n x)
  unfold-preserves-coalg-rel' rel x zero = tt*
  unfold-preserves-coalg-rel' {γ = γ} {γ'} rel x (suc n) =
    Relator-map _ _
      (λ {y} →
        J (λ b eq → Approx n (step γ n y) (step γ' n b))
          (unfold-preserves-coalg-rel' rel y n))
      (rel x)
  
  unfold-preserves-coalg-rel : {X : Type} {γ γ' : X → ΣVec X}
    → (∀ x → Relator _≡_ (γ x) (γ' x))
    → ∀ x → unfold γ x ≈ unfold γ' x
  unfold-preserves-coalg-rel rel x = bisim (unfold-preserves-coalg-rel' rel x)
  
  unfoldQ' : {X : Type} (γ : [ X ⇒FMSet X ])
    → X → UnorderedTree
  unfoldQ' =
    SQ.rec (isSetΠ (λ _ → SQ.squash/))
           (λ γ x → SQ.[ unfold γ x ])
           λ γ γ' rel → funExt (λ x → SQ.eq/ _ _ (unfold-preserves-coalg-rel rel x))

  module Unfold (ac : AC ℓ-zero ℓ-zero ℓ-zero) (X : Type) (setX : isSet X) where
    private
      pwc = AC→PointwiseChoice {ℓ-zero} {ℓ-zero} {ℓ-zero} ac
    module FMSetC = PWC pwc
      X (ΣVec X) (Relator _≡_)
      setX (BVec.isSetΣVec setX)
      (λ _ _ → BVec.isPropRelator _≡_)
      (isEquivRelRelator isEquivRelPath)

    module UTreeC = PWC pwc
      X Tree Bisim
      setX isSetTree
      isPropBisim
      isEquivRelBisim

    unfoldQ : (γ : X → FMSet X) → X → UnorderedTree
    unfoldQ γ = unfoldQ' (FMSetC.wrap γ)

    unfoldQ-coalg-morphism' : (γ : [ X ⇒FMSet X ])
      → ∀ x → fixQ⁻ (unfoldQ' γ x) ≡ mapFMSet (unfoldQ' γ) (FMSetC.unwrap γ x)
    unfoldQ-coalg-morphism' =
      SQ.elimProp (λ _ → isPropΠ (λ _ → SQ.squash/ _ _))
                 (λ γ x → cong SQ.[_] (cong (map SQ.[_]) (funExt⁻ (isCoalgebraMorphismUnfold γ) x)
                           ∙ sym (map-comp _ _ _)))

    unfoldQ-coalg-morphism : (γ : X → FMSet X)
      → ∀ x → fixQ⁻ (unfoldQ γ x) ≡ mapFMSet (unfoldQ γ) (γ x)
    unfoldQ-coalg-morphism γ x =
      unfoldQ-coalg-morphism' (FMSetC.wrap γ) x
      ∙ cong (λ f → mapFMSet (unfoldQ γ) (f x)) (FMSetC.unwrap-section γ)

    unfoldQ-unique'' : (γ : X → ΣVec X)
      → (f : [ X ⇒UTree])
      → (∀ x → fixQ⁻ (UTreeC.unwrap f x) ≡ mapFMSet (UTreeC.unwrap f) SQ.[ γ x ])
      → ∀ x → UTreeC.unwrap f x ≡ unfoldQ' SQ.[ γ ] x
    unfoldQ-unique'' γ = SQ.elimProp (λ _ → isPropΠ (λ _ → isPropΠ (λ _ → SQ.squash/ _ _))) goal
      where module _ (f : X → Tree) (feq : ∀ x → fixQ⁻ (UTreeC.unwrap SQ.[ f ] x) ≡ mapFMSet (UTreeC.unwrap SQ.[ f ]) SQ.[ γ x ]) (x : X) where
        open import Multiset.Relation.Base
        by-effectiveness : ∀ x → Relator _≈_ (fix⁻ (f x)) (map f (γ x))
        by-effectiveness x = BVec.effectiveRelator
          isPropBisim
          isEquivRelBisim
          (subst (Relator _≡_ (BVec.map SQ.[_] (fix⁻ (f x))))
            (map-comp _ _ _)
            (SQ.effective (λ _ _ → isPropRelator _≡_)
              (isEquivRelRelator isEquivRelPath)
              _ _ (feq x)
            )
          )

        bisim-f-unfold : Bisim (f x) (unfold γ x)
        bisim-f-unfold = unfold-unique γ f by-effectiveness x

        goal : UTreeC.unwrap SQ.[ f ] x ≡ unfoldQ' SQ.[ γ ] x
        goal = SQ.eq/ _ _ bisim-f-unfold

    unfoldQ-unique' : (γ : [ X ⇒FMSet X ])
      → (f : X → UnorderedTree)
      → (feq : ∀ x → fixQ⁻ (f x) ≡ mapFMSet f (FMSetC.unwrap γ x))
      → ∀ x → f x ≡ unfoldQ' γ x
    unfoldQ-unique' =
      SQ.elimProp
        (λ _ → isPropΠ (λ _ → isPropΠ (λ _ → isPropΠ (λ _ → SQ.squash/ _ _))))
        (λ γ f feq x →
           (λ i → sym (UTreeC.unwrap-section f) i x)
           ∙ unfoldQ-unique'' γ
                              (UTreeC.wrap f)
                              (λ y → (λ i → fixQ⁻ (UTreeC.unwrap-section f i y))
                                      ∙ feq y
                                      ∙ cong (λ g → SQ.[ map g (γ y) ]) (sym (UTreeC.unwrap-section f)))
                              x)

    unfoldQ-unique : (γ : X → FMSet X)
      → (f : X → UnorderedTree)
      → (feq : ∀ x → fixQ⁻ (f x) ≡ mapFMSet f (γ x))
      → f ≡ unfoldQ γ
    unfoldQ-unique γ f feq =
      funExt (unfoldQ-unique' (FMSetC.wrap γ) f (λ y → feq y ∙ λ i → mapFMSet f (FMSetC.unwrap-section γ (~ i) y)))

  module _ (ac : AC ℓ-zero ℓ-zero ℓ-zero) where
    unfoldCoalgebra : Coalgebra FMSetFunctor
    unfoldCoalgebra .Coalgebra.carrier = (Tree /₂ Bisim) , SQ.squash/
    unfoldCoalgebra .Coalgebra.str = fixQ⁻

    isTerminalFixQ⁻ : isTerminalCoalgebra FMSetFunctor unfoldCoalgebra
    isTerminalFixQ⁻ γ-coalg@(coalgebra {(C , setC)} γ) = anaQ , anaEq where
      open Unfold ac C setC
      anaQ : CoalgebraHom FMSetFunctor γ-coalg unfoldCoalgebra
      anaQ .CoalgebraHom.carrierHom = unfoldQ γ
      anaQ .CoalgebraHom.strHom = funExt (unfoldQ-coalg-morphism γ)

      anaEq : (f : CoalgebraHom FMSetFunctor γ-coalg unfoldCoalgebra) → anaQ ≡ f
      anaEq f-hom@(coalgebraHom f f-γ-unfold-sq) = CoalgebraHom≡ FMSetFunctor (sym (unfoldQ-unique γ f (funExt⁻ f-γ-unfold-sq)))

    TerminalfixQ⁻ : TerminalCoalgebra FMSetFunctor
    TerminalfixQ⁻ .fst = unfoldCoalgebra
    TerminalfixQ⁻ .snd = isTerminalFixQ⁻
