{-# OPTIONS --safe #-}

module Multiset.ListQuotient.Fixpoint where

open import Multiset.Prelude
open import Multiset.ListQuotient.Finality using (fix⁺-preserves-≈)
open import Multiset.ListQuotient.ListFinality
  using
    ( FunctorΣVec
    ; !^
    ; cut
    ; Tree
    ; fix ; fix⁺ ; fix⁻
    ; step
    ; unfold
    )
open import Multiset.ListQuotient.Bisimilarity as Bisimilarity
  using
    ( Bisim ; _≈_ ; bisim
    ; isTransApprox
    ; isReflBisim
    ; isTransBisim
    ; isPropBisim
    ; Approx
    )
open import Multiset.Util.Relation using (ReflectsRel ; PreservesRel ; isSymTot)
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

open import Cubical.Foundations.Equiv using (_≃_ ; secEq ; retEq)
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

open BVec.ΣVec
open Limit using (elements ; is-lim)
open Iso
open Functor ⦃...⦄

FMSet : ∀ {ℓ} → Type ℓ → Type ℓ
FMSet X = ΣVec X /₂ (Relator _≡_)

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

open BinaryRelation

isSymApprox : ∀ n → isSym (Approx n)
isSymApprox zero = isSymTot
isSymApprox (suc n) = isSymRelator (isSymApprox n)

isSymBisim : isSym Bisim
isSymBisim s t s≈t = bisim λ n → isSymApprox n _ _ (s≈t .elements n)

isEquivRelRelator : {X : Type} {R : X → X → Type}
  → isEquivRel R
  → isEquivRel (Relator R)
isEquivRelRelator eqR =
  equivRel (isReflRelator (isEquivRel.reflexive eqR))
           (isSymRelator (isEquivRel.symmetric eqR))
           (isTransRelator (isEquivRel.transitive eqR))


isEquivRelBisim : isEquivRel Bisim
isEquivRelBisim =
  equivRel isReflBisim
           isSymBisim
           isTransBisim

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
  inj-fixQ⁻ =
    SQ.elimProp2 (λ _ _ → isPropΠ (λ _ → SQ.squash/ _ _))
      (λ t u r →
        SQ.eq/ _ _
          (inj-fixQ⁻' (SQ.effective (λ _ _ → isPropRelator _)
                                    (isEquivRelRelator (equivRel (λ _ → refl) (λ _ _ → sym) λ _ _ _ → _∙_))
                                    _
                                    _
                                    r)) )

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
