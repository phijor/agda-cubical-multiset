{-# OPTIONS --safe #-}

module Multiset.AxiomChoice where

open import Cubical.Core.Everything
open import Cubical.Foundations.Everything
open import Cubical.Data.List renaming (map to mapList; [_] to sing)
open import Cubical.Data.Sigma
open import Cubical.Data.Unit
open import Cubical.Data.Empty renaming (elim to ⊥-elim)
open import Cubical.Data.Nat
open import Cubical.Data.Sum renaming (inl to inj₁; inr to inj₂; map to map⊎)
open import Cubical.Functions.Logic hiding (⊥)
open import Cubical.HITs.SetQuotients renaming (rec to recQ; elim to elimQ)
open import Cubical.HITs.PropositionalTruncation as PropTrunc
  renaming (map to ∥map∥; rec to ∥rec∥)
open import Cubical.HITs.SetTruncation as ST
open import Cubical.Relation.Binary hiding (Rel)
open BinaryRelation

-- open import Basics

AC : ∀ {ℓ ℓ' ℓR} → Type (ℓ-suc (ℓ-max ℓ (ℓ-max ℓ' ℓR)))
AC {ℓ} {ℓ'} {ℓR} =
  ∀ {A : Type ℓ} {B : A → Type ℓ'}
  → (R : (a : A) → (B a) → Type ℓR)
  → isSet A
  → (∀ a → isSet (B a))
  → (∀ a b → isProp (R a b))
  → (∀ a → ∥ Σ[ b ∈ B a ] R a b ∥₁)
  → ∥ Σ[ f ∈ ((a : A) → B a) ] (∀ a → R a (f a)) ∥₁


substSymInRel : {A : Type} (B : A → Type)
  → (R : ∀ a → B a → B a → Type)
  → {a a' : A} (p : a ≡ a')
  → (b : B a) (b' : B a')
  → R a' (subst B p b) b'
  → R a b (subst B (sym p) b')
substSymInRel B R {a} =
  J (λ a' p
       → (b : B a) (b' : B a')
       → R a' (subst B p b) b'
       → R a b (subst B (sym p) b'))
     (λ b b' →
        subst2 (R a)
               (substRefl {B = B} b)
               (sym (substRefl {B = B} b')))

substTransInRel : {A : Type} (B : A → Type)
  → (R : ∀ a → B a → B a → Type)
  → {a a' a'' : A} (p : a ≡ a') (q : a' ≡ a'')
  → (b : B a) (b' : B a') 
  → R a' (subst B p b) b'
  → R a'' (subst B (p ∙ q) b) (subst B q b')
substTransInRel B R {a} {a'} {a''} =
  J (λ a' p
       → (q : a' ≡ a'')
       → (b : B a) (b' : B a')
       → R a' (subst B p b) b'
       → R a'' (subst B (p ∙ q) b) (subst B q b'))
    (J (λ a'' q
       → (b b' : B a)
       → R a (subst B refl b) b'
       → R a'' (subst B (refl ∙ q) b) (subst B q b'))
       λ b b' →
         subst2 (R a)
                (cong (λ x → subst B x b) (rUnit refl))
                (sym (substRefl {B = B} b')))
       
-- pointwise lifting of a relation to a function space
PW : {X A B : Type} (R : A → B → Type) → (X → A) → (X → B) → Type
PW R f g = ∀ x → R (f x) (g x)

-- the quotient a function space by the pointwise lifted relation
[_⇒_]/_ : (A B : Type) (R : B → B → Type) → Type
[ A ⇒ B ]/ R = (A → B) / PW R

-- a function sending equivalence classes of functions wrt. pointwise
-- lifted relation to functions into equivalence classes
θ : ∀ A {B} (R : B → B → Type) → [ A ⇒ B ]/ R → A → B / R
θ A R = recQ (isSetΠ (λ _ → squash/)) (λ c x → [ c x ])
  λ c c' r → funExt (λ x → eq/ _ _ (r x))


-- equivalence between two formulation of full axiom of choice; the
-- formulation stating the surjectivity of the map λ g → [_] ∘ g is
-- proved equivalent to the usual presentation of axiom of choice

-- NB: in the first formulation we do not need to 0-truncate the
-- existence of a section, since the type of sections of θ is a
-- proposition; this follows directly from the lemma SectionIsProp.

SectionIsProp' : ∀ A {B} (R : B → B → Type)
  → isPropValued R → isEquivRel R
  → (f : A → B / R)
  → (g g' : [ A ⇒ B ]/ R) (eq : θ A R g ≡ f) (eq' : θ A R g' ≡ f)
  → g ≡ g'
SectionIsProp' A R Rprop Reqr f = elimProp2 (λ _ _ → isPropΠ (λ _ → isPropΠ λ _ → squash/ _ _))
  λ g g' eq eq' → eq/ _ _ (λ x → effective Rprop Reqr _ _ (λ i → (eq ∙ sym eq') i x))

SectionIsProp : ∀ A {B} (R : B → B → Type)
  → isPropValued R → isEquivRel R
  → (f : A → B / R)
  → isProp (Σ ([ A ⇒ B ]/ R) (λ g → θ A R g ≡ f))
SectionIsProp A R Rprop Reqr f (g , eq) (g' , eq') =
  Σ≡Prop (λ _ → isOfHLevelPathP' 1 (isSetΠ λ _ → squash/) _ f)
    (SectionIsProp' A R Rprop Reqr f g g' eq eq')

module _ (θInv : ∀ A {B} (R : B → B → Type) → (A → B / R) → [ A ⇒ B ]/ R)
         (sectionθ : ∀ A {B} (R : B → B → Type) → section (θ A R) (θInv A R)) where

  ac' : ∀ (A : Type) {B : Type} (R : B → B → Type)
    → (f : (A → B) / PW R) → ∃[ g ∈ (A → B) ] [_] ∘ g ≡ θ A R f
  ac' A R = elimProp (λ _ → isPropPropTrunc) (λ g → ∣ g , refl ∣₁)

  ac : ∀ (A : Type) {B : Type} (R : B → B → Type)
    → (f : A → B / R) → ∃[ g ∈ (A → B) ] [_] ∘ g ≡ f
  ac A R f =
    ∥map∥ (λ { (g , eq) → g , eq ∙ sectionθ A R f }) (ac' A R (θInv A R f))

module InvSec (ac : ∀ (A : Type) {B : Type} (R : B → B → Type)
             → isPropValued R → isEquivRel R
             → (f : A → B / R) → ∃[ g ∈ (A → B) ] [_] ∘ g ≡ f) where

  θInvSec : ∀ A {B} (R : B → B → Type)
    → isPropValued R → isEquivRel R
    → (f : A → B / R) → Σ ([ A ⇒ B ]/ R) (λ g → θ A R g ≡ f)
  θInvSec A R Rprop Reqr f =
    ∥rec∥ (SectionIsProp A R Rprop Reqr f)
         (λ {(g , eq) → [ g ] , eq})
         (ac A R Rprop Reqr f)

-- =====================================================================

-- "Dependent" version of axiom of choice

-- pointwise lifting of a relation to a dep. function space
PW-d : {X : Type} {A B : X → Type} (R : (x : X) → A x → B x → Type)
  → (∀ x → A x) → (∀ x → B x) → Type
PW-d R f g = ∀ x → R x (f x) (g x)

-- the quotient a function space by the pointwise lifted relation
[_⇒-d_]/_ : (A : Type) (B : A → Type) (R : (a : A) → B a → B a → Type) → Type
[ A ⇒-d B ]/ R = (∀ a → B a) / PW-d R

-- a function sending equivalence classes of functions wrt. pointwise
-- lifted relation to functions into equivalence classes
θ-d : ∀ {A} {B : A → Type} (R : (a : A) → B a → B a → Type)
  → [ A ⇒-d B ]/ R → ∀ a → B a / R a
θ-d R = recQ (isSetΠ (λ _ → squash/)) (λ c x → [ c x ])
  λ c c' r → funExt (λ x → eq/ _ _ (r x))

-- the type of sections for θ-d is a again a proposition
SectionIsProp-d' : ∀ A {B : A → Type} (R : ∀ a → B a → B a → Type)
  → (∀ a → isPropValued (R a))
  → (∀ a → isEquivRel (R a))
  → (f : ∀ a → B a / R a)
  → (g g' : [ A ⇒-d B ]/ R) (eq : θ-d R g ≡ f) (eq' : θ-d R g' ≡ f)
  → g ≡ g'
SectionIsProp-d' A R Rprop Reqr f =
  elimProp2 (λ _ _ → isPropΠ (λ _ → isPropΠ λ _ → squash/ _ _))
    λ g g' eq eq' → eq/ _ _ (λ x → effective (Rprop x) (Reqr x) _ _ (λ i → (eq ∙ sym eq') i x))

SectionIsProp-d : ∀ A {B : A → Type} (R : ∀ a → B a → B a → Type)
  → (∀ a → isPropValued (R a))
  → (∀ a → isEquivRel (R a))
  → (f : ∀ a → B a / R a)
  → isProp (Σ ([ A ⇒-d B ]/ R) (λ g → θ-d R g ≡ f))
SectionIsProp-d A R Rprop Reqr f (g , eq) (g' , eq') =
  Σ≡Prop (λ h p q i j x → squash/ (θ-d R h x) (f x) (λ i → p i x) (λ i → q i x) i j)
    (SectionIsProp-d' A R Rprop Reqr f g g' eq eq')
      
-- The "dependent" version of choice is equivalent to the usual one
module _ (ac : ∀ (A : Type) {B : Type} (R : B → B → Type)
             → isPropValued R → isEquivRel R
             → (f : A → B / R) → ∃[ g ∈ (A → B) ] [_] ∘ g ≡ f)
         {A : Type} (setA : isSet A) {B : A → Type}
         (R : ∀ a → B a → B a → Type)
         (Rprop : ∀ a → isPropValued (R a))
         (Reqr : ∀ a → isEquivRel (R a))
         where

  ΣR : Σ A B → Σ A B → Type
  ΣR (a , b) (a' , b') = Σ (a ≡ a') λ p → R a' (subst B p b) b'

  ΣRprop : isPropValued ΣR
  ΣRprop _ _ = isPropΣ (setA _ _) λ _ → Rprop _ _ _ 

  open isEquivRel
  ΣReqr : isEquivRel ΣR
  ΣReqr = equivRel
    (λ { (a , b) → refl ,
      subst (λ x → R a x b) (sym (substRefl {B = B} b)) (Reqr a .reflexive b) }) 
    (λ { (a , b) (a' , b') (eq , r) → sym eq ,
      Reqr a .symmetric _ _ (substSymInRel B R eq b b' r) })
    (λ { (a , b) (a' , b') (a'' , b'') (eq , r) (eq' , r') → (eq ∙ eq') ,
      Reqr a'' .transitive _ _ _ (substTransInRel B R eq eq' b b' r) r' })

  ac-d : (f : ∀ a → B a / R a) → ∃[ g ∈ (∀ a → B a) ] [_] ∘ g ≡ f
  ac-d f =
    ∥map∥ (λ { (g , eq) →
            (λ a → subst B (fst-eq a (g a) (f a) (λ i → eq i a)) (g a .snd)) ,
            funExt (λ a → lem a (g a) (f a) (λ i → eq i a))})
      (ac A ΣR ΣRprop ΣReqr fΣ)
    where
      [pair] : ∀ a → B a → Σ A B / ΣR
      [pair] a b = [ a , b ]

      [pair]eq : ∀ a (b : B a) (b' : B a) → R a b b' → [pair] a b ≡ [pair] a b'
      [pair]eq a b b' r =
        eq/ _ _ (refl , subst (λ z → R a z b') (sym (substRefl {B = B} b)) r)

      fΣ : A → Σ A B / ΣR
      fΣ a = recQ squash/ ([pair] a) ([pair]eq a) (f a)

      fst-eq : (a : A) (x : Σ A B) (y : B a / R a)
        → (eq : [ x ] ≡ recQ squash/ ([pair] a) ([pair]eq a) y)
        → x .fst ≡ a
      fst-eq a x =
        elimProp 
          (λ _ → isPropΠ λ _ → setA _ _)
          (λ b eq → effective ΣRprop ΣReqr x (a , b) eq .fst)

      lem : ∀ a (x : Σ A B) (y : B a / R a)
        → (eq : [ x ] ≡ recQ squash/ ([pair] a) ([pair]eq a) y)
        → [ subst B (fst-eq a x y eq) (x .snd) ] ≡ y
      lem a x =
        elimProp
          (λ _ → isPropΠ λ _ → squash/ _ _)
          (λ b eq → eq/ _ _ (effective ΣRprop ΣReqr x(a , b) eq .snd))


-- Connecting two "dependent" versions of choice 
module InvSecD (ac-d : (A : Type) {B : A → Type}
               (R : ∀ a → B a → B a → Type)
               (Rprop : ∀ a → isPropValued (R a))
               (Reqr : ∀ a → isEquivRel (R a))
               → (f : ∀ a → B a / R a) → ∃[ g ∈ (∀ a → B a) ] [_] ∘ g ≡ f)
         {A : Type} (setA : isSet A) {B : A → Type}
         (R : ∀ a → B a → B a → Type)
         (Rprop : ∀ a → isPropValued (R a))
         (Reqr : ∀ a → isEquivRel (R a))
         where

  θInvSec-d : (f : ∀ a → B a / R a) → Σ ([ A ⇒-d B ]/ R) (λ g → θ-d R g ≡ f)
  θInvSec-d f =
    ∥rec∥ (SectionIsProp-d A R Rprop Reqr f)
         (λ {(g , eq) → [ g ] , eq})
         (ac-d A R Rprop Reqr f)


-- An induction principle for arbitrary collections of quotients
module _ {A : Type} (B : A → Type)
         (R : ∀ a → B a → B a → Type)
         (Rprop : ∀ a → isPropValued (R a))
         (Reqr : ∀ a → isEquivRel (R a))
         (θInv-d : (∀ a → B a / R a) → [ A ⇒-d B ]/ R)
         (sectionθ-d : section (θ-d R) θInv-d) where

  θ-d-inj : ∀ f f' → θ-d R f ≡ θ-d R f' → f ≡ f'
  θ-d-inj = elimProp2 (λ _ _ → isPropΠ (λ _ → squash/ _ _))
    λ g g' eq → eq/ _ _ (λ a → effective (Rprop a) (Reqr a) _ _ (λ i → eq i a)) 

  θInv-d-β : (g : ∀ a → B a) → θInv-d ([_] ∘ g) ≡ [ g ]
  θInv-d-β g = θ-d-inj (θInv-d ([_] ∘ g)) [ g ] (sectionθ-d ([_] ∘ g))

  retractθ-d : retract (θ-d R) θInv-d
  retractθ-d = elimProp (λ _ → squash/ _ _) θInv-d-β

  isoθ-d : isIso (θ-d R)
  isoθ-d = θInv-d , sectionθ-d , retractθ-d

  sectionθ-d-eq : (g : ∀ a → B a) → sectionθ-d ([_] ∘ g) ≡ cong (θ-d R) (θInv-d-β g)
  sectionθ-d-eq g i j a =
    squash/ (θ-d R (θInv-d ([_] ∘ g)) a)
            [ g a ]
            (λ i → sectionθ-d ([_] ∘ g) i a)
            (λ i → θ-d R (θInv-d-β g i) a)
            i
            j
  
  elimColl' : (C : (∀ a → B a / R a) → Type)
    → (setC : ∀ f → isSet (C f))
    → ([_]C : (g : ∀ a → B a) → C ([_] ∘ g))
    → (eqC : ∀ g g' (r : PW-d R g g')
      → PathP (λ i → C (λ a → eq/ (g a) (g' a) (r a) i)) [ g ]C [ g' ]C) 
    → (f : [ A ⇒-d B ]/ R) → C (θ-d R f)
  elimColl' C setC = elimQ (λ _ → setC _)
                   
  elimColl : (C : (∀ a → B a / R a) → Type)
    → (setC : ∀ f → isSet (C f))
    → ([_]C : (g : ∀ a → B a) → C ([_] ∘ g))
    → (eqC : ∀ g g' (r : PW-d R g g')
      → PathP (λ i → C (λ a → eq/ (g a) (g' a) (r a) i)) [ g ]C [ g' ]C) 
    → (f : ∀ a → B a / R a) → C f
  elimColl C setC [_]C eqC f =
    subst C (sectionθ-d f) (elimColl' C setC [_]C eqC (θInv-d f))

  elimColl-β : (C : (∀ a → B a / R a) → Type)
    → (setC : ∀ f → isSet (C f))
    → ([_]C : (g : ∀ a → B a) → C ([_] ∘ g))
    → (eqC : ∀ g g' (r : PW-d R g g')
      → PathP (λ i → C (λ a → eq/ (g a) (g' a) (r a) i)) [ g ]C [ g' ]C) 
    → (g : ∀ a → B a)
    → elimColl C setC [_]C eqC ([_] ∘ g) ≡ [ g ]C
  elimColl-β C setC [_]C eqC g =
    (λ i → subst C (sectionθ-d-eq g i) (elimColl' C setC [_]C eqC (θInv-d ([_] ∘ g))))
    ∙ fromPathP {A = λ i → C (θ-d R (θInv-d-β g i))}
                (cong (elimColl' C setC [_]C eqC) (θInv-d-β g))

  recColl : (C : Type)
    → (setC : isSet C)
    → ([_]C : (g : ∀ a → B a) → C)
    → (eqC : ∀ g g' (r : PW-d R g g') → [ g ]C ≡ [ g' ]C)
    → (f : ∀ a → B a / R a) → C
  recColl C setC = elimColl (λ _ → C) (λ _ → setC) 

  recColl-β : (C : Type)
    → (setC : isSet C)
    → ([_]C : (g : ∀ a → B a) → C)
    → (eqC : ∀ g g' (r : PW-d R g g') → [ g ]C ≡ [ g' ]C)
    → (g : ∀ a → B a)
    → recColl C setC [_]C eqC ([_] ∘ g) ≡ [ g ]C
  recColl-β C setC = elimColl-β (λ _ → C) (λ _ → setC) 

  elimCollProp : (C : (∀ a → B a / R a) → Type)
    → (propC : ∀ f → isProp (C f))
    → ([_]C : (g : ∀ a → B a) → C ([_] ∘ g))
    → (f : ∀ a → B a / R a) → C f
  elimCollProp C propC [_]C =
    elimColl C (λ f → isProp→isSet (propC f))
             [_]C
             (λ _ _ _ → isProp→PathP (λ _ → propC _) _ _)


module ChoiceForTheorem7
         (ac : {A : Type} {B : A → Type} (R : (a : A) → B a → Type)
           → isSet A → (∀ a → isSet (B a)) → (∀ a b → isProp (R a b))
           → ((a : A) → ∥ (Σ[ b ∈ B a ] R a b ) ∥₁)
           → ∥ Σ[ f ∈ ((a : A) → B a) ] ((a : A) → R a (f a)) ∥₁)
         where

  module Hyps {X Y : Type} (R : Y → Y → Type)
              (setX : isSet X) (setY : isSet Y)
              (propR : isPropValued R) (eqR : isEquivRel R)
              where

    [surjective] : (g : X → Y / R) → ∃[ f ∈ (X → Y) ] ((x : X) → [ f x ] ≡ g x)
    [surjective] g = 
      ac (λ x y → [ y ] ≡ g x)
         setX (λ _ → setY) (λ _ _ → squash/ _ _)
         (elimProp {P = λ z → ∥ (Σ-syntax Y (λ y → [ y ] ≡ z)) ∥₁}
                   (λ _ → squash₁)
                   (λ y → ∣ y , refl ∣₁)
           ∘ g)
           
    θInvSec : (f : X → Y / R) → Σ ([ X ⇒ Y ]/ R) (λ g → θ X R g ≡ f)
    θInvSec f = 
      ∥rec∥ (SectionIsProp X R propR eqR f)
            (λ { (g , eq) → [ g ] , funExt eq })
            ([surjective] f)

    θInv : (X → Y / R) → [ X ⇒ Y ]/ R
    θInv = fst ∘ θInvSec

    sectionθ : (f : X → Y / R) → θ X R (θInv f) ≡ f
    sectionθ = snd ∘ θInvSec



module ChoiceForTheorem11
         (ac32 : {A : Type} {B : A → Type} (R : (a : A) → B a → Type)
           → isSet A → (∀ a → isGroupoid (B a)) → (∀ a b → isProp (R a b))
           → ((a : A) → ∥ (Σ[ b ∈ B a ] R a b ) ∥₂)
           → ∥ Σ[ f ∈ ((a : A) → B a) ] ((a : A) → R a (f a)) ∥₂)
         (ac : {A : Type} (B : A → Type)
           → isSet A → (∀ a → isSet (B a))
           → ((a : A) → ∥ B a ∥₁)
           → ∥ ((a : A) → B a) ∥₁)          
         where

  ∥θ∥₂ : {A B : Type} → ∥ (A → B) ∥₂ → A → ∥ B ∥₂
  ∥θ∥₂ = ST.rec (isSetΠ (λ _ → squash₂)) (∣_∣₂ ∘_)

  ∥θ∥₁ : {X : Type} {Y : X → Type} → ∥ ((x : X) → Y x) ∥₁ → (x : X) → ∥ Y x ∥₁
  ∥θ∥₁ = PropTrunc.rec (isPropΠ (λ _ → squash₁)) (∣_∣₁ ∘_)

  module Hyps {X : Type} {Y : Type} (setX : isSet X) (grpdY : isGroupoid Y) where
  
    ∥surjective∥₂ : (g : X → ∥ Y ∥₂) → ∥ Σ[ f ∈ (X → Y) ] ((x : X) → ∣ f x ∣₂ ≡ g x) ∥₂
    ∥surjective∥₂ g =
      ac32 (λ x y → ∣ y ∣₂ ≡ g x)
         setX (λ _ → grpdY) (λ _ _ → squash₂ _ _)
         (ST.elim {B = λ z → ∥ Σ[ y ∈ Y ] (∣ y ∣₂ ≡ z) ∥₂}
                  (λ _ → squash₂)
                  (λ y → ∣ y , refl ∣₂)
                  ∘ g)
  
    ∥θ∥₂InvSec :  (g : X → ∥ Y ∥₂) → Σ[ f ∈ ∥ (X → Y) ∥₂ ] ∥θ∥₂ f ≡ g
    ∥θ∥₂InvSec g =
      ST.rec (isSetΣ squash₂ (λ _ → isProp→isSet (isSetΠ (λ _ → squash₂) _ _)))
             (λ { (f , eq) → ∣ f ∣₂ , funExt eq  })
             (∥surjective∥₂ g)
  
    ∥θ∥₂Inv :  (X → ∥ Y ∥₂) → ∥ (X → Y) ∥₂
    ∥θ∥₂Inv g = ∥θ∥₂InvSec g .fst
  
    ∥θ∥₂Sec :  (g : X → ∥ Y ∥₂) → ∥θ∥₂ (∥θ∥₂Inv g) ≡ g
    ∥θ∥₂Sec g = ∥θ∥₂InvSec g .snd
  
    ∥θ∥₂-inj : (f f' : ∥ (X → Y) ∥₂) → ∥θ∥₂ f ≡ ∥θ∥₂ f' → f ≡ f'
    ∥θ∥₂-inj =
      ST.elim2 (λ _ _ → isSetΠ λ _ → isProp→isSet (squash₂ _ _))
               λ f f' eq →
                 PathIdTrunc₀Iso .Iso.inv
                   (∥map∥ funExt
                          (ac (λ x → f x ≡ f' x)
                               setX (λ _ → grpdY _ _)
                               (λ x → PathIdTrunc₀Iso .Iso.fun (λ i → eq i x))))
  
    ∥θ∥₂Inv-β : (f : X → Y) → ∥θ∥₂Inv (∣_∣₂ ∘ f) ≡ ∣ f ∣₂
    ∥θ∥₂Inv-β f = ∥θ∥₂-inj (∥θ∥₂Inv (∣_∣₂ ∘ f)) ∣ f ∣₂ (∥θ∥₂Sec (∣_∣₂ ∘ f))
  
    recColl₂ : {A : Type} → isSet A
      → ((X → Y) → A)
      → (X → ∥ Y ∥₂) → A
    recColl₂ setA h g = ST.rec setA h (∥θ∥₂Inv g)
  
    recCollβ₂ : {A : Type} (setA : isSet A)
      → (g : (X → Y) → A)
      → (f : X → Y) → recColl₂ setA g (∣_∣₂ ∘ f) ≡ g f
    recCollβ₂ {A} setA h f = cong (ST.rec setA h) (∥θ∥₂Inv-β f)
  
    elimCollProp₂' : (B : (X → ∥ Y ∥₂) → Type) → (∀ c → isProp (B c))
      → ((c : X → Y) → B (∣_∣₂ ∘ c))
      → (c : ∥ (X → Y) ∥₂) → B (∥θ∥₂ c)
    elimCollProp₂' B propB h = ST.elim (λ _ → isProp→isSet (propB _)) h
  
    elimCollProp₂ : (B : (X → ∥ Y ∥₂) → Type) → (∀ c → isProp (B c))
      → ((c : X → Y) → B (∣_∣₂ ∘ c))
      → (c : X → ∥ Y ∥₂) → B c
    elimCollProp₂ B propB h c =
      subst B (∥θ∥₂Sec c) (elimCollProp₂' B propB h (∥θ∥₂Inv c))

  module Hyps2 {X : Type} (Y : X → Type)
               (setX : isSet X) (setY : ∀ x → isSet (Y x))
               where

    ∥θ∥₁Inv : ((x : X) → ∥ Y x ∥₁) → ∥ ((x : X) → Y x) ∥₁
    ∥θ∥₁Inv = ac Y setX setY
    
    elimCollProp₁' :  (B : ((x : X) → ∥ Y x ∥₁) → Type) → (∀ c → isProp (B c))
      → ((c : (x : X) → Y x) → B (∣_∣₁ ∘ c))
      → (c : ∥ ((x : X) → Y x) ∥₁) → B (∥θ∥₁ c)
    elimCollProp₁' B propB h = PropTrunc.elim (λ _ → propB _) h

    elimCollProp₁ :  (B : ((x : X) → ∥ Y x ∥₁) → Type) → (∀ c → isProp (B c))
      → ((c : (x : X) → Y x) → B (∣_∣₁ ∘ c))
      → (c : (x : X) → ∥ Y x ∥₁) → B c
    elimCollProp₁ B propB h c =
      subst B (isPropΠ (λ _ → squash₁) _ _) (elimCollProp₁' B propB h (∥θ∥₁Inv c))


{-
module _ {A : Type} (setA : isSet A) {B : A → Type}
         (R : ∀ a → B a → B a → Type)
         (Rprop : ∀ a → isPropValued (R a))
         (Reqr : ∀ a → isEquivRel (R a))
         where

  ΣR : Σ A B → Σ A B → Type
  ΣR (a , b) (a' , b') = Σ (a ≡ a') λ p → R a' (subst B p b) b'

  ΣRprop : isPropValued ΣR
  ΣRprop _ _ = isPropΣ (setA _ _) λ _ → Rprop _ _ _ 

  open isEquivRel
  ΣReqr : isEquivRel ΣR
  ΣReqr = equivRel
    (λ { (a , b) → refl , subst (λ x → R a x b) (sym (substRefl {B = B} b)) (Reqr a .reflexive b) }) 
    (λ { (a , b) (a' , b') (eq , r) → sym eq , {!!} })
    (λ { (a , b) (a' , b') (a'' , b'') (eq , r) (eq' , r') → (eq ∙ eq') , {!!} })

  hasChoice-surj : Type
  hasChoice-surj = (f : ∀ a → B a / R a) → ∃[ g ∈ (∀ a → B a) ] [_] ∘ g ≡ f

  hasChoice-surjΣ : Type
  hasChoice-surjΣ = (f : A → Σ A B / ΣR) → ∃[ g ∈ (A → Σ A B) ] [_] ∘ g ≡ f

  hasChoice-split : Type
  hasChoice-split = (f : ∀ a → B a / R a) → Σ ([ A ⇒-d B ]/ R) (λ g → θ-d A R g ≡ f)

  hasChoice-splitΣ : Type
  hasChoice-splitΣ = (f : A → Σ A B / ΣR) → Σ ([ A ⇒ Σ A B ]/ ΣR) (λ g → θ _ ΣR g ≡ f)

  hasChoice-surjΣ→surj : hasChoice-surjΣ → hasChoice-surj
  hasChoice-surjΣ→surj ac f = 
    ∥map∥ (λ { (g , eq) →
            (λ a → subst B (fst-eq a (g a) (f a) (λ i → eq i a)) (g a .snd)) ,
            funExt (λ a → lem a (g a) (f a) (λ i → eq i a))})
      (ac fΣ)
    where
      [pair] : ∀ a → B a → Σ A B / ΣR
      [pair] a b = [ a , b ]

      [pair]eq : ∀ a (b : B a) (b' : B a) → R a b b' → [pair] a b ≡ [pair] a b'
      [pair]eq a b b' r =
        eq/ _ _ (refl , subst (λ z → R a z b') (sym (substRefl {B = B} b)) r)

      fΣ : A → Σ A B / ΣR
      fΣ a = recQ squash/ ([pair] a) ([pair]eq a) (f a)

      fst-eq : (a : A) (x : Σ A B) (y : B a / R a)
        → (eq : [ x ] ≡ recQ squash/ ([pair] a) ([pair]eq a) y)
        → x .fst ≡ a
      fst-eq a x =
        elimProp 
          (λ _ → isPropΠ λ _ → setA _ _)
          (λ b eq → effective ΣRprop ΣReqr x (a , b) eq .fst)

      lem : ∀ a (x : Σ A B) (y : B a / R a)
        → (eq : [ x ] ≡ recQ squash/ ([pair] a) ([pair]eq a) y)
        → [ subst B (fst-eq a x y eq) (x .snd) ] ≡ y
      lem a x =
        elimProp
          (λ _ → isPropΠ λ _ → squash/ _ _)
          (λ b eq → eq/ _ _ (effective ΣRprop ΣReqr x(a , b) eq .snd))

  hasChoice-surj→split : hasChoice-surj → hasChoice-split
  hasChoice-surj→split ac f = 
    ∥rec∥ (SectionIsProp-d A R Rprop Reqr f)
         (λ {(g , eq) → [ g ] , eq})
         (ac f)

  hasChoice-split→splitΣ : hasChoice-split → hasChoice-splitΣ
  hasChoice-split→splitΣ ac f =  {!f!} , {!!}
    where
      f' : ∀ a → B a / R a
      f' a = {!f a!}
-}

module _ {ℓA ℓB ℓP} {A : Type ℓA} {B : A → Type ℓB}
  {P : (a : A) → B a → Type ℓP}
  (setA : isSet A)
  (setB : ∀ a → isSet (B a))
  (propP : ∀ a b → isProp (P a b)) where

  hasChoice : Type _
  hasChoice = (∀ a → ∃[ b ∈ (B a) ] P a b) → ∃[ g ∈ ((a : A) → B a) ] (∀ a → P a (g a))
  
