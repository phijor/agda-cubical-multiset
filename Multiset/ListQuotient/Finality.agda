{-# OPTIONS --safe #-}

module Multiset.ListQuotient.Finality where

open import Multiset.Prelude
open import Multiset.ListQuotient.ListFinality
  using
    ( FunctorΣVec
    ; !^
    ; cut
    ; Tree
    ; TreePath
    ; fix ; fix⁺ ; fix⁻
    ; step
    ; unfold
    ; isCoalgebraMorphismUnfold
    )
open import Multiset.ListQuotient.Bisimilarity as Bisimilarity
  using
    ( Bisim ; _≈_ ; bisim
    ; isReflApprox
    ; isTransApprox
    ; isReflBisim
    ; isTransBisim
    ; BisimRelation
    ; Approx
    )
open import Multiset.Util.BoolSequence as Seq using (latch-even)
open import Multiset.Util.Vec as Vec using ()
open import Multiset.Util.BundledVec as BVec
  using
    ( ΣVec
    ; Relator∞ ; Relator
    ; Relator-map
    ; RelatorRelation
    )
open import Multiset.Limit.Chain using (Limit)
open import Multiset.Limit.TerminalChain as TerminalChain
  using
    ( Functor
    ; _^_
    )
open import Multiset.Omniscience using (LLPO)
open import Multiset.Relation.Base as Relation
  using
    ( Relation
    ; ReflectsRel
    ; PreservesRel
    ; PreservesRelation
    ; PreservesRel→SectionReflectsRel
    ; Rel[_⇒_]
    )

open import Cubical.Foundations.Function using (_∘_)
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.HLevels
open import Cubical.Data.Nat as Nat using (ℕ ; suc ; zero)
open import Cubical.Data.Unit.Base using (tt*)
open import Cubical.HITs.PropositionalTruncation as PT using (∥_∥₁)

open BVec.ΣVec
open Limit using (elements ; is-lim)
open Functor ⦃...⦄

Path→Approx : ∀ n {t u}
  → t ≡ u
  → Approx n t u
Path→Approx n {t} t≡u = subst (Approx n t) t≡u (isReflApprox n t)

Path→Bisim : ∀ {t u} → t ≡ u → t ≈ u
Path→Bisim {t} t≡u = subst (Bisim t) t≡u (isReflBisim t)

-- fix⁺ is a well-defined setoid morphism
fix⁺-preserves-≈' : ∀ n {t u}
  → Relator _≈_ t u
  → Approx n (!^ n (map (cut n) t)) (!^ n (map (cut n) u))
fix⁺-preserves-≈' zero _ = tt*
fix⁺-preserves-≈' (suc n) {t} {u} rel =
  let
    open BVec.Reasoning (Approx n) (isReflApprox n) (isTransApprox n) using (_Rel⟨_⟩_ ; _Rel∎ ; Path→Rel)
  in
  (map (!^ n) (map (cut (suc n)) t))  Rel⟨ Path→Rel (sym (map-comp _ _ _)) ⟩
  (map (!^ n ∘ cut (suc n)) t)        Rel⟨ Relator-map _ _ goal rel ⟩
  (map (!^ n ∘ cut (suc n)) u)        Rel⟨ Path→Rel (map-comp _ _ _) ⟩
  (!^ (suc n) (map (cut (suc n)) u))  Rel∎
  where
    goal : ∀ {t u} → t ≈ u → Approx n (!^ n (cut (suc n) t)) (!^ n (cut (suc n) u))
    goal {t} {u} r =
       isTransApprox n _ _ _
      (isTransApprox n _ _ _ (Path→Approx n (t .is-lim n))
                             (r .elements n))
                             (Path→Approx n (sym (u .is-lim n)))

fix⁺-preserves-≈ : PreservesRel (Relator _≈_) _≈_ fix⁺
fix⁺-preserves-≈ r = bisim λ n → fix⁺-preserves-≈' n r

fix⁺-relhom : Rel[ RelatorRelation BisimRelation ⇒ BisimRelation ]
fix⁺-relhom .Rel[_⇒_].morphism = fix⁺
fix⁺-relhom .Rel[_⇒_].preserves-relation = fix⁺-preserves-≈

-- Unfold is unique as a coalgebra, up to bisimilarity:
module _ {C : Type} (γ : C → ΣVec C) where
  unfold-unique' : (f : C → Tree)
    → (∀ x → f x ≈ fix⁺ (map f (γ x)))
    → ∀ x n → Approx n (f x .elements n) (step γ n x)
  unfold-unique' f feq x zero = tt*
  unfold-unique' f feq x (suc n) =
    let
      open BVec.Reasoning (Approx n) (isReflApprox n) (isTransApprox n) using (_Rel⟨_⟩_ ; _Rel∎ ; Path→Rel)
    in
    cut (suc n) (f x)                 Rel⟨ feq x .elements (suc n) ⟩
    cut (suc n) (fix⁺ (map f (γ x)))  Rel⟨ Path→Rel path ⟩
    map (cut n ∘ f) (γ x)             Rel⟨ goal ⟩
    map (step γ n) (γ x)              Rel∎
    where abstract
      goal : Relator (Approx n) (map (cut n ∘ f) (γ x)) (map (step γ n) (γ x))
      goal = Relator-map _≡_ _
        (λ {y} → J (λ z eq → Approx n (cut n (f y)) (step γ n z)) (unfold-unique' f feq y n))
        (BVec.isReflRelator (λ _ → refl) _)

      path : cut (suc n) (fix⁺ (map f (γ x))) ≡ map (cut n ∘ f) (γ x)
      path =
        cut (suc n) (fix⁺ (map f (γ x)))   ≡⟨ sym (map-comp _ _ _) ⟩
        _                                  ≡⟨ sym (map-comp _ _ _) ⟩
        _                                  ≡⟨ cong (λ g → map g (γ x)) (funExt (λ y → f y .is-lim n)) ⟩
        map (cut n ∘ f) (γ x) ∎

  unfold-unique : (f : C → Tree)
    → (∀ x → Relator _≈_ (fix⁻ (f x)) (map f (γ x)))
    → ∀ x → f x ≈ unfold γ x
  unfold-unique f feq x =
    bisim (unfold-unique' f (λ y → isTransBisim _ _ _ (Path→Bisim (sym (secEq fix (f y)))) (fix⁺-preserves-≈ (feq y))) x)

-- Assuming that fix⁻ is a setoid-morphism, i.e. preserves bisimilarity,
-- we can conclude that the functor of setoids `RelatorFunctor : (A , R) ↦ (ΣVec A , Relator R)`
-- has a terminal coalgebra:
module _
  (fix⁻-preserves-≈ : PreservesRel _≈_ (Relator _≈_) fix⁻)
  where
  open import Multiset.Categories.Coalgebra

  import Cubical.HITs.SetQuotients as SQ

  open import Multiset.Setoid.Base
  open BVec using (RelatorFunctor ; RelatorSetoid)
  open Bisimilarity using (TreeSetoid)

  fix-coalg : Coalgebra (RelatorFunctor {ℓ-zero} {ℓ-zero})
  fix-coalg .Coalgebra.carrier = TreeSetoid
  fix-coalg .Coalgebra.str = setoidhom (Relation.rel⇒ coalg coalg-pres) where
    coalg : Tree → ΣVec Tree
    coalg = fix⁻

    coalg-pres : PreservesRel _≈_ (Relator _≈_) coalg
    coalg-pres = fix⁻-preserves-≈

  fix-is-terminal : isTerminalCoalgebra RelatorFunctor fix-coalg
  fix-is-terminal (coalgebra {carrier = S} γ) = SQ.elimProp
    {P = λ γ → isContr (CoalgebraHom RelatorFunctor (coalgebra γ) fix-coalg)}
    (λ _ → isPropIsContr) coalg-lift-eq-pre γ where
    module _ {S : Setoid _ _} (γ-rel@(Relation.rel⇒ γ γ-preserves) : PreSetoidHom S (RelatorSetoid S)) where
      open CoalgebraHom
      open Rel[_⇒_]

      anaPre : PreSetoidHom S TreeSetoid
      anaPre .morphism = unfold γ
      anaPre .preserves-relation s≈s' = bisim λ { n → approx n s≈s' } where abstract
        approx : ∀ n {x y} → RelOf S x y → Approx n (step γ n x) (step γ n y)
        approx zero r = tt*
        approx (suc n) r = Relator-map (RelOf S) _ (approx n) (γ-preserves r)

      ana : CoalgebraHom RelatorFunctor (coalgebra SQ.[ γ-rel ]) fix-coalg
      ana .carrierHom = setoidhom anaPre
      ana .strHom = goal where abstract
        goal : IsCoalgebraHom RelatorFunctor (coalgebra SQ.[ γ-rel ]) fix-coalg (setoidhom anaPre)
        goal = cong SQ.[_] (Relation.Rel⇒Path (isCoalgebraMorphismUnfold γ))

      module _ (f : PreSetoidHom S TreeSetoid) (f-hom : IsCoalgebraHom _ (coalgebra SQ.[ γ-rel ]) fix-coalg (setoidhom f)) where
        f-hom-eff : (x : ⟨ S ⟩) → Relator _≈_ (fix⁻ (f .morphism x)) (BVec.map (f .morphism) (γ x))
        f-hom-eff x = effective f-hom x

        anaEq' : setoidhom anaPre ≡ setoidhom f
        anaEq' = SQ.eq/ _ _ λ (s : ⟨ S ⟩) → Bisimilarity.isSymBisim _ _ (unfold-unique γ (f .morphism) f-hom-eff s)

      anaEq : (f : CoalgebraHom RelatorFunctor (coalgebra SQ.[ γ-rel ]) fix-coalg) → ana ≡ f
      anaEq (coalgebraHom f* f-hom) = SQ.elimProp {P = λ f → (h : IsCoalgebraHom _ (coalgebra SQ.[ γ-rel ]) fix-coalg f) → ana ≡ coalgebraHom f h}
        (λ f → isPropΠ λ h → isSetCoalgebraHom _ _ (coalgebraHom f h))
        (λ f f-hom → CoalgebraHom≡ _ (anaEq' f f-hom)) f* f-hom


      coalg-lift-eq-pre : isContr (CoalgebraHom RelatorFunctor (coalgebra SQ.[ γ-rel ]) fix-coalg)
      coalg-lift-eq-pre = ana , anaEq

  finalSetoidCoalgebra : TerminalCoalgebra RelatorFunctor
  finalSetoidCoalgebra = fix-coalg , fix-is-terminal
