{-# OPTIONS --safe #-}

module Multiset.ListQuotient.Finality where

open import Multiset.Prelude
open import Multiset.ListQuotient.ListFinality
  using
    ( FunctorΣVec
    ; !^
    ; cut
    ; Tree
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
open import Multiset.Omniscience using (LLPO)
open import Multiset.Setoid.Base using (SetoidMorphism ; IsSetoidMorphism)
open import Multiset.Relation.Base as Relation
  using
    ( Relation
    ; ReflectsRel
    ; PreservesRel
    ; PreservesRelation
    ; PreservesRel→SectionReflectsRel
    ; Rel[_⇒_]
    )
open import Multiset.Coalgebra using (isCoalgebraMorphism)
open import Multiset.Categories.Coalgebra using (TerminalCoalgebra)

open import Cubical.Foundations.Function using (_∘_)
open import Cubical.Foundations.Equiv
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

module _
  (C : Relation ℓ-zero ℓ-zero)
  (γ-hom : Rel[ C ⇒ RelatorRelation C ]) where
  open Relation using (⟨_⟩ ; RelOf)

  open Rel[_⇒_] γ-hom
    renaming
      ( morphism to γ
      ; preserves-relation to γ-preserves-R
      )
  open Rel[_⇒_]

  private
    R = RelOf C

    _ : ⟨ C ⟩ → ΣVec ⟨ C ⟩
    _ = γ

  -- (unfold γ) is a setoid morphism
  unfold-hom : Rel[ C ⇒ BisimRelation ]
  unfold-hom .morphism = unfold γ
  unfold-hom .preserves-relation r = bisim (λ n → approx n r) where
    approx : ∀ n {x y} → R x y → Approx n (step γ n x) (step γ n y)
    approx zero r = tt*
    approx (suc n) r = Relator-map R _ (approx n) (γ-preserves-R r)


  -- unfold γ is a coalgebra-morphism from `γ` to `fix⁻`, up to the relation `Relator _≈_`
  unfold-coalg-morphism-γ-fix⁻ : ∀ x → Relator _≈_ (fix⁻ (unfold γ x)) (map (unfold γ) (γ x))
  unfold-coalg-morphism-γ-fix⁻ x =
    let
      open BVec.Reasoning Bisim isReflBisim isTransBisim using (Path→Rel)
    in Path→Rel (funExt⁻ (isCoalgebraMorphismUnfold γ) x)

-- uniqueness of unfold
  unfold-unique' : (f : ⟨ C ⟩ → Tree)
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
    where
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

  unfold-unique : (f : ⟨ C ⟩ → Tree)
    → (∀ x → Relator _≈_ (fix⁻ (f x)) (map f (γ x)))
    → ∀ x → f x ≈ unfold γ x
  unfold-unique f feq x =
    bisim (unfold-unique' f (λ y → isTransBisim _ _ _ (Path→Bisim (sym (secEq fix (f y)))) (fix⁺-preserves-≈ (feq y))) x)

module _
  (coalg : Tree → ΣVec Tree)
  (unfold-is-coalg-morphism : {C : Type} → (γ : C → ΣVec C) → isCoalgebraMorphism ΣVec γ coalg (unfold γ))
  (coalg-pres : PreservesRelation BisimRelation (RelatorRelation BisimRelation) coalg)
  where
  unfold-coalg : TerminalCoalgebra $ BVec.RelatorFunctor {ℓ = ℓ-zero} {ℓR = ℓ-zero}
  unfold-coalg = coalg-lift , coalg-lift-eq where
    open import Multiset.Categories.Coalgebra
    open Coalgebra
    open CoalgebraHom
    open Relation using (⟨_⟩ ; _⋆Rel⇒_ ; RelOf)

    open BVec using (RelatorFunctor)
    open Rel[_⇒_]

    coalg-lift : Coalgebra RelatorFunctor
    coalg-lift .carrier = BisimRelation
    coalg-lift .str .morphism = coalg
    coalg-lift .str .preserves-relation = coalg-pres

    coalg-lift-eq : isTerminalCoalgebra RelatorFunctor coalg-lift
    coalg-lift-eq γ-coalg = ana , anaEq where
      C = ⟨ γ-coalg .carrier ⟩
      R = RelOf (γ-coalg .carrier)

      open Rel[_⇒_] (γ-coalg .str)
        renaming
          ( morphism to γ
          ; preserves-relation to γ-preserves-R
          )

      ana : CoalgebraHom _ _ _
      ana .carrierHom = unfold-hom (γ-coalg .carrier) (γ-coalg .str)
      ana .strHom = Relation.Rel⇒Path (unfold-is-coalg-morphism γ)

      module _ (f : CoalgebraHom RelatorFunctor γ-coalg coalg-lift) where
        anaEq' : unfold γ ≡ f .carrierHom .morphism
        anaEq' = {! !}

        anaEq : ana ≡ f
        anaEq = CoalgebraHom≡ RelatorFunctor (Relation.Rel⇒Path anaEq')

-- TODO: Instanciate the above module to fix⁻ and the fact that unfold is a coalgebra-morphism
