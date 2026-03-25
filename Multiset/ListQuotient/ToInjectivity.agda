{-# OPTIONS --safe #-}

module Multiset.ListQuotient.ToInjectivity where

open import Multiset.Prelude
open import Multiset.Util using (!_ ; isInjective ; isSurjective)
open import Multiset.ListQuotient.Base

open import Multiset.Limit.Chain using (Limit)
import      Multiset.Axioms.Completeness as Completeness
open import Multiset.Limit.TerminalChain as TerminalChain hiding (cut ; pres)

open import Multiset.Omniscience using (LLPO)

open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Function using (_∘_)
open import Cubical.Foundations.HLevels

open import Cubical.Data.Unit as Unit using (Unit ; tt)
open import Cubical.Data.List as List hiding ([_])
open import Cubical.Data.Sigma as Sigma
open import Cubical.Data.Nat.Base hiding (_^_)

open import Cubical.Relation.Nullary

open import Cubical.HITs.PropositionalTruncation as PT
  using
    ( ∥_∥₁
    ; ∣_∣₁
    )
open import Cubical.HITs.PropositionalTruncation.Monad using (_>>=_ ; _>>_ ; return)

open import Cubical.HITs.SetQuotients as SQ

instance
  FunctorM : Functor M
  FunctorM .Functor.map = mapM
  FunctorM .Functor.map-id = mapM-id
  FunctorM .Functor.map-comp = mapM-comp

open Limit

decEqM^ : (n : ℕ) → Discrete (M ^ n)
decEqM^ zero xs ys = yes refl
decEqM^ (suc n) = decEqM (decEqM^ n) 

dec∈M^ : (n : ℕ) (x : M ^ n) (ys : List (M ^ n)) → Dec (x ∈ ys)
dec∈M^ n x ys with dec∈ (decEqM^ n) x ys
... | yes (y , m , p) = yes (subst (λ z → z ∈ ys) (sym p) m)
... | no ¬p = no (λ m → ¬p (x , m , refl))

isSetM^ : ∀ n → isSet (M ^ n)
isSetM^ zero = Unit.isSetUnit*
isSetM^ (suc n) = isSetM

!^ : ∀ n → M ^ (suc n) → M ^ n
!^ n = M map-!^ n

module _ where
  open Limit

  cut : (n : ℕ) → Lim M → M ^ n
  cut = TerminalChain.cut M

pres : M (Lim M) → ShLim M
pres = TerminalChain.pres M

module M-Completeness = Completeness (TerminalChain.ch M) decEqM^ isSetM^

Complete* : Type
Complete* = M-Completeness.Complete*

complete*⇒pres-inj : Complete* → isInjective pres
complete*⇒pres-inj complete* = pres-inj where
  pres-inj-drel : (xs ys : List (Lim M))
    → (∀ n → DRelator _≡_ (List.map (cut n) xs) (List.map (cut n) ys))
    → DRelator _≡_ xs ys
  pres-inj-drel [] ys drel = nil
  pres-inj-drel (x ∷ xs) ys drel = goal where
    drel∃ : ∀ n → ∃[ m ∈ (cut n x ∈ List.map (cut n) ys) ]
      DRelator _≡_ (List.map (cut n) xs)  (remove (List.map (cut n) ys) m)
    drel∃ n = do
      (y , xₙ≡y , r) ← consInvDRelator (drel n)
      return $ subst
        (λ y → Σ[ y∈ysₙ ∈ (y ∈ map (cut n) ys) ] DRelator _≡_ (map (cut n) xs) (remove (map (cut n) ys) y∈ysₙ))
        (sym xₙ≡y)
        r

    x∈ys-approx : ∀ n → ∥ cut n x ∈ map (cut n) ys ∥₁
    x∈ys-approx n = do
      (xₙ∈ysₙ , _) ← drel∃ n
      return xₙ∈ysₙ

    ∥x∈ys∥ : ∥ x ∈ ys ∥₁
    ∥x∈ys∥ = complete* x ys x∈ys-approx

    goal* : x ∈ ys → DRelator _≡_ (x ∷ xs) ys
    goal* x∈ys = cons ∣ x , (refl {x = x}) , x∈ys , ind ∣₁ where
      ys∖x = remove ys x∈ys

      ind-approx : ∀ n → DRelator _≡_ (map (cut n) xs) (map (cut n) ys∖x)
      ind-approx n = equivFun (PT.propTruncIdempotent≃ (isPropDRelator _ _ _)) $ do
        (xₙ∈ysₙ , drel) ← drel∃ n
        let ysₙ = map (cut n) ys
            xsₙ = map (cut n) xs

            xₙ∈ysₙ′ : cut n x ∈ ysₙ
            xₙ∈ysₙ′ = ∈mapList x∈ys

            ysₙ∖xₙ  = remove ysₙ xₙ∈ysₙ
            ysₙ∖xₙ′ = remove ysₙ xₙ∈ysₙ′

            d₁ : DRelator _≡_ ysₙ∖xₙ ysₙ∖xₙ′
            d₁ = removeDRelator (λ _ → refl) xₙ∈ysₙ xₙ∈ysₙ′

            d₂ : DRelator _≡_ xsₙ ysₙ∖xₙ
            d₂ = drel

            d : DRelator _≡_ xsₙ ysₙ∖xₙ′
            d = transDRelator _∙_ d₂ d₁

        let remove-path : remove ysₙ (∈mapList x∈ys) ≡ map (cut n) ys∖x
            remove-path = sym (remove-mapList x∈ys)
        return $ subst (DRelator _≡_ (map (cut n) xs)) remove-path d

      ind : DRelator _≡_ xs ys∖x
      ind = pres-inj-drel _ _ ind-approx

    goal : DRelator _≡_ (x ∷ xs) ys
    goal = PT.rec (isPropDRelator _ _ _) goal* ∥x∈ys∥

  cut-rel : {xs ys : List (Lim M)}
    → (pres-≡ : pres [ xs ] ≡ pres [ ys ])
    → ∀ n → Relator _≡_ (map (cut n) xs) (map (cut n) ys)
  cut-rel {xs} {ys} pres-≡ n = effective (isPropRelator _≡_) (isEquivRelRelator isEquivRel≡) _ _ goal
    where
      goal : [ map (cut n) xs ] ≡ [ map (cut n) ys ]
      goal = cong elements pres-≡ ≡$ n

  module _ (xs ys : List (Lim M)) (pres-≡ : pres [ xs ] ≡ pres [ ys ]) where
    pres-inj-rel : Relator _≡_ xs ys
    pres-inj-rel .fst = pres-inj-drel xs ys (fst ∘ cut-rel pres-≡)
    pres-inj-rel .snd = pres-inj-drel ys xs (snd ∘ cut-rel pres-≡)

    pres-inj* : [ xs ] ≡ [ ys ]
    pres-inj* = SQ.eq/ xs ys pres-inj-rel

  is-prop-pres-inj* : (x y : List (Lim M) / Relator _≡_) → isProp (pres x ≡ pres y → x ≡ y)
  is-prop-pres-inj* x y = isPropΠ λ _ → isSetM x y

  pres-inj : isInjective pres
  pres-inj = SQ.elimProp2 is-prop-pres-inj* pres-inj*

llpo⇒complete* : LLPO → Complete*
llpo⇒complete* = M-Completeness.llpo⇒complete*

llpo⇒pres-inj : LLPO → isInjective pres
llpo⇒pres-inj = complete*⇒pres-inj ∘ llpo⇒complete*
