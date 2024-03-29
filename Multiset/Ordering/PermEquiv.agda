{-# OPTIONS --safe #-}

module Multiset.Ordering.PermEquiv where

open import Cubical.Foundations.Everything
open import Cubical.Functions.FunExtEquiv
open import Cubical.Data.List as List
open import Cubical.Data.Sigma
open import Cubical.HITs.PropositionalTruncation as PT
open import Multiset.ListQuotient.Base
open import Multiset.Ordering.Order
open import Multiset.ListQuotient.FMSetEquiv


-- Proof of equivalence between ∥ Perm xs ys ∥₁ and Relator _≡_ xs ys

permDRelator : ∀{ℓ}{X : Type ℓ} xs {ys : List X} {x y}
  → DRelator _≡_ (xs ++ x ∷ y ∷ ys) (xs ++ y ∷ x ∷ ys)
permDRelator [] =
  cons ∣ _ , refl , there (here refl) ,
        cons ∣ _ , refl , here refl , reflDRelator (λ _ → refl) _ ∣₁ ∣₁
permDRelator (x ∷ xs) =
  cons ∣ _ , refl , here refl , permDRelator xs ∣₁

Perm→Relator= : {A : Type} {xs ys : List A}
  → Perm xs ys → Relator _≡_ xs ys
Perm→Relator= stop = reflRelator (λ _ → refl) _
Perm→Relator= (perm p) =
  transDRelator _∙_ (permDRelator _) (Perm→Relator= p .fst) ,
  transDRelator _∙_ (Perm→Relator= p .snd) (permDRelator _)

removeDRelator'' : ∀{ℓ}{X : Type ℓ}
  → {R : X → X → Type ℓ}
  → (∀ x → R x x)
  → ∀ {xs} {x : X} (m : x ∈ xs)
  → DRelator R (x ∷ remove xs m) xs
removeDRelator'' {R = R} reflR (here eq) =
  cons ∣ _ , subst (R _) eq (reflR _) , here refl , reflDRelator reflR _ ∣₁
removeDRelator'' {R = R} reflR (there m) =
  cons ∣ _ , reflR _ , there m , reflDRelator reflR _ ∣₁

emptyDRelator : {A : Type} {ys : List A}
  → DRelator _≡_ ys [] → ∥ ys ≡ [] ∥₁
emptyDRelator nil = ∣ refl ∣₁
emptyDRelator (cons p) = PT.map (λ { (y , eq , () , p') }) p

removePerm : {A : Type} {ys : List A} {y : A}
  → (y∈ys : y ∈ ys)
  → Perm (y ∷ remove ys y∈ys) ys
removePerm (here eq) = subst (λ z → Perm _ (z ∷ _)) eq stop
removePerm (there y∈ys) =
  perm {xs = []} (congPerm (removePerm y∈ys))

Relator=→∥Perm∥₁ : {A : Type} {xs ys : List A}
  → Relator _≡_ xs ys → ∥ Perm xs ys ∥₁
Relator=→∥Perm∥₁ (nil , q) =
  PT.map (λ eq → subst (Perm []) (sym eq) stop) (emptyDRelator q)
Relator=→∥Perm∥₁ (cons p , q) =
  PT.rec isPropPropTrunc
         (λ { (y , eq , y∈ys , p') →
           PT.rec isPropPropTrunc
                  (λ { (y' , eq' , here x , q') →
                    PT.map (λ r → transP (congPerm r)
                                          (subst (λ z → Perm (z ∷ remove _ y∈ys) _)
                                                 (sym eq)
                                                 (removePerm y∈ys)))
                           (Relator=→∥Perm∥₁ (p' , q'))
                     ; (y' , eq' , there m , q') →
                    PT.map (λ r → transP (congPerm r)
                                          (subst (λ z → Perm (z ∷ remove _ y∈ys) _)
                                                 (sym eq)
                                                 (removePerm y∈ys)))
                           (Relator=→∥Perm∥₁ (p' ,
                                           transDRelator _∙_ q'
                                                         (subst (λ z → DRelator _≡_ (z ∷ _) _)
                                                                (sym eq' ∙ sym eq)
                                                                (removeDRelator'' (λ _ → refl) m)))) })
                  (memDRelator y∈ys q) })
         p


∥Perm∥₁≃Relator= : {A : Type} {xs ys : List A}
  → ∥ Perm xs ys ∥₁ ≃ Relator _≡_ xs ys
∥Perm∥₁≃Relator= =
  propBiimpl→Equiv isPropPropTrunc
                   (isPropRelator _≡_ _ _)
                   (PT.rec (isPropRelator _≡_ _ _) Perm→Relator=)
                   Relator=→∥Perm∥₁

∥Perm∥₁≡Relator≡ : {A : Type} →
  (λ xs ys → ∥ Perm xs ys ∥₁) ≡ Relator _≡_
∥Perm∥₁≡Relator≡ {A} = funExt₂ λ { xs ys → ua (∥Perm∥₁≃Relator= {A = A} {xs = xs} {ys = ys}) }

-- ====================================================


permDRelatorΣ : ∀{ℓ}{X : Type ℓ} xs {ys : List X} {x y}
  → DRelatorΣ _≡_ (xs ++ x ∷ y ∷ ys) (xs ++ y ∷ x ∷ ys)
permDRelatorΣ [] =
  cons (_ , refl , there (here refl) ,
         cons (_ , refl , here refl , reflDRelatorΣ (λ _ → refl) _))
permDRelatorΣ (x ∷ xs) =
  cons (_ , refl , here refl , permDRelatorΣ xs)

Perm→RelatorΣ= : {A : Type} {xs ys : List A}
  → Perm xs ys → RelatorΣ _≡_ xs ys
Perm→RelatorΣ= stop = reflRelatorΣ (λ _ → refl) _
Perm→RelatorΣ= (perm p) =
  transDRelatorΣ _∙_ (permDRelatorΣ _) (Perm→RelatorΣ= p .fst) ,
  transDRelatorΣ _∙_ (Perm→RelatorΣ= p .snd) (permDRelatorΣ _)

--removeDRelatorΣ'' : ∀{ℓ}{X : Type ℓ}
--  → {R : X → X → Type ℓ}
--  → (∀ x → R x x)
--  → ∀ {xs} {x : X} (m : x ∈ xs)
--  → DRelatorΣ R (x ∷ remove xs m) xs
--removeDRelatorΣ'' {R = R} reflR (here eq) =
--  cons (_ , subst (R _) eq (reflR _) , here refl , reflDRelatorΣ reflR _)
--removeDRelatorΣ'' {R = R} reflR (there m) =
--  cons (_ , reflR _ , there m , reflDRelatorΣ reflR _)
--
--emptyDRelatorΣ : {A : Type} {ys : List A}
--  → DRelatorΣ _≡_ ys [] → ys ≡ []
--emptyDRelatorΣ nil = refl
--emptyDRelatorΣ (cons (y , eq , () , p))
--
--RelatorΣ=→Perm : {A : Type} {xs ys : List A}
--  → RelatorΣ _≡_ xs ys → Perm xs ys
--RelatorΣ=→Perm (nil , q) =
--  subst (Perm []) (sym (emptyDRelatorΣ q)) stop
--RelatorΣ=→Perm (cons (y , eq , y∈ys , p') , q) with memDRelatorΣ y∈ys q
--... | (y' , eq' , here x , q') =
--  transP (congPerm (RelatorΣ=→Perm (p' , q')))
--         (subst (λ z → Perm (z ∷ remove _ y∈ys) _)
--                (sym eq)
--                (removePerm y∈ys))
--... | (y' , eq' , there m , q') =
--  transP (congPerm (RelatorΣ=→Perm (p' , transDRelatorΣ _∙_ q'
--                                                        (subst (λ z → DRelatorΣ _≡_ (z ∷ _) _)
--                                                               (sym eq' ∙ sym eq)
--                                                               (removeDRelatorΣ'' (λ _ → refl) m)))))
--         (subst (λ z → Perm (z ∷ remove _ y∈ys) _)
--                (sym eq)
--                (removePerm y∈ys))
