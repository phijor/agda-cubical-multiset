module Multiset.Coinductive.ToInjectivity where

open import Multiset.Prelude
open import Multiset.Util using (!_ ; isInjective ; isSurjective)

open import Multiset.Chains
open import Multiset.Chains.FunctorChain

open import Multiset.Omniscience using (LLPO)

open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Function using (_∘_)
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.HLevels

open import Cubical.Data.Unit as Unit using (Unit ; tt)
open import Cubical.Data.Empty as Empty
open import Cubical.Data.List as List hiding ([_])
open import Cubical.Data.Sigma as Sigma
open import Cubical.Data.Sum as Sum using (_⊎_ ; inl ; inr)
open import Cubical.Data.Nat.Base hiding (_^_)
open import Cubical.Data.Nat.Order as NatOrder
open import Cubical.Data.Bool --.Base as Bool
--  using (Bool ; if_then_else_ ; true ; false ; _and_ ; not; _or_)

open import Cubical.Relation.Nullary

open import Cubical.HITs.PropositionalTruncation as PT
  using
    ( ∥_∥₁
    ; ∣_∣₁
    )

open import Cubical.HITs.SetQuotients as ST

open import Multiset.Coinductive.ListStuff

instance
  FunctorM : Functor M
  FunctorM .Functor.map = mapM
  FunctorM .Functor.map-id = mapM-id
  FunctorM .Functor.map-comp = mapM-comp

open Limit.ChainLimit

decEqM^ : (n : ℕ) → Discrete (M ^ n)
decEqM^ zero xs ys = yes refl
decEqM^ (suc n) = decEqM (decEqM^ n) 

dec∈M^ : (n : ℕ) (x : M ^ n) (ys : List (M ^ n)) → Dec (x ∈ ys)
dec∈M^ n x ys with dec∈ (decEqM^ n) x ys
... | yes (y , m , p) = yes (subst (λ z → z ∈ ys) (sym p) m)
... | no ¬p = no (λ m → ¬p (x , m , refl))

!^ : ∀ n → M ^ (suc n) → M ^ n
!^ n = M map-!^ n

≤-suc-cases : ∀ k n → k NatOrder.≤ suc n
  → (k NatOrder.≤ n) ⊎ (k ≡ suc n)
≤-suc-cases zero n le = inl zero-≤
≤-suc-cases (suc k) zero le = inr (cong suc (≤0→≡0 (pred-≤-pred le)))
≤-suc-cases (suc k) (suc n) le with ≤-suc-cases k n (pred-≤-pred le)
... | inl p = inl (suc-≤-suc p)
... | inr p = inr (cong suc p)

rep!^ : ∀ n k → NatOrder._≤_ k n → M ^ n → M ^ k
rep!^ zero k k≤n x = J (λ k _ → M ^ k) x (sym (≤0→≡0 k≤n))
rep!^ (suc n) k k≤n x with ≤-suc-cases k n k≤n
... | inl p = rep!^ n k p (!^ n x)
... | inr p = J (λ k _ → M ^ k) x (sym p)

isSetUnorderedTree : ∀ {n} → isSet (M ^ n)
isSetUnorderedTree {zero} = Unit.isSetUnit
isSetUnorderedTree {suc n} = isSetM

limitPath : ∀ {lim₁ lim₂} → (∀ n → lim₁ .elements n ≡ lim₂ .elements n) → lim₁ ≡ lim₂
limitPath = Limit.isSet→ChainLimitPathExt (ch M) (λ k → isSetUnorderedTree {k})

shiftedLimitPath : ∀ {shlim₁ shlim₂} → (∀ n → shlim₁ .elements n ≡ shlim₂ .elements n) → shlim₁ ≡ shlim₂
shiftedLimitPath = Limit.isSet→ChainLimitPathExt (shift (ch M)) (λ k → isSetM)

module _ where
  open Limit
  open ChainLimit

  cut : (n : ℕ) → Lim M → M ^ n
  cut n l = l .elements n

  zip₁ : M (Lim M) → ∀ n → M (M ^ n)
  zip₁ xs n = mapM (cut n) xs

  zip₁-islim : (xs : M (Lim M)) → isShLim M (zip₁ xs)
  zip₁-islim xs n =
    sym (mapM-comp (!^ n) (cut (suc n)) xs)
    ∙ cong (λ f → mapM f xs) (funExt (λ l → l .isChainLimit n))

zip : M (Lim M) → ShLim M
zip xs .Limit.ChainLimit.elements = zip₁ xs
zip xs .Limit.ChainLimit.isChainLimit = zip₁-islim xs


rep!Eq : (x : Lim M)
  → ∀ n k (le : k NatOrder.≤ n)
  → rep!^ n k le (cut n x) ≡ cut k x
rep!Eq x zero k le =
  J (λ k eq → J (λ k _ → M ^ k) (cut 0 x) eq ≡ cut k x) (JRefl {x = 0} (λ k _ → M ^ k) _) (sym (≤0→≡0 le))
rep!Eq x (suc n) k le with ≤-suc-cases k n le
... | inl p = cong (rep!^ n k p) (x .isChainLimit n) ∙ rep!Eq x n k p
... | inr p = J (λ k eq → J (λ k _ → M ^ k) (cut (suc n) x) eq ≡ cut k x) (JRefl {x = suc n} (λ k _ → M ^ k) _) (sym p)

parity : (a : ℕ → Bool) → Bool → ℕ → Bool
parity a b zero = (a 0 and b) or (not (a 0) and (not b))
parity a b (suc n) =
  if (a 0 and b) or (not (a 0) and (not b))
    then false
    else parity (a ∘ suc) (not b) n

parity-prop' : ∀ a b (n1 n2 : ℕ)
  → parity a b n1 ≡ true → parity a b n2 ≡ true
  → n1 ≡ n2
parity-prop' a b zero zero p q = refl
parity-prop' a b zero (suc n2) p q with a 0
parity-prop' a false zero (suc n2) p q | false = Empty.rec (false≢true q) 
parity-prop' a true zero (suc n2) p q | false = Empty.rec (false≢true p) 
parity-prop' a false zero (suc n2) p q | true = Empty.rec (false≢true p) 
parity-prop' a true zero (suc n2) p q | true = Empty.rec (false≢true q) 
parity-prop' a b (suc n1) zero p q with a 0
parity-prop' a false (suc n1) zero p q | false = Empty.rec (false≢true p) 
parity-prop' a true (suc n1) zero p q | false = Empty.rec (false≢true q) 
parity-prop' a false (suc n1) zero p q | true = Empty.rec (false≢true q) 
parity-prop' a true (suc n1) zero p q | true = Empty.rec (false≢true p) 
parity-prop' a b (suc n1) (suc n2) p q with a 0
parity-prop' a false (suc n1) (suc n2) p q | false = Empty.rec (false≢true p) 
parity-prop' a true (suc n1) (suc n2) p q | false =
  cong suc (parity-prop' (a ∘ suc) false n1 n2 p q)
parity-prop' a false (suc n1) (suc n2) p q | true =
    cong suc (parity-prop' (a ∘ suc) true n1 n2 p q)
parity-prop' a true (suc n1) (suc n2) p q | true = Empty.rec (false≢true p)

parity-prop : ∀ a b → isProp (Σ[ n ∈ ℕ ] parity a b n ≡ true)
parity-prop a b (n1 , eq1) (n2 , eq2) =
  Σ≡Prop (λ _ → isSetBool _ _) (parity-prop' a b n1 n2 eq1 eq2)

even-not-odd : ∀ n → isEvenT n → isOddT n → ⊥
even-not-odd (suc n) p q = even-not-odd n q p


isEven? : Bool → ℕ → Type
isEven? false n = isOddT n
isEven? true n = isEvenT n

decEven : ∀ n → isEvenT n ⊎ isOddT n
decEven zero = inl _
decEven (suc n) = Sum.rec inr inl (decEven n)

parity-even : (a : ℕ → Bool) 
  → ∀ n → isEvenT n
  → parity a true n ≡ false → a n ≡ true
  → Σ[ k ∈ ℕ ] Σ[ b ∈ Bool ] isEven? b k × (k < n) × (a k ≡ b) × (parity a true k ≡ true)
parity-even' : (a : ℕ → Bool) 
  → ∀ n → isOddT n
  → parity a false n ≡ false → a n ≡ true
  → Σ[ k ∈ ℕ ] Σ[ b ∈ Bool ] isEven? b k × (k < n) × (a k ≡ not b) × (parity a false k ≡ true)


parity-even a zero ev eqf eqt =
  Empty.rec (true≢false (sym (cong (λ b → b and true or not b and false) eqt) ∙  eqf))
parity-even a (suc n) ev eqf eqt with dichotomyBool (a 0)
... | inl q = 0 , true , _ , suc-≤-suc zero-≤ , q , cong (λ b → b and true or not b and false) q  
... | inr q with parity-even' (a ∘ suc) n ev (sym (cong (λ b → if b and true or not b and false then false else parity (a ∘ suc) false n) q) ∙ eqf) eqt
... | k , false , p , le , eq' , r = _ , _ , p , suc-≤-suc le , eq' , cong (λ b → if b and true or not b and false then false else parity (a ∘ suc) false k) q ∙ r
... | k , true , p , le , eq' , r = _  , _ , p , suc-≤-suc le , eq' , cong (λ b → if b and true or not b and false then false else parity (a ∘ suc) false k) q ∙ r

parity-even' a (suc n) ev eqf eqt with dichotomyBool (a 0)
... | inr q = 0 , true , _ , suc-≤-suc zero-≤ , q , cong (λ b → b and false or not b and true) q  
... | inl q with parity-even (a ∘ suc) n ev (sym (cong (λ b → if b and false or not b and true then false else parity (a ∘ suc) true n) q) ∙ eqf) eqt
... | k , false , p , le , eq' , r = _ , _ , p , suc-≤-suc le , eq' , cong (λ b → if b and false or not b and true then false else parity (a ∘ suc) true k) q ∙ r
... | k , true , p , le , eq' , r = _ , _ , p , suc-≤-suc le , eq' , cong (λ b → if b and false or not b and true then false else parity (a ∘ suc) true k) q ∙ r

parity-odd : (a : ℕ → Bool) 
  → ∀ n → isOddT n
  → parity a true n ≡ false → a n ≡ false
  → Σ[ k ∈ ℕ ] Σ[ b ∈ Bool ] isEven? b k × (k < n) × (a k ≡ b) × (parity a true k ≡ true)
parity-odd' : (a : ℕ → Bool) 
  → ∀ n → isEvenT n
  → parity a false n ≡ false → a n ≡ false
  → Σ[ k ∈ ℕ ] Σ[ b ∈ Bool ] isEven? b k × (k < n) × (a k ≡ not b) × (parity a false k ≡ true)

parity-odd a (suc n) odd eqt eqf with dichotomyBool (a 0)
... | inl q = 0 , true , _ , suc-≤-suc zero-≤ , q , cong (λ b → b and true or not b and false) q
... | inr q with parity-odd' (a ∘ suc) n odd ((sym (cong (λ b → if b and true or not b and false then false else parity (a ∘ suc) false n) q) ∙ eqt)) eqf
... | k , false , p , le , eq' , r = _ , _ , p , suc-≤-suc le , eq' , cong (λ b → if b and true or not b and false then false else parity (a ∘ suc) false k) q ∙ r
... | k , true , p , le , eq' , r = _ , _ , p , suc-≤-suc le , eq' , cong (λ b → if b and true or not b and false then false else parity (a ∘ suc) false k) q ∙ r

parity-odd' a zero _ eqt eqf =
  Empty.rec (true≢false (sym (cong (λ b → b and false or not b and true) eqf) ∙ eqt))
parity-odd' a (suc n) odd eqt eqf with dichotomyBool (a 0)
... | inr q = 0 , true , _ , suc-≤-suc zero-≤ , q , cong (λ b → b and false or not b and true) q
... | inl q with parity-odd (a ∘ suc) n odd ((sym (cong (λ b → if b and false or not b and true then false else parity (a ∘ suc) true n) q) ∙ eqt)) eqf
... | k , false , p , le , eq' , r = _ , _ , p , suc-≤-suc le , eq' , cong (λ b → if b and false or not b and true then false else parity (a ∘ suc) true k) q ∙ r
... | k , true , p , le , eq' , r = _ , _ , p , suc-≤-suc le , eq' , cong (λ b → if b and false or not b and true then false else parity (a ∘ suc) true k) q ∙ r

llpo⇒zip-inj : LLPO → isInjective zip
llpo⇒zip-inj llpo =
  elimProp2 (λ _ _ → isPropΠ (λ _ → isSetM _ _))
            (λ xs ys zip-eq →
              eq/ _ _ (zip-inj' xs ys
                         (λ n → effective (isPropRelator _≡_)
                                           (isEquivRelRelator isEquivRel≡)
                                           _ _
                                           (funExt⁻ (cong Limit.ChainLimit.elements zip-eq) n) .fst) ,
                       zip-inj' ys xs
                         (λ n → effective (isPropRelator _≡_)
                                           (isEquivRelRelator isEquivRel≡)
                                           _ _
                                           (funExt⁻ (cong Limit.ChainLimit.elements (sym zip-eq)) n) .fst)))
  where
    compl :  (x : Lim M) (ys : List (Lim M))
      → (∀ n → ∥ cut n x ∈ List.map (cut n) ys ∥₁)
      → ∥ x ∈ ys ∥₁
    compl x [] ms = PT.map (λ { () }) (ms 0)
    compl x (y ∷ ys) ms =
      PT.rec PT.isPropPropTrunc
             (Sum.rec (λ r → ∣ here (limitPath (case-even-gen r)) ∣₁) 
                      λ r → PT.map there (compl x ys (λ n → ∣ case-odd-gen r n ∣₁))) 
             magic
      where
        a : ℕ → Bool
        a n with decEven n
        ... | inl _ = not (Dec→Bool (decEqM^ n (cut n x) (cut n y)))
        ... | inr _ = Dec→Bool (dec∈M^ n (cut n x) (List.map (cut n) ys))
            
        par : ℕ → Bool
        par = parity a true

        magic : ∥ ((n : ℕ) → isEvenT n → par n ≡ false) ⊎
                  ((n : ℕ) → isOddT n → par n ≡ false) ∥₁
        magic = llpo par (parity-prop _ true)

        a-even : ∀ n → isEvenT n
          → (cut n x ≡ cut n y → ⊥) 
          → a n ≡ true
        a-even n ev mn with decEven n
        ... | inr odd = Empty.rec (even-not-odd n ev odd)
        ... | inl ev' with decEqM^ n (cut n x) (cut n y)
        ... | yes q = Empty.rec (mn q)
        ... | no ¬q = refl

        a-odd : ∀ n → isOddT n
          → (cut n x ∈ List.map (cut n) ys → ⊥) 
          → a n ≡ false
        a-odd n odd mn with decEven n
        ... | inl ev = Empty.rec (even-not-odd n ev odd)
        ... | inr _ with dec∈M^ n (cut n x) (List.map (cut n) ys)
        ... | yes p = Empty.rec (mn p)
        ... | no ¬p = refl
    
        ¬¬case-even : (∀ n → isEvenT n → par n ≡ false)
          → ∀ n → isEvenT n → (cut n x ≡ cut n y → ⊥) → ⊥
        ¬¬case-even r n evn ¬mn with parity-even a n evn (r n evn) (a-even n evn ¬mn)
        ... | k , true , evk , le , c , eqk = false≢true (sym (r k evk) ∙ eqk)
        ... | k , false , oddk , le , c , eqk with decEven k
        ... | inl evk = Empty.rec (even-not-odd k evk oddk)
        ... | inr _ with dec∈M^ k (cut k x) (List.map (cut k) ys)
        ... | yes mk = Empty.rec (true≢false c)
        ... | no ¬mk =
          PT.rec isProp⊥
                 (λ msn →
                   Sum.rec (λ mn → ¬mn (mn .fst))
                           (λ mn →
                             let (y , my , eqy) = pre∈mapList (mn .fst) in
                               ¬mk (subst (λ z → z ∈ List.map (cut k) ys)
                                          (sym (rep!Eq y n k (<-weaken le))
                                            ∙ cong (rep!^ n k (<-weaken le)) eqy
                                            ∙ rep!Eq x n k (<-weaken le))
                                          (∈mapList my)))
                           (inv∈ msn))
                 (ms n)

        ¬¬case-odd : (∀ n → isOddT n → par n ≡ false)
          → ∀ n → isOddT n → (cut n x ∈ List.map (cut n) ys → ⊥) → ⊥
        ¬¬case-odd r n oddn ¬mn with parity-odd a n oddn (r n oddn) (a-odd n oddn ¬mn)
        ... | k , false , oddk , le , c , eqk = false≢true (sym (r k oddk) ∙ eqk)
        ... | k , true , evk , le , c , eqk with decEven k
        ... | inr oddk = Empty.rec (even-not-odd k evk oddk)
        ... | inl _ with decEqM^ k (cut k x) (cut k y)
        ... | yes mk = Empty.rec (false≢true c)
        ... | no ¬mk =
          PT.rec isProp⊥
                 (λ msn →
                   Sum.rec (λ mn → ¬mk (sym (rep!Eq x n k (<-weaken le))
                                          ∙ cong (rep!^ n k (<-weaken le)) (mn .fst)
                                          ∙ rep!Eq y n k (<-weaken le)))
                           (λ mn → ¬mn (mn .fst))
                           (inv∈ msn))
                 (ms n)

        case-even : (∀ n → isEvenT n → par n ≡ false)
          → ∀ n → isEvenT n → cut n x ≡ cut n y
        case-even r n ev with decEqM^ n (cut n x) (cut n y)
        ... | yes p = p
        ... | no ¬p = Empty.rec (¬¬case-even r n ev ¬p)

        case-even-gen : (∀ n → isEvenT n → par n ≡ false)
          → ∀ n → cut n x ≡ cut n y
        case-even-gen r n with decEven n
        ... | inl ev = case-even r n ev
        ... | inr odd =
          sym (x .isChainLimit n)
          ∙ cong (!^ n) (case-even r (suc n) odd)
          ∙ y .isChainLimit n

        case-odd : (∀ n → isOddT n → par n ≡ false)
          → ∀ n → isOddT n → cut n x ∈ List.map (cut n) ys
        case-odd r n ev with dec∈M^ n (cut n x) (List.map (cut n) ys)
        ... | yes p = p
        ... | no ¬p = Empty.rec (¬¬case-odd r n ev ¬p)

        case-odd-gen : (∀ n → isOddT n → par n ≡ false)
          → ∀ n → cut n x ∈ List.map (cut n) ys
        case-odd-gen r n with decEven n
        ... | inr odd = case-odd r n odd
        ... | inl ev =
          let (y , my , eqy) = pre∈mapList (case-odd r (suc n) ev)
          in subst (λ z → z ∈ List.map (cut n) ys)
                   (sym (y .isChainLimit n)
                    ∙ cong (!^ n) eqy
                    ∙ x .isChainLimit n)
                   (∈mapList my)

    zip-inj' : (xs ys : List (Lim M))
      → (∀ n → DRelator _≡_ (List.map (cut n) xs) (List.map (cut n) ys))
      → DRelator _≡_ xs ys
    zip-inj' [] ys drel = nil
    zip-inj' (x ∷ xs) ys drel =
      PT.rec (isPropDRelator _ _ _)
        (λ m → cons ∣ x ,
                      refl ,
                      m ,
                      zip-inj' xs (remove ys m)
                        (λ n → PT.rec (isPropDRelator _ _ _)
                                       (λ d →  subst (DRelator _≡_ (map (cut n) xs))
                                                     (sym (remove-mapList m))
                                                     (transDRelator _∙_ (d .snd) (removeDRelator (λ _ → refl) (d .fst) (∈mapList m))) )
                                        (drel∃ n)) ∣₁)
        (compl x ys λ n → PT.map fst (drel∃ n) )
        where
        drel∃ : ∀ n → ∃[ m ∈ (cut n x ∈ List.map (cut n) ys) ]
          DRelator _≡_ (List.map (cut n) xs)  (remove (List.map (cut n) ys) m)
        drel∃ n =
          PT.map
            (λ { (y , p , r) →
              J (λ z _ → Σ (z ∈ map (cut n) ys) (λ m → DRelator _≡_ (map (cut n) xs) (remove (map (cut n) ys) m))) r (sym p) })
            (consInvDRelator (drel n))



    
