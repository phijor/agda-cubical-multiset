module Multiset.Axioms.Completeness where

open import Multiset.Prelude
open import Multiset.Functor
open import Multiset.Limit.Chain
open import Multiset.Limit.TerminalChain
open import Multiset.ListQuotient.Base
open import Multiset.Omniscience using (LLPO)

open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Function using (_∘_ ; _$_)
open import Cubical.Data.Bool hiding (_≤_)
open import Cubical.Data.Empty as Empty
open import Cubical.Data.List as List hiding ([_])
open import Cubical.Data.Nat.Base as ℕ hiding (_^_)
open import Cubical.Data.Nat.Order
open import Cubical.Data.Sigma as Sigma
open import Cubical.Data.Sum as Sum using (_⊎_ ; inl ; inr)
open import Cubical.Data.Unit as Unit using (Unit ; tt)
open import Cubical.Relation.Nullary using (Dec ; Discrete ; yes ; no ; ¬_)
open import Cubical.HITs.PropositionalTruncation as PT using (∥_∥₁ ; ∣_∣₁)
open import Cubical.HITs.PropositionalTruncation.Monad using (_>>=_ ; _>>_ ; return)

module Completeness {ℓ}
  (M : Type ℓ → Type ℓ)
  (dec-M : ∀ {X} → Discrete X → Discrete (M X))
  (is-set-M : ∀ {X} → isSet X → isSet (M X))
  ⦃ FM : Functor M ⦄ where

  open Limit

  private
    ≤-suc-cases : ∀ k n → k ≤ suc n
      → (k ≤ n) ⊎ (k ≡ suc n)
    ≤-suc-cases zero n le = inl zero-≤
    ≤-suc-cases (suc k) zero le = inr (cong suc (≤0→≡0 (pred-≤-pred le)))
    ≤-suc-cases (suc k) (suc n) le with ≤-suc-cases k n (pred-≤-pred le)
    ... | inl p = inl (suc-≤-suc p)
    ... | inr p = inr (cong suc p)

    decEqM^ : (n : ℕ) → Discrete (M ^ n)
    decEqM^ zero xs ys = yes refl
    decEqM^ (suc n) = dec-M (decEqM^ n)

    dec∈M^ : (n : ℕ) (x : M ^ n) (ys : List (M ^ n)) → Dec (x ∈ ys)
    dec∈M^ n x ys with dec∈ (decEqM^ n) x ys
    ... | yes (y , m , p) = yes (subst (λ z → z ∈ ys) (sym p) m)
    ... | no ¬p = no (λ m → ¬p (x , m , refl))

    !^ : ∀ n → M ^ (suc n) → M ^ n
    !^ n = M map-!^ n

    rep!^ : ∀ n k → k ≤ n → M ^ n → M ^ k
    rep!^ zero k k≤n x = J (λ k _ → M ^ k) x (sym (≤0→≡0 k≤n))
    rep!^ (suc n) k k≤n x with ≤-suc-cases k n k≤n
    ... | inl p = rep!^ n k p (!^ n x)
    ... | inr p = J (λ k _ → M ^ k) x (sym p)


    isSetM^ : ∀ n → isSet (M ^ n)
    isSetM^ zero = Unit.isSetUnit*
    isSetM^ (suc n) = is-set-M (isSetM^ n)

    limitPath : ∀ {lim₁ lim₂} → (∀ n → lim₁ .elements n ≡ lim₂ .elements n) → lim₁ ≡ lim₂
    limitPath = isSet→LimPath M isSetM^

  -- Completeness: Given a tree (x : Lim M) and a list of trees (ys : List (Lim M)),
  -- LLPO lets us conclude that, if for each depth n, the approximation xₙ of x is (merely) an approximation of one of the ys,
  -- then x is (merely) one of the ys.
  _∣_ : Lim M → (n : ℕ) → M ^ n
  x ∣ n = x .elements n
  infix 20 _∣_

  private
    rep!Eq : (x : Lim M)
      → ∀ n k (le : k ≤ n)
      → rep!^ n k le (x ∣ n) ≡ x ∣ k
    rep!Eq x zero k le =
      J (λ k eq → J (λ k _ → M ^ k) (x ∣ 0) eq ≡ x ∣ k) (JRefl {x = 0} (λ k _ → M ^ k) _) (sym (≤0→≡0 le))
    rep!Eq x (suc n) k le with ≤-suc-cases k n le
    ... | inl p = cong (rep!^ n k p) (x .is-lim n) ∙ rep!Eq x n k p
    ... | inr p = J (λ k eq → J (λ k _ → M ^ k) (x ∣ (suc n)) eq ≡ x ∣ k) (JRefl {x = suc n} (λ k _ → M ^ k) _) (sym p)

  cut-≤ : ∀ (x y : Lim M) {k n} → k ≤ n → (x ∣ n ≡ y ∣ n) → (x ∣ k ≡ y ∣ k)
  cut-≤ x y k≤n p = sym (rep!Eq x _ _ k≤n) ∙ cong (rep!^ _ _ k≤n) p ∙ rep!Eq y _ _ k≤n



  _≈⟨_⟩_ : (x : Lim M) (n : ℕ) → (y : Lim M) → Type _
  x ≈⟨ n ⟩ y = (x ∣ n) ≡ (y ∣ n)

  _≈_ : (x y : Lim M) → Type _
  x ≈ y = ∀ n → x ≈⟨ n ⟩ y

  Complete : Type _
  Complete = (x y₁ y₂ : Lim M) → (∀ n → (x ≈⟨ n ⟩ y₁) ⊎ (x ≈⟨ n ⟩ y₂)) → ∥ (x ≡ y₁) ⊎ (x ≡ y₂) ∥₁

  _≺⟨_⟩_ : (x : Lim M) → (n : ℕ) → (ys : List (Lim M)) → Type _
  x ≺⟨ n ⟩ ys = ∥ (x ∣ n) ∈ map (_∣ n) ys ∥₁

  _≺_ : (x : Lim M) → (ys : List (Lim M)) → Type _
  x ≺ ys = ∀ n → x ≺⟨ n ⟩ ys

  Complete* : Type _
  Complete* = (x : Lim M) → (ys : List (Lim M)) → x ≺ ys → ∥ x ∈ ys ∥₁

  _∈?⟨_⟩_ : (x : Lim M) (n : ℕ) (ys : List (Lim M)) → Dec ((x ∣ n) ∈ (map (_∣ n) ys))
  x ∈?⟨ n ⟩ ys = dec∈M^ n (x .elements n) (map (λ y → y .elements n) ys)

  -- XXX: Complete can be weakened to have a truncation in the assumption
  Complete*⇒Complete : Complete* → Complete
  Complete*⇒Complete complete* x y₁ y₂ approx-≡ = goal where
    lemma : x ≺ (y₁ ∷ y₂ ∷ [])
    lemma n = do
      return (Sum.rec here (there ∘ here) (approx-≡ n))

    goal : ∥ (x ≡ y₁) ⊎ (x ≡ y₂) ∥₁
    goal = do
      here x≡y₂ ← complete* x (y₁ ∷ y₂ ∷ []) lemma
        where there (here x≡y₂) → return $ inr x≡y₂
      return $ inl x≡y₂

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

  _≟⟨_⟩_ : (x : Lim M) → (n : ℕ) → (y : Lim M) → Dec (x ∣ n ≡ y ∣ n)
  _≟⟨_⟩_ x n y = decEqM^ n (x ∣ n) (y ∣ n)

  ∈-≤-weaken : ∀ x ys k n → k ≤ n
    → (x ∣ n) ∈ (map (_∣ n) ys)
    → (x ∣ k) ∈ (map (_∣ k) ys)
  ∈-≤-weaken x ys k n k≤n xₙ∈ysₙ using (x* , (x*∈ys , x*≈x)) ← pre∈mapList xₙ∈ysₙ = abs x* x*∈ys x*≈x where
    abs : (x* : Lim M) → x* ∈ ys → (x* ∣ n ≡ x ∣ n) → (x ∣ k) ∈ (map (_∣ k) ys)
    abs x* x*∈ys x*≈x = subst (_∈ (map (_∣ k) ys)) (cut-≤ x* x k≤n x*≈x) (∈mapList x*∈ys)

  ∈-<-weaken : ∀ x ys k n → k < n
    → (x ∣ n) ∈ (map (_∣ n) ys)
    → (x ∣ k) ∈ (map (_∣ k) ys)
  ∈-<-weaken x ys k n k<n = ∈-≤-weaken x ys k n (<-weaken k<n)

  llpo⇒complete* : LLPO → Complete*
  llpo⇒complete* llpo x = goal where
    goal : ∀ ys → x ≺ ys → ∥ x ∈ ys ∥₁
    goal [] x≺[] = do
      x₀∈[] ← x≺[] 0
      Empty.rec (∉[] x₀∈[])
    goal (y ∷ ys) x≺y∷ys = ∥x∈y∷ys∥₁ where
      a : ℕ → Bool
      a n with decEven n
      ... | inl _ = not $ Dec→Bool $ x ≟⟨ n ⟩ y
      ... | inr _ = Dec→Bool $ x ∈?⟨ n ⟩ ys

      a-even : ∀ n → isEvenT n → ¬ (x ∣ n ≡ y ∣ n) → a n ≡ true
      a-even n ev mn with decEven n
      ... | inr odd = Empty.rec (even-not-odd n ev odd)
      ... | inl ev' with decEqM^ n (x ∣ n) (y ∣ n)
      ... | yes q = Empty.rec (mn q)
      ... | no ¬q = refl

      a-odd : ∀ n → isOddT n → ¬ ((x ∣ n) ∈ List.map (_∣ n) ys) → a n ≡ false
      a-odd n odd mn with decEven n
      ... | inl ev = Empty.rec (even-not-odd n ev odd)
      ... | inr _ with dec∈M^ n (x ∣ n) (List.map (_∣ n) ys)
      ... | yes p = Empty.rec (mn p)
      ... | no ¬p = refl
      
      par : ℕ → Bool
      par = parity a true

      magic : ∥ ((n : ℕ) → isEvenT n → par n ≡ false) ⊎
                ((n : ℕ) → isOddT n → par n ≡ false) ∥₁
      magic = llpo par (parity-prop _ true)

      case-even : ((n : ℕ) → isEvenT n → par n ≡ false) → x ≡ y
      case-even par-even = limitPath x≈y
        where
        module is-even {n} (even : isEvenT n) where
          ¬¬x≈y : ¬ ¬ x ≈⟨ n ⟩ y
          ¬¬x≈y ¬xₙ≡yₙ with (parity-even a n even (par-even n even) (a-even n even ¬xₙ≡yₙ))
          ... | (k , true , k-even , _ , _ , par≡true) = false≢true false≡true where
            false≡true =
              false ≡⟨ sym $ par-even k k-even ⟩
              par k ≡⟨ par≡true ⟩
              true  ∎
          ... | (k , false , k-odd , k<n , c , _) with decEven k
          ... | inl k-even = Empty.rec (even-not-odd k k-even k-odd)
          ... | inr _ with x ∈?⟨ k ⟩ ys
          ... | yes xₖ∈ysₖ = true≢false c
          ... | no ¬xₖ∈ysₖ = PT.rec isProp⊥ (λ ()) bot where
            bot : ∥ ⊥ ∥₁
            bot = x≺y∷ys n >>= λ where
              (here xₙ≡yₙ) → return $ ¬xₙ≡yₙ xₙ≡yₙ
              (there xₙ∈ysₙ) → do
                return $ ¬xₖ∈ysₖ (∈-<-weaken x ys k n k<n xₙ∈ysₙ)

          x≈y : x ≈⟨ n ⟩ y
          x≈y with (decEqM^ n (x ∣ n) (y ∣ n))
          ... | yes xₙ≡yₙ = xₙ≡yₙ
          ... | no ¬xₙ≡yₙ = Empty.rec (¬¬x≈y ¬xₙ≡yₙ)

        x≈y : x ≈ y
        x≈y n with decEven n
        ... | inl even = is-even.x≈y even
        ... | inr odd =
          (x ∣ n) ≡⟨ sym $ x .is-lim n ⟩
          !^ n (x ∣ suc n) ≡⟨ cong (!^ n) (is-even.x≈y {n = suc n} odd) ⟩
          !^ n (y ∣ suc n) ≡⟨ y .is-lim n ⟩
          y ∣ n ∎

      case-odd : ((n : ℕ) → isOddT n → par n ≡ false) → ∥ x ∈ ys ∥₁
      case-odd par-odd = goal ys x≺ys
        where module _ where
          ¬¬xₙ∈ysₙ-odd : ∀ n → isOddT n → ¬ ¬ (x ∣ n) ∈ map (_∣ n) ys
          ¬¬xₙ∈ysₙ-odd n odd ¬xₙ∈ysₙ with parity-odd a n odd (par-odd n odd) (a-odd n odd ¬xₙ∈ysₙ)
          ... | (k , false , k-odd , k<n , c , par≡true) = false≢true $
            false ≡⟨ sym $ par-odd k k-odd ⟩
            par k ≡⟨ par≡true ⟩
            true  ∎
          ... | (k , true , k-even , k<n , c , _) with decEven k
          ... | inr k-odd = Empty.rec (even-not-odd k k-even k-odd)
          ... | inl _ with x ≟⟨ k ⟩ y
          ... | yes xₖ≡yₖ = false≢true c
          ... | no ¬xₖ≡yₖ = PT.rec isProp⊥ (λ ()) bot where
            bot : ∥ ⊥ ∥₁
            bot = x≺y∷ys n >>= λ where
              (here xₙ≡yₙ) → return $ ¬xₖ≡yₖ $
                x ∣ k ≡⟨ cut-≤ x y (<-weaken k<n) xₙ≡yₙ ⟩
                y ∣ k ∎
              (there xₙ∈ysₙ) → return $ Empty.rec $ ¬xₙ∈ysₙ $ xₙ∈ysₙ

          x≺ys-odd : ∀ n → isOddT n → ∥ (x ∣ n) ∈ map (_∣ n) ys ∥₁
          x≺ys-odd n odd with x ∈?⟨ n ⟩ ys
          ... | yes xₙ∈ysₙ = return xₙ∈ysₙ
          ... | no ¬xₙ∈ysₙ = Empty.rec (¬¬xₙ∈ysₙ-odd n odd ¬xₙ∈ysₙ)

          x≺ys-even : ∀ n → isEvenT n → ∥ (x ∣ n) ∈ map (_∣ n) ys ∥₁
          x≺ys-even n even = do
            xₙ₊₁∈ysₙ₊₁ ← x≺ys-odd (suc n) even
            return $ ∈-≤-weaken x ys n (suc n) (≤-sucℕ {n}) xₙ₊₁∈ysₙ₊₁

          x≺ys : ∀ n → ∥ (x ∣ n) ∈ map (_∣ n) ys ∥₁
          x≺ys n = Sum.rec (x≺ys-even n) (x≺ys-odd n) (decEven n)

      ∥x∈y∷ys∥₁ : ∥ x ∈ (y ∷ ys) ∥₁
      ∥x∈y∷ys∥₁ = magic >>= λ where
        (inl even) → return $ here $ case-even even
        (inr odd) → do
          x∈ys ← case-odd odd
          return $ there x∈ys
