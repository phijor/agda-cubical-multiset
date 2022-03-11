module Multiset.GroupoidAction where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Equiv.Properties
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Univalence
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Function using (_∘_)
open import Cubical.Foundations.Structure
  using (TypeWithStr; ⟨_⟩; str)

open import Cubical.HITs.PropositionalTruncation
  renaming
    ( ∣_∣ to ∣_∣₀
    ; ∥_∥ to ∥_∥₀
    ; rec to ∥-∥₀-rec
    ; rec2 to ∥-∥₀-rec2
    )
  using (isPropPropTrunc; rec→Set; elim→Set)
import Cubical.HITs.PropositionalTruncation.MagicTrick as ∥-∥₀-Trick
open import Cubical.HITs.SetTruncation
  using (∥_∥₂)

open import Cubical.Data.Nat
open import Cubical.Data.Sigma
open import Cubical.Data.Fin
  using (Fin; Fin-inj; isSetFin)

private
  variable
    ℓ : Level

module _ (X : Type ℓ) where

  -- A type is finite iff it is merely equivalent to a standard n-element type.
  isFinite' : Type ℓ
  isFinite' = ∃[ n ∈ ℕ ] X ≃ Fin n

  isFinite : Type ℓ
  isFinite = Σ[ n ∈ ℕ ] ∥ X ≃ Fin n ∥₀

  extract : ∀ {k} {n} → ∥ X ≃ Fin k ∥₀ → ∥ X ≃ Fin n ∥₀ → k ≡ n
  extract {k} {n} =
    -- Equality of natural numbers is a proposition, so we can
    -- prove k ≡ n by recursion on the propositional truncation.
    ∥-∥₀-rec2 (isSetℕ k n) k≡n where
    -- Assume α and β are two (untruncated) equivalences.
    module _ (α : X ≃ Fin k) (β : X ≃ Fin n) where
      -- By chaining these equivalences together,
      -- we see that Fin k ≡ Fin n.
      Fin-k≡Fin-n : Fin k ≡ Fin n
      Fin-k≡Fin-n = ua
        ( Fin k
        ≃⟨ invEquiv α ⟩ X
        ≃⟨ β ⟩ Fin n
        ■)

      -- Since Fin is injective, we deduce that k ≡ n.
      k≡n : k ≡ n
      k≡n = Fin-inj k n Fin-k≡Fin-n

  -- Being finite is a proposition.
  --
  -- Proof: Mere existence is a proposition.
  isPropIsFinite' : isProp isFinite'
  isPropIsFinite' = isPropPropTrunc

  isPropIsFinite : isProp isFinite
  isPropIsFinite (k , α) (n , β) = Σ≡Prop (λ _ → isPropPropTrunc) (extract α β)

  equivIsFinite : isFinite' ≃ isFinite
  equivIsFinite = isoToEquiv
    ( iso
      (∥-∥₀-rec isPropIsFinite (λ (n , α) → n , ∣ α ∣₀))
      (λ (n , α) → ∥-∥₀-rec isPropIsFinite' (λ α → ∣ n , α ∣₀) α)
      (λ p → isPropIsFinite _ p)
      (λ p → isPropIsFinite' _ p)
    )


-- The type of finite sets...
𝔹 : (ℓ : Level) → Type (ℓ-suc ℓ)
𝔹 ℓ = TypeWithStr ℓ λ Y → isSet Y × isFinite Y

isPropIsFinSet : {ℓ : Level} {Y : Type ℓ} → isProp (isSet Y × isFinite Y)
isPropIsFinSet = isProp× isPropIsSet (isPropIsFinite _)

-- ..forms a groupoid.
--
-- Since being finite is a proposition, finite groupoids embedd
-- into the type of all sets, which is a groupoid.  Hence 𝔹 is
-- a groupoid, too.
--
-- We prove this by expanding the definition of 𝔹 into an
-- iterated Σ-type, then reassociating its terms:
--
-- 𝔹 = Σ[ Y ∈ Type ] isSet Y × isFinite Y
--   ≃ Σ[ (Y, s) ∈ (Σ[ Y ∈ Type] isSet Y) ] isFinite Y
--   ≃ Σ[ (Y, s) ∈ hSet) ] isFinite Y ≕ 𝔹'
--
-- We know that hSet forms a groupoid (isOfHLevelTypeOfHLevel 2),
-- and being finite is a proposition; so 𝔹 has as h-level the max
-- of the two; i.e. that of a groupoid.
isGroupoid𝔹 : isGroupoid (𝔹 ℓ)
isGroupoid𝔹 {ℓ = ℓ} = isOfHLevelRespectEquiv 3 𝔹≃𝔹' isGroupoid𝔹' where

  𝔹' : Type (ℓ-suc ℓ)
  𝔹' = Σ[ Y ∈ hSet ℓ ] isFinite ⟨ Y ⟩

  𝔹≃𝔹' : 𝔹' ≃ 𝔹 ℓ
  𝔹≃𝔹' = Σ-assoc-≃

  isGroupoid𝔹' : isGroupoid 𝔹'
  isGroupoid𝔹' = isGroupoidΣ (isOfHLevelTypeOfHLevel 2) (λ Y → isProp→isOfHLevelSuc 2 (isPropIsFinite ⟨ Y ⟩))

module 𝔹 where
  open import Cubical.Foundations.Pointed
  open import Cubical.Homotopy.Loopspace

  Sk : (n : ℕ) → 𝔹 ℓ-zero
  Sk n = (Fin n) , isSetFin , n , ∣ idEquiv _ ∣₀

  sizeof : 𝔹 ℓ → ℕ
  sizeof (_ , _ , n , _) = n

  sk : (n : ℕ) → Type (ℓ-suc ℓ)
  sk = fiber sizeof

  -- skel≡ : (B : 𝔹 ℓ-zero) → B ≡ (Sk (sizeof B))
  -- skel≡ B = {! ua  !}

  symm : (B : 𝔹 ℓ) → ∥ ⟨ B ⟩ ≃ Fin (sizeof B) ∥₀
  symm (_ , _ , _ , α) = α

  ≡-intro : {X Y : 𝔹 ℓ} → (⟨ X ⟩ ≡ ⟨ Y ⟩) → X ≡ Y
  ≡-intro = Σ≡Prop (λ _ → isPropIsFinSet)

  isContr-sz : ∀ n → isContr (sk {ℓ-zero} n)
  isContr-sz n = (Sk n , refl) , lem where
    lem : (B : sk n) → (Sk n , (λ _ → sizeof (Sk n))) ≡ B
    lem (B , szB≡n) = rec→Set {!   !} (λ α → Σ≡Prop (λ B → isSetℕ _ _) (≡-intro (lem₀ (ua α)))) ({! this shit is supposed to be 2-constant  !}) (symm B) where
      lem₀ : (p : ⟨ B ⟩ ≡ Fin (sizeof B)) → ⟨ Sk n ⟩ ≡ ⟨ B ⟩
      lem₀ p = let q = p ∙ cong Fin szB≡n in sym q

  S : (n : ℕ) → Type₁
  S n = Fin n ≡ Fin n

  isSet-S : ∀{n} → isSet (S n)
  isSet-S = isOfHLevel≡ 2 (isSetFin) (isSetFin)

  -- permutation : (X Y : 𝔹 ℓ) → (eq : X ≡ Y) → PathP (λ i → {! Fin (sizeof (eq i))  !}) (Fin (sizeof X)) (Fin (sizeof Y))
  -- permutation X Y eq = λ i → {! rec→Set isSetFin ? ? (symm (eq i))  !} where
  --   open ∥-∥₀-Trick.Recover

  -- Ω≃ : {X : 𝔹 ℓ} → (X ≡ X) ≃ (Fin (sizeof X) ≡ Fin (sizeof X))
  -- Ω≃ {X = X} = isoToEquiv (iso EqToAut {!   !} {!   !} {!   !}) where
  --   EqToAut : X ≡ X → Fin (sizeof X) ≡ Fin (sizeof X)
  --   EqToAut eq = {! eq  !}

_^_ : {A : Type ℓ} {a : A} → a ≡ a → (n : ℕ) → a ≡ a
_ ^ 0 = refl
p ^(suc n)= p ∙ p ^ n

module iter {A : Type ℓ} {a : A} where
  open import Cubical.Foundations.GroupoidLaws

  ^1≡id : (p : a ≡ a) → p ≡ p ^ 1
  ^1≡id p = rUnit p

infix 31 _^_

module _ {X : Type ℓ} where
  isCyclic : (X → X) → Type ℓ
  isCyclic f = ∀ x y → ∃[ n ∈ ℕ ] y ≡ iter n f x

  isCyclic' : (X → X) → Type ℓ
  isCyclic' f = ∀ x y → Σ[ n ∈ ℕ ] y ≡ iter n f x

  isPropIsCyclic : {f : X → X} → isProp (isCyclic f)
  isPropIsCyclic {f} = isPropΠ2 (λ x y → isPropPropTrunc)

  cycleLen : {f : X → X} → isCyclic f → X → X → ℕ
  cycleLen {f} is-cyc-f x y = let ∃-n = is-cyc-f x y in rec→Set isSetℕ {!   !} {!   !} {!   !}

  isCyclic→invMap : {f : X → X} → isCyclic f → X → X
  isCyclic→invMap {f} is-cyc-f x = {! iter  !}

  isCyclic→isEquiv : {f : X → X} → isCyclic f → isEquiv f
  isCyclic→isEquiv {f} is-cyc-f .equiv-proof x = ({!   !} , {!   !}) , {!   !}

ℂ : Type (ℓ-suc ℓ)
ℂ {ℓ = ℓ} = TypeWithStr ℓ (λ X → Σ[ f ∈ (X → X) ] isCyclic f)

data Dunce (n : ℕ) : Type where
  base : Dunce n
  loop : base ≡ base
  surf : PathP (λ i → loop i ≡ loop i) (loop ^ n) refl

module Dunce' where abstract
  import Cubical.HITs.DunceCap as Lib

  Dunce₁≃Dunce : Dunce 1 ≃ Lib.Dunce
  Dunce₁≃Dunce = isoToEquiv (iso toLib ofLib {!   !} {!   !}) where
    toLib : Dunce 1 → Lib.Dunce
    toLib base = Lib.base
    toLib (loop i) = Lib.loop i
    toLib (surf i j) = Lib.surf {!   !} {!   !}

    ofLib : Lib.Dunce → Dunce 1
    ofLib = {!   !}

module _ (ℓ : Level) where

  private
    variable
      ℓ' : Level

  𝕄 : Type ℓ' → Type (ℓ-max ℓ' (ℓ-suc ℓ))
  𝕄 X = Σ[ B ∈ 𝔹 ℓ ] (⟨ B ⟩ → X)

  module 𝕄 {X : Type ℓ'} where
    open import Cubical.Foundations.Transport

    isGroupoid𝕄 : isGroupoid X → isGroupoid (𝕄 X)
    isGroupoid𝕄 isGpdX = isGroupoidΣ isGroupoid𝔹 (λ B → isGroupoidΠ (λ _ → isGpdX))

    mk : (B : 𝔹 ℓ) → (⟨ B ⟩ → X) → 𝕄 X
    mk B e = (B , e)

    El : 𝔹 ℓ → Type (ℓ-max ℓ ℓ')
    El B = ⟨ B ⟩ → X

    isOfHLevel-El : {B : 𝔹 ℓ} → ∀ {n} → isOfHLevel n X → isOfHLevel n (El B)
    isOfHLevel-El {B} {n} isOfHLevel-X = isOfHLevelΠ n (λ _ → isOfHLevel-X)

    Size : (m : 𝕄 X) → Type ℓ
    Size (B , _) = ⟨ B ⟩

    elements : (m : 𝕄 X) → (Size m → X)
    elements (_ , elems) = elems

    _∈_ : (x : X) → (m : 𝕄 X) → Type (ℓ-max ℓ ℓ')
    x ∈ m = fiber (elements m) x

    sizeof : (m : 𝕄 X) → ℕ
    sizeof (B , _) = 𝔹.sizeof B

    ≡-intro : ∀ {B₀ B₁ : 𝔹 ℓ} {e₀ : ⟨ B₀ ⟩ → X} {e₁ : ⟨ B₁ ⟩ → X}
      → (π : B₀ ≡ B₁)
      → PathP (λ i → El (π i)) e₀ e₁
      → (B₀ , e₀) ≡ (B₁ , e₁)
    ≡-intro π e = λ i → mk (π i) (e i)

    ≡-intro-subst : ∀ {B₀ B₁ : 𝔹 ℓ} {e₀ : ⟨ B₀ ⟩ → X} {e₁ : ⟨ B₁ ⟩ → X}
      → (π : ⟨ B₀ ⟩ ≃ ⟨ B₁ ⟩)
      → (subst (λ B → B → X) (ua π) e₀ ≡ e₁)
      → (B₀ , e₀) ≡ (B₁ , e₁)
    ≡-intro-subst {B₀} {B₁} {e₀} {e₁} π same-els = ≡-intro B₀≡B₁ filler where
      ua-π : ⟨ B₀ ⟩ ≡ ⟨ B₁ ⟩
      ua-π = ua π

      B₀≡B₁ : B₀ ≡ B₁
      B₀≡B₁ = 𝔹.≡-intro ua-π

      lemma : PathP (λ i → ua-π i → X) e₀ (subst (λ B → B → X) ua-π e₀)
      lemma = subst-filler (λ B → B → X) ua-π e₀

      filler : PathP (λ i → (ua-π i) → X) e₀ e₁
      filler = lemma ▷ same-els

    module Transport-lemma {ℓX ℓT : Level} {X₀ X₁ : Type ℓX} (T : Type ℓT) where
      -- Two things are the same:
      -- * composition of a function with a transport of arguments
      -- * substituting the argument type of a function
      comm-transport⁻-subst : (g : X₀ → T) → (p : X₀ ≡ X₁) → (g ∘ transport⁻ p) ≡ subst (λ X → (X → T)) p g
      comm-transport⁻-subst g p = J Pattern (funExt transport-hell) p where
        Pattern : (X : Type ℓX) → (X₀ ≡ X) → Type _
        Pattern X X₀≡X = g ∘ transport⁻ X₀≡X ≡ subst (λ X → (X → T)) X₀≡X g

        transport-hell : (x₀ : X₀) → g (transport refl x₀) ≡ transport (refl {x = T}) (g (transport (refl {x = X₀}) x₀))
        transport-hell x₀ = sym (transportRefl _)
          -- g (transport refl x₀)
          --   ≡⟨ sym (transportRefl _) ⟩
          -- transport (refl {x = T}) (g (transport (refl {x = X₀}) x₀))
          --   ∎

      comm-transport-subst-sym : (g : X₁ → T) → (p : X₀ ≡ X₁) → (g ∘ transport p) ≡ subst (λ X → (X → T)) (sym p) g
      comm-transport-subst-sym g p = J Pattern (funExt transport-hell) (sym p) where
        Pattern : (X : Type ℓX) → (X₁ ≡ X) → Type _
        Pattern X X₁≡X =  g ∘ transport⁻ X₁≡X ≡ subst (λ X → (X → T)) X₁≡X g

        g-substRefl : subst (λ X → X → T) refl g ≡ g
        g-substRefl = substRefl {B = (λ X → X → T)} g

        transport-hell : (x₁ : X₁) → g (transport⁻ refl x₁) ≡ subst (λ X → X → T) refl g x₁
        transport-hell x₁ = cong g (transportRefl x₁) ∙ sym (λ i → g-substRefl i x₁)

      comm-transport⁻-transport-symm : (p : X₀ ≡ X₁) → transport⁻ p ≡ transport (sym p)
      comm-transport⁻-transport-symm p = refl

    ≡-intro-permute : ∀ {B₀ B₁ : 𝔹 ℓ} {e₀ : ⟨ B₀ ⟩ → X} {e₁ : ⟨ B₁ ⟩ → X}
      → (π : ⟨ B₀ ⟩ ≃ ⟨ B₁ ⟩)
      → (e₀ ≡ e₁ ∘ (equivFun π))
      → (B₀ , e₀) ≡ (B₁ , e₁)
    ≡-intro-permute {B₀} {B₁} {e₀} {e₁} π same-els = ≡-intro-subst π lemma where
      open Transport-lemma

      p : ⟨ B₀ ⟩ ≡ ⟨ B₁ ⟩
      p = ua π

      uaβ⁻ : {A B : Type ℓ} (e : A ≃ B) (x : B) → transport⁻ (ua e) x ≡ invEq e x
      uaβ⁻ e x = funExt⁻ (sym (transportUaInv e)) x ∙ transportRefl (invEq e x)

      step₁ : e₀ ∘ transport⁻ p ≡ subst (λ X₁ → X₁ → X) p e₀
      step₁ = comm-transport⁻-subst X e₀ p

      step₂ : e₀ ∘ transport⁻ p ≡ e₁
      step₂ =
        e₀ ∘ transport⁻ p
          ≡⟨ cong (λ g → g ∘ transport⁻ p) same-els ⟩
        (e₁ ∘ equivFun π) ∘ transport⁻ (ua π)
          ≡⟨ funExt  (λ b → cong (e₁ ∘ equivFun π) (uaβ⁻ π b)) ⟩
        (e₁ ∘ equivFun π) ∘ invEq π
          ≡⟨ funExt (λ b → cong e₁ (secEq π b)) ⟩
        e₁ ∎

      lemma : subst (λ B → B → X) p e₀ ≡ e₁
      lemma = sym step₁ ∙ step₂

module Ex where
  open import Cubical.Data.Bool
  open import Cubical.Data.Fin
  open import Cubical.Data.Nat.Order
  open import Cubical.Data.Empty renaming (rec to ⊥-rec)

  impossible-fin : {A : Type ℓ} → ∀ {n} {k} → iter n suc k < n → A
  impossible-fin {n = zero} p = ⊥-rec (¬-<-zero p)
  impossible-fin {n = suc n} {k} p = impossible-fin (pred-≤-pred p)

  𝟚 : 𝔹 ℓ-zero
  𝟚 = Fin 2 , isSetFin , 2 , ∣ idEquiv _ ∣₀

  elems : ⟨ 𝟚 ⟩ → ℕ
  elems (0 , _) = 42
  elems (1 , _) = 1337
  elems (suc (suc k) , p) = impossible-fin p

  ex : 𝕄 ℓ-zero ℕ
  ex = 𝟚 , elems

  elems' : ⟨ 𝟚 ⟩ → ℕ
  elems' (0 , _) = 1337
  elems' (1 , _) = 42
  elems' (suc (suc k) , p) = impossible-fin p

  ex' : 𝕄 ℓ-zero ℕ
  ex' = 𝟚 , elems'

  switch : Fin 2 → Fin 2
  switch (0 , p) = 1
  switch (1 , p) = 0
  switch (suc (suc _) , p) = impossible-fin p

  switch-≃ : ⟨ 𝟚 ⟩ ≃ ⟨ 𝟚 ⟩
  switch-≃ = isoToEquiv (iso switch switch inv inv) where
    inv : ∀ k → switch (switch k) ≡ k
    inv (0 , _) = Σ≡Prop (λ _ → m≤n-isProp) refl
    inv (1 , _) = Σ≡Prop (λ _ → m≤n-isProp) refl
    inv (suc (suc _) , p) = impossible-fin p

  ex≡ : ex ≡ ex'
  ex≡ = 𝕄.≡-intro-permute _ switch-≃ (funExt same-elements) where
    same-elements : ∀ k → elems k ≡ elems' (switch k)
    same-elements (0 , _) = refl
    same-elements (1 , _) = refl
    same-elements (suc (suc _) , p) = impossible-fin p

module _ (X : Type ℓ) where

  -- A type has finitely many connected components iff its set truncation
  -- is finite.
  --
  -- The idea is that set-truncation preserves exactly the points of a type,
  -- and uniquely equates those in the same connected component.
  hasFiniteConnectedComponents : Type ℓ
  hasFiniteConnectedComponents = isFinite ∥ X ∥₂

  -- A type is a finite groupoid iff it is both a groupoid and has finitely
  -- many connected components.
  isFinGroupoid : Type ℓ
  isFinGroupoid = isGroupoid X × hasFiniteConnectedComponents

  isPropIsFinGroupoid : isProp isFinGroupoid
  isPropIsFinGroupoid = isProp× isPropIsGroupoid (isPropIsFinite _)

FinGroupoid : (ℓ : Level) → Type (ℓ-suc ℓ)
FinGroupoid ℓ = TypeWithStr ℓ isFinGroupoid


module Examples where
  open import Cubical.Data.Unit
  open import Cubical.Data.Fin.Properties
    using (Unit≃Fin1; isSetFin)
  open import Cubical.HITs.S1
  open import Cubical.HITs.SetTruncation
    renaming (elim to ∥-∥₂-elim)

  -- The set truncation of S¹ is a 2-dimensional solid disk.
  -- The boundary of D² is given by terms of S¹;  the interior
  -- by (unique) paths between points on the boundary.
  D² : Type₀
  D² = ∥ S¹ ∥₂

  -- A disk is contractible, with center of contraction at the
  -- base point of the boundary.
  isContrD² : isContr D²
  isContrD² = ∣ S¹.base ∣₂ , contraction where
    isPropPathToBase : (d : D²) → isProp (∣ S¹.base ∣₂ ≡ d)
    isPropPathToBase = isSetSetTrunc _

    -- The contraction
    contraction : (d : D²) → ∣ S¹.base ∣₂ ≡ d
    contraction = ∥-∥₂-elim
      (λ d → isProp→isSet (isPropPathToBase d))
      (λ a → PathIdTrunc₀Iso .inv (isConnectedS¹ a)) where
        open Iso

  -- ...and therefore equivalent to a point.
  unitEquiv : D² ≃ Unit
  unitEquiv = isoToEquiv (isContr→Iso isContrD² isContrUnit)

  -- So in particular, a disk is equivalent to a standard 1-element set.
  D²≃Fin1 : D² ≃ Fin 1
  D²≃Fin1 = D²
    ≃⟨ unitEquiv ⟩ Unit
    ≃⟨ Unit≃Fin1 ⟩ Fin 1 ■

  -- Therefore, the 1-sphere is a groupoid with one element.
  isFinGroupoidS₁ : isFinGroupoid S¹
  isFinGroupoidS₁ = isGroupoidS¹ , 1 , ∣ D²≃Fin1 ∣₀

  -- The standard k-element types are finite groupoids, too.
  --
  -- They are groupoids (since they are sets), and have k connected
  -- components that stay unchanged under set-truncation.
  isFinGroupoidFin : ∀ k → isFinGroupoid (Fin k)
  isFinGroupoidFin k = isSet→isGroupoid isSetFin , k , ∣ setTruncIdempotent≃ isSetFin ∣₀

module _ {ℓ : Level} where
  record IsGroup (G : Type ℓ) : Type ℓ where
    no-eta-equality
    constructor isgroup

    field
      pt : G
      is-connected : ∥ G ∥₀ × ((x y : G) → x ≡ y)
      is-groupoid : isGroupoid G

  record Group : Type (ℓ-suc ℓ) where
    field
      B : Type ℓ
      is-group : IsGroup B

