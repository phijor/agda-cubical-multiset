module Multiset.Analytic.Functor where

open import Cubical.Foundations.Prelude renaming (funExt⁻ to happly)
open import Cubical.Foundations.Structure
open import Cubical.Foundations.Function
open import Cubical.Foundations.HLevels
open import Cubical.Data.Sigma
open import Cubical.Data.Nat.Base
open import Cubical.Data.Fin.Base
open import Cubical.Algebra.Group.Base

open import Cubical.HITs.TypeQuotients.Base
open import Cubical.Categories.Instances.Sets
open import Cubical.Categories.Functor

open import Multiset.GroupAction.Base
open import Multiset.GroupAction.Induced
open import Multiset.GroupAction.Orbit hiding (_/∼)
open import Multiset.Analytic.Base

module AFunctor (ℓ : Level) (Sig : Signature ℓ ℓ ℓ) where

  F₀ : Functor (SET ℓ) (SET ℓ)
  F₀ = record { F-ob = ob ; F-hom = {!   !} ; F-id = {!   !} ; F-seq = {!   !} } where

    module _ (X : hSet ℓ) (σ : ⟨ Sig ⟩) where
      private
        open module Sig = SignatureStr (str Sig)

      inputSymmetry : GroupAction (symmetry σ) ℓ
      inputSymmetry = Induced (arity σ) X

      --- Define the set of orbits X^σ/∼ where...
      ---
      --- * X is some type
      --- * X^σ is X to the power of the arity of an operation σ
      --- * ∼ is the orbit relation on X^σ under coordinate permutation,
      ---   as induced by G.
      _^_/∼ : Type ℓ
      _^_/∼ = Orbit.OrbitType inputSymmetry

    ob : hSet ℓ → hSet ℓ
    ob X = ( Σ[ σ ∈ ⟨ Sig ⟩ ] (X ^ σ /∼) ) , isSetΣ ((str Sig) .SignatureStr.is-set-op) (λ σ → {!   !})

  -- _/∼ : (X : hSet ℓX) → Type _
  -- _/∼ {ℓX = ℓX} X = Σ[ σ ∈ ⟨ Sig ⟩ ] ( X ^ σ /∼ )

  -- private
  --   variable
  --     X : hSet ℓX
  --     Y : hSet ℓY
  --     Z : hSet ℓZ
  --   open SignatureStr (str Sig)

  -- module _ where
  --   ∼-elim : {ℓ : Level} {B : X /∼ → Type ℓ}
  --     → (f : (σ : ⟨ Sig ⟩) → (v : ⟨ arity σ ⟩ → ⟨ X ⟩) → B (σ , [ v ]))
  --     → (well-defined : ∀ σ (v w : ⟨ arity σ ⟩ → ⟨ X ⟩)
  --        → (v∼w : let open Orbit (inputSymmetry X σ) in v ∼ w) →  PathP (λ i → B (σ , eq/ v w v∼w i)) (f σ v) (f σ w)
  --     )
  --     → (x : X /∼) → B x
  --   ∼-elim {B = B} f _ (σ , [ v ]) = f σ v
  --   ∼-elim {B = B} f well-defined (σ , eq/ v w v∼w i) = well-defined σ v w v∼w i

  -- open import Multiset.Util using (_→ₛ_)

  -- _^_/ₘ∼ : (f : ⟨ X ⟩ → ⟨ Y ⟩) (σ : ⟨ Sig ⟩) → (X ^ σ /∼ → Y ^ σ /∼)
  -- _^_/ₘ∼ {X = X} {Y = Y} f σ = OrbitMap.descend (arity σ) (str X) (str Y) f

  -- _/ₘ∼ : (f : ⟨ X ⟩ → ⟨ Y ⟩) → (X /∼ → Y /∼)
  -- (f /ₘ∼) (σ , x) = σ , (f ^ σ /ₘ∼) x

  -- id-/∼ : (idfun ⟨ X ⟩) /ₘ∼ ≡ idfun (X /∼)
  -- id-/∼ {X = X} = λ i (σ , x) → σ , aux σ i x where
  --   aux : (σ : ⟨ Sig ⟩) → (idfun ⟨ X ⟩) ^ σ /ₘ∼ ≡ idfun (X ^ σ /∼)
  --   aux σ = descend-id (arity σ) X

  -- comp-/ₘ∼ : (f : ⟨ X ⟩ → ⟨ Y ⟩) → (g : ⟨ Y ⟩ → ⟨ Z ⟩)
  --   → (g ∘ f) /ₘ∼ ≡ g /ₘ∼ ∘ f /ₘ∼
  -- comp-/ₘ∼ {X = X} {Y = Y} {Z = Z} f g = λ i (σ , x) → σ , aux σ i x where
  --   open OrbitMap _ (str X) (str Y)
  --   aux : (σ : ⟨ Sig ⟩) → (g ∘ f) ^ σ /ₘ∼ ≡ (g ^ σ /ₘ∼) ∘ (f ^ σ /ₘ∼)
  --   aux σ = descend-comp (arity σ) (str X) (str Y) (str Z) f g

-- module Chain (Sig : Signature ℓG ℓS ℓσ) where
--   open import Multiset.Chains
--   open import Multiset.GroupAction.Orbit hiding (_/∼)

--   private
--     variable
--       ℓ : Level

--     open module F = Functor Sig
--     open Chain
--     open Limit
--     open ChainLimit

--   module ap (σ : ⟨ Sig ⟩) where
--     apChain : (X : Chain ℓ) → Chain (ℓ-max (ℓ-max ℓG ℓS) ℓ)
--     apChain X = chain ((_^ σ /∼) ∘ .Ob) ((_^ σ /ₘ∼) ∘ X .π)

--     α : {X : Chain ℓ}
--       → (ChainLimit X) ^ σ /∼ → ChainLimit (apChain X)
--     α {X = X} l = lim (proj' l) (isChainLimit-proj' l) {- σ-elim α-lim α-well-defined -} where
--       open SignatureStr (str Sig)

--       -- Given a family v of limiting sequences, project onto the
--       -- family containing the nᵗʰ element of each sequence.
--       proj' : (ChainLimit X) ^ σ /∼ → (n : ℕ) → (X .Ob n) ^ σ /∼
--       proj' l n = descend (λ l → l .elements n) l where
--         open OrbitMap (arity σ)

--       LimX-Sym = inputSymmetry (ChainLimit X) σ

--       module LimX-Orbit = Orbit LimX-Sym
--       open LimX-Orbit renaming ([_]∼ to [_]lim∼)
--       module X-Orbit (n : ℕ) = Orbit (inputSymmetry (X .Ob n) σ)

--       module _ (l : ⟨ arity σ ⟩ → ChainLimit X) (n : ℕ) where
--         isChainLimitLift : apChain X .π n (proj' [ l ]lim∼ (suc n)) ≡ proj' [ l ]lim∼ n
--         isChainLimitLift = X-Orbit.Path→OrbitPath n (λ i k → l k .isChainLimit n i)

--       module _ (l₀ l₁ : ⟨ arity σ ⟩ → ChainLimit X) (l₀∼l₁ : [ LimX-Sym ∣ l₀ ∼ l₁ ]) (n : ℕ) where
--         module Xₙ-Orbit = X-Orbit n

--         [l₀]≡[l₁] : [ l₀ ]lim∼ ≡ [ l₁ ]lim∼
--         [l₀]≡[l₁] = eq/ l₀ l₁ l₀∼l₁

--         Xπ-proj'≡ : apChain X .π n (proj' [ l₀ ]lim∼ (suc n)) ≡ apChain X .π n (proj' [ l₁ ]lim∼ (suc n))
--         Xπ-proj'≡ = cong (apChain X .π n ∘ (flip proj' (suc n))) [l₀]≡[l₁]

--         square : PathP (λ i → Xπ-proj'≡ i ≡ cong (flip proj' n) [l₀]≡[l₁] i)
--                 (isChainLimitLift l₀ n)
--                 (isChainLimitLift l₁ n)
--         square = {!   !}

--       isChainLimit-proj' : (l : (ChainLimit X) ^ σ /∼) → Limit.IsChainLimit (apChain X) (proj' l)
--       isChainLimit-proj' = LimX-Orbit.elim
--         isChainLimitLift
--         λ s t s∼t i n → square s t s∼t n i
--       -- module _ (v : ⟨ arity σ ⟩ → ChainLimit X) where
--       --   -- Definition of the projection vₖ ↦ vₖₙ
--       --   proj : (n : ℕ) → ⟨ arity σ ⟩ → X .Ob n
--       --   proj n = λ k → v k .elements n

--       --   module _ (n : ℕ) where
--       --     private
--       --         Sσ = inputSymmetry (X .Ob n) σ
--       --         open module Sσ = GroupActionStr (str Sσ)
--       --         open Orbit Sσ renaming (_∼_ to _∼σ_ ; [_]∼ to [_]σ∼)

--       --     isChainLimit-proj : [ (X .π n) ∘ (proj (suc n)) ]σ∼ ≡ [ proj n ]σ∼
--       --     isChainLimit-proj = Path→OrbitPath Sσ λ i k → v k .isChainLimit n i

--       --   α-lim-elements : (n : ℕ) → (X .Ob n) ^ σ /∼
--       --   α-lim-elements n = [ proj n ]


--       -- α-lim : (v : ⟨ arity σ ⟩ → ChainLimit X) → ChainLimit (apChain X)
--       -- α-lim v = lim (proj' [ v ]) (isChainLimit-proj v)

--       -- open Orbit (inputSymmetry (ChainLimit X) σ) renaming (_∼_ to _∼lim_ ; [_]∼ to [_]∼lim ; OrbitType to _/∼lim)

--       -- module _
--       --   (v w : ⟨ arity σ ⟩ → ChainLimit X)
--       --   (v∼w : v ∼lim w) where

--       --   module _ (n : ℕ) where
--       --     private
--       --         Xₙ/σ = inputSymmetry (X .Ob n) σ
--       --         open module Xₙ/σ = GroupActionStr (str Xₙ/σ)
--       --         open Orbit Xₙ/σ renaming (_∼_ to _∼σ_ ; [_]∼ to [_]σ∼)

--       --     proj-descend : [ proj v n ]σ∼ ≡ [ proj w n ]σ∼
--       --     proj-descend = OrbitMap.well-defined (arity σ) (λ l → l .elements n) v w v∼w

--       --   -- α-coherence : ∀ n → Square (isChainLimit-proj v n) (isChainLimit-proj w n) λ i → {!   !} (proj-descend n)
--       --   -- α-coherence n = {!   !}

--       --   elements≡ : α-lim-elements v ≡ α-lim-elements w
--       --   elements≡ = funExt proj-descend


--       -- α-well-defined : (v w : ⟨ arity σ ⟩ → ChainLimit X) (v∼w : v ∼ w) → α-lim v ≡ α-lim w
--       -- α-well-defined v w v∼w = ChainLimitPathP _ (elements≡ v w v∼w , funExt (λ n → {!   !}))



--   apChain : (X : Chain ℓ) → Chain (ℓ-max (ℓ-max (ℓ-max ℓG ℓS) ℓσ) ℓ)
--   apChain X = chain ((_/∼) ∘ X .Ob) ((_/ₘ∼) ∘ X .π)

--   α : {X : Chain ℓ}
--     → (ChainLimit X) /∼ → ChainLimit (apChain X)
--   α {X = X} = ∼-elim α-lim well-defined where
--       open SignatureStr (str Sig)
--       module _ (σ : ⟨ Sig ⟩) where
--         -- Given a family v of limiting sequences, project onto the
--         -- family containing the nᵗʰ element of each sequence.
--         proj : (n : ℕ) → (v : ⟨ arity σ ⟩ → ChainLimit X) → ⟨ arity σ ⟩ → X .Ob n
--         proj n v k = v k .elements n

--         open Orbit (inputSymmetry (ChainLimit X) σ) renaming (_∼_ to _∼lim_ ; [_]∼ to [_]lim∼)

--         module _ (n : ℕ) (v : ⟨ arity σ ⟩ → ChainLimit X) where
--           private
--             Sσ = inputSymmetry (X .Ob n) σ
--             open module Sσ = GroupActionStr (str Sσ)
--             open Orbit Sσ renaming (_∼_ to _∼σ_ ; [_]∼ to [_]σ∼ ; Path→OrbitPath to liftPath)

--           isChainLimit-descendOrbit : [ (X .π n) ∘ (proj (suc n)) v ]σ∼ ≡ [ proj n v ]σ∼
--           isChainLimit-descendOrbit = liftPath λ i k → v k .isChainLimit n i

--           α-lim-elements : (X .Ob n) /∼
--           α-lim-elements = ( σ , [ proj n v ] )

--         α-lim : (v : ⟨ arity σ ⟩ → ChainLimit X) → ChainLimit (apChain X)
--         α-lim v = lim (λ n → α-lim-elements n v) λ n → ΣPathP (refl , isChainLimit-descendOrbit n v)

--         module _
--           (v w : ⟨ arity σ ⟩ → ChainLimit X)
--           (v∼w : v ∼lim w) where

--           module _ (n : ℕ) where

--             private
--               Sσ = inputSymmetry (X .Ob n) σ
--               open module Sσ = GroupActionStr (str Sσ)
--               open Orbit Sσ renaming (_∼_ to _∼σ_ ; [_]∼ to [_]σ∼)

--             proj≡ : [ proj n v ]σ∼ ≡ [ proj n w ]σ∼
--             proj≡ = eq/ _ _ ((fst v∼w) , cong (proj n) (snd v∼w))

--             Xπ-proj≡ : [ X .π n ∘ proj (suc n) v ]σ∼ ≡ [ X .π n ∘ proj (suc n) w ]σ∼
--             Xπ-proj≡ = eq/ _ _ (fst v∼w , λ i k → (X .π n) (proj (suc n) (snd v∼w i) k))

--             α-coherence : Square
--               {- bot -} (isChainLimit-descendOrbit n v)
--               {- top -} (isChainLimit-descendOrbit n w)
--               {- lft -} (Xπ-proj≡)
--               {- rgt -} (proj≡)
--             α-coherence = {!   !}

--           α-lim-proj≡ : α-lim v .elements ≡ α-lim w .elements
--           α-lim-proj≡ = λ i n → σ , proj≡ n i

--           well-defined : α-lim v ≡ α-lim w
--           well-defined = ChainLimitPathP _ (α-lim-proj≡ , λ i n j → σ , α-coherence n i j)

-- module Example where
--   open import Cubical.Foundations.Equiv
--   open import Cubical.Foundations.Isomorphism
--   open import Cubical.HITs.TypeQuotients.Base
--   open import Cubical.Data.Nat.Properties
--   open import Cubical.Data.Nat.Order
--   open import Cubical.Data.Empty.Base renaming (rec to ex-falso)
--   open import Cubical.Algebra.SymmetricGroup
--   open import Cubical.Algebra.Group.Instances.Unit renaming (Unit to UnitGroup)

--   open import Multiset.GroupAction.Instances

--   private
--     arity : ℕ → ℕ
--     arity n = n

--   OrderedTreesSignature : Signature₀
--   OrderedTreesSignature = ℕ , signaturestr (λ _ → UnitGroup) λ n → UnitAction (Fin n)

--   UnorderedTreesSignature : Signature₀
--   UnorderedTreesSignature =  ℕ , signaturestr Sym SymAction

--   open Functor UnorderedTreesSignature

--   ex₁ : Type → Type
--   ex₁ X =  X ^ 2 /∼

--   m+iter-suc≡iter-suc+m : (n : ℕ) (m k : ℕ) → m + (iter n suc k) ≡ iter n suc (m + k)
--   m+iter-suc≡iter-suc+m zero m k = refl
--   m+iter-suc≡iter-suc+m (suc n) m k = +-suc m _ ∙ cong suc (m+iter-suc≡iter-suc+m n m k)

--   ¬suc-suc-k<2 : {k : ℕ} (p : suc (suc k) < 2) → ⊥
--   ¬suc-suc-k<2 {k} (m , p) = snotz (injSuc (injSuc (sym (m+iter-suc≡iter-suc+m 3 _ _) ∙ p)))

--   absurd-suc-suc-k<2 : {ℓ : Level} {X : Type ℓ} {k : ℕ} (p : suc (suc k) < 2) → X
--   absurd-suc-suc-k<2 p = ex-falso (¬suc-suc-k<2 p)

--   vec₂ : {X : Type} (x₀ x₁ : X) → Fin 2 → X
--   vec₂ x₀ _ (0 , _) = x₀
--   vec₂ _ x₁ (1 , _) = x₁
--   vec₂ _ _ ((suc (suc k)) , p) = absurd-suc-suc-k<2 p

--   ex₂ : {X : Type} (x₀ x₁ : X) → X /∼
--   ex₂ {X = X} x₀ x₁ = 2 , [ vec₂ x₀ x₁ ]

--   ex₂-swap : {X : Type} (x₀ x₁ : X) → ex₂ x₀ x₁ ≡ ex₂ x₁ x₀
--   ex₂-swap {X = X} x₀ x₁ = ΣPathP (refl , eq/ (vec₂ x₀ x₁) (vec₂ x₁ x₀) swap)
--     where
--       swap-impl : Fin 2 → Fin 2
--       swap-impl (zero , _) = (suc zero , (0 , refl))
--       swap-impl (suc zero , _) = (zero , (1 , refl))
--       swap-impl (suc (suc _) , p) = absurd-suc-suc-k<2 p

--       do-swap : ∀ s → vec₂ x₀ x₁ (swap-impl s) ≡ vec₂ x₁ x₀ s
--       do-swap (zero , snd₁) = refl
--       do-swap (suc zero , snd₁) = refl
--       do-swap (suc (suc k) , p) = absurd-suc-suc-k<2 p

--       swap : [ (Induced (SymAction 2) X) ∣ (vec₂ x₀ x₁) ∼ (vec₂ x₁ x₀) ]
--       swap = (swap-impl , equivIsEquiv (isoToEquiv swap-iso)) , funExt do-swap where
--         swap-swap-id : (k : Fin 2) → swap-impl (swap-impl k) ≡ k
--         swap-swap-id (zero , snd₁) = Σ≡Prop (λ _ → m≤n-isProp) refl
--         swap-swap-id (suc zero , snd₁) = Σ≡Prop (λ _ → m≤n-isProp) refl
--         swap-swap-id (suc (suc fst₁) , p) = absurd-suc-suc-k<2 p

--         swap-iso : Iso (Fin 2) (Fin 2)
--         swap-iso = iso swap-impl swap-impl swap-swap-id swap-swap-id
