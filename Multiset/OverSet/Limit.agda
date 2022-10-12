module Multiset.OverSet.Limit where

open import Multiset.Prelude
open import Multiset.Util using (!_)

open import Multiset.OverSet.Base as FMSet
open import Multiset.OverSet.Properties as FMSet

open import Multiset.Chains
open import Multiset.Chains.FunctorChain

open import Cubical.Foundations.Function using (_∘_)
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Isomorphism using (section)
open import Cubical.Foundations.HLevels using (isPropΠ)

open import Cubical.HITs.SetQuotients as SQ using (_/_)
open import Cubical.HITs.PropositionalTruncation as PT
  using (∥_∥₁ ; ∣_∣₁)

open import Cubical.Data.Nat.Base as Nat hiding (_^_)
open import Cubical.Data.SumFin.Base using (Fin ; isSetFin)
open import Cubical.Data.Unit as Unit using (isSetUnit)

instance
  FunctorFMSet : Functor FMSet
  FunctorFMSet .Functor.map = FMSet.map
  FunctorFMSet .Functor.map-id = FMSet.mapId
  FunctorFMSet .Functor.map-comp = λ { g f xs → sym (mapComp g f xs) }

open Limit.ChainLimit using (elements ; isChainLimit)

!^ : ∀ n → FMSet ^ (suc n) → FMSet ^ n
!^ n = FMSet map-!^ n

shiftedLimitPath : ∀ {shlim₁ shlim₂} → (∀ n → shlim₁ .elements n ≡ shlim₂ .elements n) → shlim₁ ≡ shlim₂
shiftedLimitPath = Limit.isSet→ChainLimitPathExt (shift (ch FMSet)) (λ k → isSetFMSet)

private
  cut : (n : ℕ) → Lim FMSet → FMSet ^ n
  cut n tree = tree .elements n

zip : FMSet (Lim FMSet) → ShLim FMSet
zip xs = Limit.lim trees islim where
  trees : (n : ℕ) → FMSet ^ (suc n)
  trees n = FMSet.map (cut n) xs

  islim : ∀ n → !^ (suc n) (trees (suc n)) ≡ trees n
  islim n = FMSet.elimProp {P = λ xs → !^ (suc n) (map (cut (suc n)) xs) ≡ map (cut n) xs}
    (λ xs → isSetFMSet _ (FMSet.map (cut n) xs)) goal xs where
    module _ {sz} (xs : Fin sz → Lim FMSet) where
      goal : map (!^ n) (map (cut (suc n)) (sz , [ xs ]∼)) ≡ map (cut n) (sz , [ xs ]∼)
      goal =
        map (!^ n) (map (cut (suc n)) (sz , [ xs ]∼)) ≡⟨⟩
        (sz , [ (!^ n) ∘ cut (suc n) ∘ xs ]∼)         ≡⟨ FMSetPathP (refl {x = sz}) (cong [_]∼ (funExt λ k → xs k .isChainLimit n)) ⟩
        (sz , [ (cut n) ∘ xs ]∼)                      ≡⟨⟩
        map (cut n) (sz , [ xs ]∼)                    ∎

isShLim→ConstSizeSuc :
  (xs : (n : ℕ) → FMSet ^ (suc n))
  → isShLim FMSet xs
  → ∀ n → xs (suc n) .size ≡ xs n .size
isShLim→ConstSizeSuc xs islim n = cong size (islim n)

isShLim→ConstSize :
  (xs : (n : ℕ) → FMSet ^ (suc n))
  → isShLim FMSet xs
  → ∀ n → xs n .size ≡ xs 0 .size
isShLim→ConstSize xs islim = prf where
  prf : ∀ n → xs n .size ≡ xs 0 .size
  prf zero = refl
  prf (suc n) = isShLim→ConstSizeSuc xs islim n ∙ prf n

ShLim→ConstSize : (l : ShLim FMSet) → ∀ n → l .elements n .size ≡ l .elements 0 .size
ShLim→ConstSize l = isShLim→ConstSize (l .elements) (l .isChainLimit)

open import Multiset.AxiomChoice using (elimCollProp ; hasChoice ; [_⇒-d_]/_ ; θ-d ; PW-d)

record Depth : Type where
  constructor depth
  field
    undepth : ℕ

open Depth

module _ (sz : ℕ) where
  IVec : Depth → Type
  IVec d = Fin sz → FMSet ^ (undepth d)

  R : ∀ d → (IVec d) → (IVec d) → Type _
  R d = SymmetricAction {X = FMSet ^ (undepth d)} sz

module Surjectivity
  (choice : ∀ sz → (∀ n → IVec sz n / R sz n) → (∀ n → IVec sz n) / PW-d (R sz))
  (choice-sec : ∀ sz → section (θ-d (R sz)) (choice sz))
  (chose-perm : ∀ {X : Type} sz {v w : Fin sz → X} → v ∼ w → Σ[ σ ∈ (Fin sz ≃ Fin sz) ] v ≡ w ∘ (equivFun σ))
  where

  open Limit using (lim)

  module ConstSize (sz : ℕ) (xs : (d : Depth) → PVect (FMSet ^ (undepth d)) sz) where
    constSzLim : (d : Depth) → FMSet ^ (suc (undepth d))
    constSzLim d = sz , xs d

    inhFibers : (islim : isShLim FMSet (constSzLim ∘ depth)) → ∥ fiber zip (lim (constSzLim ∘ depth) islim) ∥₁
    inhFibers = elimCollProp {A = Depth} (λ d → Fin sz → FMSet ^ (undepth d))
      (λ _ → SymmetricAction sz) (λ _ → isPropValued-∼ sz) (λ _ → isEquivRel-∼ sz)
      (choice sz) (choice-sec sz)
      Motive isPropMotive goal xs where

      Motive : (∀ d → (Fin sz → FMSet ^ undepth d) / SymmetricAction sz) → Type
      Motive = λ approx → (islim : isShLim FMSet λ d → sz , approx (depth d)) → ∥ fiber zip (lim (λ d → sz , approx (depth d)) islim) ∥₁

      isPropMotive : ∀ d → isProp (Motive d)
      isPropMotive d = isPropΠ λ _ → PT.isPropPropTrunc

      goal : (approx : ∀ d → Fin sz → FMSet ^ undepth d) → Motive (λ d → [ approx d ]∼)
      goal approx islim = ∣ preimage , shiftedLimitPath preimage-in-fiber ∣₁ where
        _ : isShLim FMSet (λ d → ⟅ [ approx (depth d) ]∼ ⟆)
        _ = islim

        islim-[approx] : ∀ d →  [ (!^ d) ∘ (approx (depth (suc d))) ]∼ ≡ [ approx (depth d) ]∼
        islim-[approx] d =
          fromPathP[] (cong size (islim d)) _ _ (cong snd (islim d))
          ∙ isSubstInvariantˡ (approx (depth d)) (cong size (islim d))

        approx-!-rel : ∀ d → (!^ d) ∘ (approx (depth (suc d))) ∼ approx (depth d)
        approx-!-rel d = effective sz (islim-[approx] d)

        σs : ∀ d → Fin sz ≃ Fin sz
        σs d = chose-perm sz (approx-!-rel d) .size

        σs⁺ : ∀ d → Fin sz → Fin sz
        σs⁺ d = equivFun (σs d)

        σs⁻ : ∀ d → Fin sz → Fin sz
        σs⁻ d = invEq (σs d)

        σs-rel : ∀ d → !^ d ∘ approx (depth (suc d)) ≡ approx (depth d) ∘ σs⁺ d
        σs-rel d = chose-perm sz (approx-!-rel d) .snd

        ρs : ∀ (d : ℕ) → Fin sz ≃ Fin sz
        ρs zero = idEquiv _
        ρs (suc d) = ρs d ∙ₑ invEquiv (σs d)

        ρs⁺ : ∀ d → Fin sz → Fin sz
        ρs⁺ d = equivFun (ρs d)

        approx' : ∀ k d → FMSet ^ d
        approx' k d = approx (depth d) (ρs⁺ d k)

        islim-approx' : ∀ k → isLim FMSet (λ d → approx' k d)
        islim-approx' k d =
          !^ d (approx (depth (suc d)) $ ρs⁺ (suc d) k) ≡⟨ funExt⁻ (σs-rel d) (ρs⁺ (suc d) k) ⟩
          (approx (depth d) $ σs⁺ d $ ρs⁺ (suc d) k)    ≡⟨⟩
          (approx (depth d) $ σs⁺ d $ σs⁻ d $ ρs⁺ d k)  ≡⟨ cong (approx (depth d)) (secEq (σs d) (ρs⁺ d k)) ⟩
          (approx (depth d) $                 ρs⁺ d k)  ≡⟨⟩
          approx' k d ∎

        preimage-members : (Fin sz → Lim FMSet)
        preimage-members k .elements = approx' k
        preimage-members k .isChainLimit = islim-approx' k

        preimage : FMSet (Lim FMSet)
        preimage = (sz , [ preimage-members ]∼)

        approx'∼approx : ∀ d → (λ k → approx' k d) ∼ approx (depth d)
        approx'∼approx d = FMSet.invariantˡ sz (ρs d)

        preimage-in-fiber : ∀ n → zip preimage .elements n ≡ (sz , [ approx (depth n) ]∼)
        preimage-in-fiber n =
          zip preimage .elements n ≡⟨⟩
          (sz , [ (λ x → (approx' x n)) ]∼) ≡⟨ FMSetPath _ _ (approx'∼approx n) ⟩
          (sz , [ approx (depth n) ]∼) ∎

  inhFibers : (base : ShLim FMSet) → ∥ fiber zip base ∥₁
  inhFibers base = subst (λ l → ∥ fiber zip l ∥₁) (shiftedLimitPath (sym ∘ elements-path)) (ConstSize.inhFibers (base .elements 0 .size) xs islim-xs) where

    sz = base .elements 0 .size

    const-sz : ∀ d → base .elements (undepth d) .size ≡ sz
    const-sz d = ShLim→ConstSize base (undepth d)

    xs : (d : Depth) → PVect (FMSet ^ undepth d) sz
    xs d = subst (PVect (FMSet ^ undepth d)) (const-sz d) (base .elements (undepth d) .members)

    xs-elems = ConstSize.constSzLim sz xs ∘ depth

    elements-path : ∀ d → base .elements d ≡ xs-elems d
    elements-path d =
      base .elements d ≡⟨ FMSetPathP (ShLim→ConstSize base d) (toPathP refl) ⟩
      (sz , xs (depth d)) ≡⟨⟩
      (ConstSize.constSzLim (base .elements 0 .size) xs ∘ depth) d ∎

    islim-xs : isShLim FMSet xs-elems
    islim-xs d = cong (!^ (suc d)) (sym (elements-path (suc d))) ∙∙ (base .isChainLimit d) ∙∙ elements-path d
