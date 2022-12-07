{-# OPTIONS --safe #-}

module Multiset.FMSet.Limit where

open import Multiset.Prelude
open import Multiset.Util using (!_)

open import Multiset.FMSet.Base as FMSet
open import Multiset.FMSet.Properties as FMSet

open import Multiset.Limit.Chain as Chain
open import Multiset.Limit.TerminalChain as TerminalChain hiding (cut ; pres)

open import Cubical.Foundations.Function using (_∘_)
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Isomorphism using (section)
open import Cubical.Foundations.HLevels using (isPropΠ)
open import Cubical.Foundations.Univalence using (ua→;ua→⁻)

open import Cubical.HITs.SetQuotients as SQ using (_/_; [_])
open import Cubical.HITs.PropositionalTruncation as PT
  using (∥_∥₁ ; ∣_∣₁)

open import Cubical.Data.Nat.Base as Nat hiding (_^_)
open import Cubical.Data.SumFin.Base using (Fin ; isSetFin; inl; inr)
open import Cubical.Data.Unit as Unit using (isSetUnit)
open import Cubical.Data.Empty as Empty
open import Multiset.ListQuotient.FMSetEquiv

instance
  FunctorFMSet : Functor {ℓ = ℓ-zero} FMSet
  FunctorFMSet .Functor.map = FMSet.map
  FunctorFMSet .Functor.map-id = FMSet.mapId
  FunctorFMSet .Functor.map-comp = λ { g f xs → sym (mapComp g f xs) }

open Limit using (elements ; is-lim)

!^ : ∀ n → FMSet ^ (suc n) → FMSet ^ n
!^ n = FMSet map-!^ n

shiftedLimitPath : ∀ {shlim₁ shlim₂} → (∀ n → shlim₁ .elements n ≡ shlim₂ .elements n) → shlim₁ ≡ shlim₂
shiftedLimitPath = isSet→ShLimPath FMSet λ k → isSetFMSet

private
  cut : (n : ℕ) → Lim FMSet → FMSet ^ n
  cut = TerminalChain.cut FMSet

pres : FMSet (Lim FMSet) → ShLim FMSet
pres = TerminalChain.pres FMSet

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
ShLim→ConstSize l = isShLim→ConstSize (l .elements) (l .is-lim)

open import Multiset.AxiomChoice using (elimCollProp ; hasChoice ; [_⇒-d_]/_ ; θ-d ; PW-d)

record Depth : Type where
  constructor depth
  field
    undepth : ℕ

open Depth

open import Multiset.Ordering.Order
open import Multiset.Ordering.FMSetOrder

isSetFMSet^ : ∀ n → isSet (FMSet ^ n)
isSetFMSet^ zero = Unit.isSetUnit*
isSetFMSet^ (suc n) = isSetFMSet

⊥Rel : {A : Type} → A → A → Type
⊥Rel _ _ = Empty.⊥

isLinOrder⊥Rel : isLinOrder {A = Unit*} ⊥Rel
isLinOrder⊥Rel =
  record { asymR = λ { () }
         ; transR = λ { () }
         ; propR = λ { () }
         ; totR = λ _ _ → inr (inr refl)
         }

open MsetLinOrder
open SortingFMSet

LexFMSet^ : ∀ n → FMSet ^ n → FMSet ^ n → Type
linLexFMSet^ : ∀ n → isLinOrder (LexFMSet^ n)

LexFMSet^ zero = ⊥Rel
LexFMSet^ (suc n) = LexFMSet (isSetFMSet^ n) (LexFMSet^ n) (linLexFMSet^ n)

linLexFMSet^ zero = isLinOrder⊥Rel
linLexFMSet^ (suc n) = linLexFMSet (isSetFMSet^ n) (LexFMSet^ n) (linLexFMSet^ n)

module _ (sz : ℕ) where
  IVec : Depth → Type
  IVec d = Fin sz → FMSet ^ (undepth d)

  R : ∀ d → (IVec d) → (IVec d) → Type _
  R d = SymmetricAction {X = FMSet ^ (undepth d)} sz

  sort^ : ∀ n → IVec n / R n → IVec n
  sort^ (depth zero) x _ = tt*
  sort^ (depth (suc n)) =
    sortPVect isSetFMSet _ (linLexFMSet^ (suc n)) sz

  section-sort^ : ∀ n (x : IVec n / R n) → SQ.[ sort^ n x ] ≡ x
  section-sort^ (depth zero) = SQ.elimProp (λ _ → _/_.squash/ _ _) (λ _ → refl)
  section-sort^ (depth (suc n)) =
    sortPVect-section isSetFMSet _ (linLexFMSet^ (suc n)) sz

  choice : (∀ n → IVec n / R n) → (∀ n → IVec n) / PW-d R
  choice x = SQ.[ (λ n → sort^ n (x n)) ]

  choice-sec : section (θ-d R) choice
  choice-sec x = funExt (λ n → section-sort^ n (x n))

  chose-perm : ∀ d {v w : Fin sz → FMSet ^ d}
    → v ∼ w → Σ[ σ ∈ (Fin sz ≃ Fin sz) ] v ≡ w ∘ (equivFun σ)
  chose-perm d {v}{w} r = cp .fst , funExt (λ k → ua→⁻ (cp .snd) k)
    where
      cp : SymmetricActionΣ sz v w
      cp = canonicalS (isSetFMSet^ d) (LexFMSet^ d) (linLexFMSet^ d) sz v w r

module Surjectivity where

  module ConstSize (sz : ℕ) (xs : (d : Depth) → PVect (FMSet ^ (undepth d)) sz) where
    constSzLim : (d : Depth) → FMSet ^ (suc (undepth d))
    constSzLim d = sz , xs d

    inhFibers : (islim : isShLim FMSet (constSzLim ∘ depth)) → ∥ fiber pres (lim (constSzLim ∘ depth) islim) ∥₁
    inhFibers = elimCollProp {A = Depth} (λ d → Fin sz → FMSet ^ (undepth d))
      (λ _ → SymmetricAction sz) (λ _ → isPropValued-∼ sz) (λ _ → isEquivRel-∼ sz)
      (choice sz) (choice-sec sz)
      Motive isPropMotive goal xs where

      Motive : (∀ d → (Fin sz → FMSet ^ undepth d) / SymmetricAction sz) → Type
      Motive = λ approx → (islim : isShLim FMSet λ d → sz , approx (depth d)) → ∥ fiber pres (lim (λ d → sz , approx (depth d)) islim) ∥₁

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

        σ[_] : ∀ d → Fin sz ≃ Fin sz
        σ[_] d = chose-perm sz d (approx-!-rel d) .fst

        σ[_]⁺ : ∀ d → Fin sz → Fin sz
        σ[_]⁺ d = equivFun σ[ d ]

        σ[_]⁻ : ∀ d → Fin sz → Fin sz
        σ[_]⁻ d = invEq σ[ d ]

        σ-rel : ∀ d → !^ d ∘ approx (depth (suc d)) ≡ approx (depth d) ∘ σ[ d ]⁺
        σ-rel d = chose-perm sz d (approx-!-rel d) .snd

        σ*[_] : ∀ (d : ℕ) → Fin sz ≃ Fin sz
        σ*[_] zero = idEquiv _
        σ*[_] (suc d) = σ*[ d ] ∙ₑ invEquiv σ[ d ]

        σ*[_]⁺ : ∀ d → Fin sz → Fin sz
        σ*[_]⁺ d = equivFun σ*[ d ]

        approx' : ∀ k d → FMSet ^ d
        approx' k d = approx (depth d) (σ*[ d ]⁺ k)

        islim-approx' : ∀ k → isLim FMSet (λ d → approx' k d)
        islim-approx' k d =
          !^ d (approx (depth (suc d)) $ σ*[ suc d ]⁺ k)       ≡⟨ funExt⁻ (σ-rel d) (σ*[ suc d ]⁺ k) ⟩
          (approx (depth d) $ σ[ d ]⁺ $ σ*[ suc d ]⁺       k)  ≡⟨⟩
          (approx (depth d) $ σ[ d ]⁺ $ σ[ d ]⁻ $ σ*[ d ]⁺ k)  ≡⟨ cong (approx (depth d)) (secEq σ[ d ] (σ*[ d ]⁺ k)) ⟩
          (approx (depth d) $                     σ*[ d ]⁺ k)  ≡⟨⟩
          approx' k d ∎

        preimage-members : (Fin sz → Lim FMSet)
        preimage-members k .elements = approx' k
        preimage-members k .is-lim = islim-approx' k

        preimage : FMSet (Lim FMSet)
        preimage = (sz , [ preimage-members ]∼)

        approx'∼approx : ∀ d → (λ k → approx' k d) ∼ approx (depth d)
        approx'∼approx d = FMSet.invariantˡ sz σ*[ d ]

        preimage-in-fiber : ∀ n → pres preimage .elements n ≡ (sz , [ approx (depth n) ]∼)
        preimage-in-fiber n =
          pres preimage .elements n         ≡⟨⟩
          (sz , [ (λ x → (approx' x n)) ]∼) ≡⟨ FMSetPath _ _ (approx'∼approx n) ⟩
          (sz , [ approx (depth n) ]∼)      ∎

  inhFibers : (base : ShLim FMSet) → ∥ fiber pres base ∥₁
  inhFibers base = subst (λ l → ∥ fiber pres l ∥₁) (shiftedLimitPath (sym ∘ elements-path)) (ConstSize.inhFibers (base .elements 0 .size) xs islim-xs) where

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
    islim-xs d = cong (!^ (suc d)) (sym (elements-path (suc d))) ∙∙ (base .is-lim d) ∙∙ elements-path d
