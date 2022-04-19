module Multiset.SigOverGroupoid.Properties where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Function
  using (_∘_)
open import Cubical.Foundations.Structure

open import Multiset.SigOverGroupoid.Base
open import Multiset.SigOverGroupoid.GroupoidToSubgroup
open import Multiset.SigOverGroupoid.SubgroupToGroupoid


private
  variable
    ℓ ℓPos ℓOp : Level

ℓSh : Level
ℓSh = ℓ-zero

invoGpd : GroupoidSignature ℓSh ℓPos → GroupoidSignature ℓSh ℓ-zero
invoGpd = toGpdSig ∘ toSubGpSig

invoGpdRefl : ∀ Sig → invoGpd Sig ≡ Sig
invoGpdRefl Sig = {! (invoGpd Sig) .Shape   !} where
  open GroupoidSignature
  open SubgroupSignature

  invoShape : (invoGpd Sig) .Shape ≡ Fatten.Fattened ((toSubGpSig Sig) .Op) λ op → ⟨ SymmGrp (toSubGpSig Sig) op ⟩
  invoShape = refl

invoSubgp : SubgroupSignature ℓ-zero → SubgroupSignature ℓ-zero
invoSubgp Sig = toSubGpSig (toGpdSig Sig)

invoSubgpRefl : (Sig : SubgroupSignature ℓ-zero) → invoSubgp Sig ≡ Sig
invoSubgpRefl Sig = {!   !} where
  open SubgroupSignature
