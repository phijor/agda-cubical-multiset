module Multiset.SigOverGroupoid.Properties where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Function
  using (_∘_)

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
invoGpdRefl Sig = {! invoGpd Sig  !}
