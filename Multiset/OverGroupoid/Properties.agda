module Multiset.OverGroupoid.Properties where

open import Multiset.OverGroupoid.Base

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
import Cubical.Data.FinSet as FinSet

private
  variable
    ℓ : Level
    X : Type ℓ

isGroupoidFMSet : isGroupoid X → isGroupoid (FMSet X)
isGroupoidFMSet h = isOfHLevelΣ 3 FinSet.isGroupoidFinSet λ _ → isOfHLevelΠ 3 (λ _ → h)
