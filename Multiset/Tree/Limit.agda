module Multiset.Tree.Limit where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Unit using (isSetUnit)
open import Cubical.Data.Sigma using (Σ≡Prop)

import Multiset.Limits

open import Multiset.Tree.Base

open module MCone = Multiset.Limits.ωCone !-ωCochain

-- To show that ωTree is a limit of the !-cochain,
-- we must construct a cone with it at the apex...
Lim : ωCone
Lim = record
  { Apex = ωTree
  ; leg = λ n (level , _) → level n
  ; cond = λ n (_ , cut) → cut n
  }

-- ...and show that this cone is terminal.
-- We get a function into ωTree for free for any other cone V:
Lim-map : (V : ωCone) → V .Apex → ωTree
Lim-map V v = (λ n → V .leg n v) , λ n → V .cond n v


-- This map is trivially a cone map.
Lim-up-∃ : (V : ωCone) → ωConeMap V Lim
Lim-up-∃ V = record
  { map = Lim-map V
  ; commutes = λ n v → refl
  }

-- Indeed, it is also equal to any other map into the limit.
Lim-up-!-map : (V : ωCone) (f : ωConeMap V Lim)
  → Lim-map V ≡ f .map
Lim-up-!-map V f = funExt (λ v → Σ≡Prop isProp-ωTree-cut (funExt λ n → sym (f .commutes n v)))

-- Since equality of cone maps is a proposition when the chain
-- consists of sets, we can show that this extends to an equality
-- of cone maps proper.
Lim-up-! : (V : ωCone) (f : ωConeMap V Lim)
  → Lim-up-∃ V ≡ f
Lim-up-! V f = ωConeMap≡Prop (isSet-iterM isSetUnit) (Lim-up-!-map V f)

-- Since we have both existence and uniqueness of a final cone map,
-- this concludes the proof that ω-Trees form a limit over the !-chain.
Lim-is-Limit : is-Limit Lim
Lim-is-Limit V = (Lim-up-∃ V) , (Lim-up-! V)
