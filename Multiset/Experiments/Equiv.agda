module Multiset.Experiments.Equiv where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
  using
    ( invEquiv
    ; idEquiv
    ; invEquivIdEquiv
    ; compEquivEquivId
    ; _∙ₑ_
    )
open import Cubical.Foundations.Univalence
  using
    ( pathToEquiv
    ; pathToEquivRefl
    )
import Cubical.Foundations.GroupoidLaws as GpdLaws

private
  variable
    ℓ : Level
    X Y Z : Type

    p : X ≡ Y
    q : Y ≡ Z

-- TODO: This is not needed anymore, but keep it for later.
-- It's a useful lemma.
pathToEquivSymRefl : pathToEquiv (sym (refl {x = X})) ≡ invEquiv (pathToEquiv refl)
pathToEquivSymRefl =
  pathToEquiv (sym refl)
    ≡⟨ pathToEquivRefl ⟩
  idEquiv _
    ≡⟨ sym (invEquivIdEquiv _) ⟩
  invEquiv (idEquiv _)
    ≡⟨ sym (cong invEquiv pathToEquivRefl) ⟩
  invEquiv (pathToEquiv refl)
    ∎

pathToEquivSym : pathToEquiv (sym p) ≡ invEquiv (pathToEquiv p)
pathToEquivSym {p = p} = J (λ Y' p' → pathToEquiv (sym p') ≡ invEquiv (pathToEquiv p')) pathToEquivSymRefl p

pathToEquivCompRefl : pathToEquiv (p ∙ refl) ≡ (pathToEquiv p ∙ₑ pathToEquiv refl)
pathToEquivCompRefl {p = p} =
  pathToEquiv (p ∙ refl)
    ≡⟨ cong pathToEquiv (sym (GpdLaws.rUnit p)) ⟩
  pathToEquiv p
    ≡⟨ sym (compEquivEquivId (pathToEquiv p)) ⟩
  (pathToEquiv p ∙ₑ idEquiv _)
    ≡⟨ cong (pathToEquiv p ∙ₑ_) (sym pathToEquivRefl) ⟩
  (pathToEquiv p ∙ₑ pathToEquiv refl)
    ∎

pathToEquivComp : pathToEquiv (p ∙ q) ≡ pathToEquiv p ∙ₑ pathToEquiv q
pathToEquivComp {p = p} {q = q} = J (λ Z' q' → pathToEquiv (p ∙ q') ≡ pathToEquiv p ∙ₑ pathToEquiv q') pathToEquivCompRefl q
