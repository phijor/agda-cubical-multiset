{-# OPTIONS --safe #-}

module Multiset.Coalgebra where

open import Multiset.Prelude
open import Multiset.Functor

open import Cubical.Foundations.Function using (idfun ; _∘_)
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism

private
  variable
    ℓ : Level

module _ {ℓ} (F : Type ℓ → Type ℓ) {{FunctorF : Functor F}} where
  open Functor FunctorF
    renaming (map to F[_])

  isCoalgebraMorphism : ∀ {A B} → (α : A → F A) → (β : B → F B) → (f : A → B) → Type _
  isCoalgebraMorphism α β f = β ∘ f ≡ F[ f ] ∘ α

  isSet→isPropIsCoalgebraMorphism : ∀ {A B}
    → (α : A → F A) → (β : B → F B) → (f : A → B)
    → isSet (F B) → isProp (isCoalgebraMorphism α β f)
  isSet→isPropIsCoalgebraMorphism {A} {B} α β f setF = setA→FB (β ∘ f) (F[ f ] ∘ α) where
    setA→FB : isSet (A → F B)
    setA→FB = isSet→ setF

  CoalgebraMorphism : ∀ {A B} → (α : A → F A) → (β : B → F B) → Type _
  CoalgebraMorphism α β = Σ[ f ∈ (_ → _) ] isCoalgebraMorphism α β f

  isTerminal : ∀ {νF} (out : νF → F νF) → Type _
  isTerminal out = ∀ {B} → (β : B → F B) → isContr (CoalgebraMorphism β out)

  module _ {νF} {out : νF → F νF} (is-terminal : isTerminal out) where
    ana : ∀ {B} → (β : B → F B) → CoalgebraMorphism β out
    ana β = is-terminal β .fst

    anaEq : ∀ {B} {β : B → F B} → (f : CoalgebraMorphism β out) → ana β ≡ f
    anaEq {β = β} f = is-terminal β .snd f

-- Set-valued functors (in the above sense) integrate nicely into to
-- hierarchy of categories defined in the Cubical library:
module _ {ℓ}
  (F : Type ℓ → Type ℓ)
  {{FunctorF : Functor F}}
  (setValued : ∀ {X} → isSet X → isSet (F X))
  where
  open Functor FunctorF

  open import Multiset.Categories.Coalgebra

  import Cubical.Categories.Functor as Cat
  open import Cubical.Categories.Instances.Sets as Sets using (SET)

  private
    F' : Cat.Functor (SET ℓ) (SET ℓ)
    F' .Cat.Functor.F-ob (X , setX) = F X , setValued setX
    F' .Cat.Functor.F-hom = map
    F' .Cat.Functor.F-id = map-id-ext
    F' .Cat.Functor.F-seq f g = map-comp-ext g f
    
  isSetValued→CatFunctor : Cat.Functor (SET ℓ) (SET ℓ)
  isSetValued→CatFunctor = F'

  module _ {νF} (set-νF : isSet νF) (out : νF → F νF) where
    open Coalgebra
    private
      out' : Coalgebra F'
      out' .carrier = νF , set-νF
      out' .str = out

    isSetValued→Coalgebra : Coalgebra F'
    isSetValued→Coalgebra = out'

    module _ (term : isTerminal F out) where
      ana' : ∀ β → CoalgebraHom F' β out'
      ana' β = CoalgebraHomIsoΣ F' .Iso.inv ana-β where
        ana-β : CoalgebraMorphism F (β .str) out
        ana-β = ana F {out = out} term (β .str)

      anaEq' : ∀ {β} → (f : CoalgebraHom F' β out') → ana' β ≡ f
      anaEq' {β} f = cong (CoalgebraHomIsoΣ F' .Iso.inv) anaEq-f where
        anaEq-f : ana F {out = out} term (β .str) ≡ CoalgebraHomIsoΣ F' .Iso.fun f
        anaEq-f = anaEq F {out = out} term (CoalgebraHomIsoΣ F' .Iso.fun f)

    isSetValued→TerminalCoalgebra : isTerminal F out → TerminalCoalgebra isSetValued→CatFunctor
    isSetValued→TerminalCoalgebra term .fst = out'
    isSetValued→TerminalCoalgebra term .snd β = ana' term β , anaEq' term
