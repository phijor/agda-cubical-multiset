# Outline

## Coalgebras

* Definition of coalgebra and coalgebra-morphism
* Definition of being a final coalgebra:

```agda
    isFinal : (C : Coalgebra F) → Type
    isFinal C = ∀ C' → isContr (CoalgebrasMap C' C)
```

* Definition of "an object A has a final coalgebra for F":
```agda
    hasFinal : (A : Type) → Type
    hasFinal A = Σ (ω : A → F A) (isFinal ω)
```
* Question/Conjecture: `hasFinal` is a proposition

## Corecursive algebras

* Definition algebra-coalgebra maps:
    - a coalgebra `ω : B → F B`
    - an algebra `α : F A → A`

    - ... is a map `f : B → A`, such that:

        ```
          B -----------> F B
          |               |
        f |               | F f
          |               |
          v               v
          A <----------- F A
        ```

* Definition of a corecursive algebra
    - an algebra `α : F A → A` such that:

        ```agda
        ∀ ω : B → F B:  isContr(AlgCoalgMap(α , ω))
        ```

* Definition of "an object A has a corecursive algebra":

    ```agda
    hasCorecursive : (A : Type) → Type
    hasCorecursive A = Σ (α : F A → A) (isCorecursive α)
    ```

* Question: Is there a theorem that says:
    TFAE:
    * A has a final coalgebra
    * A has a corecursive algebra that is an equivalence

## Limits

* should contain at least all the stuff from Multiset/Limits.agda
* A general construction of the limit-object `Lim C` for a ω-(co?)chain `C`
* define universal property of these limits: `up : (A → Lim C) ≃ Cone C F`

Preservation of limits for a functor `F: Type → Type`

* Define the canonical map

    ```
    σ : F (Lim C) → Lim (shift F C)
    ```

  where `shift F C : Chain` is the chain obtained from
  applying F at each object.

* Definition: F preserves ω-limits if σ is an equivalence for all chains C.

* Prove that there is an equivalence `Shift≃ : Lim C ≃ Lim (shift F C)`


## Putting it together

* Define:
    - `!-Chain F := 1 ← F 1 ← F² 1 ← F³ 1 ← ...`
    - `!-Lim F := Lim (!-Chain F)`
    - a canonical map `α: F(!-Lim F) → !-Lim F`

* Conjecture:
    For polynomial functors, α is an equivalence.

    Proof:
    1) α factors through the shifted limit:

        ```
                            α
        F(!-Lim F) --------------------> !-Lim F
            |                               ^
         σ  |                               | Shift≃
            |                               |
            '--> Lim (shift F (!-Chain F)) -'
        ```

    2) prove that σ is an equivalence (follows from the fact that F
        preserves ω-limits)

* Theorem: `α` is corecursive.
    (Hidden in Ahrens 2015, Proof thm 7, step 16 onwards)

## Particular functors

* Give different presentations of the multiset functor:
    OverSet (`MS`), OverGroupoid (`MG`), small version `Bij`, ...
* Lemmata connecting these:
    - set truncation of MG is equivalent to MS
    - `MS (setTrunc X) ≃ MS X`

## Construction of final coalgebra of MS via groupoid (or something)

* Corollary:
    - can define a fixed point for MS:
        It's the set truncation of the final coalgebra of MG.

        1) `ω : (!-Lim MG) → MG (!-Lim MG)` (that's the final coalgebra)
        2) `fixMS : MS (setTrunc (!-Lim MG)) ≃ setTrunc (!-Lim MG)`

        (Follows from the lemmata and the ex. of the final coalgebra,
        since `MG` is a polynomial "functor")

* Theorem (**):
    `inv(fixMS) : (setTrunc (!-Lim MG)) → MS (setTrunc (!-Lim MG))`
    is final wrt. finite coalgebra (see below)

    ```agda
    isFinalFinite : (C : Coalgebra F) → Type
    isFinalFinite C = ∀ C' → isFinite ⟨ C' ⟩ × isContr (CoalgebrasMap C' C)
    ```

* Question: Is "final wrt. finite carriers" a known concept in category theory?
    We can't say its final on the subcategory of finite things, since it does not
    have a finite carrier itself.

## Construction of final coalgebra of MS via lists

* There's another fixed point (prove directly):
    - `fixList := (!-Lim List) / R`
    - `R` := Two nested lists are related if they are level-wise
             permutation of each other.
* Proof works particularly well if MS is defined as lists quotiented by permutations.
* Theorem: Theorem (**), but with fixList instead of `setTrunc (!-Lim MG)`.

## Fun with choice arguments

* `inv(fixMS)` becomes a final coalgebra (without restrictions on size) if we
  assume *some* form of choice.
* also works for `fixList`. But this might be a different form of choice
* Question: What form(s) of choice?

## Looking at `!-Lim MS`

* We know this has a corecursive algebra structure.
* Question: is this an equivalence?
* Idea: Prove that MS preserves ω-limits. Try to replicate Ahrens' Lemma 13.
    - this seems to require countable choice for general ω-limits.
* Definition (countable choice)
    - Look at [this](https://github.com/niccoloveltri/final-pfin/blob/main/AxiomChoice.agda)
    - Take A = ℕ
    - the pair (B, R) satisfy countable choice iff θ has a section.
* Definition (dependent countable choice):
    - Have `B : ℕ → Type`, `R : (n : ℕ) → B n → B n → Type`
    - Quotient on dependent function space:
        `[n ↦ B n]/ R := ((n : ℕ) → B n) / (b b' ↦ (n : ℕ) → R n (b n) (b' n))`
    - Define `θ : [n ↦ B n]/ R → (n : ℕ) → (B n / R n)` by recursion on set quotients
    - the pair (B, R) has dependent choice if θ has a section
    - TODO: compare this to the usual definition of countable choice.
        (give a logical equivalence)
* Conjecture: The quotienting by `SymmetricAction` in `!-Lim MS` (!!!) satisfies countable choice.
    Proof: Show that each equivalence class has a canonical representative,
           by giving linear order on all elements of the chain `!-Chain MS`.
           This is order is the "almost-lexicographic order".
