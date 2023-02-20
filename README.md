# Final Coalgebras of Analytic Functors in Homotopy Type Theory

## Abstract

Finitely-branching and unlabelled dynamical systems are typically modelled as coalgebras for the finite powerset functor.
If states are reachable in multiple ways, coalgebras for the finite bag functor provide a more faithful representation.
The final coalgebra of this functor is employed as a denotational domain for the evaluation of such systems.
Elements of the final coalgebra are non-wellfounded trees with finite unordered branching,
representing the evolution of systems starting from a given initial state.

This paper is dedicated to the construction of the final coalgebra of the finite bag functor in homotopy type theory (HoTT).
We first compare various equivalent definitions of finite bags employing higher inductive types, both as sets and as groupoids (in the sense of HoTT).
We then analyze a few well-known, classical set-theoretic constructions of final coalgebras in our constructive setting.
We show that, in the case of set-based definitions of finite bags,
some constructions are intrinsically classical, in the sense that they are equivalent to some weak form of excluded middle.
Nevertheless, the final coalgebra can be safely constructed in HoTT employing the groupoid-based definition of finite bags.
We conclude by discussing generalizations of our constructions to the wider class of analytic functors.

## Formalization in Agda

Claims in the paper have been formalized in a library that lives under `Multiset/`.
The file [`README.agda`](https://phijor.github.io/agda-cubical-multiset/README.html) contains a summary of the library.
Whenever a claim in the paper is decorated with an identifier `Foo`,
the corresposing formalization can be found at `Foo` in `README.agda`.

# License

With the exception of the `tex/` directory, all files in this project are
licensed under the terms of the MIT License, see [LICENSE](LICENSE).
