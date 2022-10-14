# Final Coalgebras of Analytic Functors in Homotopy Type Theory

## Abstract

Coalgebras for the finite bag functor are dynamical systems where the
transition relation is resource-sensitive: the collection of reachable states
records the number of ways in which each state can be reached. The final
coalgebra of the finite bag functor is employed as a denotational domain for
the evaluation of such dynamical systems. Its elements are non-wellfounded
trees with finite unordered branching, representing the evolution of systems
starting from a given initial state.

This paper is dedicated to the construction of the final coalgebra of the
finite bag functor in homotopy type theory (HoTT). We first compare various
equivalent definitions of finite bags employing higher inductive types, both as
sets and as groupoids (in the sense of HoTT). We then analyze a few classical
set-theoretic constructions of final coalgebras in our constructive setting. We
show that, in the case of set-based definitions of finite bags, these
constructions are either intrinsically classical, in the sense that they are
equivalent to some weak form of excluded middle, or cannot be directly
reproduced in HoTT without the assumption of classical principles. The final
coalgebra can be safely constructed in HoTT only employing the groupoid-based
definition of finite bags. We also briefly discuss generalizations of these
constructions to other analytic functors and an alternative way of building the
final coalgebra of the finite bag functor using Cubical Agda's coinductive
types.

## Formalization in Agda

See [README.agda](README.agda) for a summary of the library that lives under
`Multiset/`.

# License

With the exception of the `tex/` directory, all files in this project are
licensed under the terms of the MIT License, see [LICENSE](LICENSE).
