# Final Coalgebras of Analytic Functors in Homotopy Type Theory

In set-theoretic foundations, the final coalgebra of a finitary functor can be
constructed in (ω+ω) steps [Worrell (2005)].  For particular finitary functors,
constructive proofs of this exist, and for polynomial functors it is known that
the same can be done constructively in ω steps [Ahrens, Capriotti (2015)].

Similarly, the intermediate class of _analytic functors_ yields final
coalgebras in ω steps when working classically.  We are interested whether the
same is true when working internally to HoTT.  We focus our work on the finite
multiset functor, a particular analytic functor.

Following [Kock (2012)], we define a polynomial functor over a groupoid and
show that its pointwise set-trunctation is equivalent to the ordinary finite
multiset functor.  We construct its final coalgebra as an ω-limit, and show
that it has as a fixed-point a type of finitely branching, non-wellfounded
trees. We conclude that the ordinary finite multiset functor has a final
coalgebra constructible in ω steps.

In the process, we give multiple formalizations of finite multisets in HoTT,
one as type of lists modulo permutations, and another one as the HIT of the
free commutative monoid, and connect these to prior work, e.g. [Choudhury, Fiore 2021].
To overcome size-issues, we port [Finster et. al.]'s axiomatization of a small
type of finite sets and bijections to cubical Agda.

[Ahrens, Capriotti (2015)]: https://doi.org/10.4230/LIPIcs.TLCA.2015.17
[Worrell (2005)]: https://doi.org/10.1016/j.tcs.2004.12.009
[Kock (2012)]: https://doi.org/10.1016/j.entcs.2013.01.001
[Choudhury, Fiore 2021]: https://arxiv.org/abs/2110.05412
[Finster et. al.]: https://arxiv.org/abs/2112.14050
