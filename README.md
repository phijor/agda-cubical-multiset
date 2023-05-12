# Final Coalgebras of Analytic Functors in Homotopy Type Theory

![Type Checking](https://github.com/phijor/agda-cubical-multiset/actions/workflows/typecheck.yaml/badge.svg)
[![License: MIT](https://img.shields.io/badge/License-MIT-yellow.svg)](https://opensource.org/licenses/MIT)
[![License: CC BY 4.0](https://img.shields.io/badge/License-CC_BY_4.0-lightgrey.svg)](https://creativecommons.org/licenses/by/4.0/)
[![Software Heritage Archive](https://archive.softwareheritage.org/badge/origin/https://github.com/phijor/agda-cubical-multiset/)](https://archive.softwareheritage.org/browse/origin/?origin_url=https://github.com/phijor/agda-cubical-multiset)


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
Nevertheless, a type satisfying the universal property of the final coalgebra can be constructed in HoTT employing the groupoid-based definition of finite bags.
We conclude by discussing generalizations of our constructions to the wider class of analytic functors.

## Formalization in Agda

Claims in the paper have been formalized in a library that lives under `Multiset/`.
The file [`README.agda`](https://phijor.github.io/agda-cubical-multiset/README.html) contains a summary of the library.
Whenever a claim in the paper is decorated with an identifier `Foo`,
the corresposing formalization can be found at `Foo` in `README.agda`.

## Prerequisites

This library has been tested with the following software versions:
 * Agda v2.6.2.2
 * The Cubical library, [version 0.4](https://github.com/agda/cubical/releases/tag/v0.4) (23th Nov 2022)

## Type checking the code

Type check the code by running Agda in Safe Mode:

```console
$ agda --safe ./README.agda
```

Alternatively, use the provided Nix flake (see file `flake.nix`) to reproducibly
type check the library with all dependencies pinned to working versions:

```console
$ nix-build
```

or (with Nix flakes [enabled](https://nixos.wiki/wiki/Flakes#Enable_flakes)):

```console
$ nix build '.#multiset'
```

After a successful build, the directory `result/` will contain the Agda interface files.


## Hacking

A development shell that includes all of the dependencies can be spawned via `nix-shell`
(or `nix shell` if [enabled](https://nixos.wiki/wiki/Nix_command)):

```console
$ nix shell
[nix-shell]$ which agda
/nix/store/dfr3d08mx77isqzkgxnm0vr2rrfpc20x-agdaWithPackages-2.6.2.2/bin/agda
[nix-shell]$ agda --safe ./README.agda
...
```

The library can be rendered to a webpage using Agda's HTML backend:

```console
$ nix build '.#multiset.html'
$ # open result-html/README.html in your browser
$ xdg-open result-html/README.html
```

# License

With the exception of the `tex/` directory, all files in this project are
licensed under the terms of the MIT License, see [LICENSE](LICENSE).

Code under the `tex/` directory is distributed under the terms of [CC-BY 4.0](https://creativecommons.org/licenses/by/4.0/).
