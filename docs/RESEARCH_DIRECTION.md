# Research roadmap

## Scope and mathematical motivation

The long-term research objective is to investigate whether topological
quantum transformations admit a computational realization as dependent-type
transport in Cubical Agda. The proposed programme is motivated by
Myers--Sati--Schreiber, [*Topological Quantum Gates in Homotopy Type
Theory*](https://arxiv.org/abs/2303.02382), in particular its Definition 6.7.

This document describes mathematical motivation and proposed constructions.
It does not assert that the listed constructions have been formalized, that
the displayed architecture is sufficient for the intended result, or that
executable quantum gates have been implemented.

## Verified foundation

The current verified component is the presentation-pushout development: the
canonical homomorphism from the algebraically presented group to the
fundamental group of the constructed truncated type is formally proved
surjective. Its injectivity, the associated group isomorphism, and the
classifying-space equivalence remain open. See
[FORMALIZATIONS.md](FORMALIZATIONS.md) for the exact theorem and source
boundary.

## Proposed formalization programme

### Braid groups and classifying spaces

A prospective direction is the study of braid-group presentations,
classifying spaces, and the homotopy-theoretic structures required to relate
their loop and transport behaviour to the intended geometric data. The
appropriate formal statements and hypotheses remain to be determined.

### Complex multiplicative groups and torsors

Another direction concerns the complex multiplicative group `C×`, torsor
constructions, and a classifying type `B(C×)`. This includes the question of
which available Cubical Agda representations of these objects support the
required homotopical and dependent-type constructions.

### Mapping types and dependent families

The proposed programme includes mapping types of the form `BG → B(C×)` and
the associated dependent families. Their precise formulation, universe
levels, basepoint data, and relation to the constructions motivated by
Definition 6.7 are open formalization questions.

### Computational transport and monodromy

The central computational issue is the behaviour of transport along loops in
the relevant dependent families. The programme seeks to study the induced
transformations, their monodromy interpretation, and the extent to which they
can be evaluated or represented computationally in Cubical Agda.

### Topological quantum transformations

The eventual objective is to investigate executable topological quantum
transformations arising from this dependent-type transport. This is a
long-term research goal rather than a theorem or an implemented subsystem of
the present repository.

## Open implementation challenges

The relationship between the verified group-presentation foundation and the
proposed later structures requires additional mathematical and formal work.
In particular, no current source proves a braid-group action, constructs the
required torsor or classifying-type machinery, formalizes Definition 6.7, or
establishes a computational realization of topological quantum gates.
