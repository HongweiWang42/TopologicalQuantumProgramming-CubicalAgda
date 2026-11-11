# Topological Quantum Programming in Cubical Agda

Research on the formalization and computational realization of topological
quantum programming in Cubical Agda.

## Overview

This repository is a long-term mathematical software research programme. Its
central question is whether dependent-type transport in Cubical Type Theory
can provide an executable realization of topological quantum transformations.
The programme relates Homotopy Type Theory and Cubical Type Theory to braid
groups and monodromy, classifying spaces, dependent type families, and
transport along loops. Its central challenge is not only to formalize the
existence and mathematical properties of the relevant transformations, but
also to determine whether the corresponding transport operations have
nontrivial computational behaviour.

The principal mathematical motivation is Myers--Sati--Schreiber,
[*Topological Quantum Gates in Homotopy Type Theory*](https://arxiv.org/abs/2303.02382),
especially Definition 6.7. This reference motivates the research direction;
it does not mean that Definition 6.7, braid-group actions, or executable
topological quantum gates have already been formalized here.

## Research objectives

The programme investigates four related directions. They are research
directions, not completed implementation stages.

1. **Homotopy-theoretic foundations.** Group presentations, classifying
   spaces, higher inductive types, braid groups, homotopy pushouts, and
   truncations.
2. **Geometric and dependent-type structures.** The complex multiplicative
   group, torsors, classifying types, mapping types, and dependent families.
3. **Computational transport and monodromy.** Transport along loops, induced
   transformations, and the computational behaviour of dependent types.
4. **Topological quantum programming.** Formal implementation and
   computational investigation of the dependent-type construction associated
   with Definition 6.7.

## Computational objective

The ultimate objective is to construct a dependent type family representing
topological quantum states and to investigate whether transport along suitable
braid-group loops can compute the corresponding state transformations.

A computational realization requires more than a type-correct formalization
of the underlying mathematics. It requires explicit transport operations with
nontrivial computational behaviour, together with a formally justified
correspondence between those operations and the intended mathematical
quantum-gate semantics. Whether this can be achieved within the current
computational capabilities of Cubical Agda remains an open research question.

## Research architecture

The diagram summarizes the intended progression from foundational
formalization to computational interpretation. Individual constructions may
be developed independently or in parallel, and their precise dependencies
remain subject to mathematical investigation.

```text
Group presentations and classifying spaces
                 ↓
Braid-group and geometric structures
                 ↓
Dependent type families
                 ↓
Transport and monodromy
                 ↓
Computational topological quantum transformations
```

## Formalized developments

| Component | Language | Status | Verified results | Outstanding results |
|---|---|---|---|---|
| [Group presentations as homotopy pushouts](docs/FORMALIZATIONS.md#group-presentations-as-homotopy-pushouts) | Cubical Agda | Type-checked foundational construction | Surjectivity of the canonical presentation homomorphism | Injectivity, the resulting group isomorphism, and the classifying-space equivalence |

Detailed source modules, precise theorem statements, and the verified boundary
are maintained in [docs/FORMALIZATIONS.md](docs/FORMALIZATIONS.md) and
[docs/FORMALIZATION_STATUS.md](docs/FORMALIZATION_STATUS.md).

## Navigation

- [Formalized developments](docs/FORMALIZATIONS.md) -- verified constructions,
  precise theorem statements, and source modules.
- [Agda source code](src/) -- current Cubical Agda developments.
- [Shadow Papers](papers/) -- mathematical exposition and compiled papers.
- [Reproducibility](docs/REPRODUCIBILITY.md) -- pinned environment and exact
  checking commands.
- [Research roadmap](docs/RESEARCH_DIRECTION.md) -- proposed constructions
  and unresolved implementation challenges.
- [Alignment and provenance](alignment/) -- statement-to-source records.

## Reproducibility and verification

The checked development uses Agda `2.8.0-3d04bac` and the project-local
Cubical Agda dependency pinned at commit
`87af036ebd1c87956cf08fea44e62c7cf76392ca` (v0.9-compatible line). The
current local source modules typecheck in that environment. Detailed setup,
commands, and source-audit procedures are in
[docs/REPRODUCIBILITY.md](docs/REPRODUCIBILITY.md).

## Research references

- Myers, Sati, and Schreiber, [*Topological Quantum Gates in Homotopy Type
  Theory*](https://arxiv.org/abs/2303.02382).
- [Cubical Agda](https://github.com/agda/cubical), used here at the pinned
  revision recorded above.

## License

The local repository material is released under the [MIT License](LICENSE).
The `cubical/` checkout retains its own upstream licensing and provenance.
