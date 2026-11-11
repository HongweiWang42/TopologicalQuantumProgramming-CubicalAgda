# Topological Quantum Programming in Cubical Agda

Research on the formalization and computational realization of topological
quantum programming in Cubical Agda.

## Overview

This repository is a long-term mathematical software research programme. Its
central question is whether topological quantum transformations can be
realized computationally as transport in dependent types within Cubical Agda.
The programme brings together Homotopy Type Theory and Cubical Type Theory
with braid groups and monodromy, classifying spaces, dependent type families,
and the computational behaviour of transport along loops.

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

## Research architecture

The following diagram is a conceptual research architecture. It is not a
claimed dependency theorem or a fully established construction.

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

| Component | Language | Status | Verified boundary | Open boundary |
|---|---|---|---|---|
| [Group presentations as homotopy pushouts](docs/FORMALIZATIONS.md#group-presentations-as-homotopy-pushouts) | Cubical Agda | Type-checked foundational construction | Surjectivity of the canonical presentation homomorphism | Injectivity, the resulting group isomorphism, and the classifying-space equivalence |

The corresponding [Agda source guide](src/GroupPresentation/README.md) and
[Shadow Paper](papers/GroupPresentations/README.md) give the mathematical
derivation order and a source-traceable exposition. The complete formalized
boundary is maintained in [docs/FORMALIZATIONS.md](docs/FORMALIZATIONS.md)
and [docs/FORMALIZATION_STATUS.md](docs/FORMALIZATION_STATUS.md).

## Navigation

- [Formalized developments](docs/FORMALIZATIONS.md) -- verified constructions,
  precise theorem statements, and source modules.
- [Agda sources](src/GroupPresentation/README.md) -- mathematical reading
  order for the current development.
- [Shadow Papers](papers/GroupPresentations/README.md) -- mathematical
  exposition and the compiled PDF.
- [Reproducibility](docs/REPRODUCIBILITY.md) -- pinned environment and exact
  checking commands.
- [Research roadmap](docs/RESEARCH_DIRECTION.md) -- proposed constructions
  and unresolved implementation challenges.
- [Alignment records](alignment/records.jsonl) -- statement-to-source
  provenance.

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
