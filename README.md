# TopologicalQuantumProgramming-CubicalAgda

This repository develops, in Cubical Agda, the generators-and-relations
construction that underlies a prospective account of computational type
transport for topological quantum gates. Its long-term mathematical target is
the construction used in Definition 6.7 of Myers--Sati--Schreiber,
*Topological Quantum Gates in Homotopy Type Theory* (arXiv:2303.02382).

The present formalization is deliberately narrower. Given arbitrary types of
generators and relations, with two finite signed words for each relation, it
constructs a suspension-based generator type, a relation-circle pushout, its
1-truncation, the algebraic presented group, and the canonical homomorphism
from that group to the fundamental group of the truncated pushout.

## Verified boundary

The following theorem is typechecked in
`src/GroupPresentation/CanonicalSurjectivity.agda`:

```agda
canonicalPresentationHom-surjective :
  (P : Presentation Gen Rel) →
  isSurjective (canonicalPresentationHom P)
```

Thus the canonical homomorphism from the algebraically presented group to the
fundamental group of the presentation type is verified to be surjective. No
claim of injectivity is made. Consequently, neither the group isomorphism nor
the identification of `BG_pres P` with a classifying space of the presented
group is formalized yet. In particular, Definition 6.7 and its computational
transport have not been formalized.

## Layout

- `src/` -- Cubical Agda sources. The mathematical reading order is recorded
  in [`src/GroupPresentation/README.md`](src/GroupPresentation/README.md).
- `papers/GroupPresentations/` -- the preliminary Shadow Paper, its compiled
  PDF, section sources, and an archived earlier draft.
- `alignment/` -- machine-readable statement-to-source traceability records.
- `docs/` -- formalization status, reproducibility notes, and the next
  research direction.
- `cubical/` -- the project-local pinned Cubical Agda checkout, retained as
  the repository's dependency; it is not locally maintained formalization
  source.

## Reproducibility

The checked environment is:

- Agda `2.8.0-3d04bac`;
- Cubical Agda commit `87af036ebd1c87956cf08fea44e62c7cf76392ca`
  (the v0.9-compatible line);
- XeLaTeX/`latexmk` for the Shadow Paper.

From the repository root, check every local module with:

```sh
for file in src/GroupPresentation.agda src/GroupPresentation/*.agda; do
  agda -i src -i cubical "$file" || exit $?
done
```

Compile the Shadow Paper with:

```sh
cd papers/GroupPresentations
latexmk -xelatex -interaction=nonstopmode -halt-on-error main.tex
```

The commands, expected results, and scope of the source audit are documented
in [`docs/REPRODUCIBILITY.md`](docs/REPRODUCIBILITY.md). The source-level
provenance of the paper is recorded in
[`alignment/records.jsonl`](alignment/records.jsonl).

On a future clone, initialize the pinned dependency before checking:

```sh
git submodule update --init --recursive
git -C cubical checkout 87af036ebd1c87956cf08fea44e62c7cf76392ca
```

## Next research direction

The next programme, discussed with Urs, is mathematical rather than an
implemented extension of this repository: braid-group classifying spaces,
`C×`-torsors and `B(C×)`, mapping types `BG → B(C×)`, and finally the
computational transport required by Definition 6.7. See
[`docs/RESEARCH_DIRECTION.md`](docs/RESEARCH_DIRECTION.md). These are
research directions, not verified results.

## License

The local repository material is released under the [MIT License](LICENSE).
The `cubical/` checkout retains its own upstream licensing and provenance.
