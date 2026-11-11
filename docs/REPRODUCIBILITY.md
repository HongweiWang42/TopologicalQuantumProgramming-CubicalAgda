# Reproducibility

## Pinned environment

The local formalization was checked with Agda `2.8.0-3d04bac` and the
project-local `cubical/` checkout at commit
`87af036ebd1c87956cf08fea44e62c7cf76392ca` (Cubical Agda's
v0.9-compatible line). The local library descriptor is
[`urs-group-presentation.agda-lib`](../urs-group-presentation.agda-lib) and
uses `--cubical --guardedness`.

The source modules have no postulates, holes, unsafe options, or unproved
helper assumptions. They are intentionally checked with explicit include
paths rather than a global Agda library registration.

After the initial repository is committed with its Cubical dependency, a fresh
clone should initialize that checkout and verify its revision with:

```sh
git submodule update --init --recursive
git -C cubical rev-parse HEAD
```

The second command must print
`87af036ebd1c87956cf08fea44e62c7cf76392ca`.

## Formalization check

Run this command from the repository root:

```sh
for file in src/GroupPresentation.agda src/GroupPresentation/*.agda; do
  agda -i src -i cubical "$file" || exit $?
done
```

Expected result: one printed pathname for each of the twelve local source
modules and exit status zero, with no diagnostics. The source dependency
order is in [`src/GroupPresentation/README.md`](../src/GroupPresentation/README.md).

## Shadow Paper

The paper is a UTF-8 XeLaTeX document. It uses `fontspec` and Arial Unicode
MS for literal Cubical Agda identifiers such as `π₁`, `≃∙`, and `≡`.

```sh
cd papers/GroupPresentations
latexmk -xelatex -interaction=nonstopmode -halt-on-error main.tex
```

Expected result: `main.pdf` is rebuilt successfully. The current paper has
five pages. `alignment/records.jsonl` supplies declaration-level
traceability; every `Formal source` annotation in the paper was checked
against the declaration in the indicated local source module.

## Scope of verification

The checked endpoint is
`GroupPresentation.CanonicalSurjectivity.canonicalPresentationHom-surjective`.
Injectivity, the group isomorphism, and the classifying-space equivalence are
not formalized. The paper describes this boundary explicitly and should not
be read as asserting a formalized Seifert--van Kampen theorem or Definition
6.7 of Myers--Sati--Schreiber.
