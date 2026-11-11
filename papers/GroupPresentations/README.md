# Group Presentations as Homotopy Pushouts

`main.tex` is the preliminary Shadow Paper, a mathematical article whose
formal-source annotations trace its local statements to `src/` and its
upstream ingredients to the pinned Cubical checkout. `main.pdf` is the
locally compiled version. The paper's central verified conclusion is
surjectivity of `canonicalPresentationHom`; it does not assert injectivity,
a group isomorphism, or a classifying-space equivalence.

Build it from this directory with:

```sh
latexmk -xelatex -interaction=nonstopmode -halt-on-error main.tex
```

The `earlier-draft/` directory preserves the former source-only companion for
historical comparison; it is not the current Shadow Paper.
