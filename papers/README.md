# CQTS Formalization Series

The three papers share
[`cqts-formalization-series.sty`](cqts-formalization-series.sty) and compile
independently:

1. [Group Presentations as Homotopy Pushouts](GroupPresentations/README.md)
   ([PDF](GroupPresentations/main.pdf))
2. [Torsors, Univalence, and Delooping](TorsorDelooping/README.md)
   ([PDF](TorsorDelooping/main.pdf))
3. [Constructive Complex Units and Their Torsor Delooping in Cubical Agda](ConstructiveComplexDelooping/README.md)
 ([PDF](ConstructiveComplexDelooping/main.pdf))

From each paper directory, run:

```sh
latexmk -xelatex -interaction=nonstopmode -halt-on-error main.tex
```

Build serially in the order listed above. The LaTeX builds are independent
from Agda verification; each paper README links to its formal source and
provenance record.
