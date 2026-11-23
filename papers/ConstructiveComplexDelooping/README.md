# Constructive Complex Units and Their Torsor Delooping in Cubical Agda

This directory is the Shadow Paper for the completed ConstructiveComplex
milestone.  It gives a mathematical account of the pair construction of HoTT
complex numbers, their algebraic units, and the specialization of the existing
univalent torsor-moduli delooping.  Formalization notes and Appendix A name
the exact declarations used in the text.

The checked endpoint is ConstructiveComplex.Delooping.complexUnitsLoopEquiv:
(bComplexUnits ≡ bComplexUnits) ≃ ComplexUnits.

It is an equivalence of underlying types.  The paper does not claim a
coordinate-level apartness characterization of units, a packaged group
isomorphism, dependent transport computation, quantum gates, or a
formalization of Definition 6.7.

The checked source remains in
[`src/ConstructiveComplex/`](../../src/ConstructiveComplex/). Its
[source README](../../src/ConstructiveComplex/README.md) records the external
HoTT Reals revision, exact Agda declarations, and sequential replay commands.
This paper shares the series
[`cqts-formalization-series.sty`](../cqts-formalization-series.sty).

Build with XeLaTeX from this directory:

```sh
latexmk -xelatex -interaction=nonstopmode -halt-on-error main.tex
```

The LaTeX build is separate from Agda checking.  For the pinned Agda
environment and sequential replay commands, see
[`src/ConstructiveComplex/README.md`](../../src/ConstructiveComplex/README.md).
