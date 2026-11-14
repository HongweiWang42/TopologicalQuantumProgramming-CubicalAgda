# Torsors, Univalence, and Delooping

*A Mathematical Companion to a Cubical Agda Formalization* is a journal-style
Shadow Paper for the generic TorsorDelooping milestone. Its seven
chapters develop left torsors, their moduli, univalence/SIP, the loop-space
calculation, the comparison with `EM₁`, and the universe-lifted path-torsor
characterization. Appendix A is the statement-to-declaration index; Appendix
B records the pinned upstream provenance.

The checked source remains in [`src/TorsorDelooping/`](../../src/TorsorDelooping/).
The paper is mathematical exposition and adds no axioms or proofs to the Agda
development. Formalization notes give repository-relative source paths and
exact checked identifiers; they are not substitutes for the proofs in the
text.

Build with XeLaTeX:

```sh
latexmk -xelatex -interaction=nonstopmode -halt-on-error main.tex
```

The text records universe-lifted equivalences of underlying types. It does not
claim a separately packaged group-isomorphism theorem, construct `C×`, or
formalize Definition 6.7.
