# Research direction toward computational transport

This note records the next mathematical programme discussed with Urs. It is
not an implementation plan completed by the current Agda sources, and it
does not add any formal claims to the verified group-presentation result.

1. Develop the relevant braid-group classifying spaces and their pointed
   structure.
2. Formalize `C×`-torsors and the classifying type `B(C×)`.
3. Study mapping types `BG → B(C×)` in the needed pointed/unpointed forms.
4. Use those ingredients to approach the construction of Definition 6.7 in
   Myers--Sati--Schreiber, *Topological Quantum Gates in Homotopy Type
   Theory* (arXiv:2303.02382), and its computational type transport.

The present repository supplies only a preliminary presentation-pushout
foundation. Its verified result is surjectivity of the canonical homomorphism
from the algebraic presented group to the fundamental group of the constructed
type. Proving injectivity and the associated classifying-space equivalence
remain prerequisite formalization tasks before this later programme can use
the construction as a classifying-space theorem.
