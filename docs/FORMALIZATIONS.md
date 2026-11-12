# Formalized developments

This document records the mathematical constructions and theorems currently
checked in the repository. It separates formalized content from proposed
research directions in [RESEARCH_DIRECTION.md](RESEARCH_DIRECTION.md).

## Group presentations as homotopy pushouts

**Milestone:** **Group Presentations as Homotopy Pushouts — Foundational
Construction v0.1**. **Language:** Cubical Agda. **Status:** type-checked
foundational construction.

For a local syntactic presentation `P : Presentation Gen Rel`, the
development constructs a suspension-based generator space, interprets signed
words as based loops, attaches relation circles by a homotopy pushout, and
takes the resulting 1-truncation `BG_pres P`. It also constructs the free
group modulo the normal closure of the relation differences, written
`PresentedGroup P`, and a canonical homomorphism to the fundamental group of
the constructed type.

The exact canonical homomorphism is defined in
[PresentationHom.agda](../src/GroupPresentation/PresentationHom.agda):

```agda
canonicalPresentationHom :
  ∀ {ℓ ℓ'} {Gen : Type ℓ} {Rel : Type ℓ'}
  (P : Presentation Gen Rel) →
  GroupHom (PresentedGroup P) (BG-π₁ P)
```

The verified endpoint is in
[CanonicalSurjectivity.agda](../src/GroupPresentation/CanonicalSurjectivity.agda):

```agda
canonicalPresentationHom-surjective :
  ∀ {ℓ ℓ'} {Gen : Type ℓ} {Rel : Type ℓ'}
  (P : Presentation Gen Rel) →
  isSurjective (canonicalPresentationHom P)
```

Thus surjectivity is formally established. The following statements remain
open in this repository:

- Injectivity of `canonicalPresentationHom`.
- An isomorphism `PresentedGroup P ≅ BG-π₁ P`.
- A classifying-space equivalence identifying `BG_pres P` with the
  classifying space of the algebraic presented group.

The name `BG_pres` denotes the checked 1-truncation construction; it is not
itself a formal proof of the final classifying-space interpretation.

### Source modules

- [GroupPresentation.agda](../src/GroupPresentation.agda) -- presentation
  syntax, relation loops, pushout, and truncation.
- [Relations.agda](../src/GroupPresentation/Relations.agda) and
  [TruncatedRelations.agda](../src/GroupPresentation/TruncatedRelations.agda)
  -- relation nullhomotopies before and after truncation.
- [PresentedGroup.agda](../src/GroupPresentation/PresentedGroup.agda) -- free
  group, normal closure, and quotient construction.
- [PresentationHom.agda](../src/GroupPresentation/PresentationHom.agda) --
  canonical homomorphism.
- [CanonicalSurjectivity.agda](../src/GroupPresentation/CanonicalSurjectivity.agda)
  -- the verified surjectivity theorem.
- [PublicAPI.agda](../src/GroupPresentation/PublicAPI.agda) -- client-facing
  aliases for the verified construction.
- [Examples.agda](../src/GroupPresentation/Examples.agda) -- minimal checked
  examples.
- [KernelReduction.agda](../src/GroupPresentation/KernelReduction.agda) -- a
  conditional injectivity reduction, without the required reverse containment.
- [Br3.agda](../src/GroupPresentation/Br3.agda) -- the checked concrete
  two-generator, one-relation Br(3) presentation instance.  It instantiates
  the existing construction and does not identify the output with an
  independently defined classical braid group or its classifying space.

The full mathematical reading order is in
[src/GroupPresentation/README.md](../src/GroupPresentation/README.md). The
formal provenance record is
[alignment/records.jsonl](../alignment/records.jsonl).

### Mathematical exposition and verification record

The source-traceable article is available as the
[Group Presentations Shadow Paper](../papers/GroupPresentations/README.md),
with its compiled [PDF](../papers/GroupPresentations/main.pdf). The detailed
verified/in-progress/not-yet-formalized inventory remains in
[FORMALIZATION_STATUS.md](FORMALIZATION_STATUS.md).
