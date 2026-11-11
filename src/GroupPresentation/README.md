# Group-presentation formalization: mathematical reading order

The Agda module names remain descriptive. This sequence gives the
mathematical derivation order; all entries below are present and typechecked
unless explicitly marked **planned**.

1. [GroupPresentation.agda](../GroupPresentation.agda) -- generator inputs,
   signed words, relation loops, the presentation pushout, and its
   1-truncation.
2. [Relations.agda](Relations.agda) -- pushout relation nullhomotopies and
   equality of the two relation-word loops.
3. [TruncatedRelations.agda](TruncatedRelations.agda) -- the corresponding
   results after 1-truncation.
4. [Connectedness.agda](Connectedness.agda) -- pointwise mere paths and
   `BG-pres-isConnected`.
5. [FundamentalGroup.agda](FundamentalGroup.agda) -- `BG-π₁` and
   `relationLoopπ₁-null`.
6. [PresentedGroup.agda](PresentedGroup.agda) -- the free group, relation
   differences, their normal closure, and `PresentedGroup`.
7. [PresentationHom.agda](PresentationHom.agda) -- the canonical homomorphism
   `canonicalPresentationHom`.
8. [BouquetFundamentalGroup.agda](BouquetFundamentalGroup.agda) -- the
   generator-compatible free-group-to-bouquet surjectivity theorem.
9. [GeneratorBouquet.agda](GeneratorBouquet.agda) -- pointed generator-space
   / bouquet equivalences, including the lifted version.
10. [Surjectivity.agda](Surjectivity.agda) -- fundamental-group surjectivity
    of the lifted left pushout inclusion.
11. [TruncationNaturality.agda](TruncationNaturality.agda) -- surjectivity of
    the fundamental-group map induced by the truncation constructor.
12. [CanonicalSurjectivity.agda](CanonicalSurjectivity.agda) --
    `canonicalPresentationHom-surjective`.

**Planned, with no source modules:** injectivity of the canonical homomorphism,
the resulting group isomorphism, and the classifying-space equivalence.

## Current mathematical boundary

For every local syntactic presentation `P : Presentation Gen Rel`, the
canonical map `canonicalPresentationHom P` is proved surjective. Its
injectivity is not proved, so the development does not establish
`PresentedGroup P ≅ BG-π₁ P` or identify `BG_pres P` as the classifying space
of the algebraic presented group. The types `Gen` and `Rel` are not silently
assumed to be sets or discrete in these local statements.
