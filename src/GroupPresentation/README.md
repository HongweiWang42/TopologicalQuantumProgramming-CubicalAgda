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
13. [PublicAPI.agda](PublicAPI.agda) -- compact public re-export surface for
    client modules.
14. [Examples.agda](Examples.agda) -- minimal one-generator examples of the
    public interface.
15. [KernelReduction.agda](KernelReduction.agda) -- a conditional reduction
    of injectivity to the unproved reverse free-kernel containment.
16. [Br3.agda](Br3.agda) -- the concrete presentation
    `⟨ σ₁, σ₂ | σ₁σ₂σ₁ = σ₂σ₁σ₂ ⟩`, its presentation pushout and
    1-truncation, relation coherence, and specialized canonical surjectivity.

**Planned, with no proof of the following statements:** injectivity of the
canonical homomorphism, the resulting group isomorphism, and the
classifying-space equivalence.  `KernelReduction.agda` records only a
conditional route to injectivity; it does not prove the missing hypothesis.

## Current mathematical boundary

For every local syntactic presentation `P : Presentation Gen Rel`, the
canonical map `canonicalPresentationHom P` is proved surjective. Its
injectivity is not proved, so the development does not establish
`PresentedGroup P ≅ BG-π₁ P` or identify `BG_pres P` as the classifying space
of the algebraic presented group. The types `Gen` and `Rel` are not silently
assumed to be sets or discrete in these local statements.
