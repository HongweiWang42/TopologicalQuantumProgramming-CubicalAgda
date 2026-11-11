# Formalization status

Environment audited for this status: Agda `2.8.0-3d04bac`; pinned Cubical Agda commit `87af036ebd1c87956cf08fea44e62c7cf76392ca` (v0.9-compatible line). Every local source module listed below typechecked with `agda -i src -i cubical <module>`.

## Verified

- Presentation syntax and geometry: `GeneratorSpace`, signed `Word`, `Presentation`, `relationLoop`, `PresentationPushout`, `BG_pres`, and `BG-basepoint` in `GroupPresentation.agda`.
- Relation imposition: `inlRelationLoop-null` and `inlRelationSidesAgree` in `GroupPresentation.Relations`; their truncated counterparts `BG-relationLoop-null` and `BG-relationSidesAgree` in `GroupPresentation.TruncatedRelations`.
- Connectedness: `BG-pres-isConnected : isConnected 2 (BG_pres P)` in `GroupPresentation.Connectedness`.
- Fundamental group interface: `BG-π₁` and `relationLoopπ₁-null` in `GroupPresentation.FundamentalGroup`.
- Algebraic quotient construction: `PresentationFreeGroup`, `relationDifference`, locally constructed `presentationNormalSubgroup`, and `PresentedGroup` in `GroupPresentation.PresentedGroup`.
- Canonical homomorphism: `canonicalPresentationHom : GroupHom (PresentedGroup P) (BG-π₁ P)` in `GroupPresentation.PresentationHom`.
- Supporting surjectivity results: `inlPresentation↑-π₁-surjective`, the bouquet/generator-space pointed equivalences, `bouquetLoopHom-surjective`, and `truncationπ₁-surjective`.
- Main current endpoint: `canonicalPresentationHom-surjective` in `GroupPresentation.CanonicalSurjectivity`.

## In Progress

- A kernel/normal-form analysis identifying all relations among generator loops in `PresentationPushout P`.
- A comparison theorem sufficient to prove injectivity of `canonicalPresentationHom`.
- A pushout fundamental-group or Seifert–van Kampen route tailored to this construction.

## Not Yet Formalized

- Injectivity of `canonicalPresentationHom`.
- An isomorphism `PresentedGroup P ≅ BG-π₁ P`.
- A full van Kampen theorem for the presentation pushout.
- A pointed equivalence between `BG_pres P` and a classifying space of `PresentedGroup P`.
- Any formalization claim about Myers–Sati–Schreiber Definition 6.7 or Theorem 6.8.

`BG_pres` is a name for the checked 1-truncation construction, not a verified proof that it is a classifying space of the algebraic presented group.
