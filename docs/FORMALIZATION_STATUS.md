# Formalization status

Milestones: **Group Presentations as Homotopy Pushouts — Foundational
Construction v0.1** and **Torsor-Based Delooping — Generic Construction
v0.1**.

Environment audited for this status: Agda `2.8.0-3d04bac`; pinned Cubical Agda commit `87af036ebd1c87956cf08fea44e62c7cf76392ca` (v0.9-compatible line). The audited source inventory contains sixteen local Agda modules: the root module and fifteen modules in `src/GroupPresentation/`. Every module typechecked with `agda -i src -i cubical <module>`.

## Verified

- Presentation syntax and geometry: `GeneratorSpace`, signed `Word`, `Presentation`, `relationLoop`, `PresentationPushout`, `BG_pres`, and `BG-basepoint` in `GroupPresentation.agda`.
- Relation imposition: `inlRelationLoop-null` and `inlRelationSidesAgree` in `GroupPresentation.Relations`; their truncated counterparts `BG-relationLoop-null` and `BG-relationSidesAgree` in `GroupPresentation.TruncatedRelations`.
- Connectedness: `BG-pres-isConnected : isConnected 2 (BG_pres P)` in `GroupPresentation.Connectedness`.
- Fundamental group interface: `BG-π₁` and `relationLoopπ₁-null` in `GroupPresentation.FundamentalGroup`.
- Algebraic quotient construction: `PresentationFreeGroup`, `relationDifference`, locally constructed `presentationNormalSubgroup`, and `PresentedGroup` in `GroupPresentation.PresentedGroup`.
- Canonical homomorphism: `canonicalPresentationHom : GroupHom (PresentedGroup P) (BG-π₁ P)` in `GroupPresentation.PresentationHom`.
- Supporting surjectivity results: `inlPresentation↑-π₁-surjective`, the bouquet/generator-space pointed equivalences, `bouquetLoopHom-surjective`, and `truncationπ₁-surjective`.
- Main current endpoint: `canonicalPresentationHom-surjective` in `GroupPresentation.CanonicalSurjectivity`.
- Public interface and examples: `GroupPresentation.PublicAPI` re-exports the
  verified surface, while `GroupPresentation.Examples` supplies minimal
  one-generator instances without group-identification claims.
- Concrete braid-presentation instance: `GroupPresentation.Br3` defines
  `⟨ σ₁, σ₂ | σ₁σ₂σ₁ = σ₂σ₁σ₂ ⟩`, its pushout and 1-truncation, the
  path-level braid relation coherence, and the specialized surjective
  canonical homomorphism.
- Conditional injectivity reduction: `GroupPresentation.KernelReduction`
  proves that the explicitly stated reverse free-kernel containment would
  imply injectivity; it does not supply that containment.

## In Progress

- A kernel/normal-form analysis identifying all relations among generator loops in `PresentationPushout P`.
- A comparison theorem sufficient to prove injectivity of `canonicalPresentationHom`.
- A pushout fundamental-group or Seifert–van Kampen route tailored to this construction.
- An identification of the concrete `Br3` instance with an independently
  defined classical braid group or its classifying space.

## Torsor-based delooping: verified

The audited `src/TorsorDelooping/` inventory contains twelve local Agda
modules. Every module typechecks with `agda --safe -i src -i cubical
<module>` in the pinned environment.

- `LeftAction` and `LeftTorsor` define set-level left actions and torsors
  using propositional-truncation inhabitation and contractible transporter
  types.
- `Regular` proves the regular left torsor; `Morphisms` proves that an
  equivariant map of torsors is an equivalence.
- `Moduli` uses SIP for paths in `LeftTorsorModuli`; `SIPCoherence`
  proves `regularTorsorLoop-comp` with
  `p (g · h) ≡ p g ∙ p h`.
- `Delooping` proves moduli connected and a 1-type, and gives
  `torsorLoopEquivGroup : (torsorBase G ≡ torsorBase G) ≃ G .fst`.
  This is an underlying type equivalence, not a packaged group isomorphism.
- `UniverseLiftedComparison.liftedEm1ToTorsorEquiv` gives the global
  universe-lifted `EM₁`-to-torsor equivalence.
- `PathTorsor.liftedPathTorsorModuliEquiv` gives the corresponding general
  universe-lifted result under `PointedLoopGroupData`, whose fields explicitly
  require connectedness, 1-truncation, a loop-type equivalence, and unit and
  multiplication coherences.

## Not Yet Formalized

- Injectivity of `canonicalPresentationHom`.
- An isomorphism `PresentedGroup P ≅ BG-π₁ P`.
- A full van Kampen theorem for the presentation pushout.
- A pointed equivalence between `BG_pres P` and a classifying space of `PresentedGroup P`.
- Any formalization claim about Myers–Sati–Schreiber Definition 6.7 or Theorem 6.8.
- The complex multiplicative group `C×`, geometric/principal-torsor
  structure, dependent computational transport or monodromy, and the
  construction of Definition 6.7.

`BG_pres` is a name for the checked 1-truncation construction, not a verified proof that it is a classifying space of the algebraic presented group.
