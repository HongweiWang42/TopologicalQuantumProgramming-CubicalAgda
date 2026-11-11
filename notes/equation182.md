# Equation (182) — Original Dependency Sketch

This is the original planning sketch for the presentation construction. Its
former statement that no construction had been implemented is obsolete. The
current verified development is documented in `docs/FORMALIZATION_STATUS.md`;
its checked endpoint is surjectivity of `canonicalPresentationHom`, not the
full fundamental-group presentation theorem or a classifying-space equivalence.

```text
Paths
-> Suspension / S¹
-> generator space S({e} ⊔ Gen)
-> FreeGroup(Gen) / words as loops
-> relation attaching map
-> Pushout
-> 1-Truncation
-> Loop space / presented group
```

The first seven stages of this sketch now have local Cubical Agda
implementations in `src/`. The missing comparison needed for injectivity and
the subsequent classifying-space interpretation remains open.
