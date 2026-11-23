# Constructive complex numbers

## Purpose and scope

This directory contains the local constructive-complex layer of the CQTS
development.  `ConstructiveComplex.Complex` defines HoTT complex numbers as
pairs of HoTT reals and proves that they form a commutative ring.
`ConstructiveComplex.Units` then packages the algebraic units of that ring as
the multiplicative group `C×` and instantiates the existing generic regular
left-torsor construction.  `ConstructiveComplex.Delooping` instantiates the
existing torsor-moduli delooping as `BComplexUnits`, with its canonical point
and a loop-space equivalence.  It does not prove a group isomorphism between
loop concatenation and multiplication in `C×`.

The companion Shadow Paper is
[`Constructive Complex Units and Their Torsor Delooping in Cubical Agda`](../../papers/ConstructiveComplexDelooping/README.md);
its compiled [PDF](../../papers/ConstructiveComplexDelooping/main.pdf)
records the mathematical exposition and declaration-level provenance.

## Upstream provenance

The real-number interface is imported, not copied, from Jackson Brough's
`hott-reals` repository:

- Repository: <https://github.com/utahplt/hott-reals>
- Revision: `9fcc142b86d0c1e2bd6d06f86f7617200ad74857` (`thesis`)
- Local checkout: an external clone supplied by the developer; it is not
  vendored into this repository.

The imported real structure is
`HoTTReals.Data.Real.Algebra.Multiplication.ℝCommutativeRing`.  Its carrier is
`HoTTReals.Data.Real.Base.ℝ`, and its set proof is
`HoTTReals.Data.Real.Properties.ℝ-isSet`.  This module contains no copied
upstream source.

## Module structure and reading order

The mathematical dependency chain is

```text
Complex
  → ComplexCommRing
  → ComplexUnits
  → ComplexUnitsGroup
  → complexUnitsRegularLeftTorsor
  → torsorBase ComplexUnitsGroup
  → BComplexUnits, bComplexUnits
  → complexUnitsLoopEquiv
```

The final arrow is a recovery equivalence of underlying types, not a
group-level isomorphism.

1. `Complex.agda`
   - Definitions: `Complex`, `complexZero`, `complexOne`, `complexAdd`,
     `complexNeg`, `complexMul`, `imaginaryUnit`, and `complexConjugate`.
   - Main local results: `complexIsSet`, the eight additive and multiplicative
     ring-law proofs, `complexIsCommRing`, and `ComplexCommRing`.
   - Upstream inputs: `ℝ`, `ℝ-isSet`, and `ℝCommutativeRing` above.
   - Cubical inputs: product set closure (`isSet×`), sigma paths (`ΣPathP`),
     `makeIsCommRing`, and `Cubical.Tactics.CommRingSolver`.
   - Proof dependencies: each local algebraic law is a pair path whose two
     real components are discharged by the verified commutative-ring solver
     instantiated with `ℝCommutativeRing`.
2. `Units.agda`
   - Definitions: `ComplexUnits`, `complexUnitOne`, `complexUnitMul`, and
     `complexUnitInv`.
   - Main local results: `complexUnitsIsSet`, `ComplexUnitsGroup`, its derived
     left unit and inverse laws, and `complexUnitsRegularLeftTorsor`.
   - Cubical inputs: `Units` from `Cubical.Algebra.CommRing.Properties`,
     `makeGroup-right`, and `regularLeftTorsor`.
   - Proof dependencies: a unit is represented by an element of `Complex`
     together with the proposition that it has a multiplicative inverse.  The
     generic units API supplies closure and the right inverse; associativity
     and the right unit law are inherited from `ComplexCommRing`.
3. `Delooping.agda`
   - Definitions: `BComplexUnits` and its canonical base point
     `bComplexUnits`.
   - Main local result: `complexUnitsLoopEquiv`.
   - Generic inputs: `LeftTorsorModuli` from
     `TorsorDelooping.Moduli`, and `torsorBase` and
     `torsorLoopEquivGroup` from `TorsorDelooping.Delooping`.
   - Proof provenance: all torsor, univalence, and loop-recovery arguments
     are reused unchanged.  This module specializes
     `torsorBase ComplexUnitsGroup` and
     `torsorLoopEquivGroup ComplexUnitsGroup`; it introduces no new generic
     delooping proof.

## Mathematical result

`Complex` is the carrier `ℝ × ℝ`, with

`(a,b) \cdot (c,d) = (ac - bd, ad + bc)`.

The checked declaration
`ComplexCommRing : CommRing ℓ-zero` packages the usual constructive complex
commutative-ring operations.  `complexIsCommRing` is its explicit
`IsCommRing` witness.  The facts about the real numbers themselves remain
upstream dependencies rather than local results.

`ComplexUnits = Σ Complex (Units.Rˣ ComplexCommRing)` is the subtype of
algebraically invertible complex numbers.  The checked declaration
`ComplexUnitsGroup : Group ℓ-zero` equips it with multiplication, unit, and
inversion.  `complexUnitsRegularLeftTorsor` is its regular left torsor in the
already-existing `TorsorDelooping` interface.  This establishes the abstract
multiplicative group of units; it does not identify units with a coordinate
level nonzero or apartness predicate.

`BComplexUnits : Type₁` is the torsor-moduli delooping
`LeftTorsorModuli ℓ-zero ComplexUnitsGroup`, and
`bComplexUnits : BComplexUnits` is its regular-torsor base point.  The checked
declaration

`complexUnitsLoopEquiv : (bComplexUnits ≡ bComplexUnits) ≃ ComplexUnits`

is the direct specialization of
`TorsorDelooping.Delooping.torsorLoopEquivGroup`.  Thus it recovers the
underlying type of complex units from the loop space at the canonical point.
It is a type equivalence only; no group-level compatibility theorem or group
isomorphism is claimed here.

## Reproducible type check

The project library `urs-group-presentation` depends on the local pinned
Cubical library `cubical-0.9` and the external `hott-reals` library.  Register
the absolute paths of all three descriptors, one per line, in Agda's active
library registry. Write `<repository-root>` and `<hott-reals-root>` below
for the absolute paths on the machine performing the check:

```sh
git clone --branch thesis --single-branch https://github.com/utahplt/hott-reals.git \
  <hott-reals-root>
git -C <hott-reals-root> checkout 9fcc142b86d0c1e2bd6d06f86f7617200ad74857
git -C <hott-reals-root> rev-parse HEAD
```

The third command must print
`9fcc142b86d0c1e2bd6d06f86f7617200ad74857`.  Add the following entries to the
registry without removing any libraries already registered there:

```text
<repository-root>/cubical/cubical.agda-lib
<hott-reals-root>/hott-reals.agda-lib
<repository-root>/urs-group-presentation.agda-lib
```

A local editor may pass `--library=urs-group-presentation`; it must resolve
these same registered library roots. Machine-specific editor settings are not
part of this formalization.

From the repository root, run the following checks in dependency order:

```sh
agda --safe --cubical --no-import-sorts --guardedness \
  --library=urs-group-presentation \
  src/ConstructiveComplex/Complex.agda

agda --safe --cubical --no-import-sorts --guardedness \
  --library=urs-group-presentation \
  src/ConstructiveComplex/Units.agda

agda --safe --cubical --no-import-sorts --guardedness \
  --library=urs-group-presentation \
  src/ConstructiveComplex/Delooping.agda
```

These commands and VS Code resolve `ConstructiveComplex.*`,
`TorsorDelooping.*`, `Cubical.*`, and `HoTTReals.*` through the same registered
libraries.  They do not modify the upstream checkout or the pinned Cubical
dependency.

## Verified now; future work

Verified locally: the complex carrier, its operations, its set property, its
commutative-ring structure, its algebraic units group `C×`, the regular left
torsor of that group, the torsor-moduli delooping `BComplexUnits`, its
canonical base point, and the underlying loop-space equivalence
`complexUnitsLoopEquiv`.

Not implemented: a constructive nonzero/apartness criterion characterizing
complex units; a group-level loop-recovery isomorphism or compatibility with
loop concatenation; geometric structures; dependent computational transport;
and Definition 6.7.
