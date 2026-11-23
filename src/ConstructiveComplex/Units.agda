{-# OPTIONS --cubical --guardedness #-}

module ConstructiveComplex.Units where

-- The multiplicative group of units of the constructive complex commutative
-- ring.  Invertibility is supplied by Cubical's generic units construction;
-- no apartness test or coordinate formula for inverses is used here.

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels using (isSetΣSndProp)
open import Cubical.Foundations.Powerset using (_∈_; ∈-isProp)
open import Cubical.Data.Sigma using (Σ; _,_; fst; snd)
open import Cubical.Algebra.CommRing.Properties
open import Cubical.Algebra.Group.Base

open import TorsorDelooping.LeftTorsor
open import TorsorDelooping.Regular using (regularLeftTorsor)

open import ConstructiveComplex.Complex

private
  module C = CommRingStr (snd ComplexCommRing)
  module U = Units ComplexCommRing

ComplexUnits : Type
ComplexUnits = Σ Complex U.Rˣ

complexUnitOne : ComplexUnits
complexUnitOne = C.1r , U.RˣContainsOne

complexUnitMul : ComplexUnits → ComplexUnits → ComplexUnits
complexUnitMul (z , z-is-unit) (w , w-is-unit) =
  C._·_ z w , U.RˣMultClosed z w ⦃ z-is-unit ⦄ ⦃ w-is-unit ⦄

complexUnitInv : ComplexUnits → ComplexUnits
complexUnitInv (z , z-is-unit) =
  U._⁻¹ z ⦃ z-is-unit ⦄ , U.RˣInvClosed z ⦃ z-is-unit ⦄

complexUnitsIsSet : isSet ComplexUnits
complexUnitsIsSet = isSetΣSndProp complexIsSet (∈-isProp U.Rˣ)

private
  unitPath : {u v : ComplexUnits} → u .fst ≡ v .fst → u ≡ v
  unitPath = Σ≡Prop (∈-isProp U.Rˣ)

complexUnitMulAssociative : (u v w : ComplexUnits) →
  complexUnitMul u (complexUnitMul v w) ≡ complexUnitMul (complexUnitMul u v) w
complexUnitMulAssociative (z , z-is-unit) (w , w-is-unit) (q , q-is-unit) =
  unitPath (complexMulAssociative z w q)

complexUnitMulUnitRight : (u : ComplexUnits) →
  complexUnitMul u complexUnitOne ≡ u
complexUnitMulUnitRight (z , z-is-unit) =
  unitPath (complexMulUnitRight z)

complexUnitMulInverseRight : (u : ComplexUnits) →
  complexUnitMul u (complexUnitInv u) ≡ complexUnitOne
complexUnitMulInverseRight (z , z-is-unit) =
  unitPath (U.·-rinv z ⦃ z-is-unit ⦄)

ComplexUnitsGroup : Group ℓ-zero
ComplexUnitsGroup =
  makeGroup-right
    complexUnitOne
    complexUnitMul
    complexUnitInv
    complexUnitsIsSet
    complexUnitMulAssociative
    complexUnitMulUnitRight
    complexUnitMulInverseRight

complexUnitMulUnitLeft : (u : ComplexUnits) →
  complexUnitMul complexUnitOne u ≡ u
complexUnitMulUnitLeft = GroupStr.·IdL (snd ComplexUnitsGroup)

complexUnitMulInverseLeft : (u : ComplexUnits) →
  complexUnitMul (complexUnitInv u) u ≡ complexUnitOne
complexUnitMulInverseLeft = GroupStr.·InvL (snd ComplexUnitsGroup)

complexUnitsRegularLeftTorsor :
  LeftTorsor ComplexUnitsGroup (ComplexUnitsGroup .fst)
complexUnitsRegularLeftTorsor = regularLeftTorsor ComplexUnitsGroup
