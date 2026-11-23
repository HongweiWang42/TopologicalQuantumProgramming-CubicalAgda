
{-# OPTIONS --cubical --guardedness #-}

module ConstructiveComplex.Delooping where

-- The torsor moduli delooping of the multiplicative group of constructive
-- complex units.  This module only instantiates the generic construction.

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv

open import TorsorDelooping.Moduli using (LeftTorsorModuli)
open import TorsorDelooping.Delooping using (torsorBase; torsorLoopEquivGroup)

open import ConstructiveComplex.Units

-- The canonical torsor-moduli delooping of ComplexUnitsGroup.
BComplexUnits : Type₁
BComplexUnits = LeftTorsorModuli ℓ-zero ComplexUnitsGroup

-- Its canonical point is the regular left torsor of ComplexUnitsGroup.
bComplexUnits : BComplexUnits
bComplexUnits = torsorBase ComplexUnitsGroup

-- This is an equivalence of underlying types.  It does not package a
-- group-level isomorphism between loop concatenation and multiplication.
complexUnitsLoopEquiv : (bComplexUnits ≡ bComplexUnits) ≃ ComplexUnits
complexUnitsLoopEquiv = torsorLoopEquivGroup ComplexUnitsGroup
