{-# OPTIONS --cubical --guardedness #-}

module ConstructiveComplex.Complex where

-- Constructive complex numbers as pairs of HoTT reals.  The real-number
-- implementation is imported from Jackson Brough's thesis revision of
-- hott-reals; no part of that development is copied here.

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels using (isSet×)
open import Cubical.Data.Sigma using (_×_; fst; snd; _,_; ΣPathP)
open import Cubical.Algebra.CommRing.Base
open import Cubical.Tactics.CommRingSolver

import HoTTReals.Data.Real.Base as RealBase
import HoTTReals.Data.Real.Properties as RealProperties
import HoTTReals.Data.Real.Algebra.Multiplication as RealMultiplication

private
  module R = CommRingStr (snd RealMultiplication.ℝCommutativeRing)

Complex : Type
Complex = RealBase.ℝ × RealBase.ℝ

complexZero : Complex
complexZero = R.0r , R.0r

complexOne : Complex
complexOne = R.1r , R.0r

complexAdd : Complex → Complex → Complex
complexAdd (a , b) (c , d) = R._+_ a c , R._+_ b d

complexNeg : Complex → Complex
complexNeg (a , b) = R.-_ a , R.-_ b

complexMul : Complex → Complex → Complex
complexMul (a , b) (c , d) =
  R._+_ (R._·_ a c) (R.-_ (R._·_ b d)) ,
  R._+_ (R._·_ a d) (R._·_ b c)

imaginaryUnit : Complex
imaginaryUnit = R.0r , R.1r

complexConjugate : Complex → Complex
complexConjugate (a , b) = a , R.-_ b

complexIsSet : isSet Complex
complexIsSet = isSet× RealProperties.ℝ-isSet RealProperties.ℝ-isSet

private
  pairPath : {a b c d : RealBase.ℝ} → a ≡ b → c ≡ d → (a , c) ≡ (b , d)
  pairPath p q = ΣPathP (p , q)

complexAddAssociative : (x y z : Complex) →
  complexAdd x (complexAdd y z) ≡ complexAdd (complexAdd x y) z
complexAddAssociative (a , b) (c , d) (e , f) =
  pairPath (solve! RealMultiplication.ℝCommutativeRing)
           (solve! RealMultiplication.ℝCommutativeRing)

complexAddUnitRight : (x : Complex) → complexAdd x complexZero ≡ x
complexAddUnitRight (a , b) =
  pairPath (solve! RealMultiplication.ℝCommutativeRing)
           (solve! RealMultiplication.ℝCommutativeRing)

complexAddInverseRight : (x : Complex) → complexAdd x (complexNeg x) ≡ complexZero
complexAddInverseRight (a , b) =
  pairPath (solve! RealMultiplication.ℝCommutativeRing)
           (solve! RealMultiplication.ℝCommutativeRing)

complexAddCommutative : (x y : Complex) → complexAdd x y ≡ complexAdd y x
complexAddCommutative (a , b) (c , d) =
  pairPath (solve! RealMultiplication.ℝCommutativeRing)
           (solve! RealMultiplication.ℝCommutativeRing)

complexMulAssociative : (x y z : Complex) →
  complexMul x (complexMul y z) ≡ complexMul (complexMul x y) z
complexMulAssociative (a , b) (c , d) (e , f) =
  pairPath (solve! RealMultiplication.ℝCommutativeRing)
           (solve! RealMultiplication.ℝCommutativeRing)

complexMulUnitRight : (x : Complex) → complexMul x complexOne ≡ x
complexMulUnitRight (a , b) =
  pairPath (solve! RealMultiplication.ℝCommutativeRing)
           (solve! RealMultiplication.ℝCommutativeRing)

complexMulDistributesOverAddLeft : (x y z : Complex) →
  complexMul x (complexAdd y z) ≡ complexAdd (complexMul x y) (complexMul x z)
complexMulDistributesOverAddLeft (a , b) (c , d) (e , f) =
  pairPath (solve! RealMultiplication.ℝCommutativeRing)
           (solve! RealMultiplication.ℝCommutativeRing)

complexMulCommutative : (x y : Complex) → complexMul x y ≡ complexMul y x
complexMulCommutative (a , b) (c , d) =
  pairPath (solve! RealMultiplication.ℝCommutativeRing)
           (solve! RealMultiplication.ℝCommutativeRing)

complexIsCommRing :
  IsCommRing complexZero complexOne complexAdd complexMul complexNeg
complexIsCommRing =
  makeIsCommRing
    complexIsSet
    complexAddAssociative
    complexAddUnitRight
    complexAddInverseRight
    complexAddCommutative
    complexMulAssociative
    complexMulUnitRight
    complexMulDistributesOverAddLeft
    complexMulCommutative

ComplexCommRing : CommRing ℓ-zero
ComplexCommRing =
  Complex , commringstr complexZero complexOne complexAdd complexMul complexNeg complexIsCommRing
