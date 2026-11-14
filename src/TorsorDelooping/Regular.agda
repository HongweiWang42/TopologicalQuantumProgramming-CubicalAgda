{-# OPTIONS --cubical --guardedness #-}

module TorsorDelooping.Regular where

{-
Phase A — the regular left torsor of a group.

The action is left multiplication.  Its regularity is obtained from the
upstream right-translation automorphism x ↦ x · g, whose inverse is
x ↦ x · g⁻¹ and whose inverse laws are proved from the group axioms in
Cubical.Algebra.Group.Properties.
-}

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv.Base using (equiv-proof)
open import Cubical.Foundations.Isomorphism using (isoToEquiv)
open import Cubical.HITs.PropositionalTruncation using (∣_∣₁)
open import Cubical.Algebra.Group.Base
open import Cubical.Algebra.Group.Properties using (·GroupAutomorphismR)

open import TorsorDelooping.LeftAction
open import TorsorDelooping.LeftTorsor

private
  variable
    ℓ : Level

regularLeftAction : (G : Group ℓ) → LeftAction G (G .fst)
LeftAction.isSetX (regularLeftAction G) = GroupStr.is-set (G .snd)
LeftAction.act (regularLeftAction G) = GroupStr._·_ (G .snd)
LeftAction.act-unit (regularLeftAction G) x = GroupStr.·IdL (G .snd) x
LeftAction.act-comp (regularLeftAction G) g h x =
  sym (GroupStr.·Assoc (G .snd) g h x)

regularLeftTorsor : (G : Group ℓ) → LeftTorsor G (G .fst)
LeftTorsor.leftAction (regularLeftTorsor G) = regularLeftAction G
IsLeftTorsor.inhabited (LeftTorsor.isTorsor (regularLeftTorsor G)) =
  ∣ GroupStr.1g (G .snd) ∣₁
IsLeftTorsor.regular (LeftTorsor.isTorsor (regularLeftTorsor G)) x y =
  (isoToEquiv (·GroupAutomorphismR G x)) .snd .equiv-proof y
