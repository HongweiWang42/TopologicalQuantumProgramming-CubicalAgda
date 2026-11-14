{-# OPTIONS --cubical --guardedness #-}

module TorsorDelooping.LeftAction where

{-
Phase A — set-level left actions.

The action convention is left-handed: (g · h) acts as g after h.
The carrier is explicitly required to be a set, as required for the
set-level torsors used in the torsor-delooping construction.
-}

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Algebra.Group.Base

private
  variable
    ℓG ℓX ℓY : Level

record LeftAction (G : Group ℓG) (X : Type ℓX) : Type (ℓ-max ℓG ℓX) where
  field
    isSetX    : isSet X
    act       : G .fst → X → X
    act-unit  : (x : X) → act (GroupStr.1g (G .snd)) x ≡ x
    act-comp  : (g h : G .fst) (x : X) →
                act (GroupStr._·_ (G .snd) g h) x ≡ act g (act h x)

open LeftAction public

record Equivariant
  {G : Group ℓG} {X : Type ℓX} {Y : Type ℓY}
  (A : LeftAction G X) (B : LeftAction G Y) (f : X → Y)
  : Type (ℓ-max ℓG (ℓ-max ℓX ℓY)) where
  field
    commutes : (g : G .fst) (x : X) →
      f (LeftAction.act A g x) ≡ LeftAction.act B g (f x)

open Equivariant public
