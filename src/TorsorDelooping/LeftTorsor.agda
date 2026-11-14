{-# OPTIONS --cubical --guardedness #-}

module TorsorDelooping.LeftTorsor where

{-
Phase A — left torsors.

For a left action A, regularity says that for every pair x y of carrier
elements, the type of group elements sending x to y is contractible.
Together with propositional-truncated inhabitation, this is the usual
free-and-transitive (left-torsor) condition.
-}

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Data.Sigma
open import Cubical.HITs.PropositionalTruncation
open import Cubical.Algebra.Group.Base

open import TorsorDelooping.LeftAction

private
  variable
    ℓG ℓX : Level

orbitMap : {G : Group ℓG} {X : Type ℓX}
  → LeftAction G X → X → G .fst → X
orbitMap A x g = LeftAction.act A g x

record IsLeftTorsor {G : Group ℓG} {X : Type ℓX}
  (A : LeftAction G X) : Type (ℓ-max ℓG ℓX) where
  field
    inhabited : ∥ X ∥₁
    regular   : (x y : X) →
      isContr (Σ[ g ∈ G .fst ] LeftAction.act A g x ≡ y)

open IsLeftTorsor public

record LeftTorsor (G : Group ℓG) (X : Type ℓX)
  : Type (ℓ-max ℓG ℓX) where
  field
    leftAction : LeftAction G X
    isTorsor   : IsLeftTorsor leftAction

open LeftTorsor public
