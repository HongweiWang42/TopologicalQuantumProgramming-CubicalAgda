{-# OPTIONS --cubical --guardedness #-}

module GroupPresentation.FundamentalGroup where

{-
Mathematical stage: 05 — the fundamental group of BG_pres.
Purpose: define the fundamental group at BG-basepoint and record that each
relation loop has the identity class.
Main declarations: BG-π₁, relationLoopπ₁-null.
Status: implemented and typechecked definition and theorem.
-}

open import GroupPresentation
open import GroupPresentation.TruncatedRelations

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Pointed
open import Cubical.Algebra.Group.Base
open import Cubical.HITs.SetTruncation.Base
open import Cubical.Homotopy.Group.Base

-- The fundamental group of the pointed presentation type.
BG-π₁ :
  ∀ {ℓ ℓ'} {Gen : Type ℓ} {Rel : Type ℓ'}
  (P : Presentation Gen Rel) →
  Group (ℓ-max ℓ ℓ')
BG-π₁ P = πGr 0 (BG_pres P , BG-basepoint P)

-- Each attaching relation represents the identity in the fundamental group.
relationLoopπ₁-null :
  ∀ {ℓ ℓ'} {Gen : Type ℓ} {Rel : Type ℓ'}
  (P : Presentation Gen Rel) (r : Rel) →
  ∣ cong (generatorSpaceToBG P) (relationLoop P r) ∣₂ ≡ 1π 1
relationLoopπ₁-null P r =
  cong ∣_∣₂ (BG-relationLoop-null P r)
