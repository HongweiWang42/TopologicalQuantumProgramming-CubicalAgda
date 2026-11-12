{-# OPTIONS --cubical --guardedness #-}

module GroupPresentation.PublicAPI where

{-
Mathematical stage: public interface for group-presentation classifying-space
candidates.
Purpose: re-export the verified construction under a compact client-facing
surface.  The aliases below add no mathematical content.
Main declarations: PresentedBG, relationPath, canonicalHom, and
canonicalHom-surjective.
Status: all exported results are definitions or proofs typechecked in their
source modules.
-}

open import GroupPresentation public
open import GroupPresentation.TruncatedRelations public
  using (generatorSpaceToBG ; BG-relationLoop-null ; BG-relationSidesAgree)
open import GroupPresentation.FundamentalGroup public
  using (BG-π₁ ; relationLoopπ₁-null)
open import GroupPresentation.PresentedGroup public
  using (PresentationFreeGroup ; wordToFreeGroup ; relationDifference
       ; presentationNormalSubgroup ; PresentedGroup)
open import GroupPresentation.PresentationHom public
  using (generatorToBG-π₁ ; freeGroupToBG-π₁ ; canonicalPresentationHom)
open import GroupPresentation.CanonicalSurjectivity public
  using (canonicalPresentationHom-surjective)

open import Cubical.Foundations.Prelude
open import Cubical.HITs.Susp.Base using (north)
open import Cubical.Algebra.Group.Morphisms using (GroupHom ; isSurjective)

-- The 1-truncated homotopy-pushout candidate for the classifying space.
PresentedBG : ∀ {ℓ ℓ'} {Gen : Type ℓ} {Rel : Type ℓ'} →
  Presentation Gen Rel → Type (ℓ-max ℓ ℓ')
PresentedBG = BG_pres

-- The loop attached to the relation indexed by r.
relationPath : ∀ {ℓ ℓ'} {Gen : Type ℓ} {Rel : Type ℓ'}
  (P : Presentation Gen Rel) (r : Rel) →
  north {A = GeneratorInput Gen} ≡ north
relationPath = relationLoop

-- The canonical map from the algebraic presentation to the fundamental group.
canonicalHom : ∀ {ℓ ℓ'} {Gen : Type ℓ} {Rel : Type ℓ'}
  (P : Presentation Gen Rel) →
  GroupHom (PresentedGroup P) (BG-π₁ P)
canonicalHom = canonicalPresentationHom

canonicalHom-surjective : ∀ {ℓ ℓ'} {Gen : Type ℓ} {Rel : Type ℓ'}
  (P : Presentation Gen Rel) →
  isSurjective (canonicalHom P)
canonicalHom-surjective = canonicalPresentationHom-surjective
