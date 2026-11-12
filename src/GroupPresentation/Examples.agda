{-# OPTIONS --cubical --guardedness #-}

module GroupPresentation.Examples where

{-
Mathematical stage: minimal instances of the public presentation interface.
Purpose: exhibit a one-generator presentation with no relations and a
one-generator, one-relation presentation.  These declarations construct the
corresponding types and canonical homomorphisms only; they do not identify
their fundamental groups with any externally named groups.
Status: typechecked examples.
-}

open import GroupPresentation.PublicAPI

open import Cubical.Foundations.Prelude
open import Cubical.Data.Empty using (⊥*)
open import Cubical.Data.Unit using (Unit* ; tt*)
open import Cubical.Data.List using ([] ; _∷_)
open import Cubical.Algebra.Group.Morphisms using (GroupHom)

-- The presentation ⟨ x |  ⟩ of the free group on one generator.
freeRankOnePresentation : Presentation Unit* ⊥*
freeRankOnePresentation .Presentation.p₀ ()
freeRankOnePresentation .Presentation.p₁ ()

freeRankOneBG : Type
freeRankOneBG = PresentedBG freeRankOnePresentation

freeRankOneCanonicalHom :
  GroupHom (PresentedGroup freeRankOnePresentation) (BG-π₁ freeRankOnePresentation)
freeRankOneCanonicalHom = canonicalHom freeRankOnePresentation

-- The syntactic presentation ⟨ x | x² = 1 ⟩.  No group-identification
-- theorem is asserted here.
cyclicTwoPresentation : Presentation Unit* Unit*
cyclicTwoPresentation .Presentation.p₀ _ = pos tt* ∷ pos tt* ∷ []
cyclicTwoPresentation .Presentation.p₁ _ = []

cyclicTwoBG : Type
cyclicTwoBG = PresentedBG cyclicTwoPresentation

cyclicTwoCanonicalHom :
  GroupHom (PresentedGroup cyclicTwoPresentation) (BG-π₁ cyclicTwoPresentation)
cyclicTwoCanonicalHom = canonicalHom cyclicTwoPresentation

cyclicTwoRelationNull :
  cong (generatorSpaceToBG cyclicTwoPresentation)
    (relationPath cyclicTwoPresentation tt*) ≡ refl
cyclicTwoRelationNull = BG-relationLoop-null cyclicTwoPresentation tt*
