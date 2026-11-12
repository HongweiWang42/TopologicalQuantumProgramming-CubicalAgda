{-# OPTIONS --cubical --guardedness #-}

module GroupPresentation.Br3 where

{-
Concrete instance of the parameterized presentation-space construction for
the three-strand braid group presentation

  Br(3) = < σ₁, σ₂ | σ₁ σ₂ σ₁ = σ₂ σ₁ σ₂ >.

This module only instantiates the existing framework.  In particular, it
does not assert that the fundamental group of Br3PresentedSpace is
isomorphic to Br(3).
-}

open import GroupPresentation.PublicAPI

open import Cubical.Foundations.Prelude
open import Cubical.Data.List using ([] ; _∷_)
open import Cubical.HITs.Susp.Base using (north)
open import Cubical.Algebra.Group.Morphisms using (GroupHom ; isSurjective)

-- The two Artin generators of Br(3).
data Br3Generator : Type where
  σ₁ : Br3Generator
  σ₂ : Br3Generator

-- The single braid relation.
data Br3Relation : Type where
  braid : Br3Relation

-- The two sides of σ₁ σ₂ σ₁ = σ₂ σ₁ σ₂ as signed words.
Br3BraidLhs : Word Br3Generator
Br3BraidLhs = pos σ₁ ∷ pos σ₂ ∷ pos σ₁ ∷ []

Br3BraidRhs : Word Br3Generator
Br3BraidRhs = pos σ₂ ∷ pos σ₁ ∷ pos σ₂ ∷ []

-- The associated relator word σ₁ σ₂ σ₁ (σ₂ σ₁ σ₂)⁻¹.  The inverse is
-- encoded by reversing the right side and changing each letter to neg.
Br3BraidRelator : Word Br3Generator
Br3BraidRelator =
  pos σ₁ ∷ pos σ₂ ∷ pos σ₁ ∷ neg σ₂ ∷ neg σ₁ ∷ neg σ₂ ∷ []

-- The presentation is supplied to the existing pair-of-words API.  Its
-- relation loop is therefore the left word followed by the inverse of the
-- right word, matching Br3BraidRelator semantically.
Br3Presentation : Presentation Br3Generator Br3Relation
Br3Presentation .Presentation.p₀ braid = Br3BraidLhs
Br3Presentation .Presentation.p₁ braid = Br3BraidRhs

-- The generator space and the untruncated homotopy pushout of this
-- presentation.
Br3GeneratorSpace : Type
Br3GeneratorSpace = GeneratorSpace Br3Generator

Br3PresentationPushout : Type
Br3PresentationPushout = PresentationPushout Br3Presentation

-- The 1-truncated presentation-space output.
Br3PresentedSpace : Type
Br3PresentedSpace = PresentedBG Br3Presentation

Br3Basepoint : Br3PresentedSpace
Br3Basepoint = BG-basepoint Br3Presentation

-- The two generator loops, first in the generator space and then in the
-- 1-truncated presentation space.
Br3σ₁-generatorLoop :
  north {A = GeneratorInput Br3Generator} ≡ north
Br3σ₁-generatorLoop = generatorLoop σ₁

Br3σ₂-generatorLoop :
  north {A = GeneratorInput Br3Generator} ≡ north
Br3σ₂-generatorLoop = generatorLoop σ₂

Br3σ₁-loop : Br3Basepoint ≡ Br3Basepoint
Br3σ₁-loop = cong (generatorSpaceToBG Br3Presentation) Br3σ₁-generatorLoop

Br3σ₂-loop : Br3Basepoint ≡ Br3Basepoint
Br3σ₂-loop = cong (generatorSpaceToBG Br3Presentation) Br3σ₂-generatorLoop

-- The two braid words become equal loops in the truncated presentation
-- space.  This is the relation coherence supplied by the general theorem.
Br3BraidLhsLoop : Br3Basepoint ≡ Br3Basepoint
Br3BraidLhsLoop =
  cong (generatorSpaceToBG Br3Presentation) (wordLoop Br3BraidLhs)

Br3BraidRhsLoop : Br3Basepoint ≡ Br3Basepoint
Br3BraidRhsLoop =
  cong (generatorSpaceToBG Br3Presentation) (wordLoop Br3BraidRhs)

Br3BraidRelationCoherence : Br3BraidLhsLoop ≡ Br3BraidRhsLoop
Br3BraidRelationCoherence = BG-relationSidesAgree Br3Presentation braid

-- Equivalently, the attached relation loop is null in Br3PresentedSpace.
Br3BraidRelatorNull :
  cong (generatorSpaceToBG Br3Presentation)
    (relationPath Br3Presentation braid) ≡ refl
Br3BraidRelatorNull = BG-relationLoop-null Br3Presentation braid

-- The existing canonical homomorphism and its proved surjectivity specialize
-- directly to this instance.
Br3CanonicalHom :
  GroupHom (PresentedGroup Br3Presentation) (BG-π₁ Br3Presentation)
Br3CanonicalHom = canonicalHom Br3Presentation

Br3CanonicalHom-surjective : isSurjective Br3CanonicalHom
Br3CanonicalHom-surjective = canonicalHom-surjective Br3Presentation
