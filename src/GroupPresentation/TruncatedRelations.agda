{-# OPTIONS --cubical --guardedness #-}

module GroupPresentation.TruncatedRelations where

{-
Mathematical stage: 03 — relations in the 1-truncated presentation type.
Purpose: transport the pushout relation nullhomotopies to BG_pres.
Main declarations: generatorSpaceToBG, BG-relationLoop-null,
BG-relationSidesAgree.
Status: implemented and typechecked theorems.
-}

open import GroupPresentation
open import GroupPresentation.Relations

open import Cubical.Foundations.Prelude
open import Cubical.HITs.Truncation

-- The canonical map of the generator space into the truncated presentation.
generatorSpaceToBG :
  ∀ {ℓ ℓ'} {Gen : Type ℓ} {Rel : Type ℓ'}
  (P : Presentation Gen Rel) →
  GeneratorSpace Gen → BG_pres P
generatorSpaceToBG P x = ∣ inlPresentation P x ∣ₕ

-- Every relation loop is null after mapping to the 1-truncated presentation.
BG-relationLoop-null :
  ∀ {ℓ ℓ'} {Gen : Type ℓ} {Rel : Type ℓ'}
  (P : Presentation Gen Rel) (r : Rel) →
  cong (generatorSpaceToBG P) (relationLoop P r) ≡ refl
BG-relationLoop-null P r j i =
  ∣ inlRelationLoop-null P r j i ∣ₕ

-- The two sides of every relation agree after mapping to BG_pres.
BG-relationSidesAgree :
  ∀ {ℓ ℓ'} {Gen : Type ℓ} {Rel : Type ℓ'}
  (P : Presentation Gen Rel) (r : Rel) →
  cong (generatorSpaceToBG P) (relationLoop₀ P r)
    ≡ cong (generatorSpaceToBG P) (relationLoop₁ P r)
BG-relationSidesAgree P r j i =
  ∣ inlRelationSidesAgree P r j i ∣ₕ
