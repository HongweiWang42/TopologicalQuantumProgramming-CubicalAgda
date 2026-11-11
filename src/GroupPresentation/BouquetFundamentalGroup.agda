{-# OPTIONS --cubical --guardedness #-}

module GroupPresentation.BouquetFundamentalGroup where

{-
Mathematical stage: support for surjectivity — generator-compatible bouquet
normal form.
Purpose: prove surjectivity of the actual free-group homomorphism that sends
each generator to its bouquet loop class.
Main declarations: bouquetLoopHom, bouquetLoopHom-surjective.
Status: implemented and typechecked intermediate theorem.
-}

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.HLevels
open import Cubical.HITs.Bouquet.Base
open import Cubical.HITs.SetTruncation as ST
open import Cubical.HITs.PropositionalTruncation
open import Cubical.Homotopy.Group.Base
open import Cubical.Algebra.Group.Base
open import Cubical.Algebra.Group.Morphisms

import Cubical.HITs.FreeGroup.Base as FG
import Cubical.HITs.FreeGroup.Properties as FreeGroup
import Cubical.HITs.FreeGroupoid.Base as FGrp
import Cubical.HITs.FreeGroupoid.Properties as FGrpProp
import Cubical.HITs.Bouquet.FundamentalGroupProof as Bouquetπ₁

private
  variable
    ℓ : Level
    A : Type ℓ

-- The canonical free-group homomorphism induced by the bouquet loops.
bouquetLoopHom :
  ∀ {ℓ} (A : Type ℓ) →
  GroupHom (FreeGroup.freeGroupGroup A) (πGr 0 (Bouquet∙ A))
bouquetLoopHom A = FreeGroup.rec (λ a → ∣ loop a ∣₂)

bouquetLoopHom-generator :
  ∀ {ℓ} {A : Type ℓ} (a : A) →
  bouquetLoopHom A .fst (FG.η a) ≡ ∣ loop a ∣₂
bouquetLoopHom-generator a = refl

-- A representative in the free group is recovered by winding a bouquet loop
-- into the free groupoid and using the library's inverse truncation map.
bouquetWinding :
  ∀ {ℓ} {A : Type ℓ} →
  π 1 (Bouquet∙ A) → FG.FreeGroup A
bouquetWinding {A = A} =
  FGrpProp.forgetfulHom⁻¹ .fst ∘ Bouquetπ₁.windingT

-- On a free-groupoid representative, the specified free-group homomorphism
-- agrees with the library's looping map.
loopingFromFreeGroupoid :
  ∀ {ℓ} {A : Type ℓ} (g : FGrp.FreeGroupoid A) →
  bouquetLoopHom A .fst
    (FGrpProp.forgetfulHom⁻¹ .fst ∣ g ∣₂) ≡
  ∣ Bouquetπ₁.looping g ∣₂
loopingFromFreeGroupoid {A = A} =
  FGrpProp.elimProp
    (λ _ → squash₂ _ _)
    (λ a → refl)
    product
    refl
    inverse
  where
  h = bouquetLoopHom A
  h⁻¹ = FGrpProp.forgetfulHom⁻¹ {A = A}

  product : (g₁ g₂ : FGrp.FreeGroupoid A) →
    h .fst (h⁻¹ .fst ∣ g₁ ∣₂) ≡ ∣ Bouquetπ₁.looping g₁ ∣₂ →
    h .fst (h⁻¹ .fst ∣ g₂ ∣₂) ≡ ∣ Bouquetπ₁.looping g₂ ∣₂ →
    h .fst (h⁻¹ .fst ∣ FGrp._·_ g₁ g₂ ∣₂) ≡
    ∣ Bouquetπ₁.looping (FGrp._·_ g₁ g₂) ∣₂
  product g₁ g₂ p₁ p₂ =
    cong (h .fst) (IsGroupHom.pres· (h⁻¹ .snd) ∣ g₁ ∣₂ ∣ g₂ ∣₂)
    ∙ IsGroupHom.pres· (h .snd) (h⁻¹ .fst ∣ g₁ ∣₂) (h⁻¹ .fst ∣ g₂ ∣₂)
    ∙ cong₂ (·π 0) p₁ p₂

  inverse : (g : FGrp.FreeGroupoid A) →
    h .fst (h⁻¹ .fst ∣ g ∣₂) ≡ ∣ Bouquetπ₁.looping g ∣₂ →
    h .fst (h⁻¹ .fst ∣ FGrp.inv g ∣₂) ≡
    ∣ Bouquetπ₁.looping (FGrp.inv g) ∣₂
  inverse g p =
    cong (h .fst) (IsGroupHom.presinv (h⁻¹ .snd) ∣ g ∣₂)
    ∙ IsGroupHom.presinv (h .snd) (h⁻¹ .fst ∣ g ∣₂)
    ∙ cong (-π 0) p

-- Thus the concrete free-group homomorphism is the library looping map after
-- the library equivalence between free groups and truncated free groupoids.
bouquetLoopHom-loopingT :
  ∀ {ℓ} {A : Type ℓ} (x : ∥ FGrp.FreeGroupoid A ∥₂) →
  bouquetLoopHom A .fst (FGrpProp.forgetfulHom⁻¹ .fst x) ≡
  Bouquetπ₁.loopingT x
bouquetLoopHom-loopingT =
  ST.elim
    (λ _ → isProp→isSet (squash₂ _ _))
    loopingFromFreeGroupoid

-- The recovered word is a section of the canonical bouquet-loop map.
bouquetLoopHom-section :
  ∀ {ℓ} {A : Type ℓ} (x : π 1 (Bouquet∙ A)) →
  bouquetLoopHom A .fst (bouquetWinding x) ≡ x
bouquetLoopHom-section {A = A} =
  ST.elim
    (λ _ → isProp→isSet (squash₂ _ _))
    (λ p →
      loopingFromFreeGroupoid (Bouquetπ₁.winding p)
      ∙ cong ∣_∣₂ (Bouquetπ₁.left-homotopy p))

bouquetLoopHom-surjective :
  ∀ {ℓ} (A : Type ℓ) → isSurjective (bouquetLoopHom A)
bouquetLoopHom-surjective A x =
  ∣ (bouquetWinding x , bouquetLoopHom-section x) ∣₁
