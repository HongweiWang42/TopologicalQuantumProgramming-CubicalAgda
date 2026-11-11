{-# OPTIONS --cubical --guardedness #-}

module GroupPresentation.GeneratorBouquet where

{-
Mathematical stage: support for surjectivity — comparison with the bouquet
model of a free group.
Purpose: identify the suspension-based generator space with the library
bouquet and compute the image of each designated generator loop.
Main declarations: generatorSpaceToBouquet, bouquetToGeneratorSpace,
generatorSpace≃∙Bouquet, generatorLoop-toBouquet.
Status: implemented and typechecked pointed equivalence.
-}

open import GroupPresentation

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.GroupoidLaws
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Pointed
open import Cubical.Data.Sum
open import Cubical.Data.Unit
open import Cubical.HITs.Susp.Base
open import Cubical.HITs.Bouquet.Base
open import Cubical.Homotopy.Group.Base
open import Cubical.Algebra.Group.Morphisms

-- Collapse the reference meridian and retain the meridian indexed by each
-- generator as the corresponding bouquet loop.
generatorSpaceToBouquet :
  ∀ {ℓ} {Gen : Type ℓ} → GeneratorSpace Gen → Bouquet Gen
generatorSpaceToBouquet =
  suspFun↑ base λ { (inl _) → refl ; (inr g) → loop g }

referenceMeridian-toBouquet :
  ∀ {ℓ} {Gen : Type ℓ} →
  cong (generatorSpaceToBouquet {Gen = Gen})
    (referenceMeridian {Gen = Gen}) ≡ refl
referenceMeridian-toBouquet = refl

generatorMeridian-toBouquet :
  ∀ {ℓ} {Gen : Type ℓ} (g : Gen) →
  cong (generatorSpaceToBouquet {Gen = Gen}) (generatorMeridian g) ≡ loop g
generatorMeridian-toBouquet g = refl

cong-sym :
  ∀ {ℓ ℓ'} {A : Type ℓ} {B : Type ℓ'} {x y : A}
  (f : A → B) (p : x ≡ y) →
  cong f (sym p) ≡ sym (cong f p)
cong-sym f p i j = f (p (~ j))

-- The chosen generator loop maps to the corresponding bouquet loop.
generatorLoop-toBouquet :
  ∀ {ℓ} {Gen : Type ℓ} (g : Gen) →
  cong (generatorSpaceToBouquet {Gen = Gen}) (generatorLoop g) ≡ loop g
generatorLoop-toBouquet {Gen = Gen} g =
  cong-∙ (generatorSpaceToBouquet {Gen = Gen})
    (generatorMeridian g) (sym (referenceMeridian {Gen = Gen}))
  ∙ cong₂ _∙_ (generatorMeridian-toBouquet g)
      (cong-sym (generatorSpaceToBouquet {Gen = Gen})
        (referenceMeridian {Gen = Gen})
       ∙ cong sym referenceMeridian-toBouquet)
  ∙ cong (loop g ∙_) (sym symRefl)
  ∙ sym (rUnit (loop g))

-- The inverse map realizes each bouquet loop by the designated generator
-- loop in GeneratorSpace.
bouquetToGeneratorSpace :
  ∀ {ℓ} {Gen : Type ℓ} → Bouquet Gen → GeneratorSpace Gen
bouquetToGeneratorSpace base = north
bouquetToGeneratorSpace (loop g i) = generatorLoop g i

bouquetLoop-toGeneratorSpace :
  ∀ {ℓ} {Gen : Type ℓ} (g : Gen) →
  cong (bouquetToGeneratorSpace {Gen = Gen}) (loop g) ≡ generatorLoop g
bouquetLoop-toGeneratorSpace g = refl

-- The forward map is a section of the inverse on the bouquet.
generatorSpaceToBouquet-section :
  ∀ {ℓ} {Gen : Type ℓ} (y : Bouquet Gen) →
  generatorSpaceToBouquet (bouquetToGeneratorSpace y) ≡ y
generatorSpaceToBouquet-section base = refl
generatorSpaceToBouquet-section (loop g i) j =
  generatorLoop-toBouquet g j i

-- The inverse is a retraction of the forward map on GeneratorSpace.  The
-- generator-meridian case is the composition filler for
-- generatorMeridian g · referenceMeridian⁻¹.
bouquetToGeneratorSpace-retraction :
  ∀ {ℓ} {Gen : Type ℓ} (x : GeneratorSpace Gen) →
  bouquetToGeneratorSpace (generatorSpaceToBouquet x) ≡ x
bouquetToGeneratorSpace-retraction north = refl
bouquetToGeneratorSpace-retraction south = referenceMeridian
bouquetToGeneratorSpace-retraction (merid (inl tt*) i) j =
  merid reference (i ∧ j)
bouquetToGeneratorSpace-retraction (merid (inr g) i) j =
  compPath-filler (generatorMeridian g) (sym referenceMeridian) (~ j) i

generatorSpaceBouquetIso :
  ∀ {ℓ} {Gen : Type ℓ} → Iso (GeneratorSpace Gen) (Bouquet Gen)
generatorSpaceBouquetIso .Iso.fun = generatorSpaceToBouquet
generatorSpaceBouquetIso .Iso.inv = bouquetToGeneratorSpace
generatorSpaceBouquetIso .Iso.sec = generatorSpaceToBouquet-section
generatorSpaceBouquetIso .Iso.ret = bouquetToGeneratorSpace-retraction

-- The comparison is pointed at north and at the bouquet base point.
generatorSpace≃∙Bouquet :
  ∀ {ℓ} {Gen : Type ℓ} →
  (GeneratorSpace Gen , north) ≃∙ Bouquet∙ Gen
generatorSpace≃∙Bouquet {Gen = Gen} .fst =
  isoToEquiv (generatorSpaceBouquetIso {Gen = Gen})
generatorSpace≃∙Bouquet .snd = refl

-- The inverse comparison is also pointed definitionally.  Keeping this
-- explicit avoids the nontrivial basepoint transport produced by the generic
-- inverse of a pointed equivalence when computing induced loop maps.
bouquet≃∙GeneratorSpace :
  ∀ {ℓ} {Gen : Type ℓ} →
  Bouquet∙ Gen ≃∙ (GeneratorSpace Gen , north)
bouquet≃∙GeneratorSpace {Gen = Gen} .fst =
  isoToEquiv (invIso (generatorSpaceBouquetIso {Gen = Gen}))
bouquet≃∙GeneratorSpace .snd = refl

-- Universe-lifted form of the comparison.  This is the form matching the
-- lifted generators used by PresentationFreeGroup.
generatorSpaceToLiftedBouquet :
  ∀ {ℓ ℓ'} {Gen : Type ℓ} →
  GeneratorSpace Gen → Bouquet (Lift ℓ' Gen)
generatorSpaceToLiftedBouquet {ℓ' = ℓ'} =
  suspFun↑ base λ { (inl _) → refl ; (inr g) → loop (lift {ℓ' = ℓ'} g) }

liftedGeneratorSpaceToBouquet :
  ∀ {ℓ ℓ'} {Gen : Type ℓ} →
  Lift ℓ' (GeneratorSpace Gen) → Bouquet (Lift ℓ' Gen)
liftedGeneratorSpaceToBouquet {ℓ' = ℓ'} (lift x) =
  generatorSpaceToLiftedBouquet {ℓ' = ℓ'} x

referenceMeridian-toLiftedBouquet :
  ∀ {ℓ ℓ'} {Gen : Type ℓ} →
  cong (generatorSpaceToLiftedBouquet {ℓ' = ℓ'} {Gen = Gen})
    (referenceMeridian {Gen = Gen}) ≡ refl
referenceMeridian-toLiftedBouquet = refl

generatorMeridian-toLiftedBouquet :
  ∀ {ℓ ℓ'} {Gen : Type ℓ} (g : Gen) →
  cong (generatorSpaceToLiftedBouquet {ℓ' = ℓ'} {Gen = Gen})
    (generatorMeridian g) ≡ loop (lift {ℓ' = ℓ'} g)
generatorMeridian-toLiftedBouquet {ℓ' = ℓ'} g = refl

generatorLoop-toLiftedBouquet :
  ∀ {ℓ ℓ'} {Gen : Type ℓ} (g : Gen) →
  cong (generatorSpaceToLiftedBouquet {ℓ' = ℓ'} {Gen = Gen})
    (generatorLoop g) ≡ loop (lift {ℓ' = ℓ'} g)
generatorLoop-toLiftedBouquet {ℓ' = ℓ'} {Gen = Gen} g =
  cong-∙ (generatorSpaceToLiftedBouquet {ℓ' = ℓ'} {Gen = Gen})
    (generatorMeridian g) (sym (referenceMeridian {Gen = Gen}))
  ∙ cong₂ _∙_ (generatorMeridian-toLiftedBouquet {ℓ' = ℓ'} g)
      (cong-sym (generatorSpaceToLiftedBouquet {ℓ' = ℓ'} {Gen = Gen})
        (referenceMeridian {Gen = Gen})
       ∙ cong sym (referenceMeridian-toLiftedBouquet {ℓ' = ℓ'}))
  ∙ cong (loop (lift {ℓ' = ℓ'} g) ∙_) (sym symRefl)
  ∙ sym (rUnit (loop (lift {ℓ' = ℓ'} g)))

liftedBouquetToGeneratorSpace :
  ∀ {ℓ ℓ'} {Gen : Type ℓ} →
  Bouquet (Lift ℓ' Gen) → Lift ℓ' (GeneratorSpace Gen)
liftedBouquetToGeneratorSpace {ℓ' = ℓ'} base = lift {ℓ' = ℓ'} north
liftedBouquetToGeneratorSpace {ℓ' = ℓ'} (loop (lift g) i) =
  lift {ℓ' = ℓ'} (generatorLoop g i)

liftedBouquetLoop-toGeneratorSpace :
  ∀ {ℓ ℓ'} {Gen : Type ℓ} (g : Gen) →
  cong (liftedBouquetToGeneratorSpace {ℓ' = ℓ'} {Gen = Gen})
    (loop (lift {ℓ' = ℓ'} g)) ≡ cong (lift {ℓ' = ℓ'}) (generatorLoop g)
liftedBouquetLoop-toGeneratorSpace {ℓ' = ℓ'} g = refl

liftedGeneratorSpaceToBouquet-section :
  ∀ {ℓ ℓ'} {Gen : Type ℓ} (y : Bouquet (Lift ℓ' Gen)) →
  liftedGeneratorSpaceToBouquet (liftedBouquetToGeneratorSpace y) ≡ y
liftedGeneratorSpaceToBouquet-section {ℓ' = ℓ'} base = refl
liftedGeneratorSpaceToBouquet-section {ℓ' = ℓ'} (loop (lift g) i) j =
  generatorLoop-toLiftedBouquet {ℓ' = ℓ'} g j i

liftedBouquetToGeneratorSpace-retraction-base :
  ∀ {ℓ ℓ'} {Gen : Type ℓ} (x : GeneratorSpace Gen) →
  liftedBouquetToGeneratorSpace {ℓ' = ℓ'}
    (generatorSpaceToLiftedBouquet {ℓ' = ℓ'} x) ≡ lift {ℓ' = ℓ'} x
liftedBouquetToGeneratorSpace-retraction-base {ℓ' = ℓ'} north = refl
liftedBouquetToGeneratorSpace-retraction-base {ℓ' = ℓ'} south =
  cong (lift {ℓ' = ℓ'}) referenceMeridian
liftedBouquetToGeneratorSpace-retraction-base {ℓ' = ℓ'}
  (merid (inl tt*) i) j =
  lift {ℓ' = ℓ'} (merid reference (i ∧ j))
liftedBouquetToGeneratorSpace-retraction-base {ℓ' = ℓ'}
  (merid (inr g) i) j =
  lift {ℓ' = ℓ'}
    (compPath-filler (generatorMeridian g) (sym referenceMeridian) (~ j) i)

liftedBouquetToGeneratorSpace-retraction :
  ∀ {ℓ ℓ'} {Gen : Type ℓ} (x : Lift ℓ' (GeneratorSpace Gen)) →
  liftedBouquetToGeneratorSpace
    (liftedGeneratorSpaceToBouquet x) ≡ x
liftedBouquetToGeneratorSpace-retraction {ℓ' = ℓ'} (lift x) =
  liftedBouquetToGeneratorSpace-retraction-base {ℓ' = ℓ'} x

liftedGeneratorSpaceBouquetIso :
  ∀ {ℓ ℓ'} {Gen : Type ℓ} →
  Iso (Lift ℓ' (GeneratorSpace Gen)) (Bouquet (Lift ℓ' Gen))
liftedGeneratorSpaceBouquetIso .Iso.fun = liftedGeneratorSpaceToBouquet
liftedGeneratorSpaceBouquetIso .Iso.inv = liftedBouquetToGeneratorSpace
liftedGeneratorSpaceBouquetIso .Iso.sec = liftedGeneratorSpaceToBouquet-section
liftedGeneratorSpaceBouquetIso .Iso.ret = liftedBouquetToGeneratorSpace-retraction

liftedGeneratorSpace≃∙Bouquet :
  ∀ {ℓ ℓ'} {Gen : Type ℓ} →
  Lift∙ ℓ' (GeneratorSpace Gen , north) ≃∙ Bouquet∙ (Lift ℓ' Gen)
liftedGeneratorSpace≃∙Bouquet {Gen = Gen} .fst =
  isoToEquiv (liftedGeneratorSpaceBouquetIso {Gen = Gen})
liftedGeneratorSpace≃∙Bouquet .snd = refl

-- Likewise, the lifted inverse has a reflexive chosen basepoint path.
liftedBouquet≃∙GeneratorSpace :
  ∀ {ℓ ℓ'} {Gen : Type ℓ} →
  Bouquet∙ (Lift ℓ' Gen) ≃∙ Lift∙ ℓ' (GeneratorSpace Gen , north)
liftedBouquet≃∙GeneratorSpace {Gen = Gen} .fst =
  isoToEquiv (invIso (liftedGeneratorSpaceBouquetIso {Gen = Gen}))
liftedBouquet≃∙GeneratorSpace .snd = refl

-- The pointed comparisons induce equivalences on fundamental groups.
generatorSpaceBouquet-π₁Equiv :
  ∀ {ℓ} {Gen : Type ℓ} →
  GroupEquiv (πGr 0 (GeneratorSpace Gen , north))
             (πGr 0 (Bouquet∙ Gen))
generatorSpaceBouquet-π₁Equiv = πIso generatorSpace≃∙Bouquet 0

liftedGeneratorSpaceBouquet-π₁Equiv :
  ∀ {ℓ ℓ'} {Gen : Type ℓ} →
  GroupEquiv (πGr 0 (Lift∙ ℓ' (GeneratorSpace Gen , north)))
             (πGr 0 (Bouquet∙ (Lift ℓ' Gen)))
liftedGeneratorSpaceBouquet-π₁Equiv = πIso liftedGeneratorSpace≃∙Bouquet 0

bouquetGeneratorSpace-π₁Equiv :
  ∀ {ℓ} {Gen : Type ℓ} →
  GroupEquiv (πGr 0 (Bouquet∙ Gen))
             (πGr 0 (GeneratorSpace Gen , north))
bouquetGeneratorSpace-π₁Equiv = πIso bouquet≃∙GeneratorSpace 0

liftedBouquetGeneratorSpace-π₁Equiv :
  ∀ {ℓ ℓ'} {Gen : Type ℓ} →
  GroupEquiv (πGr 0 (Bouquet∙ (Lift ℓ' Gen)))
             (πGr 0 (Lift∙ ℓ' (GeneratorSpace Gen , north)))
liftedBouquetGeneratorSpace-π₁Equiv =
  πIso liftedBouquet≃∙GeneratorSpace 0
