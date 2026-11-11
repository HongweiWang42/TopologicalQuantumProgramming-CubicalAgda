{-# OPTIONS --cubical --guardedness #-}

module GroupPresentation.CanonicalSurjectivity where

{-
Mathematical stage: canonical presentation homomorphism — surjectivity.
Purpose: compare free generators with generator-space loops, then compose the
free-group, pushout, and truncation surjections.
-}

open import GroupPresentation
open import GroupPresentation.GeneratorBouquet
open import GroupPresentation.BouquetFundamentalGroup
open import GroupPresentation.Relations
open import GroupPresentation.Surjectivity
open import GroupPresentation.FundamentalGroup
open import GroupPresentation.PresentedGroup
open import GroupPresentation.PresentationHom
open import GroupPresentation.TruncationNaturality
  using (truncation∙ ; truncationπ₁-surjective)

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.GroupoidLaws
open import Cubical.Foundations.Pointed
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Function
open import Cubical.HITs.Bouquet.Base
open import Cubical.HITs.Susp.Base
open import Cubical.HITs.SetTruncation
open import Cubical.HITs.Truncation
open import Cubical.HITs.PropositionalTruncation
open import Cubical.HITs.PropositionalTruncation as PropTrunc
import Cubical.HITs.FreeGroup.Base as FG
import Cubical.HITs.FreeGroup.Properties as FreeGroup
open import Cubical.Algebra.Group.Base
open import Cubical.Algebra.Group.Morphisms
open import Cubical.Algebra.Group.MorphismProperties
open import Cubical.Algebra.Group.QuotientGroup
open import Cubical.Homotopy.Group.Base

private
  variable
    ℓ ℓ' : Level
    Gen : Type ℓ
    Rel : Type ℓ'
    P : Presentation Gen Rel

-- Every group equivalence is surjective as its underlying group homomorphism.
groupEquivHom-surjective :
  ∀ {ℓ ℓ'} {G : Group ℓ} {H : Group ℓ'} (e : GroupEquiv G H) →
  isSurjective (GroupEquiv→GroupHom e)
groupEquivHom-surjective e y =
  ∣ invEq (e .fst) y , secEq (e .fst) y ∣₁

-- At a reflexively pointed map, the library πHom acts on loop classes by
-- ordinary path congruence.
πHom-refl :
  ∀ {ℓ ℓ'} {A : Type ℓ} {B : Type ℓ'} {a : A}
  (f : A → B) (p : a ≡ a) →
  ((πHom {A = (A , a)} {B = (B , f a)} 0 (f , refl)) .fst) (∣ p ∣₂) ≡
  (∣ cong f p ∣₂)
πHom-refl f p =
  cong ∣_∣₂
    (doubleCompPath-elim refl (cong f p) refl
    ∙ cong (_∙ refl) (sym (lUnit (cong f p)))
    ∙ sym (rUnit (cong f p)))

-- The inverse bouquet comparison induces a surjection on fundamental groups.
bouquetToLiftedGeneratorSpace-π₁-surjective :
  ∀ {ℓ ℓ'} {Gen : Type ℓ} →
  isSurjective
    (πHom 0 (≃∙map (liftedBouquet≃∙GeneratorSpace {ℓ = ℓ} {ℓ' = ℓ'} {Gen = Gen})))
bouquetToLiftedGeneratorSpace-π₁-surjective {ℓ = ℓ} {ℓ' = ℓ'} {Gen = Gen} =
  groupEquivHom-surjective
    (liftedBouquetGeneratorSpace-π₁Equiv {ℓ = ℓ} {ℓ' = ℓ'} {Gen = Gen})

-- The free group reaches the fundamental group of the lifted generator space.
freeGroupToLiftedGeneratorSpace-π₁ :
  ∀ {ℓ ℓ'} {Gen : Type ℓ} {Rel : Type ℓ'}
  (P : Presentation Gen Rel) →
  GroupHom (PresentationFreeGroup P)
    (πGr 0 (Lift∙ ℓ' (GeneratorSpace Gen , north)))
freeGroupToLiftedGeneratorSpace-π₁ {ℓ = ℓ} {ℓ' = ℓ'} {Gen = Gen} P =
  compGroupHom
    (bouquetLoopHom (Lift ℓ' Gen))
    (πHom 0
      (≃∙map
        (liftedBouquet≃∙GeneratorSpace {ℓ = ℓ} {ℓ' = ℓ'} {Gen = Gen})))

freeGroupToLiftedGeneratorSpace-π₁-surjective :
  ∀ {ℓ ℓ'} {Gen : Type ℓ} {Rel : Type ℓ'}
  (P : Presentation Gen Rel) →
  isSurjective (freeGroupToLiftedGeneratorSpace-π₁ P)
freeGroupToLiftedGeneratorSpace-π₁-surjective {ℓ = ℓ} {ℓ' = ℓ'} {Gen = Gen} P =
  compSurjective
    (bouquetLoopHom (Lift ℓ' Gen))
    (πHom 0
      (≃∙map
        (liftedBouquet≃∙GeneratorSpace {ℓ = ℓ} {ℓ' = ℓ'} {Gen = Gen})))
    (bouquetLoopHom-surjective (Lift ℓ' Gen))
    bouquetToLiftedGeneratorSpace-π₁-surjective

freeGroupToLiftedGeneratorSpace-π₁-generator :
  ∀ {ℓ ℓ'} {Gen : Type ℓ} {Rel : Type ℓ'}
  (P : Presentation Gen Rel) (g : Gen) →
  (freeGroupToLiftedGeneratorSpace-π₁ P) .fst
    (FG.η (lift {ℓ' = ℓ'} g)) ≡
  ∣ cong (lift {ℓ' = ℓ'}) (generatorLoop g) ∣₂
freeGroupToLiftedGeneratorSpace-π₁-generator {ℓ = ℓ} {ℓ' = ℓ'} {Gen = Gen} P g =
  πHom-refl
    (liftedBouquetToGeneratorSpace {ℓ = ℓ} {ℓ' = ℓ'} {Gen = Gen})
    (loop (lift {ℓ' = ℓ'} g))
  ∙ cong ∣_∣₂
      (liftedBouquetLoop-toGeneratorSpace {ℓ = ℓ} {ℓ' = ℓ'} {Gen = Gen} g)

-- Truncation of the presentation pushout preserves its fundamental group.
pushoutToBG-π₁ :
  ∀ {ℓ ℓ'} {Gen : Type ℓ} {Rel : Type ℓ'}
  (P : Presentation Gen Rel) →
  GroupHom (πGr 0 (PresentationPushout P , presentationBasepoint P))
    (BG-π₁ P)
pushoutToBG-π₁ P = GroupIso→GroupHom (πTruncGroupIso 0)

pushoutToBG-π₁-surjective :
  ∀ {ℓ ℓ'} {Gen : Type ℓ} {Rel : Type ℓ'}
  (P : Presentation Gen Rel) →
  isSurjective (pushoutToBG-π₁ P)
pushoutToBG-π₁-surjective P =
  groupEquivHom-surjective (GroupIso→GroupEquiv (πTruncGroupIso 0))

-- The topological factorisation of the free-group map.
freeGroupToBG-viaTopology :
  ∀ {ℓ ℓ'} {Gen : Type ℓ} {Rel : Type ℓ'}
  (P : Presentation Gen Rel) →
  GroupHom (PresentationFreeGroup P) (BG-π₁ P)
freeGroupToBG-viaTopology P =
  compGroupHom
    (compGroupHom (freeGroupToLiftedGeneratorSpace-π₁ P)
      (πHom 0 (inlPresentation↑∙ P)))
    (pushoutToBG-π₁ P)

freeGroupToBG-viaTopology-surjective :
  ∀ {ℓ ℓ'} {Gen : Type ℓ} {Rel : Type ℓ'}
  (P : Presentation Gen Rel) →
  isSurjective (freeGroupToBG-viaTopology P)
freeGroupToBG-viaTopology-surjective P =
  compSurjective
    (compGroupHom (freeGroupToLiftedGeneratorSpace-π₁ P)
      (πHom 0 (inlPresentation↑∙ P)))
    (pushoutToBG-π₁ P)
    (compSurjective
      (freeGroupToLiftedGeneratorSpace-π₁ P)
      (πHom 0 (inlPresentation↑∙ P))
      (freeGroupToLiftedGeneratorSpace-π₁-surjective P)
      (inlPresentation↑-π₁-surjective P))
    (pushoutToBG-π₁-surjective P)

-- Computation of the topological factorisation on a free generator.  This is
-- the comparison required to identify it with freeGroupToBG-π₁.
freeGroupToPushout-π₁-generator :
  ∀ {ℓ ℓ'} {Gen : Type ℓ} {Rel : Type ℓ'}
  (P : Presentation Gen Rel) (g : Gen) →
  (compGroupHom (freeGroupToLiftedGeneratorSpace-π₁ P)
    (πHom 0 (inlPresentation↑∙ P))) .fst
    (FG.η (lift {ℓ' = ℓ'} g)) ≡
  ∣ cong (inlPresentation P) (generatorLoop g) ∣₂
freeGroupToPushout-π₁-generator {ℓ = ℓ} {ℓ' = ℓ'} {Gen = Gen} P g =
  cong ((πHom 0 (inlPresentation↑∙ P)) .fst)
    (freeGroupToLiftedGeneratorSpace-π₁-generator P g)
  ∙ πHom-refl (inlPresentation P ∘ lower)
      (cong (lift {ℓ' = ℓ'}) (generatorLoop g))

-- Use the actual truncation constructor rather than the library's internally
-- transported πTruncGroupIso.  Its induced map computes directly on loops.
pushoutToBG-byTruncation-π₁ :
  ∀ {ℓ ℓ'} {Gen : Type ℓ} {Rel : Type ℓ'}
  (P : Presentation Gen Rel) →
  GroupHom (πGr 0 (PresentationPushout P , presentationBasepoint P))
    (BG-π₁ P)
pushoutToBG-byTruncation-π₁ P =
  πHom 0 (truncation∙ (PresentationPushout P , presentationBasepoint P))

pushoutToBG-byTruncation-π₁-surjective :
  ∀ {ℓ ℓ'} {Gen : Type ℓ} {Rel : Type ℓ'}
  (P : Presentation Gen Rel) →
  isSurjective (pushoutToBG-byTruncation-π₁ P)
pushoutToBG-byTruncation-π₁-surjective P =
  truncationπ₁-surjective (PresentationPushout P , presentationBasepoint P)

freeGroupToBG-byTruncation :
  ∀ {ℓ ℓ'} {Gen : Type ℓ} {Rel : Type ℓ'}
  (P : Presentation Gen Rel) →
  GroupHom (PresentationFreeGroup P) (BG-π₁ P)
freeGroupToBG-byTruncation P =
  compGroupHom
    (compGroupHom (freeGroupToLiftedGeneratorSpace-π₁ P)
      (πHom 0 (inlPresentation↑∙ P)))
    (pushoutToBG-byTruncation-π₁ P)

freeGroupToBG-byTruncation-surjective :
  ∀ {ℓ ℓ'} {Gen : Type ℓ} {Rel : Type ℓ'}
  (P : Presentation Gen Rel) →
  isSurjective (freeGroupToBG-byTruncation P)
freeGroupToBG-byTruncation-surjective P =
  compSurjective
    (compGroupHom (freeGroupToLiftedGeneratorSpace-π₁ P)
      (πHom 0 (inlPresentation↑∙ P)))
    (pushoutToBG-byTruncation-π₁ P)
    (compSurjective
      (freeGroupToLiftedGeneratorSpace-π₁ P)
      (πHom 0 (inlPresentation↑∙ P))
      (freeGroupToLiftedGeneratorSpace-π₁-surjective P)
      (inlPresentation↑-π₁-surjective P))
    (pushoutToBG-byTruncation-π₁-surjective P)

freeGroupToBG-byTruncation-generator :
  ∀ {ℓ ℓ'} {Gen : Type ℓ} {Rel : Type ℓ'}
  (P : Presentation Gen Rel) (g : Gen) →
  (freeGroupToBG-byTruncation P) .fst (FG.η (lift {ℓ' = ℓ'} g)) ≡
  generatorToBG-π₁ P g
freeGroupToBG-byTruncation-generator {ℓ = ℓ} {ℓ' = ℓ'} {Gen = Gen} P g =
  cong ((pushoutToBG-byTruncation-π₁ P) .fst)
    (freeGroupToPushout-π₁-generator P g)
  ∙ πHom-refl (λ x → ∣ x ∣ₕ)
      (cong (inlPresentation P) (generatorLoop g))

freeGroupToBG-byTruncation≡freeGroupToBG-π₁ :
  ∀ {ℓ ℓ'} {Gen : Type ℓ} {Rel : Type ℓ'}
  (P : Presentation Gen Rel) →
  freeGroupToBG-byTruncation P ≡ freeGroupToBG-π₁ P
freeGroupToBG-byTruncation≡freeGroupToBG-π₁ P =
  FreeGroup.freeGroupHom≡ (λ { (lift g) →
    freeGroupToBG-byTruncation-generator P g })

freeGroupToBG-π₁-surjective :
  ∀ {ℓ ℓ'} {Gen : Type ℓ} {Rel : Type ℓ'}
  (P : Presentation Gen Rel) →
  isSurjective (freeGroupToBG-π₁ P)
freeGroupToBG-π₁-surjective P =
  subst isSurjective
    (freeGroupToBG-byTruncation≡freeGroupToBG-π₁ P)
    (freeGroupToBG-byTruncation-surjective P)

canonicalPresentationHom-surjective :
  ∀ {ℓ ℓ'} {Gen : Type ℓ} {Rel : Type ℓ'}
  (P : Presentation Gen Rel) →
  isSurjective (canonicalPresentationHom P)
canonicalPresentationHom-surjective P y =
  PropTrunc.map
    (λ { (x , px) → quotient x , px })
    (freeGroupToBG-π₁-surjective P y)
  where
  quotient : (PresentationFreeGroup P) .fst → (PresentedGroup P) .fst
  quotient = [_]/G
    {G = PresentationFreeGroup P}
    {H = presentationNormalSubgroup P}
