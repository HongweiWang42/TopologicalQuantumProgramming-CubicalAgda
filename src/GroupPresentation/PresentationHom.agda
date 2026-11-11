{-# OPTIONS --cubical --guardedness #-}

module GroupPresentation.PresentationHom where

{-
Mathematical stage: 07 — the canonical homomorphism to the fundamental group.
Purpose: extend generator loops through the free group and factor through the
normal relation quotient.
Main declarations: freeGroupToBG-π₁, presentationNormalSubgroupInKernel,
canonicalPresentationHom.
Status: implemented and typechecked construction.  Surjectivity and
injectivity of canonicalPresentationHom remain unproved.
-}

open import GroupPresentation
open import GroupPresentation.TruncatedRelations
open import GroupPresentation.FundamentalGroup
open import GroupPresentation.PresentedGroup

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.GroupoidLaws
open import Cubical.Foundations.Powerset
open import Cubical.Data.List
open import Cubical.HITs.SetTruncation.Base
import Cubical.HITs.FreeGroup.Base as FG
import Cubical.HITs.FreeGroup.Properties as FreeGroup
import Cubical.HITs.SetQuotients.Properties as SetQuot
open import Cubical.Algebra.Group.Base
open import Cubical.Algebra.Group.Morphisms
open import Cubical.Algebra.Group.MorphismProperties
open import Cubical.Algebra.Group.Subgroup
open import Cubical.Algebra.Group.QuotientGroup
open import Cubical.Homotopy.Group.Base

-- A generator gives the corresponding loop class in the fundamental group.
generatorToBG-π₁ :
  ∀ {ℓ ℓ'} {Gen : Type ℓ} {Rel : Type ℓ'}
  (P : Presentation Gen Rel) → Gen → (BG-π₁ P) .fst
generatorToBG-π₁ P g =
  ∣ cong (generatorSpaceToBG P) (generatorLoop g) ∣₂

liftedGeneratorToBG-π₁ :
  ∀ {ℓ ℓ'} {Gen : Type ℓ} {Rel : Type ℓ'}
  (P : Presentation Gen Rel) → Lift ℓ' Gen → (BG-π₁ P) .fst
liftedGeneratorToBG-π₁ P (lift g) = generatorToBG-π₁ P g

-- The universal homomorphism from the free group on the lifted generators.
freeGroupToBG-π₁ :
  ∀ {ℓ ℓ'} {Gen : Type ℓ} {Rel : Type ℓ'}
  (P : Presentation Gen Rel) →
  GroupHom (PresentationFreeGroup P) (BG-π₁ P)
freeGroupToBG-π₁ P = FreeGroup.rec (liftedGeneratorToBG-π₁ P)

-- Evaluation in the free group agrees with concatenation of the corresponding
-- loops in BG_pres.
wordToFreeGroup-π₁ :
  ∀ {ℓ ℓ'} {Gen : Type ℓ} {Rel : Type ℓ'}
  (P : Presentation Gen Rel) (w : Word Gen) →
  (freeGroupToBG-π₁ P) .fst (wordToFreeGroup w) ≡
  ∣ cong (generatorSpaceToBG P) (wordLoop w) ∣₂
wordToFreeGroup-π₁ P [] = refl
wordToFreeGroup-π₁ P (pos g ∷ w) =
  cong (·π 0 (generatorToBG-π₁ P g)) (wordToFreeGroup-π₁ P w)
  ∙ sym (cong ∣_∣₂ (cong-∙ (generatorSpaceToBG P)
                       (generatorLoop g) (wordLoop w)))
wordToFreeGroup-π₁ P (neg g ∷ w) =
  cong (·π 0 (-π 0 (generatorToBG-π₁ P g))) (wordToFreeGroup-π₁ P w)
  ∙ sym (cong ∣_∣₂ (cong-∙ (generatorSpaceToBG P)
                       (sym (generatorLoop g)) (wordLoop w)))

cong-sym :
  ∀ {ℓ ℓ'} {A : Type ℓ} {B : Type ℓ'} {x y : A}
  (f : A → B) (p : x ≡ y) →
  cong f (sym p) ≡ sym (cong f p)
cong-sym f p i j = f (p (~ j))

loopProductInverseClass :
  ∀ {ℓ} {A : Type ℓ} {x : A} (p q : x ≡ x) →
  ·π 0 ∣ p ∣₂ (-π 0 ∣ q ∣₂) ≡ ∣ p ∙ sym q ∣₂
loopProductInverseClass p q = refl

relationLoopClass :
  ∀ {ℓ ℓ'} {Gen : Type ℓ} {Rel : Type ℓ'}
  (P : Presentation Gen Rel) (r : Rel) →
  ·π 0
    ∣ cong (generatorSpaceToBG P) (wordLoop (Presentation.p₀ P r)) ∣₂
    (-π 0
      ∣ cong (generatorSpaceToBG P) (wordLoop (Presentation.p₁ P r)) ∣₂)
  ≡ ∣ cong (generatorSpaceToBG P) (relationLoop P r) ∣₂
relationLoopClass P r =
  loopProductInverseClass
    (cong (generatorSpaceToBG P) (wordLoop (Presentation.p₀ P r)))
    (cong (generatorSpaceToBG P) (wordLoop (Presentation.p₁ P r)))
  ∙ cong ∣_∣₂
      (cong (cong (generatorSpaceToBG P) (wordLoop (Presentation.p₀ P r)) ∙_)
        (sym (cong-sym (generatorSpaceToBG P)
              (wordLoop (Presentation.p₁ P r))))
       ∙ sym (cong-∙ (generatorSpaceToBG P)
               (wordLoop (Presentation.p₀ P r))
               (sym (wordLoop (Presentation.p₁ P r)))))

-- Each defining relation difference is sent to the identity loop class.
relationDifferenceToBG-π₁-null :
  ∀ {ℓ ℓ'} {Gen : Type ℓ} {Rel : Type ℓ'}
  (P : Presentation Gen Rel) (r : Rel) →
  (freeGroupToBG-π₁ P) .fst (relationDifference P r) ≡ 1π 1
relationDifferenceToBG-π₁-null P r =
  IsGroupHom.pres· ((freeGroupToBG-π₁ P) .snd)
    (wordToFreeGroup (Presentation.p₀ P r))
    (FG.inv (wordToFreeGroup (Presentation.p₁ P r)))
  ∙ cong₂ (·π 0)
      (wordToFreeGroup-π₁ P (Presentation.p₀ P r))
      (IsGroupHom.presinv ((freeGroupToBG-π₁ P) .snd)
        (wordToFreeGroup (Presentation.p₁ P r))
       ∙ cong (-π 0) (wordToFreeGroup-π₁ P (Presentation.p₁ P r)))
  ∙ relationLoopClass P r
  ∙ relationLoopπ₁-null P r

-- The normal closure of the relation differences is contained in the kernel.
presentationNormalSubgroupInKernel :
  ∀ {ℓ ℓ'} {Gen : Type ℓ} {Rel : Type ℓ'}
  (P : Presentation Gen Rel) →
  ⟪ (presentationNormalSubgroup P) .fst ⟫ ⊆
  ⟪ kerSubgroup (freeGroupToBG-π₁ P) ⟫
presentationNormalSubgroupInKernel {ℓ = ℓ} P =
  NormalClosure.least
    (PresentationFreeGroup P)
    (liftedRelationDifference P)
    (kerSubgroup (freeGroupToBG-π₁ P) , isNormalKer (freeGroupToBG-π₁ P))
    (λ { (lift r) → relationDifferenceToBG-π₁-null P r })

-- A quotient relation is killed precisely when its two free-group elements
-- have the same image in the fundamental group.
normalRelationToBG-π₁-equal :
  ∀ {ℓ ℓ'} {Gen : Type ℓ} {Rel : Type ℓ'}
  (P : Presentation Gen Rel) (a b : (PresentationFreeGroup P) .fst) →
  GroupStr._·_ ((PresentationFreeGroup P) .snd) a
    (GroupStr.inv ((PresentationFreeGroup P) .snd) b)
    ∈ ⟪ (presentationNormalSubgroup P) .fst ⟫ →
  (freeGroupToBG-π₁ P) .fst a ≡ (freeGroupToBG-π₁ P) .fst b
normalRelationToBG-π₁-equal P a b rab =
  sym (·IdR ((freeGroupToBG-π₁ P) .fst a))
  ∙ cong ((freeGroupToBG-π₁ P) .fst a ·_)
      (sym (·InvL ((freeGroupToBG-π₁ P) .fst b)))
  ∙ ·Assoc ((freeGroupToBG-π₁ P) .fst a)
           (inv ((freeGroupToBG-π₁ P) .fst b))
           ((freeGroupToBG-π₁ P) .fst b)
  ∙ cong (_· (freeGroupToBG-π₁ P) .fst b) relation-image
  ∙ ·IdL ((freeGroupToBG-π₁ P) .fst b)
  where
  open GroupStr ((BG-π₁ P) .snd)

  relation-in-kernel :
    (freeGroupToBG-π₁ P) .fst
      (GroupStr._·_ ((PresentationFreeGroup P) .snd) a
        (GroupStr.inv ((PresentationFreeGroup P) .snd) b)) ≡
      GroupStr.1g ((BG-π₁ P) .snd)
  relation-in-kernel = presentationNormalSubgroupInKernel P _ rab

  relation-image :
    (freeGroupToBG-π₁ P) .fst a ·
    inv ((freeGroupToBG-π₁ P) .fst b) ≡ GroupStr.1g ((BG-π₁ P) .snd)
  relation-image =
    cong ((freeGroupToBG-π₁ P) .fst a ·_)
      (sym (IsGroupHom.presinv ((freeGroupToBG-π₁ P) .snd) b))
    ∙ sym (IsGroupHom.pres· ((freeGroupToBG-π₁ P) .snd) a
        (GroupStr.inv ((PresentationFreeGroup P) .snd) b))
    ∙ relation-in-kernel

-- Elimination from the quotient by the normal closure.
canonicalPresentationMap :
  ∀ {ℓ ℓ'} {Gen : Type ℓ} {Rel : Type ℓ'}
  (P : Presentation Gen Rel) →
  (PresentedGroup P) .fst → (BG-π₁ P) .fst
canonicalPresentationMap P =
  SetQuot.rec
    (GroupStr.is-set ((BG-π₁ P) .snd))
    ((freeGroupToBG-π₁ P) .fst)
    (normalRelationToBG-π₁-equal P)

-- The canonical homomorphism from the group presented by P to π₁(BG_pres P).
canonicalPresentationHom :
  ∀ {ℓ ℓ'} {Gen : Type ℓ} {Rel : Type ℓ'}
  (P : Presentation Gen Rel) →
  GroupHom (PresentedGroup P) (BG-π₁ P)
canonicalPresentationHom P .fst = canonicalPresentationMap P
canonicalPresentationHom P .snd =
  makeIsGroupHom
    (SetQuot.elimProp2
      (λ _ _ → GroupStr.is-set ((BG-π₁ P) .snd) _ _)
      (λ a b → IsGroupHom.pres· ((freeGroupToBG-π₁ P) .snd) a b))
