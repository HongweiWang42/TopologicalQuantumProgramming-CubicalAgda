{-# OPTIONS --cubical --guardedness #-}

module GroupPresentation.KernelReduction where

{-
Mathematical stage: reduction of injectivity to the reverse free-kernel
containment.
Purpose: state the missing presentation van Kampen property using the actual
normal closure and prove that this property implies injectivity of the
canonical presentation homomorphism.
Main declarations: FreeKernelContainedInNormalClosure and
canonicalPresentationHom-injective-from-freeKernel.
Status: the reduction theorem is typechecked.  No inhabitant of the reverse
kernel-containment type is constructed here.
-}

open import GroupPresentation
open import GroupPresentation.FundamentalGroup
open import GroupPresentation.PresentedGroup
open import GroupPresentation.PresentationHom

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Powerset
import Cubical.HITs.SetQuotients.Base as SetQuotBase
import Cubical.HITs.SetQuotients.Properties as SetQuot
open import Cubical.Algebra.Group.Base
open import Cubical.Algebra.Group.Properties
open import Cubical.Algebra.Group.Morphisms
open import Cubical.Algebra.Group.Subgroup
open import Cubical.Algebra.Group.QuotientGroup

-- This is the unproved reverse containment required from a presentation
-- van Kampen or loop-normal-form theorem.
FreeKernelContainedInNormalClosure :
  ∀ {ℓ ℓ'} {Gen : Type ℓ} {Rel : Type ℓ'}
  (P : Presentation Gen Rel) → Type (ℓ-max ℓ ℓ')
FreeKernelContainedInNormalClosure P =
  (x : (PresentationFreeGroup P) .fst) →
  isInKer (freeGroupToBG-π₁ P) x →
  x ∈ ⟪ (presentationNormalSubgroup P) .fst ⟫

-- The already verified direction of kernel containment.
NormalClosureContainedInFreeKernel :
  ∀ {ℓ ℓ'} {Gen : Type ℓ} {Rel : Type ℓ'}
  (P : Presentation Gen Rel) →
  ⟪ (presentationNormalSubgroup P) .fst ⟫ ⊆
  ⟪ kerSubgroup (freeGroupToBG-π₁ P) ⟫
NormalClosureContainedInFreeKernel = presentationNormalSubgroupInKernel

-- Computation of the induced quotient homomorphism on representatives.
canonicalPresentationHom-β :
  ∀ {ℓ ℓ'} {Gen : Type ℓ} {Rel : Type ℓ'}
  (P : Presentation Gen Rel) (x : (PresentationFreeGroup P) .fst) →
  (canonicalPresentationHom P) .fst
    ([_]/G {G = PresentationFreeGroup P} {H = presentationNormalSubgroup P} x)
  ≡ (freeGroupToBG-π₁ P) .fst x
canonicalPresentationHom-β P x = refl

-- Membership in the normal subgroup makes the corresponding quotient class
-- equal to the quotient identity.
normalMember→quotientIdentity :
  ∀ {ℓ ℓ'} {Gen : Type ℓ} {Rel : Type ℓ'}
  (P : Presentation Gen Rel) (x : (PresentationFreeGroup P) .fst) →
  x ∈ ⟪ (presentationNormalSubgroup P) .fst ⟫ →
  [_]/G {G = PresentationFreeGroup P} {H = presentationNormalSubgroup P} x
    ≡ GroupStr.1g ((PresentedGroup P) .snd)
normalMember→quotientIdentity P x x∈N =
  SetQuotBase.eq/ x 1g x~1
  where
  open GroupStr ((PresentationFreeGroup P) .snd)
  open GroupTheory (PresentationFreeGroup P)

  x~1 : x · inv 1g ∈ ⟪ (presentationNormalSubgroup P) .fst ⟫
  x~1 =
    subst-∈ ⟪ (presentationNormalSubgroup P) .fst ⟫
      (sym (cong (x ·_) inv1g ∙ ·IdR x)) x∈N

-- Consequently, the missing reverse containment is exactly sufficient for
-- injectivity of the canonical quotient homomorphism.
canonicalPresentationHom-injective-from-freeKernel :
  ∀ {ℓ ℓ'} {Gen : Type ℓ} {Rel : Type ℓ'}
  (P : Presentation Gen Rel) →
  FreeKernelContainedInNormalClosure P →
  isInjective (canonicalPresentationHom P)
canonicalPresentationHom-injective-from-freeKernel P reverse =
  SetQuot.elimProp
    (λ q →
      isPropΠ λ _ →
        GroupStr.is-set ((PresentedGroup P) .snd)
          q (GroupStr.1g ((PresentedGroup P) .snd)))
    (λ x x-in-kernel →
      normalMember→quotientIdentity P x
        (reverse x
          (sym (canonicalPresentationHom-β P x) ∙ x-in-kernel)))
