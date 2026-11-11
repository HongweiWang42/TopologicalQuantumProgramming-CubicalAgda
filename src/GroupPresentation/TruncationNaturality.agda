{-# OPTIONS --cubical --guardedness #-}

module GroupPresentation.TruncationNaturality where

{-
Mathematical stage: truncation compatibility for fundamental groups.
Purpose: use the path-space equivalence underlying πTruncGroupIso to build a
section for the π₁ map induced by the 3-truncation constructor.
Main declarations: truncation∙, pathIdTrunc-decode-η,
truncationπ₁-surjective.
Status: the constructor-induced π₁ map is proved surjective.  Equality with
the internally transported forward map of πTruncGroupIso is not asserted.
-}

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.GroupoidLaws
open import Cubical.HITs.Truncation
open import Cubical.HITs.Truncation.Properties
open import Cubical.HITs.SetTruncation
open import Cubical.HITs.PropositionalTruncation
open import Cubical.Foundations.Pointed
open import Cubical.Foundations.HLevels
open import Cubical.Algebra.Group.Morphisms
open import Cubical.Algebra.Group.MorphismProperties
open import Cubical.Homotopy.Group.Base
import Cubical.HITs.SetTruncation as ST

pathIdTrunc-encode-η :
  ∀ {ℓ} {A : Type ℓ} {a b : A} (p : a ≡ b) →
  Iso.fun (PathIdTruncIso 2) (cong ∣_∣ₕ p) ≡ ∣ p ∣ₕ
pathIdTrunc-encode-η {A = A} {a = a} {b = b} p =
  ΩTrunc.P-linv ∣ a ∣ₕ ∣ b ∣ₕ ∣ p ∣ₕ

pathIdTrunc-decode-η :
  ∀ {ℓ} {A : Type ℓ} {a b : A} (p : a ≡ b) →
  Iso.inv (PathIdTruncIso 2) (∣ p ∣ₕ) ≡ cong ∣_∣ₕ p
pathIdTrunc-decode-η p =
  cong (Iso.inv (PathIdTruncIso 2))
    (sym (pathIdTrunc-encode-η p))
  ∙ Iso.ret (PathIdTruncIso 2) (cong ∣_∣ₕ p)

-- The pointed 3-truncation constructor.
truncation∙ :
  ∀ {ℓ} (A : Pointed ℓ) → A →∙ hLevelTrunc∙ 3 A
truncation∙ A .fst x = ∣ x ∣ₕ
truncation∙ A .snd = refl

-- At a reflexively pointed map, πHom acts by ordinary path congruence.
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

truncationπ₁-preimage :
  ∀ {ℓ} {A : Pointed ℓ} →
  (pt (hLevelTrunc∙ 3 A) ≡ pt (hLevelTrunc∙ 3 A)) → π 1 A
truncationπ₁-preimage {A = A} q =
  Iso.inv setTruncTrunc2Iso
    (Iso.fun (PathIdTruncIso {A = typ A} 2) q)

-- Decode a path-code, then take its loop class.  This is the computation
-- needed for a section of πHom induced by the 3-truncation constructor.
truncationπ₁-preimage-computes :
  ∀ {ℓ} {A : Pointed ℓ}
  (c : hLevelTrunc 2 (pt A ≡ pt A)) →
  (πHom 0 (truncation∙ A)) .fst
    (Iso.inv setTruncTrunc2Iso c) ≡
  ∣ Iso.inv (PathIdTruncIso {A = typ A} 2) c ∣₂
truncationπ₁-preimage-computes {A = A} =
  Cubical.HITs.Truncation.elim
    (λ _ → isProp→isSet (squash₂ _ _))
    (λ p →
      πHom-refl ∣_∣ₕ p
      ∙ cong ∣_∣₂ (sym (pathIdTrunc-decode-η p)))

truncationπ₁-section :
  ∀ {ℓ} {A : Pointed ℓ}
  (q : pt (hLevelTrunc∙ 3 A) ≡ pt (hLevelTrunc∙ 3 A)) →
  (πHom 0 (truncation∙ A)) .fst (truncationπ₁-preimage q) ≡ ∣ q ∣₂
truncationπ₁-section {A = A} q =
  truncationπ₁-preimage-computes
    (Iso.fun (PathIdTruncIso {A = typ A} 2) q)
  ∙ cong ∣_∣₂ (Iso.ret (PathIdTruncIso {A = typ A} 2) q)

truncationπ₁-surjective :
  ∀ {ℓ} (A : Pointed ℓ) →
  isSurjective (πHom 0 (truncation∙ A))
truncationπ₁-surjective A =
  ST.elim
    (λ _ → isProp→isSet squash₁)
    (λ q → ∣ truncationπ₁-preimage q , truncationπ₁-section q ∣₁)
