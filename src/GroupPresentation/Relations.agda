{-# OPTIONS --cubical --guardedness #-}

module GroupPresentation.Relations where

{-
Mathematical stage: 02 — relation nullhomotopies in the pushout.
Purpose: show that the attaching circle makes each relation loop null and
identifies the two relation-word loops after the left inclusion.
Main declarations: inlPresentation, inlRelationLoop-null,
inlRelationSidesAgree.
Status: implemented and typechecked theorems.
-}

open import GroupPresentation

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function using (homotopyNatural)
open import Cubical.Foundations.GroupoidLaws
open import Cubical.Data.Sigma
open import Cubical.HITs.S1.Base
open import Cubical.HITs.Pushout.Base

-- The left inclusion of the presentation pushout, with its span fixed.
inlPresentation :
  ∀ {ℓ ℓ'} {Gen : Type ℓ} {Rel : Type ℓ'}
  (P : Presentation Gen Rel) →
  GeneratorSpace Gen → PresentationPushout P
inlPresentation P = inl {f = attachingMap P} {g = relationProjection}

-- A loop which is conjugate to refl is itself refl.
conjugacyToRefl :
  ∀ {ℓ} {A : Type ℓ} {x y : A}
  (p : x ≡ y) (q : x ≡ x) →
  p ≡ q ∙ p →
  q ≡ refl
conjugacyToRefl p q conjugacy =
  rUnit q
  ∙ cong (q ∙_) (sym (rCancel p))
  ∙ assoc q p (sym p)
  ∙ sym (cong (_∙ sym p) conjugacy)
  ∙ rCancel p

-- Naturality of the pushout glue paths around the r-th circle.
relationCircleNaturality :
  ∀ {ℓ ℓ'} {Gen : Type ℓ} {Rel : Type ℓ'}
  (P : Presentation Gen Rel) (r : Rel) →
  push {f = attachingMap P} {g = relationProjection} (r , base)
    ≡ cong (inlPresentation P) (relationLoop P r)
      ∙ push {f = attachingMap P} {g = relationProjection} (r , base)
relationCircleNaturality P r =
  rUnit (push {f = attachingMap P} {g = relationProjection} (r , base))
  ∙ homotopyNatural (λ z → push {f = attachingMap P} {g = relationProjection} (r , z)) loop

-- In the presentation pushout, every relation loop becomes null after inl.
inlRelationLoop-null :
  ∀ {ℓ ℓ'} {Gen : Type ℓ} {Rel : Type ℓ'}
  (P : Presentation Gen Rel) (r : Rel) →
  cong (inlPresentation P) (relationLoop P r) ≡ refl
inlRelationLoop-null P r =
  conjugacyToRefl
    (push {f = attachingMap P} {g = relationProjection} (r , base))
    (cong (inlPresentation P) (relationLoop P r))
    (relationCircleNaturality P r)

-- Congruence of inl with the relation difference loop.
inlRelationDifference :
  ∀ {ℓ ℓ'} {Gen : Type ℓ} {Rel : Type ℓ'}
  (P : Presentation Gen Rel) (r : Rel) →
  cong (inlPresentation P) (relationLoop P r)
    ≡ cong (inlPresentation P) (relationLoop₀ P r)
      ∙ sym (cong (inlPresentation P) (relationLoop₁ P r))
inlRelationDifference P r =
  cong-∙ (inlPresentation P) (relationLoop₀ P r) (sym (relationLoop₁ P r))

-- A null difference loop yields equality of its two sides.
differenceNullToEqual :
  ∀ {ℓ} {A : Type ℓ} {x : A}
  (p q : x ≡ x) →
  p ∙ sym q ≡ refl →
  p ≡ q
differenceNullToEqual p q difference-null =
  rUnit p
  ∙ cong (p ∙_) (sym (lCancel q))
  ∙ assoc p (sym q) q
  ∙ cong (_∙ q) difference-null
  ∙ sym (lUnit q)

-- The two word loops selected by any relation agree after inl.
inlRelationSidesAgree :
  ∀ {ℓ ℓ'} {Gen : Type ℓ} {Rel : Type ℓ'}
  (P : Presentation Gen Rel) (r : Rel) →
  cong (inlPresentation P) (relationLoop₀ P r)
    ≡ cong (inlPresentation P) (relationLoop₁ P r)
inlRelationSidesAgree P r =
  differenceNullToEqual
    (cong (inlPresentation P) (relationLoop₀ P r))
    (cong (inlPresentation P) (relationLoop₁ P r))
    (sym (inlRelationDifference P r) ∙ inlRelationLoop-null P r)
