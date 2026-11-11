{-# OPTIONS --cubical --guardedness #-}

module GroupPresentation.Surjectivity where

{-
Mathematical stage: 08 — intermediate loop normal-form surjectivity.
Purpose: prove that the lifted left inclusion into PresentationPushout is
surjective on fundamental groups.
Main declarations: relationProjection-isConnected,
inlPresentation↑-isConnected, inlPresentation↑-π₁-surjective.
Status: implemented and typechecked intermediate theorem.  This does not
prove that canonicalPresentationHom is surjective.
-}

open import GroupPresentation
open import GroupPresentation.Relations

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Pointed
open import Cubical.Homotopy.Connected
open import Cubical.Homotopy.Group.Base
open import Cubical.Homotopy.Group.Properties
open import Cubical.Algebra.Group.Morphisms
open import Cubical.Functions.Fibration
open import Cubical.HITs.Pushout.Base
open import Cubical.HITs.S1.Base
open import Cubical.HITs.S1.Properties
open import Cubical.HITs.Susp.Base
open import Cubical.HITs.Truncation as Trunc
open import Cubical.HITs.PropositionalTruncation as PropTrunc
open import Cubical.Data.Sigma

-- The circle is connected in the indexing used by isConnected.
S¹-isConnected : isConnected 2 S¹
S¹-isConnected =
  ∣ base ∣ₕ ,
  Trunc.elim
    (λ _ → isOfHLevelTruncPath {n = 2})
    (λ s →
      PropTrunc.rec
        (isOfHLevelPath' 1 (isOfHLevelTrunc 2) _ _)
        (λ p → cong ∣_∣ₕ p)
        (isConnectedS¹ s))

Lift-S¹-isConnected : (ℓ : Level) → isConnected 2 (Lift ℓ S¹)
Lift-S¹-isConnected ℓ =
  ∣ lift base ∣ₕ ,
  Trunc.elim
    (λ _ → isOfHLevelTruncPath {n = 2})
    (λ { (lift s) →
      PropTrunc.rec
        (isOfHLevelPath' 1 (isOfHLevelTrunc 2) _ _)
        (λ p → cong ∣_∣ₕ (cong lift p))
        (isConnectedS¹ s) })

-- Every fiber of Rel × S¹ → Rel is equivalent to S¹.
relationProjectionFiberIso :
  ∀ {ℓ} {Rel : Type ℓ} (r : Rel) →
  Iso (Lift ℓ S¹) (fiber (relationProjection {Rel = Rel}) r)
relationProjectionFiberIso r .Iso.fun (lift s) = (r , s) , refl
relationProjectionFiberIso r .Iso.inv ((r' , s) , p) = lift s
relationProjectionFiberIso r .Iso.sec ((r' , s) , p) =
  J (λ r' q → ((r , s) , refl) ≡ ((r' , s) , sym q)) refl (sym p)
relationProjectionFiberIso r .Iso.ret (lift s) = refl

relationProjection-isConnected :
  ∀ {ℓ} {Rel : Type ℓ} →
  isConnectedFun 2 (relationProjection {Rel = Rel})
relationProjection-isConnected r =
  subst (isConnected 2) (isoToPath (relationProjectionFiberIso r))
    (Lift-S¹-isConnected _)

-- The left inclusion into the presentation pushout is connected enough to be
-- surjective on fundamental groups.
inlPresentation-isConnected :
  ∀ {ℓ ℓ'} {Gen : Type ℓ} {Rel : Type ℓ'}
  (P : Presentation Gen Rel) →
  isConnectedFun 2 (inlPresentation P)
inlPresentation-isConnected P =
  inlConnected 2 (attachingMap P) relationProjection
    relationProjection-isConnected

inlPresentation∙ :
  ∀ {ℓ ℓ'} {Gen : Type ℓ} {Rel : Type ℓ'}
  (P : Presentation Gen Rel) →
  (GeneratorSpace Gen , north) →∙
  (PresentationPushout P , presentationBasepoint P)
inlPresentation∙ P .fst = inlPresentation P
inlPresentation∙ P .snd = refl

-- Thus every fundamental-group element of the untruncated presentation
-- pushout is represented by a loop from GeneratorSpace.
-- πHom is level-preserving.  Lift the source to the universe of the
-- pushout before applying the library's connected-map theorem.
inlPresentation↑∙ :
  ∀ {ℓ ℓ'} {Gen : Type ℓ} {Rel : Type ℓ'}
  (P : Presentation Gen Rel) →
  Lift∙ ℓ' (GeneratorSpace Gen , north) →∙
  (PresentationPushout P , presentationBasepoint P)
inlPresentation↑∙ P .fst = inlPresentation P ∘ lower
inlPresentation↑∙ P .snd = refl

inlPresentation↑-isConnected :
  ∀ {ℓ ℓ'} {Gen : Type ℓ} {Rel : Type ℓ'}
  (P : Presentation Gen Rel) →
  isConnectedFun 2 (inlPresentation↑∙ P .fst)
inlPresentation↑-isConnected P =
  isConnectedComp (inlPresentation P) lower 2
    (inlPresentation-isConnected P)
    (isEquiv→isConnected lower
      (equivIsEquiv (invEquiv LiftEquiv)) 2)

inlPresentation↑-π₁-surjective :
  ∀ {ℓ ℓ'} {Gen : Type ℓ} {Rel : Type ℓ'}
  (P : Presentation Gen Rel) →
  isSurjective (πHom 0 (inlPresentation↑∙ P))
inlPresentation↑-π₁-surjective P =
  connectedFun→πSurj 0 (inlPresentation↑∙ P)
    (inlPresentation↑-isConnected P)
