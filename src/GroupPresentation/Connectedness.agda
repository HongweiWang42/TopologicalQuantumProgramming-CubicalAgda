{-# OPTIONS --cubical --guardedness #-}

module GroupPresentation.Connectedness where

{-
Mathematical stage: 04 — connectedness of the presentation classifying type.
Purpose: prove pointwise mere paths to the base point and connectedness of
BG_pres.
Main declarations: generatorSpaceMerePathToNorth,
presentationPushoutMerePathToBase, BG-pres-isConnected.
Status: implemented and typechecked theorems.
-}

open import GroupPresentation
open import GroupPresentation.Relations
open import GroupPresentation.TruncatedRelations

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Homotopy.Connected
open import Cubical.HITs.Pushout.Base
open import Cubical.HITs.Pushout.Properties
open import Cubical.HITs.S1.Base
open import Cubical.HITs.Susp.Base
open import Cubical.HITs.Truncation as Trunc
open import Cubical.HITs.PropositionalTruncation as PropTrunc

-- Every point of the suspension is merely joined to its north pole.
generatorSpaceMerePathToNorth :
  ∀ {ℓ} {Gen : Type ℓ} (x : GeneratorSpace Gen) →
  ∥ north {A = GeneratorInput Gen} ≡ x ∥₁
generatorSpaceMerePathToNorth {Gen = Gen} north = ∣ refl ∣₁
generatorSpaceMerePathToNorth {Gen = Gen} south = ∣ referenceMeridian ∣₁
generatorSpaceMerePathToNorth {Gen = Gen} (merid a i) =
  isProp→PathP
    {B = λ j → ∥ north {A = GeneratorInput Gen} ≡ merid a j ∥₁}
    (λ _ → isPropPropTrunc)
    ∣ refl ∣₁
    ∣ referenceMeridian ∣₁ i

-- Every point of the presentation pushout is merely joined to its base point.
presentationPushoutMerePathToBase :
  ∀ {ℓ ℓ'} {Gen : Type ℓ} {Rel : Type ℓ'}
  (P : Presentation Gen Rel) (x : PresentationPushout P) →
  ∥ presentationBasepoint P ≡ x ∥₁
presentationPushoutMerePathToBase P =
  elimProp
    (λ x → ∥ presentationBasepoint P ≡ x ∥₁)
    (λ _ → isPropPropTrunc)
    (λ x →
      PropTrunc.rec isPropPropTrunc
        (λ p → ∣ cong (inlPresentation P) p ∣₁)
        (generatorSpaceMerePathToNorth x))
    (λ r →
      ∣ push {f = attachingMap P} {g = relationProjection} (r , base) ∣₁)

-- Connectedness, in pointwise form, of the 1-truncated presentation type.
BG-pres-merePathToBase :
  ∀ {ℓ ℓ'} {Gen : Type ℓ} {Rel : Type ℓ'}
  (P : Presentation Gen Rel) (x : BG_pres P) →
  ∥ BG-basepoint P ≡ x ∥₁
BG-pres-merePathToBase P =
  Trunc.elim
    (λ _ → isProp→isOfHLevelSuc 2 isPropPropTrunc)
    (λ x →
      PropTrunc.rec isPropPropTrunc
        (λ p → ∣ cong ∣_∣ₕ p ∣₁)
        (presentationPushoutMerePathToBase P x))

-- BG_pres is connected: its set truncation is contractible.
BG-pres-isConnected :
  ∀ {ℓ ℓ'} {Gen : Type ℓ} {Rel : Type ℓ'}
  (P : Presentation Gen Rel) →
  isConnected 2 (BG_pres P)
BG-pres-isConnected P =
  ∣ BG-basepoint P ∣ₕ ,
  Trunc.elim
    (λ _ →
      isOfHLevelTruncPath {n = 2})
    (λ x →
      PropTrunc.rec
        (isOfHLevelPath' 1 (isOfHLevelTrunc 2) _ _)
        (λ p → cong ∣_∣ₕ p)
        (BG-pres-merePathToBase P x))
