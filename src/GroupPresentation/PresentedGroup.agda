{-# OPTIONS --cubical --guardedness #-}

module GroupPresentation.PresentedGroup where

{-
Mathematical stage: 06 — the algebraic group presented by generators and
relations.
Purpose: form the free group, normal closure of relation differences, and
the quotient PresentedGroup.
Main declarations: PresentationFreeGroup, relationDifference,
presentationNormalSubgroup, PresentedGroup.
Status: implemented and typechecked definitions; no comparison isomorphism is
proved here.
-}

open import GroupPresentation

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Powerset
open import Cubical.Data.List
open import Cubical.HITs.PropositionalTruncation as PropTrunc
import Cubical.HITs.FreeGroup.Base as FG
open import Cubical.HITs.FreeGroup.Properties using (freeGroupGroup)
open import Cubical.Algebra.Group.Base
open import Cubical.Algebra.Group.Subgroup
open import Cubical.Algebra.Group.QuotientGroup

-- The library free group, regarded as a group object.
FreeGroupOn : ∀ {ℓ} → Type ℓ → Group ℓ
FreeGroupOn = freeGroupGroup

-- The normal closure of a family of elements in a group, at one universe level.
module NormalClosure {ℓ : Level} (G : Group ℓ)
  {Rel : Type ℓ} (relations : Rel → G .fst) where

  open GroupStr (G .snd)

  data Raw : G .fst → Type ℓ where
    relation : (r : Rel) → Raw (relations r)
    identity : Raw 1g
    product : ∀ {x y} → Raw x → Raw y → Raw (x · y)
    inverse : ∀ {x} → Raw x → Raw (inv x)
    conjugate : (g : G .fst) {x : G .fst} → Raw x → Raw (g · x · inv g)

  subset : ℙ (G .fst)
  subset x = ∥ Raw x ∥₁ , squash₁

  subgroup : Subgroup G
  fst subgroup = subset
  isSubgroup.id-closed (snd subgroup) = ∣ identity ∣₁
  isSubgroup.op-closed (snd subgroup) = PropTrunc.map2 product
  isSubgroup.inv-closed (snd subgroup) = PropTrunc.map inverse

  normal : isNormal subgroup
  normal g x = PropTrunc.map (conjugate g)

  normalSubgroup : NormalSubgroup G
  normalSubgroup = subgroup , normal

  contains : (r : Rel) → relations r ∈ ⟪ subgroup ⟫
  contains r = ∣ relation r ∣₁

  least : (H : NormalSubgroup G)
    → ((r : Rel) → relations r ∈ ⟪ H .fst ⟫)
    → ⟪ subgroup ⟫ ⊆ ⟪ H .fst ⟫
  least (H , Hnormal) contains-H x =
    PropTrunc.rec (∈-isProp ⟪ H ⟫ x) go
    where
    open isSubgroup (snd H)

    go : ∀ {x} → Raw x → x ∈ ⟪ H ⟫
    go (relation r) = contains-H r
    go identity = id-closed
    go (product px py) = op-closed (go px) (go py)
    go (inverse px) = inv-closed (go px)
    go (conjugate g px) = Hnormal g _ (go px)

-- To support independent generator and relation universes, the free group is
-- formed on lifted generators at the common level ℓ-max ℓ ℓ'.
PresentationFreeGroup :
  ∀ {ℓ ℓ'} {Gen : Type ℓ} {Rel : Type ℓ'} →
  Presentation Gen Rel → Group (ℓ-max ℓ ℓ')
PresentationFreeGroup {ℓ = ℓ} {ℓ' = ℓ'} {Gen = Gen} P =
  FreeGroupOn (Lift ℓ' Gen)

-- Evaluate a signed word in the lifted free group.
wordToFreeGroup :
  ∀ {ℓ ℓ'} {Gen : Type ℓ} →
  Word Gen → FG.FreeGroup (Lift ℓ' Gen)
wordToFreeGroup [] = FG.ε
wordToFreeGroup (pos g ∷ w) =
  FG._·_ (FG.η (lift g)) (wordToFreeGroup w)
wordToFreeGroup (neg g ∷ w) =
  FG._·_ (FG.inv (FG.η (lift g))) (wordToFreeGroup w)

-- The p₀(r) · p₁(r)⁻¹ relation element in the lifted free group.
relationDifference :
  ∀ {ℓ ℓ'} {Gen : Type ℓ} {Rel : Type ℓ'}
  (P : Presentation Gen Rel) → Rel →
  FG.FreeGroup (Lift ℓ' Gen)
relationDifference P r =
  FG._·_ (wordToFreeGroup (Presentation.p₀ P r))
          (FG.inv (wordToFreeGroup (Presentation.p₁ P r)))

-- Relation indices are lifted to the common universe for the normal closure.
liftedRelationDifference :
  ∀ {ℓ ℓ'} {Gen : Type ℓ} {Rel : Type ℓ'}
  (P : Presentation Gen Rel) → Lift ℓ Rel →
  FG.FreeGroup (Lift ℓ' Gen)
liftedRelationDifference P (lift r) = relationDifference P r

presentationNormalSubgroup :
  ∀ {ℓ ℓ'} {Gen : Type ℓ} {Rel : Type ℓ'}
  (P : Presentation Gen Rel) →
  NormalSubgroup (PresentationFreeGroup P)
presentationNormalSubgroup {ℓ} P =
  NormalClosure.normalSubgroup
    (PresentationFreeGroup P)
    (liftedRelationDifference P)

-- The group presented by P: the lifted free group modulo the normal closure
-- of its relation differences.
PresentedGroup :
  ∀ {ℓ ℓ'} {Gen : Type ℓ} {Rel : Type ℓ'} →
  Presentation Gen Rel → Group (ℓ-max ℓ ℓ')
PresentedGroup P = PresentationFreeGroup P / presentationNormalSubgroup P

relationDifferenceInNormalClosure :
  ∀ {ℓ ℓ'} {Gen : Type ℓ} {Rel : Type ℓ'}
  (P : Presentation Gen Rel) (r : Rel) →
  relationDifference P r ∈ ⟪ (presentationNormalSubgroup P) .fst ⟫
relationDifferenceInNormalClosure {ℓ} P r =
  NormalClosure.contains
    (PresentationFreeGroup P)
    (liftedRelationDifference P)
    (lift r)
