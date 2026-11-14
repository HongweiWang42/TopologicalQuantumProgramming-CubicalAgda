{-# OPTIONS --cubical --guardedness #-}

module TorsorDelooping.Morphisms where

{-
Phase B — equivariant maps and equivalences of Phase-A torsors.

For a fixed x in a torsor, its orbit map G → X is an equivalence by
regularity.  An equivariant map intertwines orbit maps.  Since the source is
merely inhabited and isEquiv is a proposition, this proves that every
equivariant map between torsors is an equivalence.
-}

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Equiv.Base using (equiv-proof)
open import Cubical.Foundations.Equiv.Properties
open import Cubical.Foundations.Function using (_∘_ ; idfun)
open import Cubical.HITs.PropositionalTruncation
open import Cubical.Algebra.Group.Base

open import TorsorDelooping.LeftAction
open import TorsorDelooping.LeftTorsor

private
  variable
    ℓG ℓX ℓY ℓZ : Level

equivariant-id : {G : Group ℓG} {X : Type ℓX}
  (A : LeftAction G X) → Equivariant A A (idfun X)
Equivariant.commutes (equivariant-id A) g x = refl

equivariant-comp : {G : Group ℓG} {X : Type ℓX} {Y : Type ℓY} {Z : Type ℓZ}
  {A : LeftAction G X} {B : LeftAction G Y} {C : LeftAction G Z}
  {f : X → Y} {g : Y → Z}
  → Equivariant A B f → Equivariant B C g → Equivariant A C (g ∘ f)
Equivariant.commutes (equivariant-comp {f = f} {g = g} ef eg) h x =
  cong g (Equivariant.commutes ef h x) ∙ Equivariant.commutes eg h (f x)

record EquivariantEquiv
  {G : Group ℓG} {X : Type ℓX} {Y : Type ℓY}
  (A : LeftAction G X) (B : LeftAction G Y)
  : Type (ℓ-max ℓG (ℓ-max ℓX ℓY)) where
  field
    equiv       : X ≃ Y
    equivariant : Equivariant A B (equiv .fst)

open EquivariantEquiv public

TorsorEquivariantEquiv : {G : Group ℓG} {X : Type ℓX} {Y : Type ℓY}
  (T : LeftTorsor G X) (U : LeftTorsor G Y)
  → Type (ℓ-max ℓG (ℓ-max ℓX ℓY))
TorsorEquivariantEquiv T U =
  EquivariantEquiv (LeftTorsor.leftAction T) (LeftTorsor.leftAction U)

orbitEquiv : {G : Group ℓG} {X : Type ℓX}
  (T : LeftTorsor G X) (x : X) → G .fst ≃ X
orbitEquiv T x .fst = orbitMap (LeftTorsor.leftAction T) x
orbitEquiv T x .snd .equiv-proof y =
  IsLeftTorsor.regular (LeftTorsor.isTorsor T) x y

equivariantMapIsEquiv : {G : Group ℓG} {X : Type ℓX} {Y : Type ℓY}
  (T : LeftTorsor G X) (U : LeftTorsor G Y) (f : X → Y)
  → Equivariant (LeftTorsor.leftAction T) (LeftTorsor.leftAction U) f
  → isEquiv f
equivariantMapIsEquiv {X = X} T U f ef =
  rec (isPropIsEquiv f) helper (IsLeftTorsor.inhabited (LeftTorsor.isTorsor T))
  where
  helper : (x : X) → isEquiv f
  helper x =
    isEquiv[f∘equivFunA≃B]→isEquiv[f]
      f
      (orbitEquiv T x)
      (subst isEquiv (sym commute) ((orbitEquiv U (f x)) .snd))
    where
    commute : f ∘ ((orbitEquiv T x) .fst) ≡ (orbitEquiv U (f x)) .fst
    commute = funExt (λ g → Equivariant.commutes ef g x)

equivariantMapEquiv : {G : Group ℓG} {X : Type ℓX} {Y : Type ℓY}
  (T : LeftTorsor G X) (U : LeftTorsor G Y) (f : X → Y)
  → Equivariant (LeftTorsor.leftAction T) (LeftTorsor.leftAction U) f
  → X ≃ Y
equivariantMapEquiv T U f ef = f , equivariantMapIsEquiv T U f ef

equivariantEquiv-of-map : {G : Group ℓG} {X : Type ℓX} {Y : Type ℓY}
  (T : LeftTorsor G X) (U : LeftTorsor G Y) (f : X → Y)
  (ef : Equivariant (LeftTorsor.leftAction T) (LeftTorsor.leftAction U) f)
  → EquivariantEquiv (LeftTorsor.leftAction T) (LeftTorsor.leftAction U)
EquivariantEquiv.equiv (equivariantEquiv-of-map T U f ef) =
  equivariantMapEquiv T U f ef
EquivariantEquiv.equivariant (equivariantEquiv-of-map T U f ef) = ef

torsorEquivariantEquiv-of-map : {G : Group ℓG} {X : Type ℓX} {Y : Type ℓY}
  (T : LeftTorsor G X) (U : LeftTorsor G Y) (f : X → Y)
  (ef : Equivariant (LeftTorsor.leftAction T) (LeftTorsor.leftAction U) f)
  → TorsorEquivariantEquiv T U
torsorEquivariantEquiv-of-map T U f ef = equivariantEquiv-of-map T U f ef
