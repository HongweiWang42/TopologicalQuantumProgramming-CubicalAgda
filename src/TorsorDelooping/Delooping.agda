{-# OPTIONS --cubical --guardedness #-}

module TorsorDelooping.Delooping where

{-
Phase C — the torsor moduli space as a delooping.

The regular left torsor supplies a canonical point.  Paths in the univalent
moduli are structured equivariant equivalences (by Phase B's SIP result).
Evaluation of a regular-torsor automorphism at the unit identifies that loop
type with the underlying group carrier; its inverse is right multiplication.
-}

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism using (Iso ; isoToEquiv)
open import Cubical.Data.Sigma using (Σ≡Prop)
open import Cubical.Data.Unit using (Unit ; tt)
open import Cubical.HITs.PropositionalTruncation
open import Cubical.HITs.PropositionalTruncation as PT
open import Cubical.HITs.Truncation as Trunc using (∣_∣ₕ)
open import Cubical.HITs.Truncation.Properties using (isOfHLevelTrunc)
open import Cubical.Homotopy.Connected
open import Cubical.Algebra.Group.Base
open import Cubical.Algebra.Group.Properties using (·GroupAutomorphismR)

open import TorsorDelooping.LeftAction as PhaseA
open import TorsorDelooping.LeftTorsor as PhaseA
open import TorsorDelooping.Regular
open import TorsorDelooping.Morphisms
open import TorsorDelooping.Moduli

private
  variable
    ℓ : Level

torsorBase : (G : Group ℓ) → LeftTorsorModuli ℓ G
torsorBase G = fromLeftTorsor (regularLeftTorsor G)

baseToTorsorEquiv : (G : Group ℓ) (T : LeftTorsorModuli ℓ G) (x : T .fst)
  → TorsorEquiv ℓ ℓ {G = G} (torsorBase G) T
baseToTorsorEquiv G T x .fst =
  equivariantMapEquiv (regularLeftTorsor G) (moduliLeftTorsor T)
    (λ g → T .snd .fst .fst g x)
    equivariance
  where
  equivariance : PhaseA.Equivariant (regularLeftAction G) (moduliLeftAction T)
    (λ g → T .snd .fst .fst g x)
  PhaseA.Equivariant.commutes equivariance g h =
    T .snd .fst .snd .snd .snd g h x
baseToTorsorEquiv G T x .snd g h = T .snd .fst .snd .snd .snd g h x

basePath : (G : Group ℓ) (T : LeftTorsorModuli ℓ G) (x : T .fst)
  → torsorBase G ≡ T
basePath G T x =
  equivFun (torsorPathEquiv G (torsorBase G) T) (baseToTorsorEquiv G T x)

merelyBasePath : (G : Group ℓ) (T : LeftTorsorModuli ℓ G)
  → ∥ torsorBase G ≡ T ∥₁
merelyBasePath G T =
  rec isPropPropTrunc (λ x → ∣ basePath G T x ∣₁) (T .snd .snd .fst)

baseConnectedMap : (G : Group ℓ)
  → isConnectedFun 1 (λ (_ : Unit) → torsorBase G)
baseConnectedMap G T =
  PT.rec (isOfHLevelTrunc 1) (λ p → ∣ tt , p ∣ₕ) (merelyBasePath G T) ,
  λ y → isOfHLevelTrunc 1 _ y

isConnectedLeftTorsorModuli : (G : Group ℓ) → isConnected 2 (LeftTorsorModuli ℓ G)
isConnectedLeftTorsorModuli G =
  isConnectedPoint2 1 (torsorBase G) (baseConnectedMap G)

isPropTorsorEquivComm : {ℓ : Level} {G : Group ℓ}
  {T U : LeftTorsorModuli ℓ G} (e : T .fst ≃ U .fst)
  → isProp (TorsorEquivStr {ℓG = ℓ} {ℓX = ℓ} G T U e)
isPropTorsorEquivComm {ℓ} {U = U} e =
  isPropΠ2 λ g x → U .snd .fst .snd .fst _ _

isSetTorsorEquiv : {ℓ : Level} {G : Group ℓ}
  (T U : LeftTorsorModuli ℓ G) → isSet (TorsorEquiv ℓ ℓ {G = G} T U)
isSetTorsorEquiv {ℓ} {G = G} T U =
  isSetΣSndProp
    (isOfHLevel≃ 2 (T .snd .fst .snd .fst) (U .snd .fst .snd .fst))
    (isPropTorsorEquivComm {ℓ} {G = G} {T = T} {U = U})

isGroupoidLeftTorsorModuli : {ℓ : Level} (G : Group ℓ) → isGroupoid (LeftTorsorModuli ℓ G)
isGroupoidLeftTorsorModuli {ℓ} G T U =
  isOfHLevelRespectEquiv 2
    (torsorPathEquiv {ℓG = ℓ} {ℓX = ℓ} G T U) (isSetTorsorEquiv {G = G} T U)

torsorLoopEquivAut : {ℓ : Level} (G : Group ℓ)
  → (torsorBase G ≡ torsorBase G) ≃ TorsorEquiv ℓ ℓ {G = G} (torsorBase G) (torsorBase G)
torsorLoopEquivAut {ℓ} G =
  invEquiv (torsorPathEquiv {ℓG = ℓ} {ℓX = ℓ} G (torsorBase G) (torsorBase G))

regularAutToGroup : {ℓ : Level} (G : Group ℓ)
  → TorsorEquiv ℓ ℓ {G = G} (torsorBase G) (torsorBase G) → G .fst
regularAutToGroup {ℓ} G e = e .fst .fst (GroupStr.1g (G .snd))

rightRegularAut : {ℓ : Level} (G : Group ℓ) (h : G .fst)
  → TorsorEquiv ℓ ℓ {G = G} (torsorBase G) (torsorBase G)
rightRegularAut {ℓ} G h .fst = isoToEquiv (·GroupAutomorphismR G h)
rightRegularAut {ℓ} G h .snd g x =
  sym (GroupStr.·Assoc (G .snd) g x h)

regularAutUnderlying : {ℓ : Level} (G : Group ℓ)
  (e : TorsorEquiv ℓ ℓ {G = G} (torsorBase G) (torsorBase G))
  → (rightRegularAut G (regularAutToGroup G e) .fst) ≡ e .fst
regularAutUnderlying {ℓ} G e =
  equivEq
    (funExt λ g →
      sym (sym (cong (e .fst .fst) (GroupStr.·IdR (G .snd) g))
        ∙ torsorEquiv-commutes {ℓG = ℓ} {ℓX = ℓ} {G = G}
            {T = torsorBase G} {U = torsorBase G}
            e g (GroupStr.1g (G .snd))))

regularAutRet : {ℓ : Level} (G : Group ℓ)
  (e : TorsorEquiv ℓ ℓ {G = G} (torsorBase G) (torsorBase G))
  → rightRegularAut G (regularAutToGroup G e) ≡ e
regularAutRet {ℓ} G e =
  Σ≡Prop
    (λ e' → isPropTorsorEquivComm {ℓ} {G = G}
      {T = torsorBase G} {U = torsorBase G} e')
    (regularAutUnderlying G e)

regularAutIsoGroup : {ℓ : Level} (G : Group ℓ)
  → Iso (TorsorEquiv ℓ ℓ {G = G} (torsorBase G) (torsorBase G)) (G .fst)
Iso.fun (regularAutIsoGroup {ℓ} G) = regularAutToGroup G
Iso.inv (regularAutIsoGroup {ℓ} G) = rightRegularAut G
Iso.sec (regularAutIsoGroup {ℓ} G) h = GroupStr.·IdL (G .snd) h
Iso.ret (regularAutIsoGroup {ℓ} G) e = regularAutRet G e

torsorLoopEquivGroup : {ℓ : Level} (G : Group ℓ)
  → (torsorBase G ≡ torsorBase G) ≃ G .fst
torsorLoopEquivGroup {ℓ} G =
  compEquiv (torsorLoopEquivAut G) (isoToEquiv (regularAutIsoGroup G))
