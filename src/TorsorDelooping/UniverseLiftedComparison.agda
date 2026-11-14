{-# OPTIONS --cubical --guardedness --lossy-unification #-}

module TorsorDelooping.UniverseLiftedComparison where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Equiv.Properties
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism
open import Cubical.Algebra.Group.Base
open import Cubical.HITs.EilenbergMacLane1
open import Cubical.HITs.SetTruncation as ST
open import Cubical.HITs.Truncation.Properties using (setTruncTrunc2Iso)
open import Cubical.Homotopy.Connected
open import Cubical.Homotopy.EilenbergMacLane.Properties
open import Cubical.Homotopy.Loopspace
open import Cubical.Homotopy.WhiteheadsLemma

open import TorsorDelooping.Moduli
open import TorsorDelooping.Delooping
open import TorsorDelooping.EM1Comparison

private
  variable
    ℓ : Level

LiftedEM₁ : (G : Group ℓ) → Type (ℓ-suc ℓ)
LiftedEM₁ {ℓ} G = Lift (ℓ-suc ℓ) (EM₁ G)

liftedEmbase : (G : Group ℓ) → LiftedEM₁ G
liftedEmbase G = lift embase

liftedEm1ToTorsor : (G : Group ℓ) → LiftedEM₁ G → LeftTorsorModuli ℓ G
liftedEm1ToTorsor G x = em1ToTorsor G (lower x)

liftedEm1ToTorsor-base : (G : Group ℓ)
  → liftedEm1ToTorsor G (liftedEmbase G) ≡ torsorBase G
liftedEm1ToTorsor-base G = refl

liftIso : {ℓ ℓ' : Level} {A : Type ℓ} → Iso (Lift ℓ' A) A
Iso.fun liftIso = lower
Iso.inv liftIso = lift
Iso.sec liftIso x = refl
Iso.ret liftIso x = liftExt refl

isConnectedLiftedEM₁ : (G : Group ℓ) → isConnected 2 (LiftedEM₁ G)
isConnectedLiftedEM₁ {ℓ} G =
  isConnectedRetractFromIso 2 liftIso (isConnectedEM₁ G)

isGroupoidLiftedEM₁ : (G : Group ℓ) → isGroupoid (LiftedEM₁ G)
isGroupoidLiftedEM₁ {ℓ} G =
  isOfHLevelRetractFromIso 3 liftIso (isGroupoidEM₁ G)

liftPathIso : {ℓ ℓ' : Level} {A : Type ℓ} (a b : A)
  → Iso (lift {ℓ' = ℓ'} a ≡ lift b) (a ≡ b)
Iso.fun (liftPathIso a b) = cong lower
Iso.inv (liftPathIso a b) = liftExt
Iso.sec (liftPathIso {ℓ'} a b) =
  J (λ b p → cong lower (liftExt {ℓ' = ℓ'} p) ≡ p) refl
Iso.ret (liftPathIso a b) =
  J (λ y p → liftExt (cong lower p) ≡ p) refl

isEquiv-em1ToTorsor-baseCong : (G : Group ℓ)
  → isEquiv (λ p → cong (em1ToTorsor G) p)
isEquiv-em1ToTorsor-baseCong G =
  subst isEquiv
    (funExt (λ p → Ω→refl-cong (em1ToTorsor G) p))
    (isEquiv-em1ToTorsor-baseLoop G)

isEquiv-liftedEm1ToTorsor-baseLoop : (G : Group ℓ)
  → isEquiv
      (Ω→ (liftedEm1ToTorsor G , refl) .fst)
isEquiv-liftedEm1ToTorsor-baseLoop {ℓ} G =
  subst isEquiv
    (sym (funExt (λ p → Ω→refl-cong (liftedEm1ToTorsor G) p)))
    (equivIsEquiv
      (compEquiv
        (isoToEquiv (liftPathIso {ℓ' = ℓ-suc ℓ} embase embase))
        ((cong (em1ToTorsor G)) , isEquiv-em1ToTorsor-baseCong G)))

LiftedLoopEquiv : {ℓ : Level} (G : Group ℓ) (x : EM₁ G) → Type (ℓ-suc ℓ)
LiftedLoopEquiv {ℓ} G x =
  isEquiv
    (Ω→ {A = LiftedEM₁ G , lift x}
        {B = LeftTorsorModuli ℓ G , liftedEm1ToTorsor G (lift x)}
        (liftedEm1ToTorsor G , refl) .fst)

isPropLiftedLoopEquiv : {ℓ : Level} (G : Group ℓ) (x : EM₁ G)
  → isProp (LiftedLoopEquiv G x)
isPropLiftedLoopEquiv {ℓ} G x = isPropIsEquiv _

isEquiv-liftedEm1ToTorsor-loop : {ℓ : Level} (G : Group ℓ) (x : LiftedEM₁ G)
  → isEquiv
      (Ω→ {A = LiftedEM₁ G , x}
          {B = LeftTorsorModuli ℓ G , liftedEm1ToTorsor G x}
          (liftedEm1ToTorsor G , refl) .fst)
isEquiv-liftedEm1ToTorsor-loop {ℓ} G (lift x) =
  elimProp G (isPropLiftedLoopEquiv G)
    (isEquiv-liftedEm1ToTorsor-baseLoop G) x

isContrSetTruncFromConnected : {ℓ : Level} {A : Type ℓ}
  → isConnected 2 A → isContr ∥ A ∥₂
isContrSetTruncFromConnected {A = A} =
  isOfHLevelRetractFromIso 0 setTruncTrunc2Iso

isEquiv-liftedEm1ToTorsor-setTrunc : (G : Group ℓ)
  → isEquiv (ST.map (liftedEm1ToTorsor G))
isEquiv-liftedEm1ToTorsor-setTrunc G =
  isEquivFromIsContr (ST.map (liftedEm1ToTorsor G))
    (isContrSetTruncFromConnected (isConnectedLiftedEM₁ G))
    (isContrSetTruncFromConnected (isConnectedLeftTorsorModuli G))

isEquiv-liftedEm1ToTorsor : (G : Group ℓ)
  → isEquiv (liftedEm1ToTorsor G)
isEquiv-liftedEm1ToTorsor G =
  ΩEquiv→Equiv (liftedEm1ToTorsor G)
    (isEquiv-liftedEm1ToTorsor-setTrunc G)
    (isEquiv-liftedEm1ToTorsor-loop G)

liftedEm1ToTorsorEquiv : (G : Group ℓ)
  → LiftedEM₁ G ≃ LeftTorsorModuli ℓ G
liftedEm1ToTorsorEquiv G =
  liftedEm1ToTorsor G , isEquiv-liftedEm1ToTorsor G
