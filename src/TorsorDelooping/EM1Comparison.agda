{-# OPTIONS --cubical --guardedness --lossy-unification #-}

module TorsorDelooping.EM1Comparison where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.GroupoidLaws
open import Cubical.Algebra.Group.Base
open import Cubical.HITs.EilenbergMacLane1
open import Cubical.Homotopy.EilenbergMacLane.Properties
open import Cubical.Homotopy.Loopspace

open import TorsorDelooping.Moduli
open import TorsorDelooping.Delooping
open import TorsorDelooping.SIPCoherence

em1ToTorsor : {ℓ : Level} (G : Group ℓ)
  → EM₁ G → LeftTorsorModuli ℓ G
em1ToTorsor G = rec' G (isGroupoidLeftTorsorModuli G) (torsorBase G)
  (regularTorsorLoop G) (regularTorsorLoop-comp G)

em1ToTorsor-base : {ℓ : Level} (G : Group ℓ)
  → em1ToTorsor G embase ≡ torsorBase G
em1ToTorsor-base G = refl

em1ToTorsor-loop : {ℓ : Level} (G : Group ℓ) (g : G .fst)
  → cong (em1ToTorsor G) (emloop g) ≡ regularTorsorLoop G g
em1ToTorsor-loop G g = refl

regularTorsorLoopIso : {ℓ : Level} (G : Group ℓ)
  → Iso (G .fst) (torsorBase G ≡ torsorBase G)
regularTorsorLoopIso {ℓ} G .Iso.fun = regularTorsorLoop G
regularTorsorLoopIso {ℓ} G .Iso.inv = torsorLoopEquivGroup G .fst
regularTorsorLoopIso {ℓ} G .Iso.sec p =
  cong (equivFun (torsorPathEquiv G (torsorBase G) (torsorBase G)))
    (regularAutRet G (equivFun (torsorLoopEquivAut G) p))
  ∙ secEq (torsorPathEquiv G (torsorBase G) (torsorBase G)) p
regularTorsorLoopIso {ℓ} G .Iso.ret g =
  cong (regularAutToGroup G)
    (retEq (torsorPathEquiv G (torsorBase G) (torsorBase G))
      (rightRegularAut G g))
  ∙ GroupStr.·IdL (G .snd) g

Ω→refl-cong : {ℓ ℓ' : Level} {A : Type ℓ} {B : Type ℓ'}
  {a : A} (f : A → B) (p : a ≡ a)
  → (Ω→ (f , refl) .fst) p ≡ cong f p
Ω→refl-cong f p =
  cong fst
    (compPath-unique refl (cong f p) refl
      (Ω→ (f , refl) .fst p , doubleCompPath-filler refl (cong f p) refl)
      (cong f p , λ _ → cong f p))

em1ToTorsor-baseLoop : {ℓ : Level} (G : Group ℓ)
  (p : embase ≡ embase)
  → (Ω→ (em1ToTorsor G , refl) .fst) p ≡
    regularTorsorLoop G (Iso.fun (ΩEM₁Iso G) p)
em1ToTorsor-baseLoop G p =
  Ω→refl-cong (em1ToTorsor G) p
  ∙ cong (cong (em1ToTorsor G)) (sym (Iso.ret (ΩEM₁Iso G) p))
  ∙ em1ToTorsor-loop G (Iso.fun (ΩEM₁Iso G) p)

isEquiv-em1ToTorsor-baseLoop : {ℓ : Level} (G : Group ℓ)
  → isEquiv (Ω→ (em1ToTorsor G , refl) .fst)
isEquiv-em1ToTorsor-baseLoop G =
  subst isEquiv
    (sym (funExt (em1ToTorsor-baseLoop G)))
    (equivIsEquiv
      (compEquiv (isoToEquiv (ΩEM₁Iso G))
        (isoToEquiv (regularTorsorLoopIso G))))
