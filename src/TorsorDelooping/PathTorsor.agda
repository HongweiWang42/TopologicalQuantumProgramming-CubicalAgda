{-# OPTIONS --cubical --guardedness --lossy-unification #-}

module TorsorDelooping.PathTorsor where

{-
Phase I — path torsors for an abstract pointed connected 1-type.

`loopEquiv` is deliberately oriented from G to loops.  Thus the left action
on paths from pt is g • p = loopEquiv g ∙ p; the stated multiplication law
is exactly the law needed for a left action.
-}

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Equiv.Base using (equiv-proof)
open import Cubical.Foundations.Equiv.Properties
open import Cubical.Foundations.GroupoidLaws
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Path
open import Cubical.Foundations.Univalence
open import Cubical.Data.Sigma
open import Cubical.HITs.PropositionalTruncation as PT
open import Cubical.HITs.SetTruncation as ST
open import Cubical.Algebra.Group.Base
open import Cubical.Functions.Surjection
open import Cubical.Homotopy.Connected
open import Cubical.Homotopy.Loopspace
open import Cubical.Homotopy.WhiteheadsLemma

open import TorsorDelooping.LeftAction
open import TorsorDelooping.LeftTorsor
open import TorsorDelooping.Regular
open import TorsorDelooping.Moduli
open import TorsorDelooping.Delooping
open import TorsorDelooping.Morphisms
open import TorsorDelooping.SIPPathEmbedding
open import TorsorDelooping.SIPCoherence
open import TorsorDelooping.EM1Comparison using (Ω→refl-cong)
open import TorsorDelooping.UniverseLiftedComparison using
  (liftIso ; liftPathIso ; isContrSetTruncFromConnected)

private
  variable
    ℓ : Level

record PointedLoopGroupData (G : Group ℓ) (BG : Type ℓ) (pt : BG) : Type ℓ where
  field
    isConnectedBG : isConnected 2 BG
    isGroupoidBG  : isGroupoid BG
    loopEquiv     : G .fst ≃ (pt ≡ pt)
    loop-unit     : equivFun loopEquiv (GroupStr.1g (G .snd)) ≡ refl
    loop-comp     : (g h : G .fst) →
      equivFun loopEquiv (GroupStr._·_ (G .snd) g h) ≡
      equivFun loopEquiv g ∙ equivFun loopEquiv h

open PointedLoopGroupData public

pathTorsorAction : (G : Group ℓ) {BG : Type ℓ} {pt : BG}
  → PointedLoopGroupData G BG pt → (t : BG) → LeftAction G (pt ≡ t)
LeftAction.isSetX (pathTorsorAction G D t) = isGroupoidBG D _ _
LeftAction.act (pathTorsorAction G D t) g p = equivFun (loopEquiv D) g ∙ p
LeftAction.act-unit (pathTorsorAction G D t) p =
  cong (_∙ p) (loop-unit D) ∙ sym (lUnit p)
LeftAction.act-comp (pathTorsorAction G D t) g h p =
  cong (_∙ p) (loop-comp D g h) ∙ sym (assoc _ _ _)

pathTorsorInhabited : (G : Group ℓ) {BG : Type ℓ} {pt : BG}
  → (D : PointedLoopGroupData G BG pt) (t : BG) → ∥ pt ≡ t ∥₁
pathTorsorInhabited G {pt = pt} D t =
  PT.map snd
    (isConnectedSuc→isSurjection
      (isConnectedPoint 1 (isConnectedBG D) pt) t)

pathTorsorOrbitEquiv : (G : Group ℓ) {BG : Type ℓ} {pt : BG}
  → (D : PointedLoopGroupData G BG pt) (t : BG) (p : pt ≡ t)
  → G .fst ≃ (pt ≡ t)
pathTorsorOrbitEquiv G D t p =
  compEquiv (loopEquiv D) (compPathrEquiv p)

pathTorsor : (G : Group ℓ) {BG : Type ℓ} {pt : BG}
  → (D : PointedLoopGroupData G BG pt) (t : BG) → LeftTorsor G (pt ≡ t)
LeftTorsor.leftAction (pathTorsor G D t) = pathTorsorAction G D t
IsLeftTorsor.inhabited (LeftTorsor.isTorsor (pathTorsor G D t)) =
  pathTorsorInhabited G D t
IsLeftTorsor.regular (LeftTorsor.isTorsor (pathTorsor G D t)) p q =
  (pathTorsorOrbitEquiv G D t p) .snd .equiv-proof q

pathTorsorModuli : (G : Group ℓ) {BG : Type ℓ} {pt : BG}
  → PointedLoopGroupData G BG pt → BG → LeftTorsorModuli ℓ G
pathTorsorModuli G D t = fromLeftTorsor (pathTorsor G D t)

pathTorsorBaseEquiv : (G : Group ℓ) {BG : Type ℓ} {pt : BG}
  → (D : PointedLoopGroupData G BG pt)
  → TorsorEquiv ℓ ℓ {G = G} (torsorBase G) (pathTorsorModuli G D pt)
pathTorsorBaseEquiv G D .fst = loopEquiv D
pathTorsorBaseEquiv G D .snd g h =
  loop-comp D g h

pathTorsorModuli-base : (G : Group ℓ) {BG : Type ℓ} {pt : BG}
  → (D : PointedLoopGroupData G BG pt)
  → torsorBase G ≡ pathTorsorModuli G D pt
pathTorsorModuli-base G D =
  equivFun (torsorPathEquiv G (torsorBase G) (pathTorsorModuli G D _))
    (pathTorsorBaseEquiv G D)

pathTorsorTransportEquiv : (G : Group ℓ) {BG : Type ℓ} {pt : BG}
  → (D : PointedLoopGroupData G BG pt) {s t : BG} (q : s ≡ t)
  → TorsorEquiv ℓ ℓ {G = G} (pathTorsorModuli G D s) (pathTorsorModuli G D t)
pathTorsorTransportEquiv G D q .fst = compPathrEquiv q
pathTorsorTransportEquiv G D q .snd g p = sym (assoc _ _ _)

pathTorsorTransportPath : (G : Group ℓ) {BG : Type ℓ} {pt : BG}
  → (D : PointedLoopGroupData G BG pt) {s t : BG} (q : s ≡ t)
  → pathTorsorModuli G D s ≡ pathTorsorModuli G D t
pathTorsorTransportPath G D {s} {t} q =
  equivFun (torsorPathEquiv G (pathTorsorModuli G D s) (pathTorsorModuli G D t))
    (pathTorsorTransportEquiv G D q)

pathFamily-ua : {BG : Type ℓ} {pt s t : BG} (q : s ≡ t)
  → cong (pt ≡_) q ≡ ua (compPathrEquiv q)
pathFamily-ua {pt = pt} {s = s} =
  J (λ t q → cong (pt ≡_) q ≡ ua (compPathrEquiv q)) base
  where
  base : cong (pt ≡_) (refl {x = s}) ≡
    ua (compPathrEquiv {x = pt} (refl {x = s}))
  base = pathFamily-cong-refl ∙
    sym (cong ua (equivEq (funExt (λ p → sym (rUnit p)))) ∙ uaIdEquiv)
    where
    pathFamily-cong-refl : cong (pt ≡_) (refl {x = s}) ≡ refl
    pathFamily-cong-refl i j = pt ≡ s

pathTorsorModuli-cong : (G : Group ℓ) {BG : Type ℓ} {pt : BG}
  → (D : PointedLoopGroupData G BG pt) {s t : BG} (q : s ≡ t)
  → cong (pathTorsorModuli G D) q ≡ pathTorsorTransportPath G D q
pathTorsorModuli-cong G D q =
  caracTorsor≡ _ _
    (pathFamily-ua q ∙
      sym (torsorPath-carrier (pathTorsorTransportEquiv G D q)))

pathTorsorAutLoopIso : (G : Group ℓ) {BG : Type ℓ} {pt : BG}
  → (D : PointedLoopGroupData G BG pt)
  → Iso (TorsorEquiv ℓ ℓ {G = G}
           (pathTorsorModuli G D pt) (pathTorsorModuli G D pt))
         (pt ≡ pt)
Iso.fun (pathTorsorAutLoopIso G D) e = e .fst .fst refl
Iso.inv (pathTorsorAutLoopIso G D) q = pathTorsorTransportEquiv G D q
Iso.sec (pathTorsorAutLoopIso G D) q = sym (lUnit q)
Iso.ret (pathTorsorAutLoopIso G D) e =
  Σ≡Prop
    (λ e' → isPropTorsorEquivComm e')
    (equivEq (funExt λ p →
      cong (_∙ (e .fst .fst refl))
        (sym (secEq (loopEquiv D) p))
      ∙ sym (e .snd (invEq (loopEquiv D) p) refl)
      ∙ cong (e .fst .fst)
          (sym (rUnit (equivFun (loopEquiv D) (invEq (loopEquiv D) p)))
           ∙ secEq (loopEquiv D) p)))

isEquiv-pathTorsorModuli-baseCong : (G : Group ℓ) {BG : Type ℓ} {pt : BG}
  → (D : PointedLoopGroupData G BG pt)
  → isEquiv (λ q → cong (pathTorsorModuli G D) q)
isEquiv-pathTorsorModuli-baseCong G D =
  subst isEquiv
    (sym (funExt (pathTorsorModuli-cong G D)))
    (equivIsEquiv
      (compEquiv
        (invEquiv (isoToEquiv (pathTorsorAutLoopIso G D)))
        (torsorPathEquiv G (pathTorsorModuli G D _) (pathTorsorModuli G D _))))

isEquiv-pathTorsorModuli-baseLoop : (G : Group ℓ) {BG : Type ℓ} {pt : BG}
  → (D : PointedLoopGroupData G BG pt)
  → isEquiv
      (Ω→ {A = BG , pt}
          {B = LeftTorsorModuli ℓ G , pathTorsorModuli G D pt}
          (pathTorsorModuli G D , refl) .fst)
isEquiv-pathTorsorModuli-baseLoop G D =
  subst isEquiv
    (sym (funExt (λ q → Ω→refl-cong (pathTorsorModuli G D) q)))
    (isEquiv-pathTorsorModuli-baseCong G D)

isEquiv-pathTorsorModuli-loopAtPath : (G : Group ℓ) {BG : Type ℓ} {pt : BG}
  → (D : PointedLoopGroupData G BG pt) {t : BG} (p : pt ≡ t)
  → isEquiv
      (Ω→ {A = BG , t}
          {B = LeftTorsorModuli ℓ G , pathTorsorModuli G D t}
          (pathTorsorModuli G D , refl) .fst)
isEquiv-pathTorsorModuli-loopAtPath G {pt = pt} D =
  J (λ t p → isEquiv
      (Ω→ {A = _ , t}
          {B = _ , pathTorsorModuli G D t}
          (pathTorsorModuli G D , refl) .fst))
    (isEquiv-pathTorsorModuli-baseLoop G D)

isEquiv-pathTorsorModuli-loop : (G : Group ℓ) {BG : Type ℓ} {pt : BG}
  → (D : PointedLoopGroupData G BG pt) (t : BG)
  → isEquiv
      (Ω→ {A = BG , t}
          {B = LeftTorsorModuli ℓ G , pathTorsorModuli G D t}
          (pathTorsorModuli G D , refl) .fst)
isEquiv-pathTorsorModuli-loop G D t =
  PT.rec (isPropIsEquiv _)
    (isEquiv-pathTorsorModuli-loopAtPath G D)
    (pathTorsorInhabited G D t)

liftedPathTorsorModuli : (G : Group ℓ) {BG : Type ℓ} {pt : BG}
  → PointedLoopGroupData G BG pt → Lift (ℓ-suc ℓ) BG → LeftTorsorModuli ℓ G
liftedPathTorsorModuli G D x = pathTorsorModuli G D (lower x)

isConnectedLiftedBG : (G : Group ℓ) {BG : Type ℓ} {pt : BG}
  → PointedLoopGroupData G BG pt → isConnected 2 (Lift (ℓ-suc ℓ) BG)
isConnectedLiftedBG G D =
  isConnectedRetractFromIso 2 liftIso (isConnectedBG D)

isGroupoidLiftedBG : (G : Group ℓ) {BG : Type ℓ} {pt : BG}
  → PointedLoopGroupData G BG pt → isGroupoid (Lift (ℓ-suc ℓ) BG)
isGroupoidLiftedBG G D =
  isOfHLevelRetractFromIso 3 liftIso (isGroupoidBG D)

isEquiv-pathTorsorModuli-loopCong : (G : Group ℓ) {BG : Type ℓ} {pt : BG}
  → (D : PointedLoopGroupData G BG pt) (t : BG)
  → isEquiv (λ q → cong (pathTorsorModuli G D) q)
isEquiv-pathTorsorModuli-loopCong G D t =
  subst isEquiv
    (funExt (λ q → Ω→refl-cong (pathTorsorModuli G D) q))
    (isEquiv-pathTorsorModuli-loop G D t)

isEquiv-liftedPathTorsorModuli-loop : (G : Group ℓ) {BG : Type ℓ} {pt : BG}
  → (D : PointedLoopGroupData G BG pt) (x : Lift (ℓ-suc ℓ) BG)
  → isEquiv
      (Ω→ {A = Lift (ℓ-suc ℓ) BG , x}
          {B = LeftTorsorModuli ℓ G , liftedPathTorsorModuli G D x}
          (liftedPathTorsorModuli G D , refl) .fst)
isEquiv-liftedPathTorsorModuli-loop {ℓ} G D (lift t) =
  subst isEquiv
    (sym (funExt (λ q → Ω→refl-cong (liftedPathTorsorModuli G D) q)))
    (equivIsEquiv
      (compEquiv
        (isoToEquiv (liftPathIso {ℓ' = ℓ-suc ℓ} t t))
        ((cong (pathTorsorModuli G D)) ,
          isEquiv-pathTorsorModuli-loopCong G D t)))

isEquiv-liftedPathTorsorModuli-setTrunc : (G : Group ℓ) {BG : Type ℓ} {pt : BG}
  → (D : PointedLoopGroupData G BG pt)
  → isEquiv (ST.map (liftedPathTorsorModuli G D))
isEquiv-liftedPathTorsorModuli-setTrunc G D =
  isEquivFromIsContr (ST.map (liftedPathTorsorModuli G D))
    (isContrSetTruncFromConnected (isConnectedLiftedBG G D))
    (isContrSetTruncFromConnected (isConnectedLeftTorsorModuli G))

isEquiv-liftedPathTorsorModuli : (G : Group ℓ) {BG : Type ℓ} {pt : BG}
  → (D : PointedLoopGroupData G BG pt)
  → isEquiv (liftedPathTorsorModuli G D)
isEquiv-liftedPathTorsorModuli G D =
  ΩEquiv→Equiv (liftedPathTorsorModuli G D)
    (isEquiv-liftedPathTorsorModuli-setTrunc G D)
    (isEquiv-liftedPathTorsorModuli-loop G D)

liftedPathTorsorModuliEquiv : (G : Group ℓ) {BG : Type ℓ} {pt : BG}
  → PointedLoopGroupData G BG pt
  → Lift (ℓ-suc ℓ) BG ≃ LeftTorsorModuli ℓ G
liftedPathTorsorModuliEquiv G D =
  liftedPathTorsorModuli G D , isEquiv-liftedPathTorsorModuli G D

liftedPathTorsorModuli-base : (G : Group ℓ) {BG : Type ℓ} {pt : BG}
  → (D : PointedLoopGroupData G BG pt)
  → liftedPathTorsorModuli G D (lift pt) ≡ pathTorsorModuli G D pt
liftedPathTorsorModuli-base G D = refl
