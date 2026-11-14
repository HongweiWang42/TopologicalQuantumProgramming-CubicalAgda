{-# OPTIONS --cubical --guardedness #-}

module TorsorDelooping.Moduli where

{-
Phase B — the univalent moduli type of set-level left torsors.

The operation part of an action uses Cubical.Structures.LeftAction.  The
sethood, unit, associativity, inhabitation, and regularity clauses are all
propositions; hence Cubical.Structures.Axioms lifts the library's univalent
action structure to the structure of torsors.
-}

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.SIP
open import Cubical.Foundations.Structure
open import Cubical.Data.Sigma
open import Cubical.HITs.PropositionalTruncation
open import Cubical.Algebra.Group.Base
open import Cubical.Structures.LeftAction as Raw
open import Cubical.Structures.Axioms

open import TorsorDelooping.LeftAction as PhaseA
open import TorsorDelooping.LeftTorsor as PhaseA

private
  variable
    ℓG ℓX : Level

ActionAxioms : (G : Group ℓG) (X : Type ℓX)
  → Raw.LeftActionStructure (G .fst) X → Type (ℓ-max ℓG ℓX)
ActionAxioms G X act =
  isSet X
  × ((x : X) → act (GroupStr.1g (G .snd)) x ≡ x)
  × ((g h : G .fst) (x : X) →
       act (GroupStr._·_ (G .snd) g h) x ≡ act g (act h x))

isPropActionAxioms : (G : Group ℓG) (X : Type ℓX)
  (act : Raw.LeftActionStructure (G .fst) X) → isProp (ActionAxioms G X act)
isPropActionAxioms G X act =
  isPropΣ isPropIsSet
    (λ isSetX →
      isProp× (isPropΠ λ x → isSetX _ _)
              (isPropΠ3 λ g h x → isSetX _ _))

ActionStructure : (G : Group ℓG) → Type ℓX → Type (ℓ-max ℓG ℓX)
ActionStructure G = AxiomsStructure (Raw.LeftActionStructure (G .fst)) (ActionAxioms G)

ActionEquivStr : {ℓG ℓX : Level} (G : Group ℓG)
  → StrEquiv {ℓ = ℓX} (ActionStructure {ℓX = ℓX} G) (ℓ-max ℓG ℓX)
ActionEquivStr {ℓX = ℓX} G =
  AxiomsEquivStr (Raw.LeftActionEquivStr (G .fst)) (ActionAxioms G)

actionUnivalentStr : {ℓG ℓX : Level} (G : Group ℓG)
  → UnivalentStr (ActionStructure {ℓX = ℓX} G) (ActionEquivStr {ℓX = ℓX} G)
actionUnivalentStr {ℓX = ℓX} G =
  axiomsUnivalentStr (Raw.LeftActionEquivStr (G .fst))
    (isPropActionAxioms G) (Raw.leftActionUnivalentStr (G .fst))

TorsorAxioms : (G : Group ℓG) (X : Type ℓX)
  → ActionStructure G X → Type (ℓ-max ℓG ℓX)
TorsorAxioms G X action =
  ∥ X ∥₁
  × ((x y : X) → isContr (Σ[ g ∈ G .fst ] action .fst g x ≡ y))

isPropTorsorAxioms : (G : Group ℓG) (X : Type ℓX)
  (action : ActionStructure G X) → isProp (TorsorAxioms G X action)
isPropTorsorAxioms G X action =
  isProp× isPropPropTrunc (isPropΠ2 λ x y → isPropIsContr)

TorsorStructure : (G : Group ℓG) → Type ℓX → Type (ℓ-max ℓG ℓX)
TorsorStructure G = AxiomsStructure (ActionStructure G) (TorsorAxioms G)

TorsorEquivStr : {ℓG ℓX : Level} (G : Group ℓG)
  → StrEquiv {ℓ = ℓX} (TorsorStructure {ℓX = ℓX} G) (ℓ-max ℓG ℓX)
TorsorEquivStr {ℓX = ℓX} G =
  AxiomsEquivStr (ActionEquivStr {ℓX = ℓX} G) (TorsorAxioms G)

torsorUnivalentStr : {ℓG ℓX : Level} (G : Group ℓG)
  → UnivalentStr (TorsorStructure {ℓX = ℓX} G) (TorsorEquivStr {ℓX = ℓX} G)
torsorUnivalentStr {ℓX = ℓX} G =
  axiomsUnivalentStr (ActionEquivStr {ℓX = ℓX} G)
    (isPropTorsorAxioms G) (actionUnivalentStr {ℓX = ℓX} G)

LeftTorsorModuli : (ℓX : Level) (G : Group ℓG) → Type (ℓ-max (ℓ-suc ℓX) ℓG)
LeftTorsorModuli ℓX G = TypeWithStr ℓX (TorsorStructure {ℓX = ℓX} G)

TorsorEquiv : (ℓG ℓX : Level) {G : Group ℓG}
  (T U : LeftTorsorModuli ℓX G) → Type (ℓ-max ℓG ℓX)
TorsorEquiv ℓG ℓX {G = G} T U =
  T ≃[ TorsorEquivStr {ℓG = ℓG} {ℓX = ℓX} G ] U

torsorPathEquiv : {ℓG ℓX : Level} (G : Group ℓG)
  (T U : LeftTorsorModuli ℓX G)
  → TorsorEquiv ℓG ℓX {G = G} T U ≃ (T ≡ U)
torsorPathEquiv {ℓG = ℓG} {ℓX = ℓX} G T U =
  SIP {S = TorsorStructure {ℓX = ℓX} G}
    {ι = TorsorEquivStr {ℓG = ℓG} {ℓX = ℓX} G}
    (torsorUnivalentStr {ℓG = ℓG} {ℓX = ℓX} G) T U

torsorEquiv-commutes : {ℓG ℓX : Level} {G : Group ℓG}
  {T U : LeftTorsorModuli ℓX G}
  (e : TorsorEquiv ℓG ℓX {G = G} T U)
  (g : G .fst) (x : T .fst) →
  e .fst .fst (T .snd .fst .fst g x) ≡ U .snd .fst .fst g (e .fst .fst x)
torsorEquiv-commutes e g x = e .snd g x

moduliLeftAction : {ℓG ℓX : Level} {G : Group ℓG}
  (T : LeftTorsorModuli ℓX G) → PhaseA.LeftAction G (T .fst)
PhaseA.LeftAction.isSetX (moduliLeftAction T) = T .snd .fst .snd .fst
PhaseA.LeftAction.act (moduliLeftAction T) = T .snd .fst .fst
PhaseA.LeftAction.act-unit (moduliLeftAction T) = T .snd .fst .snd .snd .fst
PhaseA.LeftAction.act-comp (moduliLeftAction T) = T .snd .fst .snd .snd .snd

moduliLeftTorsor : {ℓG ℓX : Level} {G : Group ℓG}
  (T : LeftTorsorModuli ℓX G) → PhaseA.LeftTorsor G (T .fst)
PhaseA.LeftTorsor.leftAction (moduliLeftTorsor T) = moduliLeftAction T
PhaseA.IsLeftTorsor.inhabited (PhaseA.LeftTorsor.isTorsor (moduliLeftTorsor T)) =
  T .snd .snd .fst
PhaseA.IsLeftTorsor.regular (PhaseA.LeftTorsor.isTorsor (moduliLeftTorsor T)) =
  T .snd .snd .snd

-- The Phase-A record packages exactly the structure used by the moduli type.
-- This conversion is kept explicit so later phases can use the regular torsor
-- as a canonical point of the univalent moduli space.
fromLeftTorsor : {ℓG ℓX : Level} {G : Group ℓG} {X : Type ℓX}
  → PhaseA.LeftTorsor G X → LeftTorsorModuli ℓX G
fromLeftTorsor {X = X} T .fst = X
fromLeftTorsor T .snd .fst .fst = PhaseA.LeftAction.act (PhaseA.LeftTorsor.leftAction T)
fromLeftTorsor T .snd .fst .snd .fst =
  PhaseA.LeftAction.isSetX (PhaseA.LeftTorsor.leftAction T)
fromLeftTorsor T .snd .fst .snd .snd .fst =
  PhaseA.LeftAction.act-unit (PhaseA.LeftTorsor.leftAction T)
fromLeftTorsor T .snd .fst .snd .snd .snd =
  PhaseA.LeftAction.act-comp (PhaseA.LeftTorsor.leftAction T)
fromLeftTorsor T .snd .snd .fst =
  PhaseA.IsLeftTorsor.inhabited (PhaseA.LeftTorsor.isTorsor T)
fromLeftTorsor T .snd .snd .snd =
  PhaseA.IsLeftTorsor.regular (PhaseA.LeftTorsor.isTorsor T)
