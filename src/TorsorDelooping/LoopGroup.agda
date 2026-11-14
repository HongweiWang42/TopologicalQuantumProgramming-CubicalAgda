{-# OPTIONS --cubical --guardedness #-}

module TorsorDelooping.LoopGroup where

{-
Phase D — composition of regular-torsor automorphisms.

The group-level comparison with path concatenation remains dependent on a
composition-coherence theorem for SIP.  This module records the checked
structured-equivalence composition law needed for that final comparison.
-}

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Data.Sigma using (Σ≡Prop)
open import Cubical.Algebra.Group.Base

open import TorsorDelooping.Delooping
open import TorsorDelooping.Moduli

torsorEquiv-comp : {ℓ : Level} {G : Group ℓ}
  {T U V : LeftTorsorModuli ℓ G}
  → TorsorEquiv ℓ ℓ {G = G} T U
  → TorsorEquiv ℓ ℓ {G = G} U V
  → TorsorEquiv ℓ ℓ {G = G} T V
torsorEquiv-comp {ℓ} {G} {T} {U} {V} e f .fst = compEquiv (e .fst) (f .fst)
torsorEquiv-comp {ℓ} {G} {T} {U} {V} e f .snd g x =
  cong (f .fst .fst)
    (torsorEquiv-commutes {ℓG = ℓ} {ℓX = ℓ} {G = G} {T = T} {U = U} e g x)
  ∙ torsorEquiv-commutes {ℓG = ℓ} {ℓX = ℓ} {G = G} {T = U} {U = V}
      f g (e .fst .fst x)

rightRegularAut-comp : {ℓ : Level} (G : Group ℓ) (h k : G .fst)
  → torsorEquiv-comp {ℓ} {G} {T = torsorBase G} {U = torsorBase G} {V = torsorBase G}
      (rightRegularAut G h) (rightRegularAut G k) ≡
    rightRegularAut G (GroupStr._·_ (G .snd) h k)
rightRegularAut-comp {ℓ} G h k =
  Σ≡Prop
    (λ e → isPropTorsorEquivComm {ℓ} {G = G}
      {T = torsorBase G} {U = torsorBase G} e)
    (equivEq (funExt λ g → sym (GroupStr.·Assoc (G .snd) g h k)))
