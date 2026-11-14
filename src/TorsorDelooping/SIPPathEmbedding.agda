{-# OPTIONS --cubical --guardedness #-}

module TorsorDelooping.SIPPathEmbedding where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Univalence
open import Cubical.Data.Sigma
open import Cubical.Functions.Embedding
open import Cubical.Algebra.Group.Base

open import TorsorDelooping.Moduli
open import TorsorDelooping.Delooping

abstract
  isPropTorsorStructurePathP : {ℓ : Level} {G : Group ℓ}
    {T U : LeftTorsorModuli ℓ G} (p : T .fst ≡ U .fst)
    → isProp (PathP (λ i → TorsorStructure G (p i)) (T .snd) (U .snd))
  isPropTorsorStructurePathP {ℓ} {G = G} {T = T} {U = U} p =
    subst
      (λ q → isProp (PathP (λ i → TorsorStructure G (q i)) (T .snd) (U .snd)))
      (ua-pathToEquiv p)
      (isOfHLevelRespectEquiv 1
        (torsorUnivalentStr {ℓG = ℓ} {ℓX = ℓ} G (pathToEquiv p))
        (isPropTorsorEquivComm {ℓ} {G = G} {T = T} {U = U}
          (pathToEquiv p)))

  caracTorsor≡ : {ℓ : Level} {G : Group ℓ} {T U : LeftTorsorModuli ℓ G}
    (p q : T ≡ U) → cong fst p ≡ cong fst q → p ≡ q
  caracTorsor≡ {ℓ} {G = G} {T = T} {U = U} p q α =
    isEmbedding→Inj (iso→isEmbedding (invIso ΣPathIsoPathΣ)) _ _
      (Σ≡Prop (λ r → isPropTorsorStructurePathP {G = G} {T = T} {U = U} r) α)
