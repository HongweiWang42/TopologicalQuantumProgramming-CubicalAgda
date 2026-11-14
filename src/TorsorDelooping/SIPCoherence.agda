{-# OPTIONS --cubical --guardedness --lossy-unification #-}

module TorsorDelooping.SIPCoherence where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Univalence
open import Cubical.Foundations.GroupoidLaws
open import Cubical.Algebra.Group.Base

open import TorsorDelooping.Moduli
open import TorsorDelooping.Delooping
open import TorsorDelooping.LoopGroup
open import TorsorDelooping.SIPPathEmbedding

private
  variable ℓ : Level

torsorPath-carrier : {ℓ : Level} {G : Group ℓ}
  {T U : LeftTorsorModuli ℓ G}
  (e : TorsorEquiv ℓ ℓ {G = G} T U)
  → cong fst (equivFun (torsorPathEquiv G T U) e) ≡ ua (e .fst)
torsorPath-carrier e = refl

regularTorsorLoop : {ℓ : Level} (G : Group ℓ) (g : G .fst)
  → torsorBase G ≡ torsorBase G
regularTorsorLoop G g =
  equivFun (torsorPathEquiv G (torsorBase G) (torsorBase G))
    (rightRegularAut G g)

regularTorsorLoop-comp : {ℓ : Level} (G : Group ℓ) (g h : G .fst)
  → regularTorsorLoop G (GroupStr._·_ (G .snd) g h) ≡
    regularTorsorLoop G g ∙ regularTorsorLoop G h
regularTorsorLoop-comp {ℓ} G g h =
  cong
    (equivFun (torsorPathEquiv G (torsorBase G) (torsorBase G)))
    (sym (rightRegularAut-comp G g h))
  ∙ caracTorsor≡
      (equivFun (torsorPathEquiv G (torsorBase G) (torsorBase G))
        (torsorEquiv-comp (rightRegularAut G g) (rightRegularAut G h)))
      (regularTorsorLoop G g ∙ regularTorsorLoop G h)
      (torsorPath-carrier (torsorEquiv-comp (rightRegularAut G g) (rightRegularAut G h))
      ∙ uaCompEquiv ((rightRegularAut G g) .fst) ((rightRegularAut G h) .fst)
      ∙ sym (cong-∙ fst (regularTorsorLoop G g) (regularTorsorLoop G h)))
