{-# OPTIONS --cubical --guardedness #-}

module GroupPresentation where

{-
Mathematical stage: 01 — presentation-space foundations.
Purpose: define generators, signed words, relation loops, the presentation
pushout, and its 1-truncation.
Main declarations: GeneratorSpace, Word, Presentation, relationLoop,
PresentationPushout, BG_pres, and BG-basepoint.
Status: implemented and typechecked definitions; no presentation-isomorphism
claim is made in this foundational module.
-}

open import Cubical.Foundations.Prelude
open import Cubical.Data.Unit
open import Cubical.Data.Sum
open import Cubical.Data.Sigma
open import Cubical.HITs.S1.Base
open import Cubical.HITs.Pushout.Base
open import Cubical.HITs.Susp.Base
open import Cubical.HITs.Truncation

{-
GroupPresentation.agda

Stage 1
  GeneratorInput
  reference
  generator
  GeneratorSpace
  referenceMeridian
  generatorMeridian
  generatorLoop

Stage 2
  Signed-word syntax / wordLoop

Stage 3
  Relation data / attaching map

Stage 4
  Pushout

Stage 5
  1-truncation / BG / basepoint
-}

-- Stage 1


{-
  GeneratorInput(Gen) := {e} ⊔ Gen

  where e is the distinguished reference element,
  not a group generator.
-}
GeneratorInput : ∀ {ℓ} → Type ℓ → Type ℓ
GeneratorInput {ℓ} Gen = Unit* {ℓ = ℓ} ⊎ Gen 


{-
  For any unierse ℓ and Gen : Type ℓ, give an element 'reference' s.t.

       reference : GeneratorInput Gen = {e} ⊔ Gen

  Where 'reference' is explicilty given by

       reference = inl tt*

  that tt* : Unit* is the unique element of the singleton type Unit* (i.e. e ∈ {e}) 
  and inl : Unit* → Unit* ⊔ Gen is the left injective inclusion of the coproduct. Thus 

      tt* ↦ inl(tt*) ∈ {e} ⊔ Gen

  Mathematically reference := e ∈ {e} ⊔ Gen, the distinguished reference element.
-}
reference : ∀ {ℓ} {Gen : Type ℓ} → GeneratorInput Gen
reference = inl tt*



{-
  So far we have GeneratorInput(Gen) = {e} ⊔ Gen, where {e} is the reference 
  constructd above by taking the singleton type Unit* included into the coproduct. 

  Now for any true g ∈ Gen, we give the image in coproduct under GeneratorInput as the 
  dierct inclusion of the right summand Gen into the coproduct {e} ⊔ Gen. That is 

    generator = inr : Gen → {e} ⊔ Gen
-}
generator : ∀ {ℓ} {Gen : Type ℓ} → Gen → GeneratorInput Gen
generator = inr



{-
  Now we define the generator space of Gen as the suspension of the generator input space, i.e.

    GeneratorSpace(Gen) := Susp(GeneratorInput(Gen))
                        = Susp({e} ⊔ Gen)

  where the suspension is defined in Cubical.HITs.Susp.Base.agda. One can check the def. of 
  suspension, for any Gen : Type ℓ, the suspension gives us two points 

    north : Susp({e} ⊔ Gen)
    south : Susp({e} ⊔ Gen)

  and for any a ∈ {e} ⊔ Gen, we have a meridian path
  
    merid : (a : ({e} ⊔ Gen))  : north ≡ south
-}
GeneratorSpace : ∀ {ℓ} → Type ℓ → Type ℓ
GeneratorSpace Gen = Susp (GeneratorInput Gen)



{-
  Motived by the loop is contructed as the map Rel × S^1 → S({e} ⊔ Gen) in the paper, 
  we define the generator loop as the north-based loop

    ℓ_g = mer(g) · mer(e)⁻¹ : north ≡ north

  We input reference = inl(tt*) to merid obtian 

    merid(reference) : north ≡ south
  
  in one sentence as tt* ↦ inl(tt*) ↦ merid(inl(tt*)) = merid(reference) = m_e : north ≡ south
-}
referenceMeridian : ∀ {ℓ} {Gen : Type ℓ} →
  north {A = GeneratorInput Gen} ≡ south
referenceMeridian = merid reference


{-
  Same as above, for any g ∈ Gen, we define the generator meridian as the path

    merid(g) : north ≡ south

  where g is included in the coproduct {e} ⊔ Gen via the right injective inclusion, 
  in one sentence as g ↦ inr (g) ↦ merid(inr(g)) = m_g : north ≡ south
-}
generatorMeridian : ∀ {ℓ} {Gen : Type ℓ} (g : Gen) → 
  north {A = GeneratorInput Gen} ≡ south
generatorMeridian g = merid (generator g)



{-
  Recall our generatorMeridian(g) : north ≡ south, we define the generator loop based 
  on the meridian of g simply by composing with the inverse of the reference meridian, i.e.

    ℓ_g = mer(g) · mer(e)⁻¹ : north ≡ north

  where mer(e)⁻¹ is the inverse of the reference meridian, i.e. mer(e)⁻¹ : south ≡ north
-}
generatorLoop : ∀ {ℓ} {Gen : Type ℓ} (g : Gen) →
  north {A = GeneratorInput Gen} ≡ north
generatorLoop g = generatorMeridian g ∙ sym referenceMeridian

{-
  One should note that lg is a term that 
    lg : Ω(X_Gen, north) 
  which return a path in the loop space of the suspension of the generator input space, 
  not a element in the fundamental group as [lg] ∈ π1 (X_Gen, north) 
-}


-- Stage 2 

{-
Signed (Gen) = Gen ⊔ Gen
-}
data Signed {ℓ : Level} (Gen : Type ℓ) : Type ℓ where
  pos : Gen → Signed Gen
  neg : Gen → Signed Gen  



{-
LetterLoop : Signed(Gen) → ΩX

LetterLoop(pos(g)) = ℓ_g : north ≡ north
LetterLoop(neg(g)) = ℓ_g⁻¹ : north ≡ north
-}

letterLoop : ∀ {ℓ} {Gen : Type ℓ} → 
  Signed Gen → 
  north {A = GeneratorInput Gen} ≡ north

letterLoop (pos g) = generatorLoop g
letterLoop (neg g) = sym (generatorLoop g)



{-
LetterLoop : Signed(Gen) → ΩX where X = Susp({e} ⊔ Gen) and ΩX = north ≡ north

Our next goal is wordLoop : Word(Gen) → ΩX
i.e. ab^-1 a → [pos(a), neg(b), pos(a)] ↦ ℓ_a · ℓ_b⁻¹ · ℓ_a : north ≡ north
-}

open import Cubical.Data.List


Word : ∀ {ℓ} → Type ℓ → Type ℓ 
Word Gen = List (Signed Gen)


wordLoop : ∀ {ℓ} {Gen : Type ℓ} →
  Word Gen →
  north {A = GeneratorInput Gen} ≡ north

wordLoop [] = refl
wordLoop (s ∷ w) = letterLoop s ∙ wordLoop w




-- Stage 3 


{-
Presentation(Gen, Rel) = (Rel → Word(Gen))^2
-} 

record Presentation {ℓ ℓ' :  Level} 
                    (Gen : Type ℓ)
                    (Rel : Type ℓ') : Type (ℓ-max ℓ ℓ') where 
  field 
    p₀ : Rel → Word Gen
    p₁ : Rel → Word Gen 


{-
For fixed P : Presentation(Gen, Rel), take p₀, p₁ : Rel → Word(Gen) 
with the definition wordLoop : Word(Gen) → ΩX, X = Susp({e} ⊔ Gen),
we have 

    Lᵢ := wordLoop ∘ pᵢ : Rel → ΩX, i = 0, 1
-}


relationLoop₀ :
  ∀ {ℓ ℓ'} {Gen : Type ℓ} {Rel : Type ℓ'} →
  Presentation Gen Rel →
  Rel →
  north {A = GeneratorInput Gen} ≡ north

relationLoop₀ P r =
  wordLoop (Presentation.p₀ P r)


{-
  The second word of a relation gives the other north-based loop

      L₁(r) = wordLoop (p₁(r)).

  The fields p₀ and p₁ deliberately contain syntactic signed words.  They are
  not arbitrary elements of the set-truncated FreeGroup HIT: a word can be
  evaluated as an actual loop without assuming that the raw loop space is a
  set.
-}
relationLoop₁ :
  ∀ {ℓ ℓ'} {Gen : Type ℓ} {Rel : Type ℓ'} →
  Presentation Gen Rel →
  Rel →
  north {A = GeneratorInput Gen} ≡ north

relationLoop₁ P r =
  wordLoop (Presentation.p₁ P r)


{-
  The loop which labels the circle indexed by r is the difference of the two
  word loops:

      L(r) = L₀(r) · L₁(r)⁻¹ : north ≡ north.
-}
relationLoop :
  ∀ {ℓ ℓ'} {Gen : Type ℓ} {Rel : Type ℓ'} →
  Presentation Gen Rel →
  Rel →
  north {A = GeneratorInput Gen} ≡ north

relationLoop P r =
  relationLoop₀ P r ∙ sym (relationLoop₁ P r)


-- Stage 4

{-
  S¹ is the HIT with constructors base : S¹ and loop : base ≡ base.  Eliminating
  it fibrewise over Rel sends every base point to north and its generating loop
  to L(r).  Hence this is the required attaching map

      Rel × S¹ → Susp (Unit* ⊎ Gen).
-}
attachingMap :
  ∀ {ℓ ℓ'} {Gen : Type ℓ} {Rel : Type ℓ'} →
  Presentation Gen Rel →
  Rel × S¹ → GeneratorSpace Gen

attachingMap P (r , base) = north
attachingMap P (r , loop i) = relationLoop P r i


-- Its value at the base point of the r-th circle is north.
attachingMap-base :
  ∀ {ℓ ℓ'} {Gen : Type ℓ} {Rel : Type ℓ'}
  (P : Presentation Gen Rel) (r : Rel) →
  attachingMap P (r , base) ≡ north {A = GeneratorInput Gen}

attachingMap-base P r = refl


{-
  This computation rule records the action of attachingMap on the generating
  circle loop.  It is definitionally relationLoop P r.
-}
attachingMap-loop :
  ∀ {ℓ ℓ'} {Gen : Type ℓ} {Rel : Type ℓ'}
  (P : Presentation Gen Rel) (r : Rel) →
  cong (λ z → attachingMap P (r , z)) loop ≡ relationLoop P r

attachingMap-loop P r = refl


-- The other leg of the span forgets the circle coordinate.
relationProjection :
  ∀ {ℓ} {Rel : Type ℓ} →
  Rel × S¹ → Rel

relationProjection = fst


{-
  Attach one 2-cell for each relation by the pushout of the span

      Rel × S¹ --attachingMap--> GeneratorSpace Gen
      Rel × S¹ --projection----> Rel.
-}
PresentationPushout :
  ∀ {ℓ ℓ'} {Gen : Type ℓ} {Rel : Type ℓ'} →
  Presentation Gen Rel →
  Type (ℓ-max ℓ ℓ')

PresentationPushout P =
  Pushout (attachingMap P) relationProjection


-- Stage 5

{-
  Cubical's ∥ A ∥ n is n-truncated in its h-level indexing: n = 1 is a
  proposition, n = 2 is a set, and n = 3 is a groupoid (a 1-type).  Thus the
  required 1-truncation of the presentation pushout is ∥ PresentationPushout P ∥ 3.
-}
BG_pres :
  ∀ {ℓ ℓ'} {Gen : Type ℓ} {Rel : Type ℓ'} →
  Presentation Gen Rel →
  Type (ℓ-max ℓ ℓ')

BG_pres P = ∥ PresentationPushout P ∥ 3


-- The north pole gives the canonical point before truncation.
presentationBasepoint :
  ∀ {ℓ ℓ'} {Gen : Type ℓ} {Rel : Type ℓ'}
  (P : Presentation Gen Rel) →
  PresentationPushout P

presentationBasepoint {Gen = Gen} P =
  inl (north {A = GeneratorInput Gen})


-- Its image under the truncation constructor is the canonical base point of BG_pres.
BG-basepoint :
  ∀ {ℓ ℓ'} {Gen : Type ℓ} {Rel : Type ℓ'}
  (P : Presentation Gen Rel) →
  BG_pres P

BG-basepoint P = ∣ presentationBasepoint P ∣ₕ
