import Formal.AG.LawAlgebra.Nullstellensatz

noncomputable section

namespace AAT.AG
namespace LawAlgebra

universe u v w

namespace AffineChart

set_option linter.unusedSectionVars false

variable (k : Type u) [CommRing k]

/--
III.定義8.1: decoration attached to the ordinary affine spectrum.

The underlying space remains `PrimeSpectrum A`; AAT-specific readings are
recorded in the decoration fields instead of replacing the spectrum theory.
-/
structure SpecAAT (A : Type v) [CommRing A] [Algebra k A] where
  Decoration : Type w
  decoration : Decoration
  obstructionIdeal : Ideal A

namespace SpecAAT

/-- III.定義8.1: the underlying ordinary affine spectrum. -/
abbrev pointSpace {A : Type v} [CommRing A] [Algebra k A] (_X : SpecAAT k A) :=
  PrimeSpectrum A

/-- III.定義8.5: local lawful chart `V(I_Ob^U(W)) ⊆ Spec_AAT`. -/
def localLawfulChart {A : Type v} [CommRing A] [Algebra k A] (X : SpecAAT k A) :
    Set (PrimeSpectrum A) :=
  PrimeSpectrum.zeroLocus X.obstructionIdeal

end SpecAAT

/-- III.定義8.2: an affine AAT chart with its chosen coordinate algebra. -/
structure AffineAATChart where
  AlgebraCarrier : Type v
  commRing : CommRing AlgebraCarrier
  algebra : Algebra k AlgebraCarrier
  spec : SpecAAT k AlgebraCarrier

attribute [instance] AffineAATChart.commRing AffineAATChart.algebra

namespace AffineAATChart

/-- III.定義8.2: `R`-valued local configuration functor `h_W^U(R)`. -/
def hWU (C : AffineAATChart k) (R : Type w) [CommRing R] [Algebra k R] :=
  C.AlgebraCarrier →ₐ[k] R

/--
III.定理8.3: raw affine chart representability.

With the chosen raw coordinate algebra exposed as `C.AlgebraCarrier`, the
configuration functor is represented by that algebra by definition.
-/
def rawAffineChartRepresentability (C : AffineAATChart k)
    (R : Type w) [CommRing R] [Algebra k R] :
    hWU k C R ≃ (C.AlgebraCarrier →ₐ[k] R) :=
  Equiv.refl _

/-- III.仮定8.4: selected presentation for a sheafified affine chart. -/
structure SheafifiedChartPresentation (raw sheafified : AffineAATChart k) where
  comparison : sheafified.AlgebraCarrier ≃ₐ[k] raw.AlgebraCarrier
  preservesDecoration : Prop
  preservesObstructionIdeal : Prop

/--
III.定理8.3 / 仮定8.4: representability for the sheafified chart under the
selected presentation package.
-/
def sheafifiedChartRepresentability {raw sheafified : AffineAATChart k}
    (_P : SheafifiedChartPresentation k raw sheafified)
    (R : Type w) [CommRing R] [Algebra k R] :
    hWU k sheafified R ≃ (sheafified.AlgebraCarrier →ₐ[k] R) :=
  Equiv.refl _

end AffineAATChart

end AffineChart

end LawAlgebra
end AAT.AG
