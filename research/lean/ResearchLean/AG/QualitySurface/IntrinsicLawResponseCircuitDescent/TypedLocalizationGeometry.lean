import Formal.Util.AssertStandardAxioms
import Mathlib.AlgebraicGeometry.AffineScheme
import Mathlib.RingTheory.Localization.Away.Basic

/-!
# Typed affine-localization geometry

This file constructs the coordinate rings of a finite family of principal
affine charts and their pairwise overlaps from a single ambient algebra.  The
two chart-to-overlap maps are the canonical maps supplied by localization.
-/

namespace ResearchLean.AG.QualitySurface
namespace IntrinsicLawResponseCircuitDescent

universe uₖ uA uChart

/--
A finite family of principal affine charts selected inside one ambient
commutative algebra.  All coordinate rings and restriction maps are derived
from `denominator` rather than stored as additional data.
-/
structure TypedLocalizationGeometry
    (k : Type uₖ) (A₀ : Type uA) (Chart : Type uChart)
    [CommRing k] [CommRing A₀] [Algebra k A₀] [Fintype Chart] where
  /-- The ambient element defining each principal affine chart. -/
  denominator : Chart → A₀

namespace TypedLocalizationGeometry

variable {k : Type uₖ} {A₀ : Type uA} {Chart : Type uChart}
variable [CommRing k] [CommRing A₀] [Algebra k A₀] [Fintype Chart]

/-- The coordinate ring of a selected principal affine chart. -/
abbrev chartRing
    (G : TypedLocalizationGeometry k A₀ Chart) (i : Chart) :=
  Localization.Away (G.denominator i)

/-- The coordinate ring of a pairwise principal affine overlap. -/
abbrev overlapRing
    (G : TypedLocalizationGeometry k A₀ Chart) (i j : Chart) :=
  Localization.Away (G.denominator i * G.denominator j)

/-- The affine scheme carried by a selected chart coordinate ring. -/
noncomputable abbrev chartSpec
    (G : TypedLocalizationGeometry k A₀ Chart) (i : Chart) :
    AlgebraicGeometry.Scheme :=
  AlgebraicGeometry.Spec (.of (G.chartRing i))

/-- The affine scheme carried by a pairwise overlap coordinate ring. -/
noncomputable abbrev overlapSpec
    (G : TypedLocalizationGeometry k A₀ Chart) (i j : Chart) :
    AlgebraicGeometry.Scheme :=
  AlgebraicGeometry.Spec (.of (G.overlapRing i j))

/-- Each chart coordinate ring has its canonical principal-localization provenance. -/
theorem chartRing_isLocalization
    (G : TypedLocalizationGeometry k A₀ Chart) (i : Chart) :
    IsLocalization (Submonoid.powers (G.denominator i)) (G.chartRing i) :=
  inferInstance

/-- Each overlap coordinate ring has its canonical principal-localization provenance. -/
theorem overlapRing_isLocalization
    (G : TypedLocalizationGeometry k A₀ Chart) (i j : Chart) :
    IsLocalization
      (Submonoid.powers (G.denominator i * G.denominator j))
      (G.overlapRing i j) :=
  inferInstance

/-- The canonical ambient-algebra map from the left chart to its overlap. -/
noncomputable def leftChartToOverlap
    (G : TypedLocalizationGeometry k A₀ Chart) (i j : Chart) :
    G.chartRing i →ₐ[A₀] G.overlapRing i j where
  toRingHom :=
    IsLocalization.Away.awayToAwayRight
      (S := G.chartRing i) (P := G.overlapRing i j)
      (G.denominator i) (G.denominator j)
  commutes' a :=
    IsLocalization.Away.awayToAwayRight_eq
      (S := G.chartRing i) (P := G.overlapRing i j)
      (G.denominator i) (G.denominator j) a

/-- The canonical ambient-algebra map from the right chart to its overlap. -/
noncomputable def rightChartToOverlap
    (G : TypedLocalizationGeometry k A₀ Chart) (i j : Chart) :
    G.chartRing j →ₐ[A₀] G.overlapRing i j where
  toRingHom :=
    IsLocalization.Away.awayToAwayLeft
      (S := G.chartRing j) (P := G.overlapRing i j)
      (G.denominator j) (G.denominator i)
  commutes' a :=
    IsLocalization.Away.awayToAwayLeft_eq
      (S := G.chartRing j) (P := G.overlapRing i j)
      (G.denominator j) (G.denominator i) a

/-- The left restriction agrees with the ambient algebra map. -/
@[simp]
theorem leftChartToOverlap_algebraMap
    (G : TypedLocalizationGeometry k A₀ Chart) (i j : Chart) (a : A₀) :
    G.leftChartToOverlap i j (algebraMap A₀ (G.chartRing i) a) =
      algebraMap A₀ (G.overlapRing i j) a :=
  IsLocalization.Away.awayToAwayRight_eq
    (S := G.chartRing i) (P := G.overlapRing i j)
    (G.denominator i) (G.denominator j) a

/-- The right restriction agrees with the ambient algebra map. -/
@[simp]
theorem rightChartToOverlap_algebraMap
    (G : TypedLocalizationGeometry k A₀ Chart) (i j : Chart) (a : A₀) :
    G.rightChartToOverlap i j (algebraMap A₀ (G.chartRing j) a) =
      algebraMap A₀ (G.overlapRing i j) a :=
  IsLocalization.Away.awayToAwayLeft_eq
    (S := G.chartRing j) (P := G.overlapRing i j)
    (G.denominator j) (G.denominator i) a

end TypedLocalizationGeometry
end IntrinsicLawResponseCircuitDescent
end ResearchLean.AG.QualitySurface

#assert_standard_axioms_only
  ResearchLean.AG.QualitySurface.IntrinsicLawResponseCircuitDescent.TypedLocalizationGeometry
