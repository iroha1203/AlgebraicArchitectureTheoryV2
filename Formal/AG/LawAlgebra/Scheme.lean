import Formal.AG.LawAlgebra.AffineChart
import Formal.AG.LawAlgebra.StructureSheaf
import Formal.AG.Site.SheafCategory
import Mathlib.AlgebraicGeometry.Spec
import Mathlib.Geometry.RingedSpace.LocallyRingedSpace

noncomputable section

namespace AAT.AG
namespace LawAlgebra

universe u v w x y

namespace Scheme

set_option linter.unusedSectionVars false

open AlgebraicGeometry
open CategoryTheory
open Opposite

variable {U : AtomCarrier.{u}} {A : ArchitectureObject U}
variable (S : Site.AATSite A) (k : Type v) [CommRing k]

/--
III.R4: the Mathlib locally ringed space read by an affine AAT chart.

This is the ordinary `Spec` of the selected chart algebra. The AAT decoration
and obstruction ideal stay in `SpecAAT`; the Mathlib-facing affine surface is
the locally ringed space attached to the carrier ring.
-/
abbrev affineChartMathlibSpecLocallyRingedSpace
    (C : AffineChart.AffineAATChart.{v, w, x} k) :
    LocallyRingedSpace.{w} :=
  AlgebraicGeometry.Spec.toLocallyRingedSpace.obj
    (op (CommRingCat.of C.AlgebraCarrier))

/-- III.R4: the affine chart point space is the ordinary prime spectrum. -/
theorem affineChart_pointSpace_eq_primeSpectrum
    (C : AffineChart.AffineAATChart.{v, w, x} k) :
    C.spec.pointSpace = PrimeSpectrum C.AlgebraCarrier :=
  rfl

/-- III.R4: the chart has a selected decoration witness. -/
theorem affineChart_decoration_nonempty
    (C : AffineChart.AffineAATChart.{v, w, x} k) :
    Nonempty C.spec.Decoration :=
  ⟨C.spec.decoration⟩

/--
III.定義9.1: ringed AAT topos package.

The AAT-facing sheaf category `AATSh(A,U,J)` and its selected law algebra
structure sheaf `O_X^U` are recorded together with the ordinary locally ringed
space that reads the same package on the Mathlib side.
-/
structure RingedAATTopos where
  aatSheafObject : Site.AATSh S
  structureSheaf : LawAlgebraSheafPackage S k
  locallyRingedSpace : LocallyRingedSpace.{y}

namespace RingedAATTopos

/-- III.定義9.1: the selected structure sheaf `O_X^U`. -/
abbrev OX (T : RingedAATTopos.{u, v, y} S k) : LawAlgebraSheaf S k :=
  T.structureSheaf.OX

/-- III.定義9.1: forget the AAT decoration to the selected locally ringed space. -/
def forgetfulLocallyRingedSpace (T : RingedAATTopos.{u, v, y} S k) :
    LocallyRingedSpace.{y} :=
  T.locallyRingedSpace

/-- III.定義9.1: the forgetful reading is the stored Mathlib locally ringed space. -/
theorem forgetfulLocallyRingedSpace_eq (T : RingedAATTopos.{u, v, y} S k) :
    T.forgetfulLocallyRingedSpace = T.locallyRingedSpace :=
  rfl

end RingedAATTopos

/--
III.定義9.2: compatibility of two affine AAT charts.

The seven conditions are kept as explicit predicates: open immersion, overlap
representability, restriction compatibility, obstruction-ideal compatibility,
decoration compatibility, cocycle compatibility, and locally ringed
compatibility.
-/
structure ChartCompatibility (C D : AffineChart.AffineAATChart.{v, w, x} k) where
  openImmersion : Prop
  overlapRepresentability : Prop
  restrictionCompatible : Prop
  obstructionIdealCompatible : Prop
  decorationCompatible : Prop
  cocycle : Prop
  locallyRingedCompatible : Prop

namespace ChartCompatibility

/-- III.定義9.2: expose the seven compatibility predicates as one condition. -/
def allConditions {C D : AffineChart.AffineAATChart.{v, w, x} k}
    (H : ChartCompatibility k C D) : Prop :=
  H.openImmersion ∧ H.overlapRepresentability ∧ H.restrictionCompatible ∧
    H.obstructionIdealCompatible ∧ H.decorationCompatible ∧ H.cocycle ∧
      H.locallyRingedCompatible

/--
III.R4: selected self-compatibility for a single affine AAT chart.

The legacy compatibility slots are no longer supplied as unrelated arbitrary
facts in this constructor: the self-chart case records the identity morphism
on the chart's ordinary Mathlib `Spec` locally ringed space, the prime-spectrum
point-space reading, the identity equivalence on selected hom surfaces, the
obstruction ideal, and the selected decoration. This is still a single-chart
identity witness, not a Mathlib open-immersion theorem or a general atlas
gluing theorem.
-/
def selfAffineSpec (C : AffineChart.AffineAATChart.{v, w, x} k) :
    ChartCompatibility k C C where
  openImmersion :=
    ∃ f : affineChartMathlibSpecLocallyRingedSpace k C ⟶
        affineChartMathlibSpecLocallyRingedSpace k C,
      f = 𝟙 _
  overlapRepresentability :=
    C.spec.pointSpace = PrimeSpectrum C.AlgebraCarrier
  restrictionCompatible :=
    ∀ (R : Type w) [CommRing R] [Algebra k R],
      Nonempty
        (AffineChart.AffineAATChart.hWU k C R ≃
          AffineChart.AffineAATChart.hWU k C R)
  obstructionIdealCompatible :=
    C.spec.obstructionIdeal = C.spec.obstructionIdeal
  decorationCompatible :=
    Nonempty C.spec.Decoration
  cocycle :=
    True
  locallyRingedCompatible :=
    affineChartMathlibSpecLocallyRingedSpace k C =
      affineChartMathlibSpecLocallyRingedSpace k C

/-- III.R4: the affine self-compatibility constructor supplies all legacy slots. -/
theorem selfAffineSpec_allConditions
    (C : AffineChart.AffineAATChart.{v, w, x} k) :
    (selfAffineSpec k C).allConditions := by
  refine ⟨⟨𝟙 _, rfl⟩, ?_, ?_, rfl, affineChart_decoration_nonempty k C, trivial, rfl⟩
  · exact affineChart_pointSpace_eq_primeSpectrum k C
  · intro R _ _
    exact ⟨Equiv.refl _⟩

end ChartCompatibility

/--
III.定義9.3: architecture scheme.

An architecture scheme is a decorated locally ringed geometry with an affine
AAT chart atlas and pairwise chart compatibility. The `underlying` field is
the Mathlib locally ringed space supplied by the forgetful reading.
-/
structure ArchitectureScheme where
  ChartIndex : Type y
  chart : ChartIndex → AffineChart.AffineAATChart.{v, w, x} k
  compatibility : ∀ i j : ChartIndex, ChartCompatibility k (chart i) (chart j)
  ringedTopos : RingedAATTopos.{u, v, y} S k
  underlying : LocallyRingedSpace.{y}
  forgetful_agrees : ringedTopos.forgetfulLocallyRingedSpace = underlying

namespace ArchitectureScheme

/-- III.定義9.3: forget an architecture scheme to its locally ringed space. -/
def forgetfulLocallyRingedSpace (X : ArchitectureScheme.{u, v, w, x, y} S k) :
    LocallyRingedSpace.{y} :=
  X.underlying

/--
III.定義9.3: the AAT forgetful reading gives a Mathlib `LocallyRingedSpace`.
-/
theorem forgetful_reading_locallyRingedSpace
    (X : ArchitectureScheme.{u, v, w, x, y} S k) :
    X.forgetfulLocallyRingedSpace = X.underlying :=
  rfl

/--
III.定義9.3: the topos-side and scheme-side locally ringed readings agree.
-/
theorem ringedTopos_forgetful_eq_underlying
    (X : ArchitectureScheme.{u, v, w, x, y} S k) :
    X.ringedTopos.forgetfulLocallyRingedSpace = X.underlying :=
  X.forgetful_agrees

/--
III.R4: build an architecture scheme from a single affine AAT chart whose
selected ringed topos reads the same Mathlib affine `Spec` locally ringed
space.

This realizes the PRD-R III-4 affine alternative additively: the atlas has one
chart, its compatibility is the selected affine self-chart constructor, and the
underlying locally ringed space is the chart's Mathlib `Spec` reading.
-/
def singleAffineSpec
    (T : RingedAATTopos.{u, v, w} S k)
    (C : AffineChart.AffineAATChart.{v, w, x} k)
    (hT :
      T.forgetfulLocallyRingedSpace =
        affineChartMathlibSpecLocallyRingedSpace k C) :
    ArchitectureScheme.{u, v, w, x, w} S k where
  ChartIndex := PUnit
  chart _ := C
  compatibility _ _ := ChartCompatibility.selfAffineSpec k C
  ringedTopos := T
  underlying := affineChartMathlibSpecLocallyRingedSpace k C
  forgetful_agrees := hT

@[simp]
theorem singleAffineSpec_underlying
    (T : RingedAATTopos.{u, v, w} S k)
    (C : AffineChart.AffineAATChart.{v, w, x} k)
    (hT :
      T.forgetfulLocallyRingedSpace =
        affineChartMathlibSpecLocallyRingedSpace k C) :
    (singleAffineSpec S k T C hT).underlying =
      affineChartMathlibSpecLocallyRingedSpace k C :=
  rfl

@[simp]
theorem singleAffineSpec_chart
    (T : RingedAATTopos.{u, v, w} S k)
    (C : AffineChart.AffineAATChart.{v, w, x} k)
    (hT :
      T.forgetfulLocallyRingedSpace =
        affineChartMathlibSpecLocallyRingedSpace k C)
    (i : (singleAffineSpec S k T C hT).ChartIndex) :
    (singleAffineSpec S k T C hT).chart i = C := by
  cases i
  rfl

/-- III.R4: the single affine scheme supplies the selected self-chart compatibility. -/
theorem singleAffineSpec_compatibility_allConditions
    (T : RingedAATTopos.{u, v, w} S k)
    (C : AffineChart.AffineAATChart.{v, w, x} k)
    (hT :
      T.forgetfulLocallyRingedSpace =
        affineChartMathlibSpecLocallyRingedSpace k C)
    (i j : (singleAffineSpec S k T C hT).ChartIndex) :
    ((singleAffineSpec S k T C hT).compatibility i j).allConditions := by
  cases i
  cases j
  exact ChartCompatibility.selfAffineSpec_allConditions k C

/--
III.R4: the single affine constructor ties the topos-side locally ringed
reading to the chart's Mathlib affine `Spec`.
-/
theorem singleAffineSpec_ringedTopos_forgetful_eq_chartSpec
    (T : RingedAATTopos.{u, v, w} S k)
    (C : AffineChart.AffineAATChart.{v, w, x} k)
    (hT :
      T.forgetfulLocallyRingedSpace =
        affineChartMathlibSpecLocallyRingedSpace k C) :
    (singleAffineSpec S k T C hT).ringedTopos.forgetfulLocallyRingedSpace =
      affineChartMathlibSpecLocallyRingedSpace k C :=
  hT

end ArchitectureScheme

/--
III.定義10.3: scheme gluing data for affine AAT charts.

This is only the selected gluing package and the bridge predicate to the
ordinary Mathlib gluing side. It does not construct a general decorated
gluing theory.
-/
structure SchemeGluingData where
  ChartIndex : Type y
  chart : ChartIndex → AffineChart.AffineAATChart.{v, w, x} k
  overlap : ChartIndex → ChartIndex → Type y
  compatibility : ∀ i j : ChartIndex, ChartCompatibility k (chart i) (chart j)
  cocycleOnTripleOverlaps : Prop
  underlyingMathlibGluingBridge : Prop

/--
III.定義10.3: extra assumptions needed to return a glued object to a single
affine AAT chart.
-/
structure AffineReturnConditions (G : SchemeGluingData.{v, w, x, y} k) where
  context : S.category
  lawAlgebra : LawAlgebraSheafPackage S k
  gluedLocallyRingedSpace : LocallyRingedSpace.{y}
  gluedGlobalSections : Type y
  affineChart : AffineChart.AffineAATChart.{v, w, x} k
  canonicalComparison :
    affineChart.AlgebraCarrier ≃+* (lawAlgebra.OX.val.obj (op context)).right
  sectionComparison : (lawAlgebra.OX.val.obj (op context)).right ≃ gluedGlobalSections
  gluedAffine : Prop
  sectionIdentification : Prop
  decorationIdentification : Prop

namespace AffineReturnConditions

/--
III.定義10.3: expose the four affine-return assumptions as one condition.
-/
def affineReturnAssumptions
    {G : SchemeGluingData.{v, w, x, y} k} (H : AffineReturnConditions S k G) :
    Prop :=
  H.gluedAffine ∧ H.sectionIdentification ∧ H.decorationIdentification

end AffineReturnConditions

end Scheme

end LawAlgebra
end AAT.AG
