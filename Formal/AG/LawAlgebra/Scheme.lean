import Formal.AG.LawAlgebra.AffineChart
import Formal.AG.LawAlgebra.StructureSheaf
import Formal.AG.Site.SheafCategory
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
