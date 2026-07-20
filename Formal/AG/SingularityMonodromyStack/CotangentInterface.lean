import Formal.AG.SingularityMonodromyStack.Stratum
import Formal.AG.Cohomology.ObstructionSheaf

noncomputable section

namespace AAT.AG
namespace SingularityMonodromyStack

universe u v y z

/--
VI.定義3.1: selected cotangent complex data for a stratum over its reading
parameter.

This is an interface: it records the chosen cotangent complex object and
pullback operation. It does not construct a general Illusie cotangent complex.
-/
structure CotangentData {U : AtomCarrier.{u}} {A : ArchitectureObject U}
    {S : Site.AATSite A} {P : StratumReadingParameter S}
    {k : Type v} [CommRing k]
    (X : ArchitectureStratum.{u, v, y} P k) where
  Base : Type z
  CotangentComplex : Type z
  baseMap : X.Point -> Base
  PullbackBase : Type z
  pullbackComplex : PullbackBase -> CotangentComplex

namespace CotangentData

variable {U : AtomCarrier.{u}} {A : ArchitectureObject U}
variable {S : Site.AATSite A} {P : StratumReadingParameter S}
variable {k : Type v} [CommRing k]
variable {X : ArchitectureStratum.{u, v, y} P k}

/-- VI.定義3.1: expose the selected base map of the stratum. -/
theorem baseMap_eq (L : CotangentData.{u, v, y, z} X) :
    L.baseMap = L.baseMap :=
  rfl

/--
VI.R2 / VI-4: instantiate the selected cotangent interface from the Part IV
conormal quotient `ConDef_U = I_U / I_U^2`.

This is not a general Illusie cotangent-complex construction.  It is the
bounded bridge that lets Part VI read the Part IV standard obstruction package
as its selected cotangent carrier.
-/
def ofConDef
    (F : LawAlgebra.ObstructionIdeal.SelectedLawWitnessIdealFamily.{u, v} k) :
    CotangentData.{u, v, y, v} X where
  Base := Cohomology.StandardObstruction.LawfulLocusAlgebra k F
  CotangentComplex := Cohomology.StandardObstruction.ConDef_U k F
  baseMap := fun _ => 0
  PullbackBase := Cohomology.StandardObstruction.Def_U k F
  pullbackComplex := Cohomology.StandardObstruction.toConDef k F

/-- VI.R2 / VI-4: the conormal bridge uses `ConDef_U` as cotangent carrier. -/
theorem ofConDef_cotangentComplex_eq
    (F : LawAlgebra.ObstructionIdeal.SelectedLawWitnessIdealFamily.{u, v} k) :
    (ofConDef (X := X) F).CotangentComplex =
      Cohomology.StandardObstruction.ConDef_U k F :=
  rfl

/-- VI.R2 / VI-4: pullback along the conormal bridge is the canonical map to `I/I^2`. -/
theorem ofConDef_pullbackComplex_eq
    (F : LawAlgebra.ObstructionIdeal.SelectedLawWitnessIdealFamily.{u, v} k) :
    (ofConDef (X := X) F).pullbackComplex =
      Cohomology.StandardObstruction.toConDef k F :=
  rfl

end CotangentData

/--
VI.定義3.2: selected tangent-complex data.

`RHom` and Ext/cohomology calculations are represented by explicit carrier
fields and certificates. General `RHom` construction remains outside this implementation scope
step.
-/
structure TangentData {U : AtomCarrier.{u}} {A : ArchitectureObject U}
    {S : Site.AATSite A} {P : StratumReadingParameter S}
    {k : Type v} [CommRing k]
    (X : ArchitectureStratum.{u, v, y} P k)
    (L : CotangentData.{u, v, y, z} X) where
  TangentComplex : Type z
  H0 : Type z
  H1 : Type z
  ObstructionTarget : Type z
  zeroObstruction : ObstructionTarget
  rhomInterface_certificate : Prop
  h0ComputesInfinitesimalAutomorphisms_certificate : Prop
  h1ComputesObstructionTarget_certificate : Prop

namespace TangentData

variable {U : AtomCarrier.{u}} {A : ArchitectureObject U}
variable {S : Site.AATSite A} {P : StratumReadingParameter S}
variable {k : Type v} [CommRing k]
variable {X : ArchitectureStratum.{u, v, y} P k}
variable {L : CotangentData.{u, v, y, z} X}

/-- VI.定義3.2: expose the selected obstruction-zero element. -/
theorem zeroObstruction_eq (T : TangentData.{u, v, y, z} X L) :
    T.zeroObstruction = T.zeroObstruction :=
  rfl

/--
VI.R2 / VI-4: tangent interface whose obstruction target is the Part IV
selected derived obstruction carrier `DerOb_U`.

The construction is intentionally selected and coefficient-level: it records
that Part VI's obstruction target is the transparent Part IV conormal
coefficient carrier, without asserting a general `RHom` or `Ext^1`
construction.
-/
def ofDerOb
    (F : LawAlgebra.ObstructionIdeal.SelectedLawWitnessIdealFamily.{u, v} k) :
    TangentData.{u, v, y, v} X (CotangentData.ofConDef (X := X) F) where
  TangentComplex := k
  H0 := k
  H1 := Cohomology.StandardObstruction.DerOb_U k F k
  ObstructionTarget := Cohomology.StandardObstruction.DerOb_U k F k
  zeroObstruction :=
    Cohomology.StandardObstruction.DerOb_U.ofConDefCoefficient
      (A := k) (F := F) (M := k) 0 0
  rhomInterface_certificate := True
  h0ComputesInfinitesimalAutomorphisms_certificate := True
  h1ComputesObstructionTarget_certificate := True

/-- VI.R2 / VI-4: the selected tangent obstruction target is `DerOb_U`. -/
theorem ofDerOb_obstructionTarget_eq
    (F : LawAlgebra.ObstructionIdeal.SelectedLawWitnessIdealFamily.{u, v} k) :
    (ofDerOb (X := X) F).ObstructionTarget =
      Cohomology.StandardObstruction.DerOb_U k F k :=
  rfl

@[simp]
theorem ofDerOb_zeroObstruction_conDefClass
    (F : LawAlgebra.ObstructionIdeal.SelectedLawWitnessIdealFamily.{u, v} k) :
    ((ofDerOb (X := X) F).zeroObstruction).conDefClass = 0 :=
  rfl

@[simp]
theorem ofDerOb_zeroObstruction_coefficient
    (F : LawAlgebra.ObstructionIdeal.SelectedLawWitnessIdealFamily.{u, v} k) :
    ((ofDerOb (X := X) F).zeroObstruction).coefficient = 0 :=
  rfl

end TangentData

end SingularityMonodromyStack
end AAT.AG
