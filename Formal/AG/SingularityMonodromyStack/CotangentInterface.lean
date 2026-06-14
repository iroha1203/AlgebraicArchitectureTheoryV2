import Formal.AG.SingularityMonodromyStack.Stratum

noncomputable section

namespace AAT.AG
namespace SingularityMonodromyStack

universe u v w x y z

/--
VI.定義3.1: selected cotangent complex data for a stratum over its reading
parameter.

This is an interface: it records the chosen cotangent complex object and
pullback operation. It does not construct a general Illusie cotangent complex.
-/
structure CotangentData {U : AtomCarrier.{u}} {A : ArchitectureObject U}
    {S : Site.AATSite A} {P : StratumReadingParameter S}
    {k : Type v} [CommRing k]
    (X : ArchitectureStratum.{u, v, w, x, y} P k) where
  Base : Type z
  CotangentComplex : Type z
  baseMap : X.Point -> Base
  PullbackBase : Type z
  pullbackComplex : PullbackBase -> CotangentComplex

namespace CotangentData

variable {U : AtomCarrier.{u}} {A : ArchitectureObject U}
variable {S : Site.AATSite A} {P : StratumReadingParameter S}
variable {k : Type v} [CommRing k]
variable {X : ArchitectureStratum.{u, v, w, x, y} P k}

/-- VI.定義3.1: expose the selected base map of the stratum. -/
theorem baseMap_eq (L : CotangentData.{u, v, w, x, y, z} X) :
    L.baseMap = L.baseMap :=
  rfl

end CotangentData

/--
VI.定義3.2: selected tangent-complex data.

`RHom` and Ext/cohomology calculations are represented by explicit carrier
fields and certificates. General `RHom` construction remains outside this PRD
step.
-/
structure TangentData {U : AtomCarrier.{u}} {A : ArchitectureObject U}
    {S : Site.AATSite A} {P : StratumReadingParameter S}
    {k : Type v} [CommRing k]
    (X : ArchitectureStratum.{u, v, w, x, y} P k)
    (L : CotangentData.{u, v, w, x, y, z} X) where
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
variable {X : ArchitectureStratum.{u, v, w, x, y} P k}
variable {L : CotangentData.{u, v, w, x, y, z} X}

/-- VI.定義3.2: expose the selected obstruction-zero element. -/
theorem zeroObstruction_eq (T : TangentData.{u, v, w, x, y, z} X L) :
    T.zeroObstruction = T.zeroObstruction :=
  rfl

end TangentData

end SingularityMonodromyStack
end AAT.AG
