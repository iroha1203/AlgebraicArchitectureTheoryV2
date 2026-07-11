import Formal.AG.SingularityMonodromyStack.SingularityTheorems
import Formal.AG.Derived.Transversality

noncomputable section

namespace AAT.AG
namespace SingularityMonodromyStack

universe u v w x y z

/--
VI.定義6.3: selected Kuranishi data at a chosen local base point.

This records the formal deformation germ, selected obstruction space, and
Kuranishi map. It is not a general construction of Kuranishi theory.
-/
structure KuranishiData {U : AtomCarrier.{u}} {A : ArchitectureObject U}
    {S : Site.AATSite A} {P : StratumReadingParameter S}
    {k : Type v} [CommRing k]
    {X : ArchitectureStratum.{u, v, w, x, y} P k}
    {L : CotangentData.{u, v, w, x, y, z} X}
    {T : TangentData.{u, v, w, x, y, z} X L}
    (D : DeformationObstructionTheory.{u, v, w, x, y, z} T) where
  LocalBase : Type z
  selectedPoint : LocalBase
  Tan : Type z
  Obs : Type z
  Defhat : Type z
  zeroObs : Obs
  kappa : Defhat -> Obs
  lawfulDeformationGerm : Defhat -> Prop
  tangentSpaceReadsDefhat : Prop
  obstructionSpaceReadsH1 : Prop
  controlledByCotangentComplex : Prop
  effectiveAtPoint : Prop

/--
VI.定理候補6.4: Kuranishi local model statement.

The statement is data: lawful deformation germs are the zero locus of `kappa`.
the current implementation does not require a proof of a general Kuranishi local model theorem.
-/
structure KuranishiLocalModelStatement {U : AtomCarrier.{u}} {A : ArchitectureObject U}
    {S : Site.AATSite A} {P : StratumReadingParameter S}
    {k : Type v} [CommRing k]
    {X : ArchitectureStratum.{u, v, w, x, y} P k}
    {L : CotangentData.{u, v, w, x, y, z} X}
    {T : TangentData.{u, v, w, x, y, z} X L}
    {D : DeformationObstructionTheory.{u, v, w, x, y, z} T}
    (K : KuranishiData.{u, v, w, x, y, z} D) : Prop where
  lawful_eq_zeroLocus :
    ∀ v : K.Defhat, K.lawfulDeformationGerm v ↔ K.kappa v = K.zeroObs

namespace KuranishiLocalModelStatement

variable {U : AtomCarrier.{u}} {A : ArchitectureObject U}
variable {S : Site.AATSite A} {P : StratumReadingParameter S}
variable {k : Type v} [CommRing k]
variable {X : ArchitectureStratum.{u, v, w, x, y} P k}
variable {L : CotangentData.{u, v, w, x, y, z} X}
variable {T : TangentData.{u, v, w, x, y, z} X L}
variable {D : DeformationObstructionTheory.{u, v, w, x, y, z} T}
variable {K : KuranishiData.{u, v, w, x, y, z} D}

/--
VI.定理候補6.4 statement consequence: a nonzero Kuranishi value is not a
selected lawful deformation germ.
-/
theorem nonzero_not_lawful_lift
    (M : KuranishiLocalModelStatement.{u, v, w, x, y, z} K)
    {v0 : K.Defhat} (hne : K.kappa v0 ≠ K.zeroObs) :
    ¬ K.lawfulDeformationGerm v0 := by
  intro hlawful
  exact hne ((M.lawful_eq_zeroLocus v0).1 hlawful)

end KuranishiLocalModelStatement

/--
VI.定義7.1: God object reading.

A God object is a selected singular stratum together with selected derived
non-transversality of multiple law loci. It is not defined by size metrics.
-/
structure GodObject {U : AtomCarrier.{u}} {A : ArchitectureObject U}
    {S : Site.AATSite A} {P : StratumReadingParameter S}
    {k : Type v} [CommRing k]
    {X : ArchitectureStratum.{u, v, w, x, y} P k}
    {L : CotangentData.{u, v, w, x, y, z} X}
    {T : TangentData.{u, v, w, x, y, z} X L}
    (D : DeformationObstructionTheory.{u, v, w, x, y, z} T)
    (LawCoordinateAlgebra : Type z) [CommRing LawCoordinateAlgebra]
    {I_U I_V : Ideal LawCoordinateAlgebra}
    (P_law : Derived.Intersection.LawConflictPackage.{u, z}
      LawCoordinateAlgebra I_U I_V) where
  singular : USingular D
  multipleLawLociNonTransverse :
    Derived.Transversality.DerivedNonTransverse LawCoordinateAlgebra P_law

namespace GodObject

variable {U : AtomCarrier.{u}} {A : ArchitectureObject U}
variable {S : Site.AATSite A} {P : StratumReadingParameter S}
variable {k : Type v} [CommRing k]
variable {X : ArchitectureStratum.{u, v, w, x, y} P k}
variable {L : CotangentData.{u, v, w, x, y, z} X}
variable {T : TangentData.{u, v, w, x, y, z} X L}
variable {D : DeformationObstructionTheory.{u, v, w, x, y, z} T}
variable {LawCoordinateAlgebra : Type z} [CommRing LawCoordinateAlgebra]
variable {I_U I_V : Ideal LawCoordinateAlgebra}
variable {P_law : Derived.Intersection.LawConflictPackage.{u, z}
  LawCoordinateAlgebra I_U I_V}

/-- VI.定義7.1: expose the singularity component of a God object reading. -/
theorem singular_holds
    (G : GodObject.{u, v, w, x, y, z} D LawCoordinateAlgebra P_law) :
    USingular D :=
  G.singular

/-- VI.定義7.1: expose the selected non-transversality component. -/
theorem multipleLawLociNonTransverse_holds
    (G : GodObject.{u, v, w, x, y, z} D LawCoordinateAlgebra P_law) :
    Derived.Transversality.DerivedNonTransverse LawCoordinateAlgebra P_law :=
  G.multipleLawLociNonTransverse

end GodObject

end SingularityMonodromyStack
end AAT.AG
