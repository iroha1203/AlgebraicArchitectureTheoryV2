import Formal.AG.SingularityMonodromyStack.SmoothSingular

noncomputable section

namespace AAT.AG
namespace SingularityMonodromyStack

universe u v w x y z

/--
VI.定理6.1 input package: a selected first-order deformation whose
obstruction class is nonzero in the chosen `H1` obstruction target.
-/
structure FirstOrderObstructionWitness {U : AtomCarrier.{u}} {A : ArchitectureObject U}
    {S : Site.AATSite A} {P : StratumReadingParameter S}
    {k : Type v} [CommRing k]
    {X : ArchitectureStratum.{u, v, w, x, y} P k}
    {L : CotangentData.{u, v, w, x, y, z} X}
    {T : TangentData.{u, v, w, x, y, z} X L}
    (D : DeformationObstructionTheory.{u, v, w, x, y, z} T) where
  eta : D.DeformationTest
  h1ComputesObstructionTarget : T.h1ComputesObstructionTarget_certificate
  nonzero_obstruction : D.ob eta ≠ T.zeroObstruction

namespace DeformationObstructionTheory

variable {U : AtomCarrier.{u}} {A : ArchitectureObject U}
variable {S : Site.AATSite A} {P : StratumReadingParameter S}
variable {k : Type v} [CommRing k]
variable {X : ArchitectureStratum.{u, v, w, x, y} P k}
variable {L : CotangentData.{u, v, w, x, y, z} X}
variable {T : TangentData.{u, v, w, x, y, z} X L}

/--
VI.定理6.1 Architecture Singularity Criterion.

Within the selected deformation-obstruction interface, a selected nonzero
first-order obstruction class is exactly the witness required by `USingular`.
-/
theorem architectureSingularityCriterion
    (D : DeformationObstructionTheory.{u, v, w, x, y, z} T)
    (W : FirstOrderObstructionWitness.{u, v, w, x, y, z} D) :
    USingular D :=
  ⟨W.eta, W.nonzero_obstruction⟩

end DeformationObstructionTheory

/--
VI.定理6.2 data: a selected square-zero lifting problem read through the
already selected deformation-obstruction interface.
-/
structure SquareZeroExtensionData {U : AtomCarrier.{u}} {A : ArchitectureObject U}
    {S : Site.AATSite A} {P : StratumReadingParameter S}
    {k : Type v} [CommRing k]
    {X : ArchitectureStratum.{u, v, w, x, y} P k}
    {L : CotangentData.{u, v, w, x, y, z} X}
    {T : TangentData.{u, v, w, x, y, z} X L}
    (D : DeformationObstructionTheory.{u, v, w, x, y, z} T) where
  TestObject : Type z
  DeformationModule : Type z
  SquareZeroExtension : Type z
  xi : D.DeformationTest
  pullbackCotangentComplex : Type z
  obstructionClass : T.ObstructionTarget
  obstructionClass_eq_ob : obstructionClass = D.ob xi
  Lift : Prop
  lift_eq_liftFill : Lift = D.LiftFill xi
  LiftTorsor : obstructionClass = T.zeroObstruction -> Type z
  AutomorphismSpace : obstructionClass = T.zeroObstruction -> Type z

namespace SquareZeroExtensionData

variable {U : AtomCarrier.{u}} {A : ArchitectureObject U}
variable {S : Site.AATSite A} {P : StratumReadingParameter S}
variable {k : Type v} [CommRing k]
variable {X : ArchitectureStratum.{u, v, w, x, y} P k}
variable {L : CotangentData.{u, v, w, x, y, z} X}
variable {T : TangentData.{u, v, w, x, y, z} X L}
variable {D : DeformationObstructionTheory.{u, v, w, x, y, z} T}

/--
VI.定理6.2 Square-Zero Lifting Obstruction.

If the selected obstruction class of the square-zero lifting problem is
nonzero, the selected lift predicate fails.
-/
theorem squareZeroLiftingObstruction
    (E : SquareZeroExtensionData.{u, v, w, x, y, z} D)
    (hne : E.obstructionClass ≠ T.zeroObstruction) :
    ¬ E.Lift := by
  have hD : D.ob E.xi ≠ T.zeroObstruction := by
    intro hzero
    exact hne (by rw [E.obstructionClass_eq_ob, hzero])
  rw [E.lift_eq_liftFill]
  exact DeformationObstructionTheory.not_liftFill_of_ob_ne_zero D hD

/--
VI.定理6.2 zero-obstruction side: under the explicit effectiveness field of
the selected obstruction theory, obstruction zero supplies a selected lift.
-/
theorem lift_of_obstruction_zero
    (E : SquareZeroExtensionData.{u, v, w, x, y, z} D)
    (hzero : E.obstructionClass = T.zeroObstruction) :
    E.Lift := by
  have hD : D.ob E.xi = T.zeroObstruction := by
    rw [← E.obstructionClass_eq_ob, hzero]
  rw [E.lift_eq_liftFill]
  exact DeformationObstructionTheory.liftFill_of_ob_eq_zero D hD

/-- VI.定理6.2: expose the selected lift torsor reading when obstruction vanishes. -/
def liftTorsor_of_obstruction_zero
    (E : SquareZeroExtensionData.{u, v, w, x, y, z} D)
    (hzero : E.obstructionClass = T.zeroObstruction) : Type z :=
  E.LiftTorsor hzero

/-- VI.定理6.2: expose the selected automorphism reading when obstruction vanishes. -/
def automorphisms_of_obstruction_zero
    (E : SquareZeroExtensionData.{u, v, w, x, y, z} D)
    (hzero : E.obstructionClass = T.zeroObstruction) : Type z :=
  E.AutomorphismSpace hzero

end SquareZeroExtensionData

/--
VI.系6.5 input package: a boundary stratum with a selected nonzero class in
the chosen `H1(T_{B/U})` obstruction reading.
-/
structure BoundaryObstructionFamily {U : AtomCarrier.{u}} {A : ArchitectureObject U}
    {S : Site.AATSite A} {P : StratumReadingParameter S}
    {k : Type v} [CommRing k]
    {X : ArchitectureStratum.{u, v, w, x, y} P k}
    {L : CotangentData.{u, v, w, x, y, z} X}
    {T : TangentData.{u, v, w, x, y, z} X L}
    (D : DeformationObstructionTheory.{u, v, w, x, y, z} T) where
  boundaryTest : D.DeformationTest
  h1NonzeroClass : Prop
  realizes_nonzero_obstruction :
    h1NonzeroClass -> D.ob boundaryTest ≠ T.zeroObstruction

/-- VI.系6.5: selected singular boundary predicate. -/
def USingularBoundary {U : AtomCarrier.{u}} {A : ArchitectureObject U}
    {S : Site.AATSite A} {P : StratumReadingParameter S}
    {k : Type v} [CommRing k]
    {X : ArchitectureStratum.{u, v, w, x, y} P k}
    {L : CotangentData.{u, v, w, x, y, z} X}
    {T : TangentData.{u, v, w, x, y, z} X L}
    (D : DeformationObstructionTheory.{u, v, w, x, y, z} T) : Prop :=
  ∃ W : BoundaryObstructionFamily.{u, v, w, x, y, z} D,
    W.h1NonzeroClass ∧ USingular D

namespace BoundaryObstructionFamily

variable {U : AtomCarrier.{u}} {A : ArchitectureObject U}
variable {S : Site.AATSite A} {P : StratumReadingParameter S}
variable {k : Type v} [CommRing k]
variable {X : ArchitectureStratum.{u, v, w, x, y} P k}
variable {L : CotangentData.{u, v, w, x, y, z} X}
variable {T : TangentData.{u, v, w, x, y, z} X L}
variable {D : DeformationObstructionTheory.{u, v, w, x, y, z} T}

/--
VI.系6.5 Singular Boundary.

A selected nonzero `H1(T_{B/U})` class that realizes a boundary obstruction
turns the boundary into a selected `U`-singular boundary.
-/
theorem singularBoundary
    (W : BoundaryObstructionFamily.{u, v, w, x, y, z} D)
    (h : W.h1NonzeroClass) :
    USingularBoundary D :=
  ⟨W, h, ⟨W.boundaryTest, W.realizes_nonzero_obstruction h⟩⟩

end BoundaryObstructionFamily

end SingularityMonodromyStack
end AAT.AG
