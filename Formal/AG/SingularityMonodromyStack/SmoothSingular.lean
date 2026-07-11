import Formal.AG.SingularityMonodromyStack.CotangentInterface
import Formal.AG.LawAlgebra.LawfulLocus

noncomputable section

namespace AAT.AG
namespace SingularityMonodromyStack

universe u v w x y z

/--
VI.定義4.1: selected deformation-obstruction theory for a stratum.

The fields `effective` and `sound` are explicit assumptions of the chosen
interface. They are not global deformation theory theorems.
-/
structure DeformationObstructionTheory {U : AtomCarrier.{u}} {A : ArchitectureObject U}
    {S : Site.AATSite A} {P : StratumReadingParameter S}
    {k : Type v} [CommRing k]
    {X : ArchitectureStratum.{u, v, w, x, y} P k}
    {L : CotangentData.{u, v, w, x, y, z} X}
    (T : TangentData.{u, v, w, x, y, z} X L) where
  DeformationTest : Type z
  LiftFill : DeformationTest -> Prop
  ob : DeformationTest -> T.ObstructionTarget
  effective : ∀ eta : DeformationTest, ob eta = T.zeroObstruction -> LiftFill eta
  sound : ∀ eta : DeformationTest, LiftFill eta -> ob eta = T.zeroObstruction

namespace DeformationObstructionTheory

variable {U : AtomCarrier.{u}} {A : ArchitectureObject U}
variable {S : Site.AATSite A} {P : StratumReadingParameter S}
variable {k : Type v} [CommRing k]
variable {X : ArchitectureStratum.{u, v, w, x, y} P k}
variable {L : CotangentData.{u, v, w, x, y, z} X}
variable {T : TangentData.{u, v, w, x, y, z} X L}

/-- VI.定義4.1: nonzero obstruction refutes the selected lift/fill predicate. -/
theorem not_liftFill_of_ob_ne_zero
    (D : DeformationObstructionTheory.{u, v, w, x, y, z} T)
    {eta : D.DeformationTest} (hne : D.ob eta ≠ T.zeroObstruction) :
    ¬ D.LiftFill eta := by
  intro hlift
  exact hne (D.sound eta hlift)

/-- VI.定義4.1: obstruction zero produces a selected lift/fill. -/
theorem liftFill_of_ob_eq_zero
    (D : DeformationObstructionTheory.{u, v, w, x, y, z} T)
    {eta : D.DeformationTest} (hzero : D.ob eta = T.zeroObstruction) :
    D.LiftFill eta :=
  D.effective eta hzero

end DeformationObstructionTheory

/-- VI.定義4.1: `U`-smoothness for the selected deformation tests. -/
def USmooth {U : AtomCarrier.{u}} {A : ArchitectureObject U}
    {S : Site.AATSite A} {P : StratumReadingParameter S}
    {k : Type v} [CommRing k]
    {X : ArchitectureStratum.{u, v, w, x, y} P k}
    {L : CotangentData.{u, v, w, x, y, z} X}
    {T : TangentData.{u, v, w, x, y, z} X L}
    (D : DeformationObstructionTheory.{u, v, w, x, y, z} T) : Prop :=
  ∀ eta : D.DeformationTest, D.LiftFill eta ∧ D.ob eta = T.zeroObstruction

/-- VI.定義5.1: `U`-singularity is existence of a selected nonzero obstruction. -/
def USingular {U : AtomCarrier.{u}} {A : ArchitectureObject U}
    {S : Site.AATSite A} {P : StratumReadingParameter S}
    {k : Type v} [CommRing k]
    {X : ArchitectureStratum.{u, v, w, x, y} P k}
    {L : CotangentData.{u, v, w, x, y, z} X}
    {T : TangentData.{u, v, w, x, y, z} X L}
    (D : DeformationObstructionTheory.{u, v, w, x, y, z} T) : Prop :=
  ∃ eta : D.DeformationTest, D.ob eta ≠ T.zeroObstruction

namespace USmooth

variable {U : AtomCarrier.{u}} {A : ArchitectureObject U}
variable {S : Site.AATSite A} {P : StratumReadingParameter S}
variable {k : Type v} [CommRing k]
variable {X : ArchitectureStratum.{u, v, w, x, y} P k}
variable {L : CotangentData.{u, v, w, x, y, z} X}
variable {T : TangentData.{u, v, w, x, y, z} X L}
variable {D : DeformationObstructionTheory.{u, v, w, x, y, z} T}

/-- VI.R2: smoothness exposes obstruction vanishing on each selected test. -/
theorem obstruction_eq_zero (h : USmooth D) (eta : D.DeformationTest) :
    D.ob eta = T.zeroObstruction :=
  (h eta).2

/-- VI.R2: smoothness exposes the selected lift/fill on each selected test. -/
theorem liftFill (h : USmooth D) (eta : D.DeformationTest) :
    D.LiftFill eta :=
  (h eta).1

end USmooth

namespace DeformationObstructionTheory

variable {U : AtomCarrier.{u}} {A : ArchitectureObject U}
variable {S : Site.AATSite A} {P : StratumReadingParameter S}
variable {k : Type v} [CommRing k]
variable {X : ArchitectureStratum.{u, v, w, x, y} P k}
variable {L : CotangentData.{u, v, w, x, y, z} X}
variable {T : TangentData.{u, v, w, x, y, z} X L}

/--
VI.R2: selected smoothness criterion under the explicit effectiveness field.

If every selected obstruction class vanishes, the effective interface supplies
all selected lift/fill data, so the stratum is `U`-smooth.
-/
theorem uSmooth_of_all_obstruction_zero
    (D : DeformationObstructionTheory.{u, v, w, x, y, z} T)
    (hzero : ∀ eta : D.DeformationTest, D.ob eta = T.zeroObstruction) :
    USmooth D := by
  intro eta
  exact ⟨D.effective eta (hzero eta), hzero eta⟩

/-- VI.R2: `U`-smoothness is equivalent to selected obstruction vanishing. -/
theorem uSmooth_iff_all_obstruction_zero
    (D : DeformationObstructionTheory.{u, v, w, x, y, z} T) :
    USmooth D ↔ ∀ eta : D.DeformationTest, D.ob eta = T.zeroObstruction :=
  ⟨fun h eta => (h eta).2, D.uSmooth_of_all_obstruction_zero⟩

/-- VI.R2: selected singularity refutes selected smoothness. -/
theorem not_uSmooth_of_uSingular
    (D : DeformationObstructionTheory.{u, v, w, x, y, z} T)
    (hsing : USingular D) :
    ¬ USmooth D := by
  intro hsmooth
  rcases hsing with ⟨eta, hne⟩
  exact hne ((hsmooth eta).2)

end DeformationObstructionTheory

/--
VI.定義5.2: selected normal cone reading relative to `Flat_U`.

The lawful locus, obstruction ideal, and normal cone are explicit selected
carriers; this does not build a general normal cone theory.
-/
structure NormalConeReading {U : AtomCarrier.{u}} {A : ArchitectureObject U}
    {S : Site.AATSite A} {P : StratumReadingParameter S}
    {k : Type v} [CommRing k]
    (X : ArchitectureStratum.{u, v, w, x, y} P k) where
  LawCoordinateAlgebra : Type z
  lawCoordinateCommRing : CommRing LawCoordinateAlgebra
  obstructionFamily :
    LawAlgebra.ObstructionIdeal.SelectedLawWitnessIdealFamily.{u, z} LawCoordinateAlgebra
  pointToPrime : X.Point -> PrimeSpectrum LawCoordinateAlgebra
  lawfulLocus : Set (PrimeSpectrum LawCoordinateAlgebra)
  lawfulLocus_eq_flatU :
    lawfulLocus =
      LawAlgebra.LawfulLocus.localLawfulLocus LawCoordinateAlgebra obstructionFamily
  obstructionIdealCarrier : Ideal LawCoordinateAlgebra
  obstructionIdealCarrier_eq_I_U : obstructionIdealCarrier = obstructionFamily.localObstructionIdeal
  normalCone : Type z
  normalConeOverFlat : normalCone -> Prop
  stratumToLawfulLocus : X.Point -> Prop

attribute [instance] NormalConeReading.lawCoordinateCommRing

namespace NormalConeReading

variable {U : AtomCarrier.{u}} {A : ArchitectureObject U}
variable {S : Site.AATSite A} {P : StratumReadingParameter S}
variable {k : Type v} [CommRing k]
variable {X : ArchitectureStratum.{u, v, w, x, y} P k}

/-- VI.定義5.2: the selected lawful locus is the Part III `Flat_U` locus. -/
theorem lawfulLocus_eq_flatU_holds
    (N : NormalConeReading.{u, v, w, x, y, z} X) :
    N.lawfulLocus =
      LawAlgebra.LawfulLocus.localLawfulLocus N.LawCoordinateAlgebra N.obstructionFamily :=
  N.lawfulLocus_eq_flatU

/-- VI.定義5.2: the selected obstruction ideal is the Part III local `I_U`. -/
theorem obstructionIdealCarrier_eq_I_U_holds
    (N : NormalConeReading.{u, v, w, x, y, z} X) :
    N.obstructionIdealCarrier = N.obstructionFamily.localObstructionIdeal :=
  N.obstructionIdealCarrier_eq_I_U

end NormalConeReading

/-- VI.定義5.2: selected structural repair direction read from a normal cone. -/
structure StructuralRepairDirection {U : AtomCarrier.{u}} {A : ArchitectureObject U}
    {S : Site.AATSite A} {P : StratumReadingParameter S}
    {k : Type v} [CommRing k]
    {X : ArchitectureStratum.{u, v, w, x, y} P k}
    (N : NormalConeReading.{u, v, w, x, y, z} X) where
  Direction : Type z
  pointsTowardVanishing : Direction -> Prop
  selectedDirection : Direction
  selected_pointsTowardVanishing : pointsTowardVanishing selectedDirection

namespace StructuralRepairDirection

variable {U : AtomCarrier.{u}} {A : ArchitectureObject U}
variable {S : Site.AATSite A} {P : StratumReadingParameter S}
variable {k : Type v} [CommRing k]
variable {X : ArchitectureStratum.{u, v, w, x, y} P k}
variable {N : NormalConeReading.{u, v, w, x, y, z} X}

/-- VI.定義5.2: expose the selected direction's vanishing certificate. -/
theorem selected_pointsTowardVanishing_holds
    (R : StructuralRepairDirection.{u, v, w, x, y, z} N) :
    R.pointsTowardVanishing R.selectedDirection :=
  R.selected_pointsTowardVanishing

end StructuralRepairDirection

end SingularityMonodromyStack
end AAT.AG
