import ResearchLean.AG.RelativeRepairComposition.W1ActualRepairs
import ResearchLean.AG.RelativeRepairComposition.NativeAffineDifferentials
import ResearchLean.AG.RelativeRepairComposition.GeneratedNativeRelation

/-!
# Full original W1 kernel coordinates and authored differentials

## Implementation notes

Every coordinate uses the entire native translation kernel on the original
vertex. The differential is evaluated from the original authored paths by the
general native affine value laws. In particular the complete d1 is read before
imposing physical rx,ry values or eliminating any private always edge. The
bases and complete finite lists depend on structure, not on repair parameters.
-/
namespace AAT.AG.RelativeRepairComposition.W1FiniteCoefficients
open CategoryTheory TransportCoherence TransportCoherence.Arbitrary AbelianLiftingObstruction
open NativeAffine W1AffineInput W1AuthoredOperations W1Regions W1ActualRepairs

variable (negative : Bool) (x y : ZMod 3)
local notation "T" => originalTower negative x y
local notation "M" => TowerPresentation.localCoefficients
  (OriginalTowerPresentation.toTower (originalTower negative x y))

/-- The original e reference is the whole actual identity operation, independently of x,y. -/
theorem reference_e : reference negative x y (i := ()) (j := ()) edgeE = (1 : Op) := by
  simp [geometry, reference, edgeE, edgeA, edgeRx, edgeRy]

/-- The original a reference is its complete specified negative or identity linear operation. -/
theorem reference_a : reference negative x y (i := ()) (j := ()) edgeA = linearA negative := by
  simp [reference]

/-- The original candidate b reference is the whole actual identity operation, independently of its correction. -/
theorem reference_b : reference negative x y (i := ()) (j := ()) edgeB = (1 : Op) := by
  simp [geometry, reference, edgeB, edgeA, edgeRx, edgeRy]

/-- Every original full categorical kernel is linearly identified with the entire F3 translation space. -/
noncomputable def kernelCoordinate (v : geometry.Vertex) : (M).A v ≃ₗ[ZMod 3] ZMod 3 :=
  NativeAffine.linearCoefficient geometry (reference negative x y) (reference negative x y)
    comparison (linear_faces negative x y) v

/-- Full standard coordinates have dimension one without removing the private h direction. -/
noncomputable def bases : FiniteFamily.Bases (k := ZMod 3) (M).A where
  dimension _ := 1
  coordinate v := (kernelCoordinate negative x y v).trans
    (LinearEquiv.funUnique (Fin 1) (ZMod 3) (ZMod 3)).symm

/-- The original sole basis component is constructed from its actual complete dimension. -/
def basisIndex (v : geometry.Vertex) : Fin ((bases negative x y).dimension v) :=
  ⟨0, by change 0 < 1; decide⟩

/-- Full finite basis readings keep every actual original native kernel coordinate. -/
theorem basis_value (v : geometry.Vertex) (a : (M).A v) :
    (bases negative x y).coordinate v a (basisIndex negative x y v) =
      kernelCoordinate negative x y v a := rfl

/-- Every original finite-basis inverse includes as the same full actual affine translation. -/
theorem kernel_inverse_value (v : geometry.Vertex) (a : ZMod 3) :
    FiberAut.hom (kernelInclusion
      (GroupExtension.projection (projection (k := ZMod 3) (A := ZMod 3)))
      (GroupExtension.terminal (ZMod 3 ≃ₗ[ZMod 3] ZMod 3)) ((T).original.object v)
      (Additive.toMul ((kernelCoordinate negative x y v).symm a))) =
      translation (k := ZMod 3) a :=
  NativeAffine.coefficient_inverse_value geometry (reference negative x y) (reference negative x y)
    comparison (linear_faces negative x y) v a

/-- All original edge transports are linear on the same generated whole-kernel modules. -/
theorem original_linear {i j : geometry.Vertex} (e : geometry.Edge i j) (t : ZMod 3) (a : (M).A i) :
    (M).edge e (t • a) = t • (M).edge e a :=
  NativeAffine.edge_linear geometry (reference negative x y) (reference negative x y)
    comparison (linear_faces negative x y) e t a

/-- The complete first native face differential is the original e+b-rx correction, before physical restriction. -/
theorem d1_first (a : C1 M) :
    kernelCoordinate negative x y () (d1 M a false) =
      kernelCoordinate negative x y () (a (name edgeE)) +
        kernelCoordinate negative x y () (a (name edgeB)) -
          kernelCoordinate negative x y () (a (name edgeRx)) := by
  refine (NativeAffine.d1_value geometry (reference negative x y) (reference negative x y)
    comparison (linear_faces negative x y) a false).trans ?_
  simp only [geometry, vectorPath, GroupExtension.pathValue]
  change kernelCoordinate negative x y () (a (name edgeB)) +
      (kernelCoordinate negative x y () (a (name edgeE)) + 0) -
        (kernelCoordinate negative x y () (a (name edgeRx)) + 0) = _
  abel

/-- The complete negative-holonomy native second differential derives both a cancellations and the transported minus b. -/
theorem d1_second_negative (a : C1 ((originalTower true x y).toTower.localCoefficients)) :
    kernelCoordinate true x y () (d1 ((originalTower true x y).toTower.localCoefficients) a true) =
      kernelCoordinate true x y () (a (name edgeE)) -
        kernelCoordinate true x y () (a (name edgeB)) +
          kernelCoordinate true x y () (a (name edgeC)) -
            kernelCoordinate true x y () (a (name edgeRy)) := by
  refine (NativeAffine.d1_value geometry (reference true x y) (reference true x y)
    comparison (linear_faces true x y) a true).trans ?_
  simp only [geometry, ite_true, vectorPath, GroupExtension.pathValue]
  rw [reference_e, reference_a, reference_b]
  simp only [one_mul, mul_one, linearA_square]
  change kernelCoordinate true x y () (a (name edgeC)) +
      (-(kernelCoordinate true x y () (a (name edgeA))) +
        (-(kernelCoordinate true x y () (a (name edgeB))) +
          (kernelCoordinate true x y () (a (name edgeA)) +
            (kernelCoordinate true x y () (a (name edgeE)) + 0)))) -
              (kernelCoordinate true x y () (a (name edgeRy)) + 0) = _
  abel

/-- The same full native differential with identity a retains both private h contributions. -/
theorem d1_second_identity (a : C1 ((originalTower false x y).toTower.localCoefficients)) :
    kernelCoordinate false x y () (d1 ((originalTower false x y).toTower.localCoefficients) a true) =
      kernelCoordinate false x y () (a (name edgeE)) +
        2 * kernelCoordinate false x y () (a (name edgeA)) +
          kernelCoordinate false x y () (a (name edgeB)) +
            kernelCoordinate false x y () (a (name edgeC)) -
              kernelCoordinate false x y () (a (name edgeRy)) := by
  refine (NativeAffine.d1_value geometry (reference false x y) (reference false x y)
    comparison (linear_faces false x y) a true).trans ?_
  simp only [geometry, ite_true, vectorPath, GroupExtension.pathValue]
  change kernelCoordinate false x y () (a (name edgeC)) +
      (kernelCoordinate false x y () (a (name edgeA)) +
        (kernelCoordinate false x y () (a (name edgeB)) +
          (kernelCoordinate false x y () (a (name edgeA)) +
            (kernelCoordinate false x y () (a (name edgeE)) + 0)))) -
              (kernelCoordinate false x y () (a (name edgeRy)) + 0) = _
  ring

/-- Full inverse original input translations have the actual inverse coordinate at every field point. -/
theorem translation_inverse_apply (a t : ZMod 3) :
    ((translation (k := ZMod 3) a)⁻¹ : Op) t = -a + t := by
  change (AffineEquiv.constVAdd (ZMod 3) (ZMod 3) a).symm t = _
  rw [AffineEquiv.constVAdd_symm]
  rfl

/-- The same native original obstruction representative is (-x,-y), derived from the real reference words. -/
theorem defect_coordinate (f : geometry.TwoCell) :
    kernelCoordinate negative x y () ((T).toTower.defect f) =
      -(if (f : Bool) = true then y else x) := by
  have hv := NativeAffine.defect_value geometry (reference negative x y) (reference negative x y)
    comparison (linear_faces negative x y) f
  rw [reference_left_path, reference_right_path, comparison, zero_translation, one_mul, one_mul] at hv
  exact hv.trans (by rw [translation_inverse_apply, add_zero])

/-- Every original signed defect is closed in degree two because this specified input has no original three-cell. -/
theorem d2_zero (a : C2 M) : d2 M a = 0 := by
  funext s
  exact s.elim

/-- The complete arithmetic input enumeration precedes every local generation and every x,y value. -/
def enumK : FiniteElimination.Enumeration (ZMod 3) :=
  ⟨[0, 1, 2], by intro a; fin_cases a <;> simp⟩

/-- The full six original edge names are listed once without permission or repair selection. -/
def enumEdges : FiniteElimination.Enumeration (EdgeName (K := geometry)) :=
  ⟨[name edgeE, name edgeA, name edgeB, name edgeC, name edgeRx, name edgeRy], by
    rintro ⟨s, t, e⟩
    cases s
    cases t
    fin_cases e <;> simp [name, edgeE, edgeA, edgeB, edgeC, edgeRx, edgeRy]⟩

/-- Both complete authored face names are listed before any right-hand side or local elimination. -/
def enumFaces : FiniteElimination.Enumeration geometry.TwoCell :=
  ⟨[false, true], by intro f; cases f <;> simp⟩

end AAT.AG.RelativeRepairComposition.W1FiniteCoefficients
#assert_standard_axioms_only AAT.AG.RelativeRepairComposition.W1FiniteCoefficients
