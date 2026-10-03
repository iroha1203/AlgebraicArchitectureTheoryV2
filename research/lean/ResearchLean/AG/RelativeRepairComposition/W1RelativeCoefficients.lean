import ResearchLean.AG.RelativeRepairComposition.W1FiniteCoefficients
import ResearchLean.AG.RelativeRepairComposition.OriginalCandidateColumns
import ResearchLean.AG.RelativeRepairComposition.NativeEquationBridge
import ResearchLean.AG.RelativeRepairComposition.NativeAffineCorrection

/-!
# W1's whole relative cochains and actual signed defect

## Implementation notes

These are the original full relative families of P, with rx,ry corrections
zero and all four u,h,z,v otherwise unrestricted. The face family retains both
whole original kernel coefficients. Its differential is identified with the
original native d1 before any always/candidate or private/public split.
-/
namespace AAT.AG.RelativeRepairComposition.W1RelativeCoefficients
open CategoryTheory TransportCoherence TransportCoherence.Arbitrary AbelianLiftingObstruction
open NativeAffine W1AffineInput W1AuthoredOperations W1Regions W1ActualRepairs W1FiniteCoefficients

variable (negative : Bool) (x y : ZMod 3)
local notation "T" => originalTower negative x y
local notation "M" => TowerPresentation.localCoefficients (OriginalTowerPresentation.toTower T)
attribute [local instance] Classical.propDecidable

/-- The specified fixed part has no face, so its original native coherence is discharged directly from its cell set. -/
theorem fixed_faces (f : geometry.TwoCell) (hf : f ∈ fixedRegion.faces) :
    (T).toTower.upper.pathLift (geometry.twoLeft f) ≫ FiberAut.hom ((T).comparator f) =
      (T).toTower.upper.pathLift (geometry.twoRight f) := hf.elim

/-- Both original candidates lie outside the original physical fixed edge set. -/
theorem candidates_outside : ∀ e ∈ candidates, e ∉ fixedRegion.edges := by
  intro e he
  rcases he with he | he <;> subst e <;>
    simp [geometry, fixedRegion, name, edgeB, edgeC, edgeRx, edgeRy]

/-- The entire relative face family is all pairs of original full F3 kernel coordinates. -/
noncomputable def faceCoordinates : RelativeCover.C2 (M) ClosedRegion.all fixedRegion ≃ₗ[ZMod 3]
    (Bool → ZMod 3) where
  toFun c f := kernelCoordinate negative x y () (c.1 ⟨f, Set.mem_univ f⟩)
  invFun t := ⟨fun f => (kernelCoordinate negative x y (geometry.twoTarget f.1)).symm (t f.1),
    by intro f hf; exact hf.elim⟩
  left_inv c := by
    apply Subtype.ext
    funext f
    exact (kernelCoordinate negative x y ()).symm_apply_apply _
  right_inv t := by
    funext f
    exact (kernelCoordinate negative x y ()).apply_symm_apply _
  map_add' c d := by
    funext f
    exact (kernelCoordinate negative x y ()).map_add _ _
  map_smul' t c := by
    funext f
    exact (kernelCoordinate negative x y ()).map_smul _ _

/-- Reading either whole original face keeps its actual native kernel value. -/
theorem faceCoordinates_value (c : RelativeCover.C2 (M) ClosedRegion.all fixedRegion) (f : Bool) :
    faceCoordinates negative x y c f = kernelCoordinate negative x y () (c.1 ⟨f, Set.mem_univ f⟩) := rfl

/-- A whole relative degree-one family retains its full original terminal coefficient at each original name. -/
noncomputable def edgeCoordinate (a : RelativeCover.C1 (M) ClosedRegion.all fixedRegion)
    (e : EdgeName (K := geometry)) : ZMod 3 :=
  kernelCoordinate negative x y e.2.1 (a.1 ⟨e, Set.mem_univ e⟩)

/-- The physically fixed rx,ry corrections vanish in the whole relative family without any candidate closure. -/
theorem fixed_edge_coordinate (a : RelativeCover.C1 (M) ClosedRegion.all fixedRegion)
    (e : EdgeName (K := geometry)) (he : e ∈ fixedRegion.edges) : edgeCoordinate negative x y a e = 0 := by
  rw [edgeCoordinate, a.2 ⟨e, Set.mem_univ e⟩ he, map_zero]

/-- The four whole original corrections reconstruct a relative cochain before either face equation is imposed. -/
noncomputable def relativeCochain (u h z v : ZMod 3) :
    RelativeCover.C1 (M) ClosedRegion.all fixedRegion :=
  ⟨fun e => (kernelCoordinate negative x y e.1.2.1).symm
      (correctionValue u h z v e.1.2.2), by
    intro e he
    rcases he with he | he
    · have he' : e.1 = name edgeRx := he
      rcases e with ⟨e, hu⟩
      change e = name edgeRx at he'
      subst e
      simp [geometry, correctionValue, name, edgeE, edgeA, edgeB, edgeC, edgeRx]
    · have he' : e.1 = name edgeRy := he
      rcases e with ⟨e, hu⟩
      change e = name edgeRy at he'
      subst e
      simp [geometry, correctionValue, name, edgeE, edgeA, edgeB, edgeC, edgeRy]⟩

/-- Every original relative cochain constructor preserves all four corrections and both zero physical anchors. -/
theorem relativeCochain_value (u h z v : ZMod 3) (e : EdgeName (K := geometry)) :
    edgeCoordinate negative x y (relativeCochain negative x y u h z v) e =
      correctionValue u h z v e.2.2 :=
  (kernelCoordinate negative x y e.2.1).apply_symm_apply _

/-- The full relative finite differential equals the original native differential on every original face. -/
theorem relative_differential_value (a : RelativeCover.C1 (M) ClosedRegion.all fixedRegion)
    (f : geometry.TwoCell) :
    (FiniteCoefficients.differential1 (M) (original_linear negative x y) ClosedRegion.all fixedRegion a).1
        ⟨f, Set.mem_univ f⟩ =
      d1 (M) (fun e => a.1 ⟨e, Set.mem_univ e⟩) f := by
  rw [FiniteCoefficients.differential1_eq]
  have hr := congrFun (RelativeCover.original2_restrict (M) fixedRegion
    (RelativeCover.d1 (M) ClosedRegion.all fixedRegion a)) ⟨f, Set.mem_univ f⟩
  have hd := congrArg (fun c : RelativeComplex.relativeC2 (M) fixedRegion => c.1 f)
    (RelativeCover.original_d1 (M) fixedRegion a)
  exact hr.symm.trans hd

/-- The relative first face derives u+z after the same physical rx correction vanishes. -/
theorem relative_d1_first (a : RelativeCover.C1 (M) ClosedRegion.all fixedRegion) :
    faceCoordinates negative x y
        (FiniteCoefficients.differential1 (M) (original_linear negative x y) ClosedRegion.all fixedRegion a) false =
      edgeCoordinate negative x y a (name edgeE) + edgeCoordinate negative x y a (name edgeB) := by
  rw [faceCoordinates_value, relative_differential_value, d1_first]
  change edgeCoordinate negative x y a (name edgeE) + edgeCoordinate negative x y a (name edgeB) -
    edgeCoordinate negative x y a (name edgeRx) = _
  rw [fixed_edge_coordinate negative x y a (name edgeRx) (Or.inl rfl), sub_zero]

/-- The negative relative second face derives u-z+v from the same original five-occurrence path. -/
theorem relative_d1_second_negative
    (a : RelativeCover.C1 ((originalTower true x y).toTower.localCoefficients) ClosedRegion.all fixedRegion) :
    faceCoordinates true x y
        (FiniteCoefficients.differential1 ((originalTower true x y).toTower.localCoefficients)
          (original_linear true x y) ClosedRegion.all fixedRegion a) true =
      edgeCoordinate true x y a (name edgeE) - edgeCoordinate true x y a (name edgeB) +
        edgeCoordinate true x y a (name edgeC) := by
  rw [faceCoordinates_value, relative_differential_value, d1_second_negative]
  change edgeCoordinate true x y a (name edgeE) - edgeCoordinate true x y a (name edgeB) +
    edgeCoordinate true x y a (name edgeC) - edgeCoordinate true x y a (name edgeRy) = _
  rw [fixed_edge_coordinate true x y a (name edgeRy) (Or.inr rfl), sub_zero]

/-- The identity relative second face retains 2h on the unchanged original permissions and authored word. -/
theorem relative_d1_second_identity
    (a : RelativeCover.C1 ((originalTower false x y).toTower.localCoefficients) ClosedRegion.all fixedRegion) :
    faceCoordinates false x y
        (FiniteCoefficients.differential1 ((originalTower false x y).toTower.localCoefficients)
          (original_linear false x y) ClosedRegion.all fixedRegion a) true =
      edgeCoordinate false x y a (name edgeE) + 2 * edgeCoordinate false x y a (name edgeA) +
        edgeCoordinate false x y a (name edgeB) + edgeCoordinate false x y a (name edgeC) := by
  rw [faceCoordinates_value, relative_differential_value, d1_second_identity]
  change edgeCoordinate false x y a (name edgeE) + 2 * edgeCoordinate false x y a (name edgeA) +
    edgeCoordinate false x y a (name edgeB) + edgeCoordinate false x y a (name edgeC) -
      edgeCoordinate false x y a (name edgeRy) = _
  rw [fixed_edge_coordinate false x y a (name edgeRy) (Or.inr rfl), sub_zero]

/-- The whole relative face right-hand side is generated from the actual original native defect. -/
noncomputable def actualDefect := ActualEquation.defectFamily (T) fixedRegion (fixed_faces negative x y)

/-- Both original full relative defect coordinates are exactly the values of the independently evaluated native defect. -/
theorem actualDefect_coordinates (f : Bool) :
    faceCoordinates negative x y (actualDefect negative x y) f = -(if f = true then y else x) :=
  defect_coordinate negative x y f

/-- The signed repair right-hand side retains x,y on the same two original authored faces. -/
theorem signedDefect_coordinates (f : Bool) :
    faceCoordinates negative x y (-actualDefect negative x y) f = if f = true then y else x := by
  rw [faceCoordinates_value]
  change kernelCoordinate negative x y () (-((actualDefect negative x y).1 ⟨f, Set.mem_univ f⟩)) = _
  rw [map_neg]
  change -(faceCoordinates negative x y (actualDefect negative x y) f) = _
  rw [actualDefect_coordinates, neg_neg]

end AAT.AG.RelativeRepairComposition.W1RelativeCoefficients
#assert_standard_axioms_only AAT.AG.RelativeRepairComposition.W1RelativeCoefficients
