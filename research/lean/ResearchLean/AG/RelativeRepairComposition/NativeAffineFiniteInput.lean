import ResearchLean.AG.RelativeRepairComposition.NativeAffineDifferentials
import ResearchLean.AG.RelativeRepairComposition.GeneratedNativeRelation

/-! # Full finite-coordinate input from original affine evaluations -/
namespace AAT.AG.RelativeRepairComposition.NativeAffine
open CategoryTheory TransportCoherence TransportCoherence.Arbitrary AbelianLiftingObstruction
universe uk uG
variable {k : Type uk} [Field k] (d : Nat)
variable (K : FiniteTransportPresentation.{uG})
variable (L R : ∀ {i j : K.Vertex}, K.Edge i j → Operations k (Fin d → k))
variable (c : K.TwoCell → (Fin d → k))
variable (hfaces : ∀ f : K.TwoCell,
  (GroupExtension.pathValue K R (K.twoLeft f)).linear =
    (GroupExtension.pathValue K R (K.twoRight f)).linear)
local notation "M" => TowerPresentation.localCoefficients
  (OriginalTowerPresentation.toTower (tower K L R c hfaces))

/-- The entire native translation kernel uses all d standard coordinates at every original vertex. -/
noncomputable def standardBases : FiniteFamily.Bases (k := k) (M).A where
  dimension _ := d
  coordinate v := linearCoefficient K L R c hfaces v

/-- Every original native kernel vector retains its full real coordinate family. -/
theorem standard_basis_value (v : K.Vertex) (x : (M).A v) (j : Fin d) :
    (standardBases d K L R c hfaces).coordinate v x j =
      coefficient K L R c hfaces v x j := rfl

/-- Every full original coordinate reconstructs the same real translation operation. -/
theorem standard_basis_inverse (v : K.Vertex) (x : Fin d → k) :
    FiberAut.hom (kernelInclusion (GroupExtension.projection (projection (k := k) (A := Fin d → k)))
      (GroupExtension.terminal ((Fin d → k) ≃ₗ[k] (Fin d → k)))
      ((tower K L R c hfaces).original.object v)
      (Additive.toMul ((standardBases d K L R c hfaces).coordinate v).symm x)) =
        translation (k := k) x := coefficient_inverse_value K L R c hfaces v x

variable [DecidableEq K.Vertex] [DecidableEq (EdgeName (K := K))] [DecidableEq K.TwoCell]

/-- An original vertex column is its full standard vector, zero at all other original vertices. -/
def vertexColumn (v : K.Vertex) (j : Fin d) : K.Vertex → (Fin d → k) :=
  fun w => if w = v then Pi.single j 1 else 0

/-- An original edge column is its full terminal standard vector, zero on all other original names. -/
def edgeColumn (e : EdgeName (K := K)) (j : Fin d) : EdgeName (K := K) → (Fin d → k) :=
  fun a => if a = e then Pi.single j 1 else 0

/-- An original face column is its full terminal standard vector, zero on all other original faces. -/
def faceColumn (f : K.TwoCell) (j : Fin d) : K.TwoCell → (Fin d → k) :=
  fun a => if a = f then Pi.single j 1 else 0

/-- Original degree-zero matrix entries are actual reference linear evaluations on standard vertex columns. -/
def vertexMatrix : Matrix (EdgeName (K := K) × Fin d) (K.Vertex × Fin d) k :=
  fun e v => (vertexColumn (k := k) d K v.1 v.2 e.1.2.1 -
    (R e.1.2.2).linear (vertexColumn (k := k) d K v.1 v.2 e.1.1)) e.2

/-- Original degree-one matrix entries evaluate both complete authored real words on full edge columns. -/
def edgeMatrix : Matrix (K.TwoCell × Fin d) (EdgeName (K := K) × Fin d) k :=
  fun f e => (vectorPath K R (edgeColumn d K e.1 e.2) (K.twoLeft f.1) -
    vectorPath K R (edgeColumn d K e.1 e.2) (K.twoRight f.1)) f.2

/-- Original degree-two matrix entries evaluate both complete typed real pastings on full face columns. -/
def faceMatrix : Matrix (K.ThreeCell × Fin d) (K.TwoCell × Fin d) k :=
  fun s f => (vectorPasting K R (faceColumn d K f.1 f.2) (K.threeLeft s.1) -
    vectorPasting K R (faceColumn d K f.1 f.2) (K.threeRight s.1)) s.2

/-- Defect entries evaluate the authored translation and the original reference word quotient at zero. -/
def defectCoordinates : K.TwoCell × Fin d → k := fun f =>
  (translation (k := k) (c f.1) * GroupExtension.pathValue K R (K.twoLeft f.1) *
    (GroupExtension.pathValue K R (K.twoRight f.1))⁻¹) 0 f.2

omit [DecidableEq (EdgeName (K := K))] [DecidableEq K.TwoCell] in
/-- Every primitive degree-zero entry equals the differential on the entire original native vertex column. -/
theorem vertex_matrix_value (e : EdgeName (K := K) × Fin d) (v : K.Vertex × Fin d) :
    vertexMatrix d K R e v =
      coefficient K L R c hfaces e.1.2.1
        (d0 (M) (fun w => (coefficient K L R c hfaces w).symm
          (vertexColumn d K v.1 v.2 w)) e.1) e.2 := by
  rw [d0_value]
  simp only [AddEquiv.apply_symm_apply]
  rfl

omit [DecidableEq K.Vertex] [DecidableEq K.TwoCell] in
/-- Every primitive degree-one entry equals the differential on the entire original native edge column. -/
theorem edge_matrix_value (f : K.TwoCell × Fin d) (e : EdgeName (K := K) × Fin d) :
    edgeMatrix d K R f e =
      coefficient K L R c hfaces (K.twoTarget f.1)
        (d1 (M) (fun a => (coefficient K L R c hfaces a.2.1).symm
          (edgeColumn d K e.1 e.2 a)) f.1) f.2 := by
  rw [d1_value]
  simp only [AddEquiv.apply_symm_apply]
  rfl

omit [DecidableEq K.Vertex] [DecidableEq (EdgeName (K := K))] in
/-- Every primitive degree-two entry equals the differential on the entire original native face column. -/
theorem face_matrix_value (s : K.ThreeCell × Fin d) (f : K.TwoCell × Fin d) :
    faceMatrix d K R s f =
      coefficient K L R c hfaces (K.threeTarget s.1)
        (d2 (M) (fun a => (coefficient K L R c hfaces (K.twoTarget a)).symm
          (faceColumn d K f.1 f.2 a)) s.1) s.2 := by
  rw [d2_value]
  simp only [AddEquiv.apply_symm_apply]
  rfl

omit [DecidableEq K.Vertex] [DecidableEq (EdgeName (K := K))] [DecidableEq K.TwoCell] in
/-- Every primitive defect entry is the coordinate of the same original full native obstruction representative. -/
theorem defect_coordinate_value (f : K.TwoCell × Fin d) :
    defectCoordinates d K R c f =
      coefficient K L R c hfaces (K.twoTarget f.1) ((tower K L R c hfaces).toTower.defect f.1) f.2 := by
  rw [defect_value]
  rfl

end AAT.AG.RelativeRepairComposition.NativeAffine
#assert_standard_axioms_only AAT.AG.RelativeRepairComposition
