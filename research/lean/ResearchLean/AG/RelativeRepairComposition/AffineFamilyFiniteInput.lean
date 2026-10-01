import ResearchLean.AG.RelativeRepairComposition.AffineConstantCoefficients
import ResearchLean.AG.RelativeRepairComposition.AffineFamilyLaws
import ResearchLean.AG.RelativeRepairComposition.NativeAffineFiniteInput

/-!
# Full original coordinate matrices stay fixed across primitive values

## Implementation notes

The native coefficient system and every full standard basis are identified with
the base data. Degree-zero, degree-one and degree-two matrices are evaluated on
the same original columns. Only the full defect vector changes affinely. These
equalities retain typed paths, repeated occurrences and both complete pastings.
-/
namespace AAT.AG.RelativeRepairComposition.NativeAffine
open CategoryTheory TransportCoherence TransportCoherence.Arbitrary AbelianLiftingObstruction
universe uk uG uV
variable {k : Type uk} [Field k] {V : Type uV} [AddCommGroup V] [Module k V]
variable (d : Nat) (K : FiniteTransportPresentation.{uG})
variable (L R : ∀ {i j : K.Vertex}, K.Edge i j → Operations k (Fin d → k))
variable (c : K.TwoCell → (Fin d → k))
variable (θL θR : V →ₗ[k] (EdgeName (K := K) → (Fin d → k)))
variable (η : V →ₗ[k] (K.TwoCell → (Fin d → k)))
variable (hf : ∀ f : K.TwoCell,
  (GroupExtension.pathValue K R (K.twoLeft f)).linear =
    (GroupExtension.pathValue K R (K.twoRight f)).linear)

/-- The parameter family uses the same bundled whole-kernel local system as its base original tower. -/
theorem family_coefficients (v : V) :
    (familyTower K L R c θL θR η hf v).toTower.localCoefficients =
      (tower K L R c hf).toTower.localCoefficients :=
  same_linear_coefficients K L R (familyOriginal K L θL v) (familyReference K R θR v)
    c (familyComparisons K c η v) hf (family_aligned K R θR hf v)
    (fun e => translated_linear K R (θR v) e)

/-- Every original vertex retains the same entire standard-basis dimension at every parameter value. -/
theorem family_standard_dimension (v : V) (w : K.Vertex) :
    (standardBases (k := k) d K (familyOriginal K L θL v) (familyReference K R θR v)
      (familyComparisons K c η v) (family_aligned K R θR hf v)).dimension w =
      (standardBases (k := k) d K L R c hf).dimension w := rfl

/-- Every full original kernel vector has the identical standard coordinates at every parameter value. -/
theorem family_standard_coordinate (v : V) (w : K.Vertex)
    (a : (tower K L R c hf).toTower.localCoefficients.A w) :
    (standardBases (k := k) d K (familyOriginal K L θL v) (familyReference K R θR v)
      (familyComparisons K c η v) (family_aligned K R θR hf v)).coordinate w a =
      (standardBases (k := k) d K L R c hf).coordinate w a := rfl

/-- Every full standard vector reconstructs the identical original kernel element at every parameter value. -/
theorem family_standard_inverse (v : V) (w : K.Vertex) (a : Fin d → k) :
    ((standardBases (k := k) d K (familyOriginal K L θL v) (familyReference K R θR v)
      (familyComparisons K c η v) (family_aligned K R θR hf v)).coordinate w).symm a =
      ((standardBases (k := k) d K L R c hf).coordinate w).symm a := rfl

variable [DecidableEq K.Vertex] [DecidableEq (EdgeName (K := K))] [DecidableEq K.TwoCell]

omit [DecidableEq (EdgeName (K := K))] [DecidableEq K.TwoCell] in
/-- The entire original vertex matrix is reused at every parameter value. -/
theorem family_vertex_matrix (v : V) :
    vertexMatrix d K (familyReference K R θR v) = vertexMatrix d K R := by
  funext e a
  unfold vertexMatrix familyReference
  rw [translated_linear]

omit [DecidableEq K.Vertex] [DecidableEq K.TwoCell] in
/-- The entire original face matrix, with full word occurrences, is reused at every parameter value. -/
theorem family_edge_matrix (v : V) :
    edgeMatrix d K (familyReference K R θR v) = edgeMatrix d K R := by
  funext f e
  unfold edgeMatrix familyReference
  rw [translated_vector_path, translated_vector_path]

omit [DecidableEq K.Vertex] [DecidableEq (EdgeName (K := K))] in
/-- The entire original three-cell matrix, with full typed pastings, is reused at every parameter value. -/
theorem family_face_matrix (v : V) :
    faceMatrix d K (familyReference K R θR v) = faceMatrix d K R := by
  funext s f
  unfold faceMatrix familyReference
  rw [translated_vector_pasting, translated_vector_pasting]

include hf in
omit [DecidableEq K.Vertex] [DecidableEq (EdgeName (K := K))] [DecidableEq K.TwoCell] in
/-- Every actual original defect entry changes by the generated parameter linear term alone. -/
theorem family_defect_coordinates (v : V) (f : K.TwoCell × Fin d) :
    defectCoordinates d K (familyReference K R θR v) (familyComparisons K c η v) f =
      defectCoordinates d K R c f + familyDefectLinear K R θR η v f.1 f.2 := by
  change realDefectVector K (familyReference K R θR v) (familyComparisons K c η v) f.1 f.2 =
    realDefectVector K R c f.1 f.2 + familyDefectLinear K R θR η v f.1 f.2
  rw [family_defect_affine K R c θR η hf v f.1]
  rfl

end AAT.AG.RelativeRepairComposition.NativeAffine
#assert_standard_axioms_only AAT.AG.RelativeRepairComposition
