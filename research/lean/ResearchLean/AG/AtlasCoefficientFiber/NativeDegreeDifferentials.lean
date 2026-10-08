import ResearchLean.AG.AtlasCoefficientFiber.NativeDegreeCoordinates

/-!
# Primitive differentials and the original two maps in native coordinates

Position: G-135 E degree transport. The fine differential tables use original
signed endpoint/three-occurrence formulas. P and Q differential tables are
p-next*dFine*p and q-next*dFine*q from the same original L projections.

## Implementation notes

Standard function single coordinates present the original fine complex. The
native P/Q spaces remain the Kan complex and actual dual L, respectively.
Full representative equations discharge differential compatibility from C3/C4;
no square-zero, image, or preservation certificate is an input. Matrices on
ambient cell functions are always applied to the proved native image when
representing native maps, so unused ambient components are not counted as P/Q.
The original unit and comparison are computed from actual Option transport,
including none cells; a pure-only comparison presentation is not substituted.
-/

noncomputable section
namespace AAT.AG.AtlasCoefficientFiber
open CanonicalResolution ResolutionInvariance FaceRelationSubdivision Module Matrix
universe u

/-- E original function-space map table, with standard named-cell singles.
Finite enumeration and equality are input-cell data, without semantic bases. -/
def cochainMatrix {I J : Type u} [Fintype J] [DecidableEq J]
    (f : (J → ℚ) →ₗ[ℚ] (I → ℚ)) : Matrix I J ℚ := LinearMap.toMatrix' f

/-- Owner entry API exposes each original named single-vector image. -/
theorem cochainMatrix_entry {I J : Type u} [Fintype J] [DecidableEq J]
    (f : (J → ℚ) →ₗ[ℚ] (I → ℚ)) (i : I) (j : J) :
    cochainMatrix f i j = f (Pi.single j 1) i :=
  LinearMap.toMatrix'_apply f i j

/-- Owner whole-vector API retains every original function coefficient. -/
theorem cochainMatrix_mulVec {I J : Type u} [Fintype J] [DecidableEq J]
    (f : (J → ℚ) →ₗ[ℚ] (I → ℚ)) (x : J → ℚ) : cochainMatrix f *ᵥ x = f x := by
  rw [← Matrix.toLin'_apply, cochainMatrix, Matrix.toLin'_toMatrix']

variable {Source : Type u} {q qc qf : Reading Source} {h : qc.CoarserThan qf}
variable {Nc : TargetSupportedNerve.{u,u} qc} {Nf : TargetSupportedNerve.{u,u} qf}

/-- E primitive degree-zero differential table of the original selected nerve.
This same constructor applies to the original coarse and fine nerves. -/
def primitiveD0Matrix (N : TargetSupportedNerve.{u,u} q) (S : Set q.Target)
    [Fintype (N.ChartInTargetSubset S)] [DecidableEq (N.ChartInTargetSubset S)] :
    Matrix (N.EdgeInTargetSubset S) (N.ChartInTargetSubset S) ℚ :=
  cochainMatrix (N.targetSubsetComplex S).d0

/-- Owner original endpoint entry preserves both signed incidences, including
loop endpoints which cancel without removing their original edge names. -/
theorem primitiveD0Matrix_entry (N : TargetSupportedNerve.{u,u} q) (S : Set q.Target)
    [Fintype (N.ChartInTargetSubset S)] [DecidableEq (N.ChartInTargetSubset S)]
    (e : N.EdgeInTargetSubset S) (c : N.ChartInTargetSubset S) :
    primitiveD0Matrix N S e c = (Pi.single c (1 : ℚ) : N.ChartInTargetSubset S → ℚ) (N.targetSubsetEdgeRight S e) -
      (Pi.single c (1 : ℚ) : N.ChartInTargetSubset S → ℚ) (N.targetSubsetEdgeLeft S e) := by
  rw [primitiveD0Matrix, cochainMatrix_entry]
  exact N.targetSubsetComplex_d0_apply S (Pi.single c 1) e

/-- Owner original degree-zero table represents the full native differential. -/
theorem primitiveD0Matrix_mulVec (N : TargetSupportedNerve.{u,u} q) (S : Set q.Target)
    [Fintype (N.ChartInTargetSubset S)] [DecidableEq (N.ChartInTargetSubset S)]
    (x : (N.targetSubsetComplex S).C0) :
    primitiveD0Matrix N S *ᵥ x = (N.targetSubsetComplex S).d0 x :=
  cochainMatrix_mulVec _ x

/-- E primitive degree-one differential table keeps original face names and
all three signed edge occurrences, even when some coincide. -/
def primitiveD1Matrix (N : TargetSupportedNerve.{u,u} q) (S : Set q.Target)
    [Fintype (N.EdgeInTargetSubset S)] [DecidableEq (N.EdgeInTargetSubset S)] :
    Matrix (N.FaceInTargetSubset S) (N.EdgeInTargetSubset S) ℚ :=
  cochainMatrix (N.targetSubsetComplex S).d1

/-- Owner original face entry retains the signed three-occurrence formula. -/
theorem primitiveD1Matrix_entry (N : TargetSupportedNerve.{u,u} q) (S : Set q.Target)
    [Fintype (N.EdgeInTargetSubset S)] [DecidableEq (N.EdgeInTargetSubset S)]
    (f : N.FaceInTargetSubset S) (e : N.EdgeInTargetSubset S) :
    primitiveD1Matrix N S f e = (Pi.single e (1 : ℚ) : N.EdgeInTargetSubset S → ℚ) (N.targetSubsetFaceEdge0 S f) -
      (Pi.single e (1 : ℚ) : N.EdgeInTargetSubset S → ℚ) (N.targetSubsetFaceEdge1 S f) +
      (Pi.single e (1 : ℚ) : N.EdgeInTargetSubset S → ℚ) (N.targetSubsetFaceEdge2 S f) := by
  rw [primitiveD1Matrix, cochainMatrix_entry]
  exact N.targetSubsetComplex_d1_apply S (Pi.single e 1) f

/-- Owner original degree-one table represents every native edge cochain. -/
theorem primitiveD1Matrix_mulVec (N : TargetSupportedNerve.{u,u} q) (S : Set q.Target)
    [Fintype (N.EdgeInTargetSubset S)] [DecidableEq (N.EdgeInTargetSubset S)]
    (x : (N.targetSubsetComplex S).C1) :
    primitiveD1Matrix N S *ᵥ x = (N.targetSubsetComplex S).d1 x :=
  cochainMatrix_mulVec _ x

/-- E original differential square is inherited from the constructed native
complex, and is proved for the full table, not supplied as matrix data. -/
theorem primitiveD1Matrix_mul_D0 (N : TargetSupportedNerve.{u,u} q) (S : Set q.Target)
    [Fintype (N.ChartInTargetSubset S)] [DecidableEq (N.ChartInTargetSubset S)]
    [Fintype (N.EdgeInTargetSubset S)] [DecidableEq (N.EdgeInTargetSubset S)] :
    primitiveD1Matrix N S * primitiveD0Matrix N S = 0 := by
  apply Matrix.ext_of_mulVec_single
  intro c
  rw [← Matrix.mulVec_mulVec, primitiveD0Matrix_mulVec, primitiveD1Matrix_mulVec,
    Matrix.zero_mulVec]
  exact (N.targetSubsetComplex S).d1_comp_d0 (Pi.single c 1)

variable (M : IncidenceSupportedComparison qc qf h Nc Nf) (A : Set qc.Target)

section P0
variable [Fintype (Nf.ChartInTargetSubset (comparisonFactor qc qf h ⁻¹' A))] [Fintype (Nf.EdgeInTargetSubset (comparisonFactor qc qf h ⁻¹' A))]
variable [Fintype (VerticalEdge M A)] [Fintype (MixedFace M A)]
variable [DecidableEq (Nf.ChartInTargetSubset (comparisonFactor qc qf h ⁻¹' A))] [DecidableEq (Nf.EdgeInTargetSubset (comparisonFactor qc qf h ⁻¹' A))]

/-- E degree-0 P differential table is generated from the same original
fine differential and the original primitive annihilator projections. -/
def nativeP0Differential : Matrix (Nf.EdgeInTargetSubset (comparisonFactor qc qf h ⁻¹' A)) (Nf.ChartInTargetSubset (comparisonFactor qc qf h ⁻¹' A)) ℚ :=
  nativeP1Projection M A * primitiveD0Matrix Nf _ * nativeP0Projection M A

/-- Owner full ambient-vector formula exposes only original fine differential
and generated projections, without assuming their compatibility. -/
theorem nativeP0Differential_mulVec (x : Nf.ChartInTargetSubset (comparisonFactor qc qf h ⁻¹' A) → ℚ) :
    nativeP0Differential M A *ᵥ x =
      nativeP1Projection M A *ᵥ ((Nf.targetSubsetComplex _).d0 (nativeP0Projection M A *ᵥ x)) := by
  rw [nativeP0Differential, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
    primitiveD0Matrix_mulVec]

/-- E native P degree-0 differential is represented on every original
Kan vector by the generated table, via its actual evaluation map. -/
theorem nativeP0Differential_represents (x : (pushforwardComplex M A).C0) :
    nativeP0Differential M A *ᵥ
      (nativeP0CoordinateEquiv M A x : Nf.ChartInTargetSubset (comparisonFactor qc qf h ⁻¹' A) → ℚ) =
      (nativeP1CoordinateEquiv M A ((pushforwardComplex M A).d0 x) : Nf.EdgeInTargetSubset (comparisonFactor qc qf h ⁻¹' A) → ℚ) := by
  rw [nativeP0Differential_mulVec, nativeP0CoordinateEquiv_apply,
    nativeP0Projection_evaluation, ← evaluation_comm0, nativeP1Projection_evaluation,
    nativeP1CoordinateEquiv_apply]

/-- Owner P differential absorption holds on every fine vector, using C4's
actual Kan preimage; it is not an input projector compatibility premise. -/
theorem nativeP0Differential_all_representatives (x : Nf.ChartInTargetSubset (comparisonFactor qc qf h ⁻¹' A) → ℚ) :
    ∃ w : (pushforwardComplex M A).C0,
      evaluation0 M A w = nativeP0Projection M A *ᵥ x ∧
      nativeP0Differential M A *ᵥ x = evaluation1 M A ((pushforwardComplex M A).d0 w) := by
  obtain ⟨w, hw⟩ := nativeP0Projection_preimage M A x
  refine ⟨w, hw, ?_⟩
  rw [nativeP0Differential_mulVec, ← hw, ← evaluation_comm0, nativeP1Projection_evaluation]

/-- Owner generated P absorption is derived on all vectors from original
Kan preimages and original evaluation cochain compatibility. -/
theorem nativeP0Differential_absorption :
    nativeP0Differential M A = primitiveD0Matrix Nf _ * nativeP0Projection M A := by
  apply Matrix.ext_of_mulVec_single
  intro j
  rw [nativeP0Differential_mulVec, ← Matrix.mulVec_mulVec, primitiveD0Matrix_mulVec]
  obtain ⟨w, hw⟩ := nativeP0Projection_preimage M A (Pi.single j 1)
  rw [← hw, ← evaluation_comm0, nativeP1Projection_evaluation]

end P0

section Q0
variable [Fintype (Nf.ChartInTargetSubset (comparisonFactor qc qf h ⁻¹' A))] [Fintype (Nf.EdgeInTargetSubset (comparisonFactor qc qf h ⁻¹' A))]
variable [Fintype (VerticalEdge M A)] [Fintype (MixedFace M A)]
variable [DecidableEq (Nf.ChartInTargetSubset (comparisonFactor qc qf h ⁻¹' A))]

/-- E degree-0 Q differential table uses the same original fine map and
primitive L image projections, representing actual dual L rather than new Q. -/
def nativeQ0Differential : Matrix (Nf.EdgeInTargetSubset (comparisonFactor qc qf h ⁻¹' A)) (Nf.ChartInTargetSubset (comparisonFactor qc qf h ⁻¹' A)) ℚ :=
  nativeQ1Projection M A * primitiveD0Matrix Nf _ * nativeQ0Projection M A

/-- Owner Q table evaluates the original fine differential between generated
primitive image projections, for every ambient fine vector. -/
theorem nativeQ0Differential_mulVec (x : Nf.ChartInTargetSubset (comparisonFactor qc qf h ⁻¹' A) → ℚ) :
    nativeQ0Differential M A *ᵥ x =
      nativeQ1Projection M A *ᵥ ((Nf.targetSubsetComplex _).d0 (nativeQ0Projection M A *ᵥ x)) := by
  rw [nativeQ0Differential, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
    primitiveD0Matrix_mulVec]

/-- E the generated Q degree-0 table represents the differential of the
original dual-L Q on all original Q vectors, using actual restriction. -/
theorem nativeQ0Differential_represents (z : (restrictionComplex M A).C0) :
    nativeQ0Differential M A *ᵥ
      (nativeQ0CoordinateEquiv M A z : Nf.ChartInTargetSubset (comparisonFactor qc qf h ⁻¹' A) → ℚ) =
      (nativeQ1CoordinateEquiv M A ((restrictionComplex M A).d0 z) : Nf.EdgeInTargetSubset (comparisonFactor qc qf h ⁻¹' A) → ℚ) := by
  rw [nativeQ0Differential_mulVec, nativeQ0Projection_coordinate]
  obtain ⟨x, rfl⟩ := restriction0_surjective M A z
  rw [nativeQ0CoordinateEquiv_apply, ← nativeQ1CoordinateEquiv_apply,
    restriction_comm0, restriction0_nativeQProjection]

/-- Owner Q table represents the actual restricted native differential for
every fine representative, preserving its original Q class. -/
theorem nativeQ0Differential_all_representatives (x : Nf.ChartInTargetSubset (comparisonFactor qc qf h ⁻¹' A) → ℚ) :
    nativeQ0Differential M A *ᵥ x =
      (nativeQ1CoordinateEquiv M A
        ((restrictionComplex M A).d0 (restriction0 M A x)) : Nf.EdgeInTargetSubset (comparisonFactor qc qf h ⁻¹' A) → ℚ) := by
  rw [nativeQ0Differential_mulVec, ← nativeQ1CoordinateEquiv_apply,
    restriction_comm0, restriction0_nativeQProjection]

end Q0

section P1
variable [Fintype (Nf.EdgeInTargetSubset (comparisonFactor qc qf h ⁻¹' A))] [Fintype (Nf.FaceInTargetSubset (comparisonFactor qc qf h ⁻¹' A))]
variable [Fintype (VerticalEdge M A)] [Fintype (MixedFace M A)]
variable [Fintype (DegenerateFace M A)]
variable [DecidableEq (Nf.EdgeInTargetSubset (comparisonFactor qc qf h ⁻¹' A))] [DecidableEq (Nf.FaceInTargetSubset (comparisonFactor qc qf h ⁻¹' A))]

/-- E degree-1 P differential table is generated from the same original
fine differential and the original primitive annihilator projections. -/
def nativeP1Differential : Matrix (Nf.FaceInTargetSubset (comparisonFactor qc qf h ⁻¹' A)) (Nf.EdgeInTargetSubset (comparisonFactor qc qf h ⁻¹' A)) ℚ :=
  nativeP2Projection M A * primitiveD1Matrix Nf _ * nativeP1Projection M A

/-- Owner full ambient-vector formula exposes only original fine differential
and generated projections, without assuming their compatibility. -/
theorem nativeP1Differential_mulVec (x : Nf.EdgeInTargetSubset (comparisonFactor qc qf h ⁻¹' A) → ℚ) :
    nativeP1Differential M A *ᵥ x =
      nativeP2Projection M A *ᵥ ((Nf.targetSubsetComplex _).d1 (nativeP1Projection M A *ᵥ x)) := by
  rw [nativeP1Differential, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
    primitiveD1Matrix_mulVec]

/-- E native P degree-1 differential is represented on every original
Kan vector by the generated table, via its actual evaluation map. -/
theorem nativeP1Differential_represents (x : (pushforwardComplex M A).C1) :
    nativeP1Differential M A *ᵥ
      (nativeP1CoordinateEquiv M A x : Nf.EdgeInTargetSubset (comparisonFactor qc qf h ⁻¹' A) → ℚ) =
      (nativeP2CoordinateEquiv M A ((pushforwardComplex M A).d1 x) : Nf.FaceInTargetSubset (comparisonFactor qc qf h ⁻¹' A) → ℚ) := by
  rw [nativeP1Differential_mulVec, nativeP1CoordinateEquiv_apply,
    nativeP1Projection_evaluation, ← evaluation_comm1, nativeP2Projection_evaluation,
    nativeP2CoordinateEquiv_apply]

/-- Owner P differential absorption holds on every fine vector, using C4's
actual Kan preimage; it is not an input projector compatibility premise. -/
theorem nativeP1Differential_all_representatives (x : Nf.EdgeInTargetSubset (comparisonFactor qc qf h ⁻¹' A) → ℚ) :
    ∃ w : (pushforwardComplex M A).C1,
      evaluation1 M A w = nativeP1Projection M A *ᵥ x ∧
      nativeP1Differential M A *ᵥ x = evaluation2 M A ((pushforwardComplex M A).d1 w) := by
  obtain ⟨w, hw⟩ := nativeP1Projection_preimage M A x
  refine ⟨w, hw, ?_⟩
  rw [nativeP1Differential_mulVec, ← hw, ← evaluation_comm1, nativeP2Projection_evaluation]

/-- Owner generated P absorption is derived on all vectors from original
Kan preimages and original evaluation cochain compatibility. -/
theorem nativeP1Differential_absorption :
    nativeP1Differential M A = primitiveD1Matrix Nf _ * nativeP1Projection M A := by
  apply Matrix.ext_of_mulVec_single
  intro j
  rw [nativeP1Differential_mulVec, ← Matrix.mulVec_mulVec, primitiveD1Matrix_mulVec]
  obtain ⟨w, hw⟩ := nativeP1Projection_preimage M A (Pi.single j 1)
  rw [← hw, ← evaluation_comm1, nativeP2Projection_evaluation]

end P1

section Q1
variable [Fintype (Nf.EdgeInTargetSubset (comparisonFactor qc qf h ⁻¹' A))] [Fintype (Nf.FaceInTargetSubset (comparisonFactor qc qf h ⁻¹' A))]
variable [Fintype (VerticalEdge M A)] [Fintype (MixedFace M A)]
variable [Fintype (DegenerateFace M A)]
variable [DecidableEq (Nf.EdgeInTargetSubset (comparisonFactor qc qf h ⁻¹' A))]

/-- E degree-1 Q differential table uses the same original fine map and
primitive L image projections, representing actual dual L rather than new Q. -/
def nativeQ1Differential : Matrix (Nf.FaceInTargetSubset (comparisonFactor qc qf h ⁻¹' A)) (Nf.EdgeInTargetSubset (comparisonFactor qc qf h ⁻¹' A)) ℚ :=
  nativeQ2Projection M A * primitiveD1Matrix Nf _ * nativeQ1Projection M A

/-- Owner Q table evaluates the original fine differential between generated
primitive image projections, for every ambient fine vector. -/
theorem nativeQ1Differential_mulVec (x : Nf.EdgeInTargetSubset (comparisonFactor qc qf h ⁻¹' A) → ℚ) :
    nativeQ1Differential M A *ᵥ x =
      nativeQ2Projection M A *ᵥ ((Nf.targetSubsetComplex _).d1 (nativeQ1Projection M A *ᵥ x)) := by
  rw [nativeQ1Differential, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
    primitiveD1Matrix_mulVec]

/-- E the generated Q degree-1 table represents the differential of the
original dual-L Q on all original Q vectors, using actual restriction. -/
theorem nativeQ1Differential_represents (z : (restrictionComplex M A).C1) :
    nativeQ1Differential M A *ᵥ
      (nativeQ1CoordinateEquiv M A z : Nf.EdgeInTargetSubset (comparisonFactor qc qf h ⁻¹' A) → ℚ) =
      (nativeQ2CoordinateEquiv M A ((restrictionComplex M A).d1 z) : Nf.FaceInTargetSubset (comparisonFactor qc qf h ⁻¹' A) → ℚ) := by
  rw [nativeQ1Differential_mulVec, nativeQ1Projection_coordinate]
  obtain ⟨x, rfl⟩ := restriction1_surjective M A z
  rw [nativeQ1CoordinateEquiv_apply, ← nativeQ2CoordinateEquiv_apply,
    restriction_comm1, restriction1_nativeQProjection]

/-- Owner Q table represents the actual restricted native differential for
every fine representative, preserving its original Q class. -/
theorem nativeQ1Differential_all_representatives (x : Nf.EdgeInTargetSubset (comparisonFactor qc qf h ⁻¹' A) → ℚ) :
    nativeQ1Differential M A *ᵥ x =
      (nativeQ2CoordinateEquiv M A
        ((restrictionComplex M A).d1 (restriction1 M A x)) : Nf.FaceInTargetSubset (comparisonFactor qc qf h ⁻¹' A) → ℚ) := by
  rw [nativeQ1Differential_mulVec, ← nativeQ2CoordinateEquiv_apply,
    restriction_comm1, restriction1_nativeQProjection]

end Q1

section Squares
variable [Fintype (Nf.ChartInTargetSubset (comparisonFactor qc qf h ⁻¹' A))] [DecidableEq (Nf.ChartInTargetSubset (comparisonFactor qc qf h ⁻¹' A))]
variable [Fintype (Nf.EdgeInTargetSubset (comparisonFactor qc qf h ⁻¹' A))] [DecidableEq (Nf.EdgeInTargetSubset (comparisonFactor qc qf h ⁻¹' A))]
variable [Fintype (Nf.FaceInTargetSubset (comparisonFactor qc qf h ⁻¹' A))] [DecidableEq (Nf.FaceInTargetSubset (comparisonFactor qc qf h ⁻¹' A))]
variable [Fintype (VerticalEdge M A)] [Fintype (MixedFace M A)] [Fintype (DegenerateFace M A)]

/-- E generated native P differential square vanishes on the whole ambient
table using original Kan representatives and the original P square theorem. -/
theorem nativeP1Differential_mul_P0 :
    nativeP1Differential M A * nativeP0Differential M A = 0 := by
  apply Matrix.ext_of_mulVec_single
  intro j
  rw [← Matrix.mulVec_mulVec, Matrix.zero_mulVec]
  obtain ⟨w, _, hw⟩ := nativeP0Differential_all_representatives M A (Pi.single j 1)
  rw [hw]
  have he := nativeP1Differential_represents M A ((pushforwardComplex M A).d0 w)
  rw [nativeP1CoordinateEquiv_apply, nativeP2CoordinateEquiv_apply] at he
  rw [he, (pushforwardComplex M A).d1_comp_d0, map_zero]

omit [DecidableEq (Nf.FaceInTargetSubset (comparisonFactor qc qf h ⁻¹' A))] in
/-- E generated native Q differential square vanishes on the whole ambient
table from actual dual-L differentials and full restriction representatives. -/
theorem nativeQ1Differential_mul_Q0 :
    nativeQ1Differential M A * nativeQ0Differential M A = 0 := by
  apply Matrix.ext_of_mulVec_single
  intro j
  rw [← Matrix.mulVec_mulVec, Matrix.zero_mulVec,
    nativeQ0Differential_all_representatives, nativeQ1Differential_represents,
    (restrictionComplex M A).d1_comp_d0, map_zero]
  rfl

end Squares

/-- Owner actual comparison component is the same original pullback,
derived from C3's full Hom factorization through the actual unit/evaluation. -/
theorem originalComparison_f0 : (M.aSubnerveComparisonHom A).f0 =
    M.targetSubsetPullback0 A (comparisonFactor qc qf h ⁻¹' A) (fun _ ht => ht) := by
  rw [aSubnerveComparisonHom_factorization]
  apply LinearMap.ext
  intro x
  rw [AtlasDefectComposition.cochainComp_f0, unitHom_f0, evaluationHom_f0, evaluation0_unit]
  rfl

section Comparison0
variable [Fintype (Nc.ChartInTargetSubset A)] [DecidableEq (Nc.ChartInTargetSubset A)]

/-- E actual degree-0 comparison table uses original named-cell Option
transport, including none cells and empty coarse cell types. -/
def primitiveComparison0Matrix : Matrix (Nf.ChartInTargetSubset (comparisonFactor qc qf h ⁻¹' A)) (Nc.ChartInTargetSubset A) ℚ :=
  cochainMatrix (M.targetSubsetPullback0 A (comparisonFactor qc qf h ⁻¹' A) (fun _ ht => ht))

/-- Owner whole-vector table represents the same original comparison Hom. -/
theorem primitiveComparison0Matrix_mulVec (x : (Nc.targetSubsetComplex A).C0) :
    primitiveComparison0Matrix M A *ᵥ x = (M.aSubnerveComparisonHom A).f0 x := by
  rw [primitiveComparison0Matrix, cochainMatrix_mulVec, originalComparison_f0]
  rfl

/-- Owner comparison entry is the original transported named single;
no expected rank or semantic preservation field contributes a column. -/
theorem primitiveComparison0Matrix_entry (i : Nf.ChartInTargetSubset (comparisonFactor qc qf h ⁻¹' A)) (j : Nc.ChartInTargetSubset A) :
    primitiveComparison0Matrix M A i j =
      M.targetSubsetPullback0 A (comparisonFactor qc qf h ⁻¹' A) (fun _ ht => ht) (Pi.single j 1) i :=
  cochainMatrix_entry _ i j

/-- Owner actual comparison entry reads its original cell transport table,
retaining every none/mapped cell and original name. -/
theorem primitiveComparison0Matrix_transport (i : Nf.ChartInTargetSubset (comparisonFactor qc qf h ⁻¹' A)) (j : Nc.ChartInTargetSubset A) :
    primitiveComparison0Matrix M A i j = (Pi.single j (1 : ℚ) : Nc.ChartInTargetSubset A → ℚ)
      (M.targetSubsetChartMap A (comparisonFactor qc qf h ⁻¹' A) (fun _ ht => ht) i) := by
  rw [primitiveComparison0Matrix_entry, M.targetSubsetPullback0_apply]

variable [Fintype (Nf.ChartInTargetSubset (comparisonFactor qc qf h ⁻¹' A))] [DecidableEq (Nf.ChartInTargetSubset (comparisonFactor qc qf h ⁻¹' A))]
variable [Fintype (VerticalEdge M A)]

/-- E the same degree-0 comparison table represents the actual Kan unit
on every original coarse vector, via the constructed native P coordinates. -/
theorem primitiveComparison0Matrix_unit (x : (Nc.targetSubsetComplex A).C0) :
    primitiveComparison0Matrix M A *ᵥ x =
      (nativeP0CoordinateEquiv M A ((unitHom M A).f0 x) : Nf.ChartInTargetSubset (comparisonFactor qc qf h ⁻¹' A) → ℚ) := by
  rw [primitiveComparison0Matrix, cochainMatrix_mulVec, unitHom_f0,
    nativeP0CoordinateEquiv_apply, evaluation0_unit]
  rfl

end Comparison0

section Evaluation0
variable [Fintype (Nf.ChartInTargetSubset (comparisonFactor qc qf h ⁻¹' A))] [DecidableEq (Nf.ChartInTargetSubset (comparisonFactor qc qf h ⁻¹' A))]
variable [Fintype (VerticalEdge M A)]

/-- E identity in the original cell coordinates represents actual epsilon
on the full original Kan space; its domain is the proved P image. -/
theorem nativeEvaluation0_represents (x : (pushforwardComplex M A).C0) :
    (1 : Matrix (Nf.ChartInTargetSubset (comparisonFactor qc qf h ⁻¹' A)) (Nf.ChartInTargetSubset (comparisonFactor qc qf h ⁻¹' A)) ℚ) *ᵥ
      (nativeP0CoordinateEquiv M A x : Nf.ChartInTargetSubset (comparisonFactor qc qf h ⁻¹' A) → ℚ) = (evaluationHom M A).f0 x := by
  rw [Matrix.one_mulVec, nativeP0CoordinateEquiv_apply, evaluationHom_f0]

omit [DecidableEq (Nf.ChartInTargetSubset (comparisonFactor qc qf h ⁻¹' A))] in
/-- E the same original L image projection represents actual restriction
Hom on every fine vector and preserves its original dual-L target. -/
theorem nativeRestriction0_represents (x : Nf.ChartInTargetSubset (comparisonFactor qc qf h ⁻¹' A) → ℚ) :
    nativeQ0Projection M A *ᵥ x =
      (nativeQ0CoordinateEquiv M A ((restrictionHom M A).f0 x) : Nf.ChartInTargetSubset (comparisonFactor qc qf h ⁻¹' A) → ℚ) := by
  rw [restrictionHom_f0]
  exact (nativeQ0CoordinateEquiv_apply M A x).symm

end Evaluation0

/-- Owner actual comparison component is the same original pullback,
derived from C3's full Hom factorization through the actual unit/evaluation. -/
theorem originalComparison_f1 : (M.aSubnerveComparisonHom A).f1 =
    M.targetSubsetPullback1 A (comparisonFactor qc qf h ⁻¹' A) (fun _ ht => ht) := by
  rw [aSubnerveComparisonHom_factorization]
  apply LinearMap.ext
  intro x
  rw [AtlasDefectComposition.cochainComp_f1, unitHom_f1, evaluationHom_f1, evaluation1_unit]
  rfl

section Comparison1
variable [Fintype (Nc.EdgeInTargetSubset A)] [DecidableEq (Nc.EdgeInTargetSubset A)]

/-- E actual degree-1 comparison table uses original named-cell Option
transport, including none cells and empty coarse cell types. -/
def primitiveComparison1Matrix : Matrix (Nf.EdgeInTargetSubset (comparisonFactor qc qf h ⁻¹' A)) (Nc.EdgeInTargetSubset A) ℚ :=
  cochainMatrix (M.targetSubsetPullback1 A (comparisonFactor qc qf h ⁻¹' A) (fun _ ht => ht))

/-- Owner whole-vector table represents the same original comparison Hom. -/
theorem primitiveComparison1Matrix_mulVec (x : (Nc.targetSubsetComplex A).C1) :
    primitiveComparison1Matrix M A *ᵥ x = (M.aSubnerveComparisonHom A).f1 x := by
  rw [primitiveComparison1Matrix, cochainMatrix_mulVec, originalComparison_f1]
  rfl

/-- Owner comparison entry is the original transported named single;
no expected rank or semantic preservation field contributes a column. -/
theorem primitiveComparison1Matrix_entry (i : Nf.EdgeInTargetSubset (comparisonFactor qc qf h ⁻¹' A)) (j : Nc.EdgeInTargetSubset A) :
    primitiveComparison1Matrix M A i j =
      M.targetSubsetPullback1 A (comparisonFactor qc qf h ⁻¹' A) (fun _ ht => ht) (Pi.single j 1) i :=
  cochainMatrix_entry _ i j

/-- Owner actual comparison entry reads its original cell transport table,
retaining every none/mapped cell and original name. -/
theorem primitiveComparison1Matrix_transport (i : Nf.EdgeInTargetSubset (comparisonFactor qc qf h ⁻¹' A)) (j : Nc.EdgeInTargetSubset A) :
    primitiveComparison1Matrix M A i j = (M.targetSubsetEdgeMapOption A (comparisonFactor qc qf h ⁻¹' A) (fun _ ht => ht) i).elim
      0 (Pi.single j (1 : ℚ) : Nc.EdgeInTargetSubset A → ℚ) := by
  rw [primitiveComparison1Matrix_entry, M.targetSubsetPullback1_apply]

variable [Fintype (Nf.EdgeInTargetSubset (comparisonFactor qc qf h ⁻¹' A))] [DecidableEq (Nf.EdgeInTargetSubset (comparisonFactor qc qf h ⁻¹' A))]
variable [Fintype (VerticalEdge M A)] [Fintype (MixedFace M A)]

/-- E the same degree-1 comparison table represents the actual Kan unit
on every original coarse vector, via the constructed native P coordinates. -/
theorem primitiveComparison1Matrix_unit (x : (Nc.targetSubsetComplex A).C1) :
    primitiveComparison1Matrix M A *ᵥ x =
      (nativeP1CoordinateEquiv M A ((unitHom M A).f1 x) : Nf.EdgeInTargetSubset (comparisonFactor qc qf h ⁻¹' A) → ℚ) := by
  rw [primitiveComparison1Matrix, cochainMatrix_mulVec, unitHom_f1,
    nativeP1CoordinateEquiv_apply, evaluation1_unit]
  rfl

end Comparison1

section Evaluation1
variable [Fintype (Nf.EdgeInTargetSubset (comparisonFactor qc qf h ⁻¹' A))] [DecidableEq (Nf.EdgeInTargetSubset (comparisonFactor qc qf h ⁻¹' A))]
variable [Fintype (VerticalEdge M A)] [Fintype (MixedFace M A)]

/-- E identity in the original cell coordinates represents actual epsilon
on the full original Kan space; its domain is the proved P image. -/
theorem nativeEvaluation1_represents (x : (pushforwardComplex M A).C1) :
    (1 : Matrix (Nf.EdgeInTargetSubset (comparisonFactor qc qf h ⁻¹' A)) (Nf.EdgeInTargetSubset (comparisonFactor qc qf h ⁻¹' A)) ℚ) *ᵥ
      (nativeP1CoordinateEquiv M A x : Nf.EdgeInTargetSubset (comparisonFactor qc qf h ⁻¹' A) → ℚ) = (evaluationHom M A).f1 x := by
  rw [Matrix.one_mulVec, nativeP1CoordinateEquiv_apply, evaluationHom_f1]

omit [DecidableEq (Nf.EdgeInTargetSubset (comparisonFactor qc qf h ⁻¹' A))] in
/-- E the same original L image projection represents actual restriction
Hom on every fine vector and preserves its original dual-L target. -/
theorem nativeRestriction1_represents (x : Nf.EdgeInTargetSubset (comparisonFactor qc qf h ⁻¹' A) → ℚ) :
    nativeQ1Projection M A *ᵥ x =
      (nativeQ1CoordinateEquiv M A ((restrictionHom M A).f1 x) : Nf.EdgeInTargetSubset (comparisonFactor qc qf h ⁻¹' A) → ℚ) := by
  rw [restrictionHom_f1]
  exact (nativeQ1CoordinateEquiv_apply M A x).symm

end Evaluation1

/-- Owner actual comparison component is the same original pullback,
derived from C3's full Hom factorization through the actual unit/evaluation. -/
theorem originalComparison_f2 : (M.aSubnerveComparisonHom A).f2 =
    M.targetSubsetPullback2 A (comparisonFactor qc qf h ⁻¹' A) (fun _ ht => ht) := by
  rw [aSubnerveComparisonHom_factorization]
  apply LinearMap.ext
  intro x
  rw [AtlasDefectComposition.cochainComp_f2, unitHom_f2, evaluationHom_f2, evaluation2_unit]
  rfl

section Comparison2
variable [Fintype (Nc.FaceInTargetSubset A)] [DecidableEq (Nc.FaceInTargetSubset A)]

/-- E actual degree-2 comparison table uses original named-cell Option
transport, including none cells and empty coarse cell types. -/
def primitiveComparison2Matrix : Matrix (Nf.FaceInTargetSubset (comparisonFactor qc qf h ⁻¹' A)) (Nc.FaceInTargetSubset A) ℚ :=
  cochainMatrix (M.targetSubsetPullback2 A (comparisonFactor qc qf h ⁻¹' A) (fun _ ht => ht))

/-- Owner whole-vector table represents the same original comparison Hom. -/
theorem primitiveComparison2Matrix_mulVec (x : (Nc.targetSubsetComplex A).C2) :
    primitiveComparison2Matrix M A *ᵥ x = (M.aSubnerveComparisonHom A).f2 x := by
  rw [primitiveComparison2Matrix, cochainMatrix_mulVec, originalComparison_f2]
  rfl

/-- Owner comparison entry is the original transported named single;
no expected rank or semantic preservation field contributes a column. -/
theorem primitiveComparison2Matrix_entry (i : Nf.FaceInTargetSubset (comparisonFactor qc qf h ⁻¹' A)) (j : Nc.FaceInTargetSubset A) :
    primitiveComparison2Matrix M A i j =
      M.targetSubsetPullback2 A (comparisonFactor qc qf h ⁻¹' A) (fun _ ht => ht) (Pi.single j 1) i :=
  cochainMatrix_entry _ i j

/-- Owner actual comparison entry reads its original cell transport table,
retaining every none/mapped cell and original name. -/
theorem primitiveComparison2Matrix_transport (i : Nf.FaceInTargetSubset (comparisonFactor qc qf h ⁻¹' A)) (j : Nc.FaceInTargetSubset A) :
    primitiveComparison2Matrix M A i j = (M.targetSubsetFaceMapOption A (comparisonFactor qc qf h ⁻¹' A) (fun _ ht => ht) i).elim
      0 (Pi.single j (1 : ℚ) : Nc.FaceInTargetSubset A → ℚ) := by
  rw [primitiveComparison2Matrix_entry, M.targetSubsetPullback2_apply]

variable [Fintype (Nf.FaceInTargetSubset (comparisonFactor qc qf h ⁻¹' A))] [DecidableEq (Nf.FaceInTargetSubset (comparisonFactor qc qf h ⁻¹' A))]
variable [Fintype (DegenerateFace M A)]

/-- E the same degree-2 comparison table represents the actual Kan unit
on every original coarse vector, via the constructed native P coordinates. -/
theorem primitiveComparison2Matrix_unit (x : (Nc.targetSubsetComplex A).C2) :
    primitiveComparison2Matrix M A *ᵥ x =
      (nativeP2CoordinateEquiv M A ((unitHom M A).f2 x) : Nf.FaceInTargetSubset (comparisonFactor qc qf h ⁻¹' A) → ℚ) := by
  rw [primitiveComparison2Matrix, cochainMatrix_mulVec, unitHom_f2,
    nativeP2CoordinateEquiv_apply, evaluation2_unit]
  rfl

end Comparison2

section Evaluation2
variable [Fintype (Nf.FaceInTargetSubset (comparisonFactor qc qf h ⁻¹' A))] [DecidableEq (Nf.FaceInTargetSubset (comparisonFactor qc qf h ⁻¹' A))]
variable [Fintype (DegenerateFace M A)]

/-- E identity in the original cell coordinates represents actual epsilon
on the full original Kan space; its domain is the proved P image. -/
theorem nativeEvaluation2_represents (x : (pushforwardComplex M A).C2) :
    (1 : Matrix (Nf.FaceInTargetSubset (comparisonFactor qc qf h ⁻¹' A)) (Nf.FaceInTargetSubset (comparisonFactor qc qf h ⁻¹' A)) ℚ) *ᵥ
      (nativeP2CoordinateEquiv M A x : Nf.FaceInTargetSubset (comparisonFactor qc qf h ⁻¹' A) → ℚ) = (evaluationHom M A).f2 x := by
  rw [Matrix.one_mulVec, nativeP2CoordinateEquiv_apply, evaluationHom_f2]

omit [DecidableEq (Nf.FaceInTargetSubset (comparisonFactor qc qf h ⁻¹' A))] in
/-- E the same original L image projection represents actual restriction
Hom on every fine vector and preserves its original dual-L target. -/
theorem nativeRestriction2_represents (x : Nf.FaceInTargetSubset (comparisonFactor qc qf h ⁻¹' A) → ℚ) :
    nativeQ2Projection M A *ᵥ x =
      (nativeQ2CoordinateEquiv M A ((restrictionHom M A).f2 x) : Nf.FaceInTargetSubset (comparisonFactor qc qf h ⁻¹' A) → ℚ) := by
  rw [restrictionHom_f2]
  exact (nativeQ2CoordinateEquiv_apply M A x).symm

end Evaluation2

end AAT.AG.AtlasCoefficientFiber

#print axioms AAT.AG.AtlasCoefficientFiber.cochainMatrix
#print axioms AAT.AG.AtlasCoefficientFiber.cochainMatrix_entry
#print axioms AAT.AG.AtlasCoefficientFiber.cochainMatrix_mulVec
#print axioms AAT.AG.AtlasCoefficientFiber.primitiveD0Matrix
#print axioms AAT.AG.AtlasCoefficientFiber.primitiveD0Matrix_entry
#print axioms AAT.AG.AtlasCoefficientFiber.primitiveD0Matrix_mulVec
#print axioms AAT.AG.AtlasCoefficientFiber.primitiveD1Matrix
#print axioms AAT.AG.AtlasCoefficientFiber.primitiveD1Matrix_entry
#print axioms AAT.AG.AtlasCoefficientFiber.primitiveD1Matrix_mulVec
#print axioms AAT.AG.AtlasCoefficientFiber.primitiveD1Matrix_mul_D0
#print axioms AAT.AG.AtlasCoefficientFiber.nativeP0Differential
#print axioms AAT.AG.AtlasCoefficientFiber.nativeP0Differential_mulVec
#print axioms AAT.AG.AtlasCoefficientFiber.nativeP0Differential_represents
#print axioms AAT.AG.AtlasCoefficientFiber.nativeP0Differential_all_representatives
#print axioms AAT.AG.AtlasCoefficientFiber.nativeP0Differential_absorption
#print axioms AAT.AG.AtlasCoefficientFiber.nativeQ0Differential
#print axioms AAT.AG.AtlasCoefficientFiber.nativeQ0Differential_mulVec
#print axioms AAT.AG.AtlasCoefficientFiber.nativeQ0Differential_represents
#print axioms AAT.AG.AtlasCoefficientFiber.nativeQ0Differential_all_representatives
#print axioms AAT.AG.AtlasCoefficientFiber.nativeP1Differential
#print axioms AAT.AG.AtlasCoefficientFiber.nativeP1Differential_mulVec
#print axioms AAT.AG.AtlasCoefficientFiber.nativeP1Differential_represents
#print axioms AAT.AG.AtlasCoefficientFiber.nativeP1Differential_all_representatives
#print axioms AAT.AG.AtlasCoefficientFiber.nativeP1Differential_absorption
#print axioms AAT.AG.AtlasCoefficientFiber.nativeQ1Differential
#print axioms AAT.AG.AtlasCoefficientFiber.nativeQ1Differential_mulVec
#print axioms AAT.AG.AtlasCoefficientFiber.nativeQ1Differential_represents
#print axioms AAT.AG.AtlasCoefficientFiber.nativeQ1Differential_all_representatives
#print axioms AAT.AG.AtlasCoefficientFiber.nativeP1Differential_mul_P0
#print axioms AAT.AG.AtlasCoefficientFiber.nativeQ1Differential_mul_Q0
#print axioms AAT.AG.AtlasCoefficientFiber.originalComparison_f0
#print axioms AAT.AG.AtlasCoefficientFiber.primitiveComparison0Matrix
#print axioms AAT.AG.AtlasCoefficientFiber.primitiveComparison0Matrix_mulVec
#print axioms AAT.AG.AtlasCoefficientFiber.primitiveComparison0Matrix_entry
#print axioms AAT.AG.AtlasCoefficientFiber.primitiveComparison0Matrix_transport
#print axioms AAT.AG.AtlasCoefficientFiber.primitiveComparison0Matrix_unit
#print axioms AAT.AG.AtlasCoefficientFiber.nativeEvaluation0_represents
#print axioms AAT.AG.AtlasCoefficientFiber.nativeRestriction0_represents
#print axioms AAT.AG.AtlasCoefficientFiber.originalComparison_f1
#print axioms AAT.AG.AtlasCoefficientFiber.primitiveComparison1Matrix
#print axioms AAT.AG.AtlasCoefficientFiber.primitiveComparison1Matrix_mulVec
#print axioms AAT.AG.AtlasCoefficientFiber.primitiveComparison1Matrix_entry
#print axioms AAT.AG.AtlasCoefficientFiber.primitiveComparison1Matrix_transport
#print axioms AAT.AG.AtlasCoefficientFiber.primitiveComparison1Matrix_unit
#print axioms AAT.AG.AtlasCoefficientFiber.nativeEvaluation1_represents
#print axioms AAT.AG.AtlasCoefficientFiber.nativeRestriction1_represents
#print axioms AAT.AG.AtlasCoefficientFiber.originalComparison_f2
#print axioms AAT.AG.AtlasCoefficientFiber.primitiveComparison2Matrix
#print axioms AAT.AG.AtlasCoefficientFiber.primitiveComparison2Matrix_mulVec
#print axioms AAT.AG.AtlasCoefficientFiber.primitiveComparison2Matrix_entry
#print axioms AAT.AG.AtlasCoefficientFiber.primitiveComparison2Matrix_transport
#print axioms AAT.AG.AtlasCoefficientFiber.primitiveComparison2Matrix_unit
#print axioms AAT.AG.AtlasCoefficientFiber.nativeEvaluation2_represents
#print axioms AAT.AG.AtlasCoefficientFiber.nativeRestriction2_represents

#assert_standard_axioms_only AAT.AG.AtlasCoefficientFiber
