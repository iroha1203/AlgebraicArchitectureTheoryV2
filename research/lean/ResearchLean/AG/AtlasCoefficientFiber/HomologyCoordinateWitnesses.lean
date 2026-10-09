import ResearchLean.AG.AtlasCoefficientFiber.NativeDiagnosticMatrices
import ResearchLean.AG.AtlasCoefficientFiber.DegreeCoordinateWitnesses

/-!
# W3 original homology and transgression through the same producer

Position: G-135 E/W homology connection. Original named selected cells are
explicitly enumerated from the fixed primitive table. The computed native
homology and tau retain the original Kan P, dual-L Q and literal R.

## Implementation notes

Only primitive cell enumerations are input to the table producer. Entry
identification precedes calculation. Verified duplicate-column reductions use
the full range equality of the original table; they introduce no expected
rank or homology basis. The original nonzero connectingTau is also transported
by the all-R correctness theorem, preserving its sign and source.
-/
noncomputable section
namespace AAT.AG.AtlasCoefficientFiber.WitnessThree
open CanonicalResolution ResolutionInvariance FaceRelationSubdivision WitnessCommon Matrix
open RationalCoordinates AtlasDefectComposition
open AAT.AG.ResolutionInvariance.ExecutableRationalLinearAlgebra

/-- Owner selected chart has the same primitive W3 chart name. -/
def homologySelectedChart (i : Fin 3) : Nf.ChartInTargetSubset
    (comparisonFactor qc qf coarser ⁻¹' (Set.univ : Set Bool)) :=
  ⟨i, (false,false), Set.mem_univ _, Set.mem_univ _⟩

/-- Owner chart enumeration retains its raw name. -/
theorem homologySelectedChart_val (i : Fin 3) : (homologySelectedChart i).1 = i := rfl

/-- Full original selected chart enumeration with both inverses. -/
def homologyChartEquiv : Fin 3 ≃ Nf.ChartInTargetSubset
    (comparisonFactor qc qf coarser ⁻¹' (Set.univ : Set Bool)) where
  toFun := homologySelectedChart
  invFun := Subtype.val
  left_inv := homologySelectedChart_val
  right_inv x := Subtype.ext (homologySelectedChart_val x.1)

/-- Full original selected edge enumeration retains all six original names. -/
def homologyEdgeEquiv : Fin 6 ≃ Nf.EdgeInTargetSubset
    (comparisonFactor qc qf coarser ⁻¹' (Set.univ : Set Bool)) where
  toFun := selectedEdge
  invFun := Subtype.val
  left_inv := selectedEdge_val
  right_inv x := Subtype.ext (selectedEdge_val x.1)

/-- Actual original vertical edge is k, derived from the fixed Option table. -/
theorem homologyVertical_name (e : VerticalEdge M Set.univ) : e.1.1 = 5 :=
  (edgeMap_none_iff e.1.1).mp e.2

/-- Vertical enumeration has exactly the actual none edge, with both inverses. -/
def homologyVerticalEquiv : Fin 1 ≃ VerticalEdge M Set.univ where
  toFun _ := k
  invFun _ := 0
  left_inv i := Subsingleton.elim _ i
  right_inv e := by
    apply Subtype.ext
    apply Subtype.ext
    exact (selectedEdge_val 5).trans (homologyVertical_name e).symm

/-- Mixed enumeration has exactly the original relation m, with both inverses. -/
def homologyMixedEquiv : Fin 1 ≃ MixedFace M Set.univ where
  toFun _ := m
  invFun _ := 0
  left_inv i := Subsingleton.elim _ i
  right_inv f := (mixedFace_eq_m f).symm

/-- Original W3 chart enumeration is primitive input data. -/
local instance homologyChartFintype : Fintype (Nf.ChartInTargetSubset
    (comparisonFactor qc qf coarser ⁻¹' (Set.univ : Set Bool))) := Fintype.ofEquiv (Fin 3) homologyChartEquiv
/-- Original W3 edge enumeration is primitive input data. -/
local instance homologyEdgeFintype : Fintype (Nf.EdgeInTargetSubset
    (comparisonFactor qc qf coarser ⁻¹' (Set.univ : Set Bool))) := Fintype.ofEquiv (Fin 6) homologyEdgeEquiv
/-- Original W3 face enumeration is primitive input data. -/
local instance homologyFaceFintype : Fintype (Nf.FaceInTargetSubset
    (comparisonFactor qc qf coarser ⁻¹' (Set.univ : Set Bool))) := Fintype.ofEquiv (Fin 3) degreeFaceEquiv
/-- Original W3 vertical enumeration is generated from its Option table. -/
local instance homologyVerticalFintype : Fintype (VerticalEdge M Set.univ) := Fintype.ofEquiv (Fin 1) homologyVerticalEquiv
/-- Original W3 mixed enumeration is generated from its Option table. -/
local instance homologyMixedFintype : Fintype (MixedFace M Set.univ) := Fintype.ofEquiv (Fin 1) homologyMixedEquiv
/-- Original W3 none-face enumeration is generated from its Option table. -/
local instance homologyNoneFaceFintype : Fintype (DegenerateFace M Set.univ) := Fintype.ofEquiv (Fin 1) degreeNoneFaceEquiv
/-- Original chart equality is its finite underlying named-cell equality. -/
local instance homologyChartDecidableEq : DecidableEq (Nf.ChartInTargetSubset
    (comparisonFactor qc qf coarser ⁻¹' (Set.univ : Set Bool))) := inferInstance
/-- Original edge equality is its finite underlying named-cell equality. -/
local instance homologyEdgeDecidableEq : DecidableEq (Nf.EdgeInTargetSubset
    (comparisonFactor qc qf coarser ⁻¹' (Set.univ : Set Bool))) := inferInstance
/-- Original face equality is its finite underlying named-cell equality. -/
local instance homologyFaceDecidableEq : DecidableEq (Nf.FaceInTargetSubset
    (comparisonFactor qc qf coarser ⁻¹' (Set.univ : Set Bool))) := inferInstance

/-- W3 same-producer literal R coordinates have both original inverses. -/
theorem originalR_coordinate_inverses (x : R M Set.univ)
    (y : LinearMap.range (nativeQ1HomologyProjection M Set.univ).mulVecLin) :
    (nativeRCoordinateEquiv M Set.univ).symm (nativeRCoordinateEquiv M Set.univ x) = x ∧
      nativeRCoordinateEquiv M Set.univ ((nativeRCoordinateEquiv M Set.univ).symm y) = y :=
  ⟨(nativeRCoordinateEquiv M Set.univ).symm_apply_apply x,
    (nativeRCoordinateEquiv M Set.univ).apply_symm_apply y⟩

/-- W3 original nonzero transgression is retained by the very same generated
tau matrix; zero matrix would contradict its all-R representation. -/
theorem originalTauMatrix_ne_zero : nativeTauMatrix M Set.univ ≠ 0 := by
  intro hz
  apply connectingTau_ne_zero
  apply LinearMap.ext
  intro x
  apply (nativeP2StandardHomologyCoordinateEquiv M Set.univ).injective
  apply Subtype.ext
  rw [nativeTauMatrix_connectingTau, hz, Matrix.zero_mulVec]
  simp only [LinearMap.zero_apply, map_zero]
  rfl

/-- Original L1 table has its vertical single and full mixed signed boundary. -/
def homologyL1Table : Matrix (Nf.EdgeInTargetSubset
    (comparisonFactor qc qf coarser ⁻¹' (Set.univ : Set Bool)))
    (VerticalEdge M Set.univ ⊕ MixedFace M Set.univ) ℚ :=
  fun i j => match j with
  | .inl _ => if i.1 = 5 then 1 else 0
  | .inr _ => (if i.1 = 5 then 1 else 0) - (if i.1 = 1 then 1 else 0) +
      (if i.1 = 0 then 1 else 0)

/-- Owner vertical table entry keeps k's primitive single. -/
theorem homologyL1Table_inl (i : Nf.EdgeInTargetSubset
    (comparisonFactor qc qf coarser ⁻¹' (Set.univ : Set Bool))) (e : VerticalEdge M Set.univ) :
    homologyL1Table i (.inl e) = if i.1 = 5 then 1 else 0 := rfl

/-- Owner mixed table entry keeps all three signed m occurrences. -/
theorem homologyL1Table_inr (i : Nf.EdgeInTargetSubset
    (comparisonFactor qc qf coarser ⁻¹' (Set.univ : Set Bool))) (f : MixedFace M Set.univ) :
    homologyL1Table i (.inr f) = (if i.1 = 5 then 1 else 0) -
      (if i.1 = 1 then 1 else 0) + (if i.1 = 0 then 1 else 0) := rfl

/-- Whole original primitive L1 table equals the computational primitive table. -/
theorem primitiveL1Matrix_eq_homologyTable : primitiveL1Matrix M Set.univ = homologyL1Table := by
  ext i j
  cases j with
  | inl e =>
    rw [primitiveL1Matrix_entry_inl, homologyL1Table_inl]
    have heq : e.1 = i ↔ i.1 = 5 := by
      constructor
      · intro hi
        exact (congrArg Subtype.val hi).symm.trans (homologyVertical_name e)
      · intro hi
        apply Subtype.ext
        exact (homologyVertical_name e).trans hi.symm
    simp only [Finsupp.single_apply, heq]
  | inr f =>
    rw [primitiveL1Matrix_entry_inr, mixedFace_eq_m f, m_edge0, m_edge1, m_edge2,
      homologyL1Table_inr]
    have h5 : k.1.1 = 5 := homologyVertical_name k
    have h1 : a1.1.1 = 1 := selectedEdge_val 1
    have h0 : a0.1.1 = 0 := selectedEdge_val 0
    simp only [Finsupp.add_apply, Finsupp.sub_apply, Finsupp.single_apply, Subtype.ext_iff]
    have h5i : k.1.1 = i.1 ↔ i.1 = 5 :=
      ⟨fun hi => hi.symm.trans h5, fun hi => h5.trans hi.symm⟩
    have h1i : a1.1.1 = i.1 ↔ i.1 = 1 :=
      ⟨fun hi => hi.symm.trans h1, fun hi => h1.trans hi.symm⟩
    have h0i : a0.1.1 = i.1 ↔ i.1 = 0 :=
      ⟨fun hi => hi.symm.trans h0, fun hi => h0.trans hi.symm⟩
    simp only [h5i, h1i, h0i]

/-- W3 same-producer degree-one image evaluates the actual two primitive columns. -/
theorem homologyL1Table_image : imageProjection homologyL1Table =
    fun i j => if i.1 = 5 ∧ j.1 = 5 then 1 else
      if (i.1 = 0 ∨ i.1 = 1) ∧ (j.1 = 0 ∨ j.1 = 1) then
        (if i.1 = j.1 then (1/2 : ℚ) else -1/2) else 0 := by
  decide +kernel

/-- W3 original P1 projection comes from the same original columns. -/
theorem homologyP1Projection : nativeP1Projection M Set.univ =
    fun i j => if i.1 = j.1 ∧ (i.1 = 2 ∨ i.1 = 3 ∨ i.1 = 4) then 1 else
      if (i.1 = 0 ∨ i.1 = 1) ∧ (j.1 = 0 ∨ j.1 = 1) then (1/2 : ℚ) else 0 := by
  rw [nativeP1Projection_eq, kernelProjection_eq_complement, Matrix.transpose_transpose,
    primitiveL1Matrix_eq_homologyTable, homologyL1Table_image]
  decide +kernel

/-- W3 original Q1 projection comes from the same original columns. -/
theorem homologyQ1Projection : nativeQ1Projection M Set.univ =
    fun i j => if i.1 = 5 ∧ j.1 = 5 then 1 else
      if (i.1 = 0 ∨ i.1 = 1) ∧ (j.1 = 0 ∨ j.1 = 1) then
        (if i.1 = j.1 then (1/2 : ℚ) else -1/2) else 0 := by
  rw [nativeQ1Projection_eq, primitiveL1Matrix_eq_homologyTable, homologyL1Table_image]

/-- Computation-ready fine differential contains every signed original
boundary occurrence, including the two a names of the mixed face. -/
def homologyD1Table : Matrix (Nf.FaceInTargetSubset
    (comparisonFactor qc qf coarser ⁻¹' (Set.univ : Set Bool)))
    (Nf.EdgeInTargetSubset (comparisonFactor qc qf coarser ⁻¹' (Set.univ : Set Bool))) ℚ :=
  fun f e => if f.1 = 0 then ![1,0,-1,1,0,0] e.1 else
    if f.1 = 1 then ![0,1,-1,1,0,0] e.1 else ![1,-1,0,0,0,1] e.1

/-- Owner raw differential entry is the fixed three-occurrence cell formula. -/
theorem homologyD1Table_entry (f : Nf.FaceInTargetSubset
    (comparisonFactor qc qf coarser ⁻¹' (Set.univ : Set Bool)))
    (e : Nf.EdgeInTargetSubset (comparisonFactor qc qf coarser ⁻¹' (Set.univ : Set Bool))) :
    homologyD1Table f e = if f.1 = 0 then ![1,0,-1,1,0,0] e.1 else
      if f.1 = 1 then ![0,1,-1,1,0,0] e.1 else ![1,-1,0,0,0,1] e.1 := rfl

/-- Original whole fine d1 table equals its computation-ready raw table. -/
theorem primitiveD1Matrix_eq_homologyTable :
    primitiveD1Matrix Nf (comparisonFactor qc qf coarser ⁻¹' (Set.univ : Set Bool)) = homologyD1Table := by
  ext f e
  rw [primitiveD1Matrix_entry, homologyD1Table_entry]
  obtain ⟨i, rfl⟩ := degreeFaceEquiv.surjective f
  obtain ⟨j, rfl⟩ := homologyEdgeEquiv.surjective e
  fin_cases i <;> fin_cases j <;> decide +kernel

/-- Original P2 projection evaluates the same none-face producer. -/
theorem homologyP2Projection : nativeP2Projection M Set.univ =
    fun i j => if i.1 = j.1 ∧ i.1 ≠ 2 then 1 else 0 := by
  rw [nativeP2Projection_eq, primitiveL2Matrix_eq_degreeL2Table, degreeL2Table_annihilator]

/-- Original Q2 projection evaluates the same none-face producer. -/
theorem homologyQ2Projection : nativeQ2Projection M Set.univ =
    fun i j => if i.1 = 2 ∧ j.1 = 2 then 1 else 0 := by
  rw [nativeQ2Projection_eq, primitiveL2Matrix_eq_degreeL2Table, degreeL2Table_image]

/-- Complete original P incoming top table, after its generated projections. -/
def homologyP1DifferentialTable : Matrix (Nf.FaceInTargetSubset
    (comparisonFactor qc qf coarser ⁻¹' (Set.univ : Set Bool)))
    (Nf.EdgeInTargetSubset (comparisonFactor qc qf coarser ⁻¹' (Set.univ : Set Bool))) ℚ :=
  fun f e => if f.1 = 2 then 0 else ![(1/2 : ℚ),1/2,-1,1,0,0] e.1

/-- Owner computed original incoming entry keeps its original cell indices. -/
theorem homologyP1DifferentialTable_entry (f : Nf.FaceInTargetSubset
    (comparisonFactor qc qf coarser ⁻¹' (Set.univ : Set Bool)))
    (e : Nf.EdgeInTargetSubset (comparisonFactor qc qf coarser ⁻¹' (Set.univ : Set Bool))) :
    homologyP1DifferentialTable f e = if f.1 = 2 then 0 else ![(1/2 : ℚ),1/2,-1,1,0,0] e.1 := rfl

/-- Original all-vector d1 owner API proves equality of the complete native
incoming table, not only the selected representative columns. -/
theorem nativeP1Differential_eq_homologyTable :
    nativeP1Differential M Set.univ = homologyP1DifferentialTable := by
  have he : nativeP1Differential M Set.univ =
      nativeP2Projection M Set.univ *
        primitiveD1Matrix Nf (comparisonFactor qc qf coarser ⁻¹' (Set.univ : Set Bool)) *
          nativeP1Projection M Set.univ := by
    apply Matrix.mulVec_injective
    funext x
    rw [nativeP1Differential_mulVec, ← primitiveD1Matrix_mulVec,
      ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
  rw [he, homologyP2Projection, primitiveD1Matrix_eq_homologyTable, homologyP1Projection]
  decide +kernel

/-- Verified primitive one-column table spans the full original incoming
image. This is column elimination after all original entries are identified. -/
def homologyP2IncomingColumn : Matrix (Nf.FaceInTargetSubset
    (comparisonFactor qc qf coarser ⁻¹' (Set.univ : Set Bool))) (Fin 1) ℚ :=
  fun f _ => if f.1 = 2 then 0 else 1

/-- Owner primitive column formula keeps the two mapped face coordinates. -/
theorem homologyP2IncomingColumn_entry (f : Nf.FaceInTargetSubset
    (comparisonFactor qc qf coarser ⁻¹' (Set.univ : Set Bool))) (j : Fin 1) :
    homologyP2IncomingColumn f j = if f.1 = 2 then 0 else 1 := rfl

/-- Complete original incoming range equals the range of its verified
primitive column reduction, in both directions. -/
theorem homologyP2IncomingColumn_range :
    LinearMap.range homologyP1DifferentialTable.mulVecLin =
      LinearMap.range homologyP2IncomingColumn.mulVecLin := by
  apply le_antisymm
  · rintro _ ⟨x, rfl⟩
    refine ⟨fun _ => (homologyP1DifferentialTable *ᵥ x) (selectedFace 0), ?_⟩
    ext f
    obtain ⟨i, rfl⟩ := degreeFaceEquiv.surjective f
    fin_cases i <;>
      simp [Matrix.mulVec_eq_sum, homologyP1DifferentialTable_entry,
        homologyP2IncomingColumn_entry, selectedFace_val]
  · rintro _ ⟨x, rfl⟩
    refine ⟨Pi.single (selectedEdge 2) (-x 0), ?_⟩
    ext f
    simp only [Matrix.mulVecLin_apply]
    rw [Matrix.mulVec_single]
    simp only [Pi.smul_apply, Matrix.col_apply, op_smul_eq_smul, smul_eq_mul]
    rw [homologyP1DifferentialTable_entry, selectedEdge_val]
    obtain ⟨i, rfl⟩ := degreeFaceEquiv.surjective f
    fin_cases i <;> simp [Matrix.mulVec_eq_sum, homologyP2IncomingColumn_entry]

/-- Same generic producer evaluates the verified primitive incoming column. -/
theorem homologyP2IncomingColumn_image : imageProjection homologyP2IncomingColumn =
    fun i j => if i.1 ≠ 2 ∧ j.1 ≠ 2 then (1/2 : ℚ) else 0 := by
  decide +kernel

/-- Same producer computes original native P H2; no expected rank is input. -/
theorem homologyP2HomologyProjection : nativeP2HomologyProjection M Set.univ =
    fun i j => if i.1 ≠ 2 ∧ j.1 ≠ 2 then
      (if i.1 = j.1 then (1/2 : ℚ) else -1/2) else 0 := by
  rw [nativeP2HomologyProjection_eq, secondHomologyProjection_sub,
    homologyP2Projection, nativeP1Differential_eq_homologyTable,
    imageProjection_eq_of_range_eq _ _ homologyP2IncomingColumn_range,
    homologyP2IncomingColumn_image]
  decide +kernel

/-- W3 same-producer native top-homology rank is one, computed from its
full generated projection entries after verified primitive column reduction. -/
theorem homologyP2HomologyProjection_rank_one :
    rationalMatrixRank (nativeP2HomologyProjection M Set.univ) = 1 := by
  rw [homologyP2HomologyProjection]
  decide +kernel

/-- Same computed native coordinates give the dimension of the literal
original P2 incoming-boundary quotient. -/
theorem originalP2Homology_finrank :
    Module.finrank ℚ ((pushforwardComplex M Set.univ).C2 ⧸
      LinearMap.range (pushforwardComplex M Set.univ).d1) = 1 := by
  rw [← nativeP2HomologyProjection_rank]
  exact homologyP2HomologyProjection_rank_one

/-- The same computed dimension is the original standard P H2 dimension. -/
theorem originalP2StandardHomology_finrank :
    Module.finrank ℚ ((zeroExtension (pushforwardComplex M Set.univ)).homology (2 : ℤ)) = 1 := by
  rw [← (oldH2Equiv (pushforwardComplex M Set.univ)).finrank_eq]
  exact originalP2Homology_finrank

end AAT.AG.AtlasCoefficientFiber.WitnessThree

#print axioms AAT.AG.AtlasCoefficientFiber.WitnessThree.homologySelectedChart
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessThree.homologySelectedChart_val
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessThree.homologyChartEquiv
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessThree.homologyEdgeEquiv
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessThree.homologyVertical_name
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessThree.homologyVerticalEquiv
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessThree.homologyMixedEquiv
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessThree.homologyChartFintype
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessThree.homologyEdgeFintype
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessThree.homologyFaceFintype
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessThree.homologyVerticalFintype
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessThree.homologyMixedFintype
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessThree.homologyNoneFaceFintype
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessThree.homologyChartDecidableEq
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessThree.homologyEdgeDecidableEq
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessThree.homologyFaceDecidableEq
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessThree.originalR_coordinate_inverses
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessThree.originalTauMatrix_ne_zero
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessThree.homologyL1Table
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessThree.homologyL1Table_inl
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessThree.homologyL1Table_inr
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessThree.primitiveL1Matrix_eq_homologyTable
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessThree.homologyL1Table_image
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessThree.homologyP1Projection
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessThree.homologyQ1Projection
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessThree.homologyD1Table
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessThree.homologyD1Table_entry
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessThree.primitiveD1Matrix_eq_homologyTable
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessThree.homologyP2Projection
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessThree.homologyQ2Projection
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessThree.homologyP1DifferentialTable
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessThree.homologyP1DifferentialTable_entry
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessThree.nativeP1Differential_eq_homologyTable
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessThree.homologyP2IncomingColumn
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessThree.homologyP2IncomingColumn_entry
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessThree.homologyP2IncomingColumn_range
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessThree.homologyP2IncomingColumn_image
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessThree.homologyP2HomologyProjection
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessThree.homologyP2HomologyProjection_rank_one
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessThree.originalP2Homology_finrank
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessThree.originalP2StandardHomology_finrank

#assert_standard_axioms_only AAT.AG.AtlasCoefficientFiber.WitnessThree
