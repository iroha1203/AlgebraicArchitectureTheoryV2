import ResearchLean.AG.AtlasCoefficientFiber.WitnessThreeInput
import ResearchLean.AG.AtlasCoefficientFiber.TransgressionVanishing

/-!
# G-135 W3：原始消滅条件の否定例

## Implementation notes

指定表の選択済み原始セルをそのままFinsuppの基底とする。B・D・Hは既存の
原支持微分から評価し、期待するrankや商同型を入力しない。
τ非零を仮定して消滅条件を否定する案は非空虚性を放電しないため採用しない。
ここではmとf₀−f₁に対する原始式とBの実単射性から否定を生成する。
W3の全診断・全Law・錐評価は後続の同じ入力についての義務として残す。
-/
noncomputable section
namespace AAT.AG.AtlasCoefficientFiber.WitnessThree
open CanonicalResolution ResolutionInvariance FaceRelationSubdivision WitnessCommon

/-- 全支持で選択した同じ原始細辺。 -/
def selectedEdge (e : Fin 6) : Nf.EdgeInTargetSubset
    (comparisonFactor qc qf coarser ⁻¹' (Set.univ : Set Bool)) :=
  ⟨e, (false,false), ⟨Set.mem_univ _, Set.mem_univ _⟩, Set.mem_univ _⟩
/-- 全支持で選択した同じ原始細面。 -/
def selectedFace (f : Fin 3) : Nf.FaceInTargetSubset
    (comparisonFactor qc qf coarser ⁻¹' (Set.univ : Set Bool)) :=
  ⟨f, (false,false), ⟨⟨Set.mem_univ _, Set.mem_univ _⟩,
    ⟨Set.mem_univ _, Set.mem_univ _⟩, ⟨Set.mem_univ _, Set.mem_univ _⟩⟩, Set.mem_univ _⟩
/-- Owner selected-face API retains the same original Fin cell name.
This supports input-derived enumeration without unfolding selected supports. -/
theorem selectedFace_val (f : Fin 3) : (selectedFace f).1 = f := rfl

/-- 垂直loop kは同じnone辺。 -/
def k : VerticalEdge M Set.univ := ⟨selectedEdge 5, rfl⟩
/-- mapped辺a₀。 -/
def a0 : HorizontalEdge M Set.univ := ⟨selectedEdge 0, by simp [M, selectedEdge]⟩
/-- mapped辺a₁。 -/
def a1 : HorizontalEdge M Set.univ := ⟨selectedEdge 1, by simp [M, selectedEdge]⟩
/-- mapped辺b。 -/
def b : HorizontalEdge M Set.univ := ⟨selectedEdge 2, by simp [M, selectedEdge]⟩
/-- mapped辺c。 -/
def c : HorizontalEdge M Set.univ := ⟨selectedEdge 3, by simp [M, selectedEdge]⟩
/-- mapped面f₀は粗F₀へ送る。 -/
def f0 : HorizontalFace M Set.univ := ⟨selectedFace 0, by simp [M, selectedFace]⟩
/-- mapped面f₁は粗F₁へ送る。 -/
def f1 : HorizontalFace M Set.univ := ⟨selectedFace 1, by simp [M, selectedFace]⟩
/-- 混在面m=(k,a₁,a₀)。 -/
def m : MixedFace M Set.univ := ⟨selectedFace 2, rfl, 0, rfl⟩
/-- 元の二つのa出現は異なる細辺である。 -/
theorem a0_ne_a1 : a0 ≠ a1 := by
  intro h
  have hv := congrArg (fun e => e.1.1) h
  exact (by decide : (0 : Fin 6) ≠ 1) hv
/-- 全混在面は指定mであり、面名を失わない。 -/
theorem mixedFace_eq_m (f : MixedFace M Set.univ) : f = m := by
  apply Subtype.ext
  apply Subtype.ext
  rcases f with ⟨⟨f,hf⟩,hn,hm⟩
  fin_cases f <;> simp [M, m, selectedFace] at hn ⊢
/-- 指定表には垂直面がない。 -/
instance verticalFaceIsEmpty : IsEmpty (VerticalFace M Set.univ) where
  false f := by
    rcases f with ⟨⟨f,hf⟩,hn,h0,h1,h2⟩
    fin_cases f <;> simp [M] at hn h0 h1
/-- 指定mの原辺出現0を返す所有API。 -/
theorem m_edge0 : Nf.targetSubsetFaceEdge0
    (comparisonFactor qc qf coarser ⁻¹' (Set.univ : Set Bool)) m.1 = k.1 := by
  apply Subtype.ext
  rfl
/-- 指定mの原辺出現1を返す所有API。 -/
theorem m_edge1 : Nf.targetSubsetFaceEdge1
    (comparisonFactor qc qf coarser ⁻¹' (Set.univ : Set Bool)) m.1 = a1.1 := by
  apply Subtype.ext
  rfl
/-- 指定mの原辺出現2を返す所有API。 -/
theorem m_edge2 : Nf.targetSubsetFaceEdge2
    (comparisonFactor qc qf coarser ⁻¹' (Set.univ : Set Bool)) m.1 = a0.1 := by
  apply Subtype.ext
  rfl
/-- 指定f0の原辺出現0を返す所有API。 -/
theorem f0_edge0 : Nf.targetSubsetFaceEdge0
    (comparisonFactor qc qf coarser ⁻¹' (Set.univ : Set Bool)) f0.1 = a0.1 := by
  apply Subtype.ext
  rfl
/-- 指定f0の原辺出現1を返す所有API。 -/
theorem f0_edge1 : Nf.targetSubsetFaceEdge1
    (comparisonFactor qc qf coarser ⁻¹' (Set.univ : Set Bool)) f0.1 = b.1 := by
  apply Subtype.ext
  rfl
/-- 指定f0の原辺出現2を返す所有API。 -/
theorem f0_edge2 : Nf.targetSubsetFaceEdge2
    (comparisonFactor qc qf coarser ⁻¹' (Set.univ : Set Bool)) f0.1 = c.1 := by
  apply Subtype.ext
  rfl
/-- 指定f1の原辺出現0を返す所有API。 -/
theorem f1_edge0 : Nf.targetSubsetFaceEdge0
    (comparisonFactor qc qf coarser ⁻¹' (Set.univ : Set Bool)) f1.1 = a1.1 := by
  apply Subtype.ext
  rfl
/-- 指定f1の原辺出現1を返す所有API。 -/
theorem f1_edge1 : Nf.targetSubsetFaceEdge1
    (comparisonFactor qc qf coarser ⁻¹' (Set.univ : Set Bool)) f1.1 = b.1 := by
  apply Subtype.ext
  rfl
/-- 指定f1の原辺出現2を返す所有API。 -/
theorem f1_edge2 : Nf.targetSubsetFaceEdge2
    (comparisonFactor qc qf coarser ⁻¹' (Set.univ : Set Bool)) f1.1 = c.1 := by
  apply Subtype.ext
  rfl
/-- 同じ原混在微分の水平成分はa₀−a₁。 -/
theorem B_m : mixedHorizontalBoundary M Set.univ (Finsupp.single m 1) =
    Finsupp.single a0 1 - Finsupp.single a1 1 := by
  rw [mixedHorizontalBoundary_apply, mixedFaceInclusion_single, chainD2_single, one_smul,
    m_edge0, m_edge1, m_edge2]
  simp only [map_add, map_sub, horizontalEdgeProjection_vertical_single,
    horizontalEdgeProjection_single, zero_sub]
  abel
/-- 同じ原混在微分の垂直成分はk。 -/
theorem D_m : mixedVerticalBoundary M Set.univ (Finsupp.single m 1) =
    Finsupp.single k 1 := by
  rw [mixedVerticalBoundary_apply, mixedFaceInclusion_single, chainD2_single, one_smul,
    m_edge0, m_edge1, m_edge2]
  simp only [map_add, map_sub, verticalEdgeProjection_single,
    verticalEdgeProjection_horizontal_single, sub_zero, add_zero]
/-- f₀の原水平微分。 -/
theorem H_f0 : horizontalFaceBoundary M Set.univ (Finsupp.single f0 1) =
    Finsupp.single a0 1 - Finsupp.single b 1 + Finsupp.single c 1 := by
  rw [horizontalFaceBoundary_apply, horizontalFaceInclusion_single, chainD2_single, one_smul,
    f0_edge0, f0_edge1, f0_edge2]
  simp only [map_add, map_sub, horizontalEdgeProjection_single]
/-- f₁の原水平微分。 -/
theorem H_f1 : horizontalFaceBoundary M Set.univ (Finsupp.single f1 1) =
    Finsupp.single a1 1 - Finsupp.single b 1 + Finsupp.single c 1 := by
  rw [horizontalFaceBoundary_apply, horizontalFaceInclusion_single, chainD2_single, one_smul,
    f1_edge0, f1_edge1, f1_edge2]
  simp only [map_add, map_sub, horizontalEdgeProjection_single]
/-- 指定二面の差と同じmは原By=Hxを満たす。 -/
theorem B_m_eq_H_difference : mixedHorizontalBoundary M Set.univ (Finsupp.single m 1) =
    horizontalFaceBoundary M Set.univ (Finsupp.single f0 1 - Finsupp.single f1 1) := by
  rw [map_sub, H_f0, H_f1, B_m]
  abel
/-- 混在鎖は唯一の原面mの係数で復元する。 -/
theorem mixedChain_single (y : MixedFace M Set.univ →₀ ℚ) : y = Finsupp.single m (y m) := by
  classical
  ext f
  rw [mixedFace_eq_m f]
  simp
/-- 原Bの核は零であり、rankを入力として受け取らない。 -/
theorem B_kernel_zero (y : MixedFace M Set.univ →₀ ℚ)
    (hy : mixedHorizontalBoundary M Set.univ y = 0) : y = 0 := by
  classical
  have he : y = y m • Finsupp.single m 1 := by
    rw [Finsupp.smul_single, smul_eq_mul, mul_one]
    exact mixedChain_single y
  have hz := congrArg (fun x => x a0) hy
  rw [he, map_smul, B_m] at hz
  have hc : y m = 0 := by
    simpa only [Finsupp.smul_apply, Finsupp.sub_apply, Finsupp.single_eq_same,
      Finsupp.single_eq_of_ne a0_ne_a1, sub_zero, smul_eq_mul, mul_one,
      Finsupp.zero_apply] using hz
  rw [he, hc, zero_smul]
/-- mを除いた指定paired入力には混在面がない。 -/
instance pairedMixedIsEmpty : IsEmpty (MixedFace pairedM Set.univ) where
  false f := by cases f.2.1
/-- 指定paired原始入力の全支持は消滅条件を満たす。 -/
theorem primitiveTransgressionVanishing_paired_true :
    PrimitiveTransgressionVanishing pairedM Set.univ := by
  intro x y hy
  have he : y = 0 := Subsingleton.elim _ _
  refine ⟨0, 0, ?_⟩
  simp only [he, Submodule.coe_zero, map_zero, zero_add]
/-- 同じ具体入力の空支持では消滅条件を満たす。 -/
theorem primitiveTransgressionVanishing_empty_true : PrimitiveTransgressionVanishing M ∅ := by
  letI : IsEmpty (MixedFace M ∅) := ⟨fun f => by
    obtain ⟨t, _, ht⟩ := f.1.2
    exact ht⟩
  intro x y hy
  have he : y = 0 := Subsingleton.elim _ _
  refine ⟨0, 0, ?_⟩
  simp only [he, Submodule.coe_zero, map_zero, zero_add]
/-- 新規消滅述語の否定は指定原始W3表から生成する。 -/
theorem primitiveTransgressionVanishing_false : ¬ PrimitiveTransgressionVanishing M Set.univ := by
  intro hp
  obtain ⟨v,t,he⟩ := hp (Finsupp.single f0 1 - Finsupp.single f1 1)
    (Finsupp.single m 1) B_m_eq_H_difference
  have hv : v = 0 := Subsingleton.elim _ _
  have ht : t.1 = 0 := B_kernel_zero t.1 t.2
  rw [hv, ht, map_zero, map_zero, zero_add, D_m] at he
  have hh := congrArg (fun x => x k) he
  simp at hh
/-- 同じ実標準τは零写像でない。 -/
theorem connectingTau_ne_zero : connectingTau M Set.univ ≠ 0 := by
  intro h
  exact primitiveTransgressionVanishing_false ((connectingTau_zero_iff_primitive M Set.univ).mp h)

end AAT.AG.AtlasCoefficientFiber.WitnessThree
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessThree.selectedEdge
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessThree.selectedFace
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessThree.selectedFace_val
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessThree.k
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessThree.a0
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessThree.a1
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessThree.b
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessThree.c
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessThree.f0
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessThree.f1
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessThree.m
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessThree.a0_ne_a1
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessThree.mixedFace_eq_m
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessThree.verticalFaceIsEmpty
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessThree.m_edge0
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessThree.m_edge1
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessThree.m_edge2
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessThree.f0_edge0
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessThree.f0_edge1
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessThree.f0_edge2
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessThree.f1_edge0
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessThree.f1_edge1
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessThree.f1_edge2
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessThree.B_m
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessThree.D_m
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessThree.H_f0
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessThree.H_f1
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessThree.B_m_eq_H_difference
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessThree.mixedChain_single
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessThree.B_kernel_zero
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessThree.pairedMixedIsEmpty
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessThree.primitiveTransgressionVanishing_paired_true
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessThree.primitiveTransgressionVanishing_empty_true
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessThree.primitiveTransgressionVanishing_false
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessThree.connectingTau_ne_zero
#assert_standard_axioms_only AAT.AG.AtlasCoefficientFiber.WitnessThree
