import ResearchLean.AG.AtlasCoefficientFiber.DegenerateCells

/-!
# G-135 A §4：退化セルが生成するLの原始三次数

## Implementation notes

L₁には垂直辺と混在面の全境界を含める。L₂は分類済みの全退化面、
L₀は垂直辺境界の実像である。原支持chainへの包含と比較の零像を先に証明し、
完全性・homologyの期待値を構造fieldへ置かない。
-/
noncomputable section
namespace AAT.AG.AtlasCoefficientFiber
open CategoryTheory CanonicalResolution ResolutionInvariance FaceRelationSubdivision
universe u
variable {Source : Type u} {qc qf : Reading Source} {h : qc.CoarserThan qf}
variable {Nc : TargetSupportedNerve.{u, u} qc} {Nf : TargetSupportedNerve.{u, u} qf}
variable (M : IncidenceSupportedComparison qc qf h Nc Nf) (A : Set qc.Target)

/-- 指定L₀は垂直辺の原始境界の実像。 -/
def degenerateL0 : Submodule ℚ (K0 Nf (comparisonFactor qc qf h ⁻¹' A)) :=
  LinearMap.range ((chainD1 Nf (comparisonFactor qc qf h ⁻¹' A)).comp (verticalEdgeInclusion M A))

/-- 指定L₁は垂直辺の部分空間と混在面の全境界の和。 -/
def degenerateL1 : Submodule ℚ (K1 Nf (comparisonFactor qc qf h ⁻¹' A)) :=
  LinearMap.range (verticalEdgeInclusion M A) ⊔
    LinearMap.range ((chainD2 Nf (comparisonFactor qc qf h ⁻¹' A)).comp (mixedFaceInclusion M A))

/-- 指定L₂は分類済みF_v⊔F_mの自由部分空間。 -/
def degenerateL2 : Submodule ℚ (K2 Nf (comparisonFactor qc qf h ⁻¹' A)) :=
  LinearMap.range (degenerateFaceInclusion M A)

/-- L₀のmembershipを原始垂直辺chainの像で読む所有API。 -/
theorem mem_degenerateL0 (x : K0 Nf (comparisonFactor qc qf h ⁻¹' A)) :
    x ∈ degenerateL0 M A ↔ ∃ v, chainD1 Nf (comparisonFactor qc qf h ⁻¹' A)
      (verticalEdgeInclusion M A v) = x := Iff.rfl

/-- L₁のmembershipを垂直辺と混在境界の和で読む所有API。 -/
theorem mem_degenerateL1 (x : K1 Nf (comparisonFactor qc qf h ⁻¹' A)) :
    x ∈ degenerateL1 M A ↔ ∃ v m, verticalEdgeInclusion M A v +
      chainD2 Nf (comparisonFactor qc qf h ⁻¹' A) (mixedFaceInclusion M A m) = x := by
  constructor
  · rintro hx
    rcases Submodule.mem_sup.mp hx with ⟨v, ⟨w, hw⟩, m, ⟨f, hf⟩, hsum⟩
    exact ⟨w, f, by simpa only [← hw, ← hf, LinearMap.comp_apply] using hsum⟩
  · rintro ⟨v, m, rfl⟩
    exact Submodule.mem_sup.mpr ⟨_, ⟨v, rfl⟩, _, ⟨m, rfl⟩, rfl⟩

/-- L₂のmembershipは同じ退化面包含の実像。 -/
theorem mem_degenerateL2 (x : K2 Nf (comparisonFactor qc qf h ⁻¹' A)) :
    x ∈ degenerateL2 M A ↔ ∃ f, degenerateFaceInclusion M A f = x := Iff.rfl

/-- L₂を設計のF_vとF_mの和へ同定する。分類を入力にしない。 -/
theorem degenerateL2_vertical_mixed : degenerateL2 M A =
    LinearMap.range (verticalFaceInclusion M A) ⊔ LinearMap.range (mixedFaceInclusion M A) :=
  degenerateFaceInclusion_range_eq M A

/-- 垂直辺の部分空間は指定L₁に含まれる。 -/
theorem verticalEdge_range_le_L1 : LinearMap.range (verticalEdgeInclusion M A) ≤ degenerateL1 M A :=
  le_sup_left

/-- 混在面の境界の部分空間は指定L₁に含まれる。 -/
theorem mixedBoundary_range_le_L1 :
    LinearMap.range ((chainD2 Nf (comparisonFactor qc qf h ⁻¹' A)).comp (mixedFaceInclusion M A)) ≤
      degenerateL1 M A := le_sup_right

/-- 原始三辺と退化分類から、全L₂境界がL₁に入る。 -/
theorem degenerateL2_boundary_le :
    (degenerateL2 M A).map (chainD2 Nf (comparisonFactor qc qf h ⁻¹' A)) ≤ degenerateL1 M A := by
  rw [degenerateL2_vertical_mixed, Submodule.map_sup]
  apply sup_le
  · rw [← LinearMap.range_comp, ← verticalBoundary_inclusion]
    exact (LinearMap.range_comp_le_range _ _).trans (verticalEdge_range_le_L1 M A)
  · rw [← LinearMap.range_comp]
    exact mixedBoundary_range_le_L1 M A

/-- square-zeroによりL₁の境界の実像は指定L₀そのもの。H₀零性を仮定しない。 -/
theorem degenerateL1_boundary_eq :
    (degenerateL1 M A).map (chainD1 Nf (comparisonFactor qc qf h ⁻¹' A)) = degenerateL0 M A := by
  have hz : (chainD1 Nf (comparisonFactor qc qf h ⁻¹' A)).comp
      ((chainD2 Nf (comparisonFactor qc qf h ⁻¹' A)).comp (mixedFaceInclusion M A)) = 0 := by
    rw [← LinearMap.comp_assoc, chainD1_comp_chainD2, LinearMap.zero_comp]
  rw [degenerateL1, Submodule.map_sup, ← LinearMap.range_comp, ← LinearMap.range_comp,
    hz, LinearMap.range_zero, sup_bot_eq]
  rfl

/-- L₁からL₀への微分は原支持chain微分の実制限。 -/
def degenerateBoundary1 : degenerateL1 M A →ₗ[ℚ] degenerateL0 M A :=
  (chainD1 Nf (comparisonFactor qc qf h ⁻¹' A)).restrict (fun x hx =>
    (degenerateL1_boundary_eq M A).le ⟨x, hx, rfl⟩)

/-- L₂からL₁への微分は原支持chain微分の実制限。 -/
def degenerateBoundary2 : degenerateL2 M A →ₗ[ℚ] degenerateL1 M A :=
  (chainD2 Nf (comparisonFactor qc qf h ⁻¹' A)).restrict (fun x hx =>
    degenerateL2_boundary_le M A ⟨x, hx, rfl⟩)

/-- Lの第一微分の元支持chain上の値。 -/
@[simp] theorem degenerateBoundary1_val (x : degenerateL1 M A) :
    (degenerateBoundary1 M A x).1 = chainD1 Nf (comparisonFactor qc qf h ⁻¹' A) x.1 := rfl

/-- Lの第二微分の元支持chain上の値。 -/
@[simp] theorem degenerateBoundary2_val (x : degenerateL2 M A) :
    (degenerateBoundary2 M A x).1 = chainD2 Nf (comparisonFactor qc qf h ⁻¹' A) x.1 := rfl

/-- Lの二微分は元の同じchainのsquare-zeroから零になる。 -/
theorem degenerateBoundary_square : (degenerateBoundary1 M A).comp (degenerateBoundary2 M A) = 0 := by
  apply LinearMap.ext
  intro x
  apply Subtype.ext
  exact LinearMap.congr_fun (chainD1_comp_chainD2 Nf (comparisonFactor qc qf h ⁻¹' A)) x.1

/-- 原始L₀の像生成から、L₁境界の全射性を出力する。 -/
theorem degenerateBoundary1_surjective : Function.Surjective (degenerateBoundary1 M A) := by
  intro y
  obtain ⟨v, hv⟩ := (mem_degenerateL0 M A y.1).mp y.2
  refine ⟨⟨verticalEdgeInclusion M A v, verticalEdge_range_le_L1 M A ⟨v, rfl⟩⟩, ?_⟩
  apply Subtype.ext
  exact hv

/-- 垂直辺包含は同じMの支持chain比較で零となる。 -/
theorem verticalEdgeInclusion_map_zero :
    (M.supportedChainMap1 A (comparisonFactor qc qf h ⁻¹' A) (fun _ ht => ht)).comp
      (verticalEdgeInclusion M A) = 0 := by
  apply Finsupp.lhom_ext
  intro e r
  simp only [LinearMap.comp_apply, verticalEdgeInclusion_single, M.supportedChainMap1_single,
    M.targetSubsetEdgeMapOption_eq_none A _ _ e.1 e.2, rationalOptionCell_none, smul_zero,
    LinearMap.zero_apply]

/-- 全退化面包含は同じMの支持chain比較で零となる。 -/
theorem degenerateFaceInclusion_map_zero :
    (M.supportedChainMap2 A (comparisonFactor qc qf h ⁻¹' A) (fun _ ht => ht)).comp
      (degenerateFaceInclusion M A) = 0 := by
  apply Finsupp.lhom_ext
  intro f r
  simp only [LinearMap.comp_apply, degenerateFaceInclusion_single, M.supportedChainMap2_single,
    M.targetSubsetFaceMapOption_eq_none A _ _ f.1 f.2, rationalOptionCell_none, smul_zero,
    LinearMap.zero_apply]

/-- 原始L₂は実支持chain比較の核に含まれる。 -/
theorem degenerateL2_le_ker : degenerateL2 M A ≤
    LinearMap.ker (M.supportedChainMap2 A (comparisonFactor qc qf h ⁻¹' A) (fun _ ht => ht)) := by
  intro x hx
  obtain ⟨f, rfl⟩ := (mem_degenerateL2 M A x).mp hx
  exact LinearMap.congr_fun (degenerateFaceInclusion_map_zero M A) f

/-- 原始L₀は垂直辺の境界像なので実支持chain比較で零になる。 -/
theorem degenerateL0_le_ker : degenerateL0 M A ≤
    LinearMap.ker (M.supportedChainMap0 A (comparisonFactor qc qf h ⁻¹' A) (fun _ ht => ht)) := by
  intro x hx
  obtain ⟨v, rfl⟩ := (mem_degenerateL0 M A x).mp hx
  rw [LinearMap.mem_ker, M.supportedChainMap_comm1]
  have hv := LinearMap.congr_fun (verticalEdgeInclusion_map_zero M A) v
  rw [LinearMap.comp_apply, LinearMap.zero_apply] at hv
  rw [hv, map_zero]

/-- 原始L₁の垂直辺と混在境界は実支持chain比較でともに零になる。 -/
theorem degenerateL1_le_ker : degenerateL1 M A ≤
    LinearMap.ker (M.supportedChainMap1 A (comparisonFactor qc qf h ⁻¹' A) (fun _ ht => ht)) := by
  intro x hx
  obtain ⟨v, m, rfl⟩ := (mem_degenerateL1 M A x).mp hx
  rw [LinearMap.mem_ker, map_add, M.supportedChainMap_comm2]
  have hv := LinearMap.congr_fun (verticalEdgeInclusion_map_zero M A) v
  rw [LinearMap.comp_apply, LinearMap.zero_apply] at hv
  have hm : mixedFaceInclusion M A m ∈ degenerateL2 M A :=
    mixedFaceInclusion_range_le_degenerate M A ⟨m, rfl⟩
  have hmf := degenerateL2_le_ker M A hm
  rw [LinearMap.mem_ker] at hmf
  rw [hv, hmf, map_zero, add_zero]

end AAT.AG.AtlasCoefficientFiber

#print axioms AAT.AG.AtlasCoefficientFiber.degenerateL0
#print axioms AAT.AG.AtlasCoefficientFiber.degenerateL1
#print axioms AAT.AG.AtlasCoefficientFiber.degenerateL2
#print axioms AAT.AG.AtlasCoefficientFiber.mem_degenerateL0
#print axioms AAT.AG.AtlasCoefficientFiber.mem_degenerateL1
#print axioms AAT.AG.AtlasCoefficientFiber.mem_degenerateL2
#print axioms AAT.AG.AtlasCoefficientFiber.degenerateL2_vertical_mixed
#print axioms AAT.AG.AtlasCoefficientFiber.verticalEdge_range_le_L1
#print axioms AAT.AG.AtlasCoefficientFiber.mixedBoundary_range_le_L1
#print axioms AAT.AG.AtlasCoefficientFiber.degenerateL2_boundary_le
#print axioms AAT.AG.AtlasCoefficientFiber.degenerateL1_boundary_eq
#print axioms AAT.AG.AtlasCoefficientFiber.degenerateBoundary1
#print axioms AAT.AG.AtlasCoefficientFiber.degenerateBoundary2
#print axioms AAT.AG.AtlasCoefficientFiber.degenerateBoundary1_val
#print axioms AAT.AG.AtlasCoefficientFiber.degenerateBoundary2_val
#print axioms AAT.AG.AtlasCoefficientFiber.degenerateBoundary_square
#print axioms AAT.AG.AtlasCoefficientFiber.degenerateBoundary1_surjective
#print axioms AAT.AG.AtlasCoefficientFiber.verticalEdgeInclusion_map_zero
#print axioms AAT.AG.AtlasCoefficientFiber.degenerateFaceInclusion_map_zero
#print axioms AAT.AG.AtlasCoefficientFiber.degenerateL2_le_ker
#print axioms AAT.AG.AtlasCoefficientFiber.degenerateL0_le_ker
#print axioms AAT.AG.AtlasCoefficientFiber.degenerateL1_le_ker
#assert_standard_axioms_only AAT.AG.AtlasCoefficientFiber
