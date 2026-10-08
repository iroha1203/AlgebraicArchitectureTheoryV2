import ResearchLean.AG.FaceRelationSubdivision.IncidenceBasis
import ResearchLean.AG.FaceRelationSubdivision.SourceSupportedBasis
import ResearchLean.AG.FaceRelationSubdivision.MixedSubsetHom

/-!
# 原始部分セル比較のSource支持基底

Implementation notes: 同じchart/Option表をSource台の自由線形延長へ送る。
reading因子式が支持を運ぶ。保存同値や逆有限和を入力にしない。
-/
noncomputable section
namespace AAT.AG.AtlasCoefficientFiber.PrimitiveSource
open CanonicalResolution ResolutionInvariance FaceRelationSubdivision
universe u
variable {Source : Type u} {qc qf qm : Reading Source}
variable {h : qc.CoarserThan qf} {hc : qc.CoarserThan qm} {hf : qm.CoarserThan qf}
variable {Nc : TargetSupportedNerve qc} {Nm : TargetSupportedNerve qm}
variable {Nf : TargetSupportedNerve qf}
variable (M : IncidenceSupportedComparison qc qf h Nc Nf)

/-- 元chart像をSource支持の単一基底へ送る。 -/
def basis0 : SupportedBasisMap (sourceSupport qf Nf.chartSupport)
    (sourceSupport qc Nc.chartSupport) :=
  SupportedBasisMap.ofSingle M.chartMap (by
    intro i x hx
    rw [mem_sourceSupport] at hx ⊢
    rw [← comparisonFactor_commutes qc qf h x]
    exact M.chartSupport_compatible i (qf.read x) hx)

/-- 元Option辺像をSource支持の零・単一基底へ送る。 -/
def basis1 : SupportedBasisMap (sourceSupport qf Nf.edgeSupport)
    (sourceSupport qc Nc.edgeSupport) :=
  SupportedBasisMap.ofOption M.edgeMap (by
    intro i j hij x hx
    rw [mem_sourceSupport] at hx ⊢
    rw [← comparisonFactor_commutes qc qf h x]
    exact M.edgeSupport_compatible hij hx)

/-- 元Option面像をSource支持の零・単一基底へ送る。 -/
def basis2 : SupportedBasisMap (sourceSupport qf Nf.faceSupport)
    (sourceSupport qc Nc.faceSupport) :=
  SupportedBasisMap.ofOption M.faceMap (by
    intro i j hij x hx
    rw [mem_sourceSupport] at hx ⊢
    rw [← comparisonFactor_commutes qc qf h x]
    exact M.faceSupport_compatible hij hx)

/-- chart基底値は元primitive像。 -/
@[simp] theorem basis0_image (v) :
    (basis0 M).basisImage v = Finsupp.single (M.chartMap v) 1 := rfl
/-- 辺基底値は元primitive Option像。 -/
@[simp] theorem basis1_image (e) :
    (basis1 M).basisImage e = rationalOptionCell (M.edgeMap e) := rfl
/-- 面基底値は元primitive Option像。 -/
@[simp] theorem basis2_image (f) :
    (basis2 M).basisImage f = rationalOptionCell (M.faceMap f) := rfl

/-- 同じreadingのSource表示は既存chart基底と一致する。 -/
theorem basis0_self {q : Reading Source} {N N' : TargetSupportedNerve q}
    (M : IncidenceSupportedComparison q q (Reading.coarserThan_refl q) N N') :
    basis0 M = M.basis0.toSource := by
  apply SupportedBasisMap.ext
  intro v
  rw [basis0_image, SupportedBasisMap.toSource_basis, M.basis0_image]
/-- 同じreadingのSource表示は既存辺基底と一致する。 -/
theorem basis1_self {q : Reading Source} {N N' : TargetSupportedNerve q}
    (M : IncidenceSupportedComparison q q (Reading.coarserThan_refl q) N N') :
    basis1 M = M.basis1.toSource := by
  apply SupportedBasisMap.ext
  intro e
  rw [basis1_image, SupportedBasisMap.toSource_basis, M.basis1_image]
/-- 同じreadingのSource表示は既存面基底と一致する。 -/
theorem basis2_self {q : Reading Source} {N N' : TargetSupportedNerve q}
    (M : IncidenceSupportedComparison q q (Reading.coarserThan_refl q) N N') :
    basis2 M = M.basis2.toSource := by
  apply SupportedBasisMap.ext
  intro f
  rw [basis2_image, SupportedBasisMap.toSource_basis, M.basis2_image]

variable (M₀ : IncidenceSupportedComparison qc qm hc Nc Nm)
variable (M₁ : IncidenceSupportedComparison qm qf hf Nm Nf)

/-- chart基底は同じ元部分セル合成と可換。 -/
theorem basis0_comp : basis0 (IncidenceSupportedComparison.comp M₀ M₁) =
    (basis0 M₁).comp (basis0 M₀) := by
  apply SupportedBasisMap.ext
  intro v
  rw [basis0_image, IncidenceSupportedComparison.comp_chartMap,
    SupportedBasisMap.comp_basis, basis0_image, SupportedBasisMap.raw_single,
    basis0_image, one_smul]
/-- 辺基底は二退化経路を含む元部分セル合成と可換。 -/
theorem basis1_comp : basis1 (IncidenceSupportedComparison.comp M₀ M₁) =
    (basis1 M₁).comp (basis1 M₀) := by
  apply SupportedBasisMap.ext
  intro e
  rw [basis1_image, IncidenceSupportedComparison.comp_edgeMap,
    SupportedBasisMap.comp_basis, basis1_image]
  cases M₁.edgeMap e with
  | none => simp only [Option.bind_none, rationalOptionCell_none, map_zero]
  | some j => simp only [Option.bind_some, rationalOptionCell_some,
      SupportedBasisMap.raw_single, one_smul, basis1_image]
/-- 面基底は二退化経路を含む元部分セル合成と可換。 -/
theorem basis2_comp : basis2 (IncidenceSupportedComparison.comp M₀ M₁) =
    (basis2 M₁).comp (basis2 M₀) := by
  apply SupportedBasisMap.ext
  intro f
  rw [basis2_image, IncidenceSupportedComparison.comp_faceMap,
    SupportedBasisMap.comp_basis, basis2_image]
  cases M₁.faceMap f with
  | none => simp only [Option.bind_none, rationalOptionCell_none, map_zero]
  | some j => simp only [Option.bind_some, rationalOptionCell_some,
      SupportedBasisMap.raw_single, one_smul, basis2_image]

end AAT.AG.AtlasCoefficientFiber.PrimitiveSource

#print axioms AAT.AG.AtlasCoefficientFiber.PrimitiveSource.basis0
#print axioms AAT.AG.AtlasCoefficientFiber.PrimitiveSource.basis1
#print axioms AAT.AG.AtlasCoefficientFiber.PrimitiveSource.basis2
#print axioms AAT.AG.AtlasCoefficientFiber.PrimitiveSource.basis0_image
#print axioms AAT.AG.AtlasCoefficientFiber.PrimitiveSource.basis1_image
#print axioms AAT.AG.AtlasCoefficientFiber.PrimitiveSource.basis2_image
#print axioms AAT.AG.AtlasCoefficientFiber.PrimitiveSource.basis0_self
#print axioms AAT.AG.AtlasCoefficientFiber.PrimitiveSource.basis1_self
#print axioms AAT.AG.AtlasCoefficientFiber.PrimitiveSource.basis2_self
#print axioms AAT.AG.AtlasCoefficientFiber.PrimitiveSource.basis0_comp
#print axioms AAT.AG.AtlasCoefficientFiber.PrimitiveSource.basis1_comp
#print axioms AAT.AG.AtlasCoefficientFiber.PrimitiveSource.basis2_comp
#assert_standard_axioms_only AAT.AG.AtlasCoefficientFiber.PrimitiveSource
