import ResearchLean.AG.FaceRelationSubdivision.ElementaryRawEquivalence
import ResearchLean.AG.FaceRelationSubdivision.PresentationRawEquivalence
import ResearchLean.AG.FaceRelationSubdivision.PrimitiveTriangleInverse
import ResearchLean.AG.FaceRelationSubdivision.SubdivisionReconstruction

/-!
# 原始基本操作からなる有限列

## Implementation notes

操作のconstructorには辺、原始逆pattern、名前/台の表示だけを置く。
chain式・診断同型・期待rankは入力fieldにない。正逆出力を各constructorから
生成し、snoc有限帰納で直接有限和と二補正を計算する。任意の同値を操作として
受け取る案は固定B/Cの原始構成を未放電にするため採らない。
-/
noncomputable section
namespace AAT.AG.FaceRelationSubdivision
open CanonicalResolution ResolutionInvariance AtlasDefectComposition
universe u
variable {Source : Type u}

/-- Bの原始許容操作。表示にはT0のreading支持逆像も含む。 -/
inductive PrimitiveOperation : (qc : Reading Source) → TargetSupportedNerve.{u,u} qc →
    (qf : Reading Source) → TargetSupportedNerve.{u,u} qf → Type (u+1)
  | triangle {q : Reading Source} (N : TargetSupportedNerve q) (e : N.nerve.EdgeComponent) :
      PrimitiveOperation q N q (TriangleAddition.supported N e)
  | subdivision {q : Reading Source} (N : TargetSupportedNerve q) (e : N.nerve.EdgeComponent) :
      PrimitiveOperation q N q (EdgeSubdivision.supported N e)
  | triangleInverse {q : Reading Source} {N : TargetSupportedNerve q} (P : TriangleInversePattern N) :
      PrimitiveOperation q N q P.restored
  | subdivisionInverse {q : Reading Source} {N : TargetSupportedNerve q} (P : SubdivisionInversePattern N) :
      PrimitiveOperation q N q P.restored
  | presentation {qc qf : Reading Source} {Nc : TargetSupportedNerve qc} {Nf : TargetSupportedNerve qf}
      (h : qc.CoarserThan qf) (E : CellPresentationEquiv qc qf h Nc Nf) :
      PrimitiveOperation qc Nc qf Nf

namespace PrimitiveOperation
variable {qc qf : Reading Source} {Nc : TargetSupportedNerve qc} {Nf : TargetSupportedNerve qf}

/-- 原始操作から同じ全セル有限和と二補正を生成する。 -/
def rawEquivalence (op : PrimitiveOperation qc Nc qf Nf) : RawChainEquivalence Nc Nf :=
  match op with
  | .triangle N e => TriangleAddition.rawEquivalence N e
  | .subdivision N e => EdgeSubdivision.rawEquivalence N e
  | .triangleInverse P =>
      ((TriangleAddition.rawEquivalence P.restored P.restoredBase).trans P.presentation.rawEquivalence.symm).symm
  | .subdivisionInverse P =>
      ((EdgeSubdivision.rawEquivalence P.restored P.commonEdge).trans P.presentation.rawEquivalence.symm).symm
  | .presentation _ E => E.rawEquivalence

/-- triangle操作出力は同じ原始基本表。 -/
@[simp] theorem rawEquivalence_triangle {q : Reading Source} (N : TargetSupportedNerve q)
    (e : N.nerve.EdgeComponent) : (PrimitiveOperation.triangle N e).rawEquivalence = TriangleAddition.rawEquivalence N e := rfl
/-- subdivision操作出力は同じ原始基本表。 -/
@[simp] theorem rawEquivalence_subdivision {q : Reading Source} (N : TargetSupportedNerve q)
    (e : N.nerve.EdgeComponent) : (PrimitiveOperation.subdivision N e).rawEquivalence = EdgeSubdivision.rawEquivalence N e := rfl
/-- triangleInverse操作出力は復元正表・原始表示・正逆交換の同じ計算。 -/
@[simp] theorem rawEquivalence_triangleInverse {q : Reading Source} {N : TargetSupportedNerve q}
    (P : TriangleInversePattern N) : (PrimitiveOperation.triangleInverse P).rawEquivalence =
      ((TriangleAddition.rawEquivalence P.restored P.restoredBase).trans P.presentation.rawEquivalence.symm).symm := rfl
/-- subdivisionInverse操作出力は復元正表・原始表示・正逆交換の同じ計算。 -/
@[simp] theorem rawEquivalence_subdivisionInverse {q : Reading Source} {N : TargetSupportedNerve q}
    (P : SubdivisionInversePattern N) : (PrimitiveOperation.subdivisionInverse P).rawEquivalence =
      ((EdgeSubdivision.rawEquivalence P.restored P.commonEdge).trans P.presentation.rawEquivalence.symm).symm := rfl
/-- 原始表示操作出力は同じ全単射基底表。 -/
@[simp] theorem rawEquivalence_presentation (h : qc.CoarserThan qf)
    (E : CellPresentationEquiv qc qf h Nc Nf) :
    (PrimitiveOperation.presentation h E).rawEquivalence = E.rawEquivalence := rfl

/-- 原始操作のreadingは粗readingを細かくする向きだけ。 -/
theorem coarser (op : PrimitiveOperation qc Nc qf Nf) : qc.CoarserThan qf := by
  cases op with
  | triangle N e => exact Reading.coarserThan_refl _
  | subdivision N e => exact Reading.coarserThan_refl _
  | triangleInverse P => exact Reading.coarserThan_refl _
  | subdivisionInverse P => exact Reading.coarserThan_refl _
  | presentation h E => exact h

/-- セル名を保つT0のreading支持逆像は原始許容操作。 -/
def reading (N : TargetSupportedNerve qc) (h : qc.CoarserThan qf) :
    PrimitiveOperation qc N qf (readingPullback N h) := .presentation h (readingPresentation N h)

end PrimitiveOperation

/-- 任意の原始操作を連ねた有限列。空列も量化する。 -/
inductive PrimitiveOperationPath : (qc : Reading Source) → TargetSupportedNerve.{u,u} qc →
    (qf : Reading Source) → TargetSupportedNerve.{u,u} qf → Type (u+1)
  | nil {q : Reading Source} (N : TargetSupportedNerve q) : PrimitiveOperationPath q N q N
  | snoc {qc qm qf : Reading Source} {Nc : TargetSupportedNerve qc}
      {Nm : TargetSupportedNerve qm} {Nf : TargetSupportedNerve qf}
      (path : PrimitiveOperationPath qc Nc qm Nm) (op : PrimitiveOperation qm Nm qf Nf) :
      PrimitiveOperationPath qc Nc qf Nf

namespace PrimitiveOperationPath
variable {qc qm qf : Reading Source} {Nc : TargetSupportedNerve qc}
variable {Nm : TargetSupportedNerve qm} {Nf : TargetSupportedNerve qf}

/-- 有限帰納で原始基底有限和・逆・両補正を直接計算する。 -/
def rawEquivalence {qc qf : Reading Source} {Nc : TargetSupportedNerve qc}
    {Nf : TargetSupportedNerve qf} (path : PrimitiveOperationPath qc Nc qf Nf) : RawChainEquivalence Nc Nf :=
  match path with
  | .nil N => RawChainEquivalence.refl N
  | .snoc path op => path.rawEquivalence.trans op.rawEquivalence

/-- 空列の原始出力は同じセル恒等。 -/
@[simp] theorem rawEquivalence_nil (N : TargetSupportedNerve qc) :
    (PrimitiveOperationPath.nil N).rawEquivalence = RawChainEquivalence.refl N := rfl
/-- 一段延長の原始出力は原始有限和の同じ直接合成。 -/
@[simp] theorem rawEquivalence_snoc (path : PrimitiveOperationPath qc Nc qm Nm)
    (op : PrimitiveOperation qm Nm qf Nf) :
    (path.snoc op).rawEquivalence = path.rawEquivalence.trans op.rawEquivalence := rfl

/-- 任意有限列のreading因子は原始各段の粗細関係から導く。 -/
theorem coarser (path : PrimitiveOperationPath qc Nc qf Nf) : qc.CoarserThan qf := by
  induction path with
  | nil N => exact Reading.coarserThan_refl _
  | snoc path op ih => exact Reading.coarserThan_trans ih op.coarser

/-- 幾何列を先に固定し、最初のadequacyから終点adequacyを導く。 -/
theorem adequate (path : PrimitiveOperationPath qc Nc qf Nf) (laws : FiniteLawFamily Source)
    (ha : laws.Adequate qc) : laws.Adequate qf := adequate_of_coarser laws path.coarser ha

/-- 各段の支持選択に使う終点target部分集合。 -/
def targetSubset (path : PrimitiveOperationPath qc Nc qf Nf) (A : Set qc.Target) : Set qf.Target :=
  comparisonFactor qc qf path.coarser ⁻¹' A

/-- 終点部分集合は固定T0の因子逆像。 -/
@[simp] theorem targetSubset_eq_preimage (path : PrimitiveOperationPath qc Nc qf Nf) (A : Set qc.Target) :
    path.targetSubset A = comparisonFactor qc qf path.coarser ⁻¹' A := rfl

/-- 全AのSource支持適合を原始列のreading因子から放電する。 -/
theorem source_subset_eq (path : PrimitiveOperationPath qc Nc qf Nf) (A : Set qc.Target) :
    qf.read ⁻¹' path.targetSubset A = qc.read ⁻¹' A := by
  ext x
  simp only [targetSubset_eq_preimage, Set.mem_preimage, comparisonFactor_commutes]

end PrimitiveOperationPath
end AAT.AG.FaceRelationSubdivision
#assert_standard_axioms_only AAT.AG.FaceRelationSubdivision
