import ResearchLean.AG.AtlasCoefficientFiber.PrimitiveSourceBasis
import ResearchLean.AG.FaceRelationSubdivision.PrimitiveOperationPath

/-!
# 指定正操作の原始部分セル比較

Implementation notes: 操作入力は辺またはセル名・incidence・台の表示だけ。
G134の原始r/s/h/k生成経路へ接続し、順像入力は同じOption比較とする。
-/
noncomputable section
namespace AAT.AG.AtlasCoefficientFiber
open CanonicalResolution ResolutionInvariance FaceRelationSubdivision
universe u
variable {Source : Type u}

/-- G135 Dの原始正操作。逆有限和は操作入力ではなく保存出力に残す。 -/
inductive PositiveOperation : (qc : Reading Source) → TargetSupportedNerve.{u,u} qc →
    (qf : Reading Source) → TargetSupportedNerve.{u,u} qf → Type (u+1)
  | triangle {q : Reading Source} (N : TargetSupportedNerve q) (e : N.nerve.EdgeComponent) :
      PositiveOperation q N q (TriangleAddition.supported N e)
  | subdivision {q : Reading Source} (N : TargetSupportedNerve q) (e : N.nerve.EdgeComponent) :
      PositiveOperation q N q (EdgeSubdivision.supported N e)
  | presentation {qc qf : Reading Source} {Nc : TargetSupportedNerve qc} {Nf : TargetSupportedNerve qf}
      (h : qc.CoarserThan qf) (E : CellPresentationEquiv qc qf h Nc Nf) :
      PositiveOperation qc Nc qf Nf

namespace PositiveOperation
variable {qc qf : Reading Source} {Nc : TargetSupportedNerve qc} {Nf : TargetSupportedNerve qf}

/-- 同じ正操作を既存G134原始操作へ含める。 -/
def toPrimitive (op : PositiveOperation qc Nc qf Nf) : PrimitiveOperation qc Nc qf Nf :=
  match op with
  | .triangle N e => .triangle N e
  | .subdivision N e => .subdivision N e
  | .presentation h E => .presentation h E

/-- 粗細関係は元primitive操作の出力。 -/
theorem coarser (op : PositiveOperation qc Nc qf Nf) : qc.CoarserThan qf := op.toPrimitive.coarser

/-- 元chart/Option表から同じ原始部分セル比較を作る。 -/
def comparison (op : PositiveOperation qc Nc qf Nf) :
    IncidenceSupportedComparison qc qf op.coarser Nc Nf :=
  match op with
  | .triangle N e => TriangleAddition.collapse N e
  | .subdivision N e => EdgeSubdivision.collapse N e
  | .presentation _ E => E.comparison

/-- 指定reading pullbackは同じ原始表示操作。 -/
def reading (N : TargetSupportedNerve qc) (h : qc.CoarserThan qf) :
    PositiveOperation qc N qf (readingPullback N h) := .presentation h (readingPresentation N h)

/-- reading操作のG134像は同じ既存reading操作。 -/
theorem reading_toPrimitive (N : TargetSupportedNerve qc) (h : qc.CoarserThan qf) :
    (reading N h).toPrimitive = PrimitiveOperation.reading N h := rfl

/-- 元G134正操作のr0は同じ原始部分セルchart表。 -/
theorem primitive_r0 (op : PositiveOperation qc Nc qf Nf) :
    op.toPrimitive.rawEquivalence.r0 = PrimitiveSource.basis0 op.comparison := by
  cases op with
  | @triangle Nc e =>
    change (TriangleAddition.rawEquivalence Nc e).r0 = PrimitiveSource.basis0 (TriangleAddition.collapse Nc e)
    rw [TriangleAddition.rawEquivalence_r0]
    apply SupportedBasisMap.ext
    intro x
    rw [SupportedBasisMap.toSource_basis, TriangleAddition.r0_basis, PrimitiveSource.basis0_image]
  | @subdivision Nc e =>
    change (EdgeSubdivision.rawEquivalence Nc e).r0 = PrimitiveSource.basis0 (EdgeSubdivision.collapse Nc e)
    rw [EdgeSubdivision.rawEquivalence_r0]
    apply SupportedBasisMap.ext
    intro x
    rw [SupportedBasisMap.toSource_basis, EdgeSubdivision.r0_basis, PrimitiveSource.basis0_image]
    rfl
  | @presentation qf Nc Nf h E =>
    change E.rawEquivalence.r0 = PrimitiveSource.basis0 E.comparison
    rw [E.rawEquivalence_r0]
    apply SupportedBasisMap.ext
    intro x
    rw [E.sourceR0_basis, PrimitiveSource.basis0_image, E.comparison_chart]

/-- 元G134正操作のr1は同じ原始部分セルedge表。 -/
theorem primitive_r1 (op : PositiveOperation qc Nc qf Nf) :
    op.toPrimitive.rawEquivalence.r1 = PrimitiveSource.basis1 op.comparison := by
  cases op with
  | @triangle Nc e =>
    change (TriangleAddition.rawEquivalence Nc e).r1 = PrimitiveSource.basis1 (TriangleAddition.collapse Nc e)
    rw [TriangleAddition.rawEquivalence_r1]
    apply SupportedBasisMap.ext
    intro x
    rw [SupportedBasisMap.toSource_basis, TriangleAddition.r1_basis, PrimitiveSource.basis1_image]
  | @subdivision Nc e =>
    change (EdgeSubdivision.rawEquivalence Nc e).r1 = PrimitiveSource.basis1 (EdgeSubdivision.collapse Nc e)
    rw [EdgeSubdivision.rawEquivalence_r1]
    apply SupportedBasisMap.ext
    intro x
    rw [SupportedBasisMap.toSource_basis, EdgeSubdivision.r1_basis, PrimitiveSource.basis1_image]
    rfl
  | @presentation qf Nc Nf h E =>
    change E.rawEquivalence.r1 = PrimitiveSource.basis1 E.comparison
    rw [E.rawEquivalence_r1]
    apply SupportedBasisMap.ext
    intro x
    rw [E.sourceR1_basis, PrimitiveSource.basis1_image, E.comparison_edge]
    rw [rationalOptionCell_some]

/-- 元G134正操作のr2は同じ原始部分セルface表。 -/
theorem primitive_r2 (op : PositiveOperation qc Nc qf Nf) :
    op.toPrimitive.rawEquivalence.r2 = PrimitiveSource.basis2 op.comparison := by
  cases op with
  | @triangle Nc e =>
    change (TriangleAddition.rawEquivalence Nc e).r2 = PrimitiveSource.basis2 (TriangleAddition.collapse Nc e)
    rw [TriangleAddition.rawEquivalence_r2]
    apply SupportedBasisMap.ext
    intro x
    rw [SupportedBasisMap.toSource_basis, TriangleAddition.r2_basis, PrimitiveSource.basis2_image]
  | @subdivision Nc e =>
    change (EdgeSubdivision.rawEquivalence Nc e).r2 = PrimitiveSource.basis2 (EdgeSubdivision.collapse Nc e)
    rw [EdgeSubdivision.rawEquivalence_r2]
    apply SupportedBasisMap.ext
    intro x
    rw [SupportedBasisMap.toSource_basis, EdgeSubdivision.r2_basis, PrimitiveSource.basis2_image]
    rfl
  | @presentation qf Nc Nf h E =>
    change E.rawEquivalence.r2 = PrimitiveSource.basis2 E.comparison
    rw [E.rawEquivalence_r2]
    apply SupportedBasisMap.ext
    intro x
    rw [E.sourceR2_basis, PrimitiveSource.basis2_image, E.comparison_face]
    rw [rationalOptionCell_some]

end PositiveOperation
end AAT.AG.AtlasCoefficientFiber
#print axioms AAT.AG.AtlasCoefficientFiber.PositiveOperation
#print axioms AAT.AG.AtlasCoefficientFiber.PositiveOperation.toPrimitive
#print axioms AAT.AG.AtlasCoefficientFiber.PositiveOperation.coarser
#print axioms AAT.AG.AtlasCoefficientFiber.PositiveOperation.comparison
#print axioms AAT.AG.AtlasCoefficientFiber.PositiveOperation.reading
#print axioms AAT.AG.AtlasCoefficientFiber.PositiveOperation.reading_toPrimitive
#print axioms AAT.AG.AtlasCoefficientFiber.PositiveOperation.primitive_r0
#print axioms AAT.AG.AtlasCoefficientFiber.PositiveOperation.primitive_r1
#print axioms AAT.AG.AtlasCoefficientFiber.PositiveOperation.primitive_r2
#print axioms AAT.AG.AtlasCoefficientFiber.PositiveOperation.casesOn
#print axioms AAT.AG.AtlasCoefficientFiber.PositiveOperation.ctorElim
#print axioms AAT.AG.AtlasCoefficientFiber.PositiveOperation.ctorElimType
#print axioms AAT.AG.AtlasCoefficientFiber.PositiveOperation.ctorIdx
#print axioms AAT.AG.AtlasCoefficientFiber.PositiveOperation.noConfusion
#print axioms AAT.AG.AtlasCoefficientFiber.PositiveOperation.noConfusionType
#print axioms AAT.AG.AtlasCoefficientFiber.PositiveOperation.presentation
#print axioms AAT.AG.AtlasCoefficientFiber.PositiveOperation.presentation.elim
#print axioms AAT.AG.AtlasCoefficientFiber.PositiveOperation.presentation.inj
#print axioms AAT.AG.AtlasCoefficientFiber.PositiveOperation.presentation.injEq
#print axioms AAT.AG.AtlasCoefficientFiber.PositiveOperation.presentation.noConfusion
#print axioms AAT.AG.AtlasCoefficientFiber.PositiveOperation.presentation.sizeOf_spec
#print axioms AAT.AG.AtlasCoefficientFiber.PositiveOperation.rec
#print axioms AAT.AG.AtlasCoefficientFiber.PositiveOperation.recOn
#print axioms AAT.AG.AtlasCoefficientFiber.PositiveOperation.subdivision
#print axioms AAT.AG.AtlasCoefficientFiber.PositiveOperation.subdivision.elim
#print axioms AAT.AG.AtlasCoefficientFiber.PositiveOperation.subdivision.noConfusion
#print axioms AAT.AG.AtlasCoefficientFiber.PositiveOperation.subdivision.sizeOf_spec
#print axioms AAT.AG.AtlasCoefficientFiber.PositiveOperation.triangle
#print axioms AAT.AG.AtlasCoefficientFiber.PositiveOperation.triangle.elim
#print axioms AAT.AG.AtlasCoefficientFiber.PositiveOperation.triangle.noConfusion
#print axioms AAT.AG.AtlasCoefficientFiber.PositiveOperation.triangle.sizeOf_spec
#assert_standard_axioms_only AAT.AG.AtlasCoefficientFiber
