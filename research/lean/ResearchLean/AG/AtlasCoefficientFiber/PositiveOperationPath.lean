import ResearchLean.AG.AtlasCoefficientFiber.PositiveOperation
import ResearchLean.AG.AtlasCoefficientFiber.PrimitiveSourceComparison
import ResearchLean.AG.FaceRelationSubdivision.OperationPathMaps

/-!
# 原始正操作の部分セル有限合成

Implementation notes: 空列とsnocは元Option比較を直接合成する。
同じG134列のr表との一致を原始基底の有限帰納で導く。
-/
noncomputable section
namespace AAT.AG.AtlasCoefficientFiber
open CanonicalResolution ResolutionInvariance FaceRelationSubdivision TwoPhase AtlasDefectComposition
universe u
variable {Source : Type u}

/-- 原始正操作だけを有限回連ねる。全逆写像は既存G134出力から得る。 -/
inductive PositiveOperationPath : (qc : Reading Source) → TargetSupportedNerve.{u,u} qc →
    (qf : Reading Source) → TargetSupportedNerve.{u,u} qf → Type (u+1)
  | nil {q : Reading Source} (N : TargetSupportedNerve q) : PositiveOperationPath q N q N
  | snoc {qc qm qf : Reading Source} {Nc : TargetSupportedNerve qc}
      {Nm : TargetSupportedNerve qm} {Nf : TargetSupportedNerve qf}
      (path : PositiveOperationPath qc Nc qm Nm) (op : PositiveOperation qm Nm qf Nf) :
      PositiveOperationPath qc Nc qf Nf

namespace PositiveOperationPath
variable {qc qm qf : Reading Source} {Nc : TargetSupportedNerve qc}
variable {Nm : TargetSupportedNerve qm} {Nf : TargetSupportedNerve qf}

/-- 同じ有限列を既存G134列へ含める。 -/
def toPrimitive {qc qf : Reading Source} {Nc : TargetSupportedNerve qc}
    {Nf : TargetSupportedNerve qf} (path : PositiveOperationPath qc Nc qf Nf) : PrimitiveOperationPath qc Nc qf Nf :=
  match path with
  | .nil N => .nil N
  | .snoc path op => path.toPrimitive.snoc op.toPrimitive

/-- 空列のG134像は同じ空列。 -/
theorem toPrimitive_nil (N : TargetSupportedNerve qc) :
    (PositiveOperationPath.nil N).toPrimitive = PrimitiveOperationPath.nil N := rfl
/-- 延長列のG134像は同じ各段を連ねる列。 -/
theorem toPrimitive_snoc (path : PositiveOperationPath qc Nc qm Nm)
    (op : PositiveOperation qm Nm qf Nf) :
    (path.snoc op).toPrimitive = path.toPrimitive.snoc op.toPrimitive := rfl

/-- 粗細関係は同じG134列の出力。 -/
theorem coarser (path : PositiveOperationPath qc Nc qf Nf) : qc.CoarserThan qf :=
  path.toPrimitive.coarser

/-- 各原始部分比較を直接Option合成し、元Pの入力比較を作る。 -/
def comparison {qc qf : Reading Source} {Nc : TargetSupportedNerve qc}
    {Nf : TargetSupportedNerve qf} (path : PositiveOperationPath qc Nc qf Nf) :
    IncidenceSupportedComparison qc qf path.coarser Nc Nf :=
  match path with
  | .nil N => IncidenceSupportedComparison.identity _ N
  | .snoc path op => IncidenceSupportedComparison.comp path.comparison op.comparison

/-- 空列の元比較は恒等部分セル表。 -/
theorem comparison_nil (N : TargetSupportedNerve qc) :
    (PositiveOperationPath.nil N).comparison = IncidenceSupportedComparison.identity qc N := rfl
/-- 延長列の元比較は同じ各段の部分セル合成。 -/
theorem comparison_snoc (path : PositiveOperationPath qc Nc qm Nm)
    (op : PositiveOperation qm Nm qf Nf) :
    (path.snoc op).comparison = IncidenceSupportedComparison.comp path.comparison op.comparison := rfl

/-- 一つの指定正操作を同じ有限列へ含める。 -/
def single (op : PositiveOperation qc Nc qf Nf) : PositiveOperationPath qc Nc qf Nf :=
  (PositiveOperationPath.nil Nc).snoc op
/-- 単一操作列の原始比較は同じ元操作比較。 -/
theorem single_comparison (op : PositiveOperation qc Nc qf Nf) :
    (single op).comparison = op.comparison := by
  dsimp only [single]
  rw [comparison_snoc, comparison_nil, IncidenceSupportedComparison.comp_identity_left]

/-- 任意有限列の元G134 r0は同じ原始部分セルchart基底表。 -/
theorem primitive_r0 (path : PositiveOperationPath qc Nc qf Nf) :
    path.toPrimitive.rawEquivalence.r0 = PrimitiveSource.basis0 path.comparison := by
  induction path with
  | @nil N =>
    rw [toPrimitive_nil, PrimitiveOperationPath.rawEquivalence_nil, RawChainEquivalence.refl_r0]
    apply SupportedBasisMap.ext_raw
    apply Finsupp.lhom_ext
    intro x a
    rw [SupportedBasisMap.raw_identity, LinearMap.id_apply, SupportedBasisMap.raw_single,
      PrimitiveSource.basis0_image, comparison_nil, IncidenceSupportedComparison.identity_chartMap]
    simp only [Finsupp.smul_single, smul_eq_mul, mul_one]
  | @snoc qm qf Nc Nm Nf path op ih =>
    rw [toPrimitive_snoc, PrimitiveOperationPath.rawEquivalence_snoc,
      RawChainEquivalence.trans_r0, ih, op.primitive_r0, comparison_snoc,
      PrimitiveSource.basis0_comp]

/-- 任意有限列の元G134 r1は同じ原始部分セルedge基底表。 -/
theorem primitive_r1 (path : PositiveOperationPath qc Nc qf Nf) :
    path.toPrimitive.rawEquivalence.r1 = PrimitiveSource.basis1 path.comparison := by
  induction path with
  | @nil N =>
    rw [toPrimitive_nil, PrimitiveOperationPath.rawEquivalence_nil, RawChainEquivalence.refl_r1]
    apply SupportedBasisMap.ext_raw
    apply Finsupp.lhom_ext
    intro x a
    rw [SupportedBasisMap.raw_identity, LinearMap.id_apply, SupportedBasisMap.raw_single,
      PrimitiveSource.basis1_image, comparison_nil, IncidenceSupportedComparison.identity_edgeMap]
    rw [rationalOptionCell_some]
    simp only [Finsupp.smul_single, smul_eq_mul, mul_one]
  | @snoc qm qf Nc Nm Nf path op ih =>
    rw [toPrimitive_snoc, PrimitiveOperationPath.rawEquivalence_snoc,
      RawChainEquivalence.trans_r1, ih, op.primitive_r1, comparison_snoc,
      PrimitiveSource.basis1_comp]

/-- 任意有限列の元G134 r2は同じ原始部分セルface基底表。 -/
theorem primitive_r2 (path : PositiveOperationPath qc Nc qf Nf) :
    path.toPrimitive.rawEquivalence.r2 = PrimitiveSource.basis2 path.comparison := by
  induction path with
  | @nil N =>
    rw [toPrimitive_nil, PrimitiveOperationPath.rawEquivalence_nil, RawChainEquivalence.refl_r2]
    apply SupportedBasisMap.ext_raw
    apply Finsupp.lhom_ext
    intro x a
    rw [SupportedBasisMap.raw_identity, LinearMap.id_apply, SupportedBasisMap.raw_single,
      PrimitiveSource.basis2_image, comparison_nil, IncidenceSupportedComparison.identity_faceMap]
    rw [rationalOptionCell_some]
    simp only [Finsupp.smul_single, smul_eq_mul, mul_one]
  | @snoc qm qf Nc Nm Nf path op ih =>
    rw [toPrimitive_snoc, PrimitiveOperationPath.rawEquivalence_snoc,
      RawChainEquivalence.trans_r2, ih, op.primitive_r2, comparison_snoc,
      PrimitiveSource.basis2_comp]

/-- 同じ元G134 r全Homは独立に生成した元部分集合比較に一致する。 -/
theorem subsetR_eq_generated (path : PositiveOperationPath qc Nc qf Nf) (A : Set qc.Target) :
    path.toPrimitive.subsetR A = path.comparison.aSubnerveComparisonHom A :=
  PrimitiveSource.rawR_eq_generated path.comparison path.toPrimitive.rawEquivalence
    (path.primitive_r0) (path.primitive_r1) (path.primitive_r2) A

/-- 同じG134 Law有限和は元独立generatedComparisonHomに全三成分で一致する。 -/
theorem lawR_eq_generated [Fintype Source] (path : PositiveOperationPath qc Nc qf Nf)
    (laws : FiniteLawFamily Source) (ha : laws.Adequate qc) :
    path.toPrimitive.lawR laws ha = path.comparison.generatedComparisonHom laws ha
      (adequate_of_coarser laws path.coarser ha) :=
  PrimitiveSource.rawLawR_eq_generated path.comparison path.toPrimitive.rawEquivalence
    (path.primitive_r0) (path.primitive_r1) (path.primitive_r2) laws ha

end PositiveOperationPath
end AAT.AG.AtlasCoefficientFiber
#print axioms AAT.AG.AtlasCoefficientFiber.PositiveOperationPath
#print axioms AAT.AG.AtlasCoefficientFiber.PositiveOperationPath.toPrimitive
#print axioms AAT.AG.AtlasCoefficientFiber.PositiveOperationPath.toPrimitive_nil
#print axioms AAT.AG.AtlasCoefficientFiber.PositiveOperationPath.toPrimitive_snoc
#print axioms AAT.AG.AtlasCoefficientFiber.PositiveOperationPath.coarser
#print axioms AAT.AG.AtlasCoefficientFiber.PositiveOperationPath.comparison
#print axioms AAT.AG.AtlasCoefficientFiber.PositiveOperationPath.comparison_nil
#print axioms AAT.AG.AtlasCoefficientFiber.PositiveOperationPath.comparison_snoc
#print axioms AAT.AG.AtlasCoefficientFiber.PositiveOperationPath.single
#print axioms AAT.AG.AtlasCoefficientFiber.PositiveOperationPath.single_comparison
#print axioms AAT.AG.AtlasCoefficientFiber.PositiveOperationPath.primitive_r0
#print axioms AAT.AG.AtlasCoefficientFiber.PositiveOperationPath.primitive_r1
#print axioms AAT.AG.AtlasCoefficientFiber.PositiveOperationPath.primitive_r2
#print axioms AAT.AG.AtlasCoefficientFiber.PositiveOperationPath.subsetR_eq_generated
#print axioms AAT.AG.AtlasCoefficientFiber.PositiveOperationPath.lawR_eq_generated
#print axioms AAT.AG.AtlasCoefficientFiber.PositiveOperationPath.below
#print axioms AAT.AG.AtlasCoefficientFiber.PositiveOperationPath.brecOn
#print axioms AAT.AG.AtlasCoefficientFiber.PositiveOperationPath.brecOn.eq
#print axioms AAT.AG.AtlasCoefficientFiber.PositiveOperationPath.brecOn.go
#print axioms AAT.AG.AtlasCoefficientFiber.PositiveOperationPath.casesOn
#print axioms AAT.AG.AtlasCoefficientFiber.PositiveOperationPath.ctorElim
#print axioms AAT.AG.AtlasCoefficientFiber.PositiveOperationPath.ctorElimType
#print axioms AAT.AG.AtlasCoefficientFiber.PositiveOperationPath.ctorIdx
#print axioms AAT.AG.AtlasCoefficientFiber.PositiveOperationPath.nil
#print axioms AAT.AG.AtlasCoefficientFiber.PositiveOperationPath.nil.elim
#print axioms AAT.AG.AtlasCoefficientFiber.PositiveOperationPath.nil.noConfusion
#print axioms AAT.AG.AtlasCoefficientFiber.PositiveOperationPath.nil.sizeOf_spec
#print axioms AAT.AG.AtlasCoefficientFiber.PositiveOperationPath.noConfusion
#print axioms AAT.AG.AtlasCoefficientFiber.PositiveOperationPath.noConfusionType
#print axioms AAT.AG.AtlasCoefficientFiber.PositiveOperationPath.rec
#print axioms AAT.AG.AtlasCoefficientFiber.PositiveOperationPath.recOn
#print axioms AAT.AG.AtlasCoefficientFiber.PositiveOperationPath.snoc
#print axioms AAT.AG.AtlasCoefficientFiber.PositiveOperationPath.snoc.elim
#print axioms AAT.AG.AtlasCoefficientFiber.PositiveOperationPath.snoc.inj
#print axioms AAT.AG.AtlasCoefficientFiber.PositiveOperationPath.snoc.injEq
#print axioms AAT.AG.AtlasCoefficientFiber.PositiveOperationPath.snoc.noConfusion
#print axioms AAT.AG.AtlasCoefficientFiber.PositiveOperationPath.snoc.sizeOf_spec
#assert_standard_axioms_only AAT.AG.AtlasCoefficientFiber
