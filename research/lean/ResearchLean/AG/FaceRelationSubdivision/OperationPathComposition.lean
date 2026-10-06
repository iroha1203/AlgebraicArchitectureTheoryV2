import ResearchLean.AG.FaceRelationSubdivision.PrimitiveOperationPath
import ResearchLean.AG.FaceRelationSubdivision.RawCompositionLaws

/-!
# 原始有限操作列の連結

## Implementation notes

終点を保つsnoc帰納で列を連結し、各原始有限和と二補正の同じ合成を検査する。
同じ始終点の別列を同一視する案は固定Cの要求を越えるため採らない。
-/
noncomputable section
namespace AAT.AG.FaceRelationSubdivision
open CanonicalResolution ResolutionInvariance
universe u
variable {Source : Type u}
namespace PrimitiveOperationPath

/-- 任意の原始操作を一段の有限列へ置く。 -/
def single {qc qf : Reading Source} {Nc : TargetSupportedNerve qc} {Nf : TargetSupportedNerve qf}
    (op : PrimitiveOperation qc Nc qf Nf) : PrimitiveOperationPath qc Nc qf Nf := (nil Nc).snoc op
/-- 一段列の原始出力は同じ原始操作出力。 -/
@[simp] theorem rawEquivalence_single {qc qf : Reading Source} {Nc : TargetSupportedNerve qc}
    {Nf : TargetSupportedNerve qf} (op : PrimitiveOperation qc Nc qf Nf) :
    (single op).rawEquivalence = op.rawEquivalence := by
  rw [single, rawEquivalence_snoc, rawEquivalence_nil, RawChainEquivalence.refl_trans]

/-- 原始二列を終点で連結する。 -/
def append {qc qm qf : Reading Source} {Nc : TargetSupportedNerve qc}
    {Nm : TargetSupportedNerve qm} {Nf : TargetSupportedNerve qf}
    (P : PrimitiveOperationPath qc Nc qm Nm) (Q : PrimitiveOperationPath qm Nm qf Nf) :
    PrimitiveOperationPath qc Nc qf Nf :=
  match Q with
  | .nil _ => P
  | .snoc Q op => (P.append Q).snoc op

/-- 空列の右連結は元の列。 -/
@[simp] theorem append_nil {qc qm : Reading Source} {Nc : TargetSupportedNerve qc}
    {Nm : TargetSupportedNerve qm} (P : PrimitiveOperationPath qc Nc qm Nm) : P.append (.nil Nm) = P := rfl
/-- 一段延長の連結は同じ終段を保つ。 -/
@[simp] theorem append_snoc {qc qm qf qg : Reading Source} {Nc : TargetSupportedNerve qc}
    {Nm : TargetSupportedNerve qm} {Nf : TargetSupportedNerve qf} {Ng : TargetSupportedNerve qg}
    (P : PrimitiveOperationPath qc Nc qm Nm) (Q : PrimitiveOperationPath qm Nm qf Nf)
    (op : PrimitiveOperation qf Nf qg Ng) : P.append (Q.snoc op) = (P.append Q).snoc op := rfl

/-- 空列の左連結も同じ原始列。 -/
@[simp] theorem nil_append {qc qf : Reading Source} {Nc : TargetSupportedNerve qc}
    {Nf : TargetSupportedNerve qf} (Q : PrimitiveOperationPath qc Nc qf Nf) :
    (nil Nc).append Q = Q := by
  induction Q with
  | nil N => rfl
  | snoc Q op ih => rw [append_snoc, ih]

/-- 原始列の連結は同じ順序を保った括り直しで一致する。 -/
theorem append_assoc {qa qb qc qd : Reading Source} {Na : TargetSupportedNerve qa}
    {Nb : TargetSupportedNerve qb} {Nc : TargetSupportedNerve qc} {Nd : TargetSupportedNerve qd}
    (P : PrimitiveOperationPath qa Na qb Nb) (Q : PrimitiveOperationPath qb Nb qc Nc)
    (R : PrimitiveOperationPath qc Nc qd Nd) : (P.append Q).append R = P.append (Q.append R) := by
  induction R with
  | nil N => rw [append_nil, append_nil]
  | snoc R op ih => rw [append_snoc, append_snoc, append_snoc, ih]

/-- 直接有限列の出力は二列の原始有限和・二補正の同じ合成。 -/
theorem rawEquivalence_append {qc qm qf : Reading Source} {Nc : TargetSupportedNerve qc}
    {Nm : TargetSupportedNerve qm} {Nf : TargetSupportedNerve qf}
    (P : PrimitiveOperationPath qc Nc qm Nm) (Q : PrimitiveOperationPath qm Nm qf Nf) :
    (P.append Q).rawEquivalence = P.rawEquivalence.trans Q.rawEquivalence := by
  induction Q with
  | nil N => rw [append_nil, rawEquivalence_nil, RawChainEquivalence.trans_refl]
  | snoc Q op ih =>
    rw [append_snoc, rawEquivalence_snoc, ih, rawEquivalence_snoc, RawChainEquivalence.trans_assoc]

end PrimitiveOperationPath
end AAT.AG.FaceRelationSubdivision
#assert_standard_axioms_only AAT.AG.FaceRelationSubdivision
