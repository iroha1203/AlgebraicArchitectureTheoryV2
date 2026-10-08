import ResearchLean.AG.FaceRelationSubdivision.IncidenceComparison
import ResearchLean.AG.ResolutionInvariance.LawValueBlockDecomposition

/-!
# G-135 W1–W3・W5の共通原始入力

## Implementation notes

指定SourceはBool×Bool、粗readingは第一座標、細readingは恒等、Lawは第一座標。
期待する行列やrankを入力にする案は原始入力からの生成を変えるため採用しない。
-/
noncomputable section
namespace AAT.AG.AtlasCoefficientFiber.WitnessCommon
open CanonicalResolution ResolutionInvariance

/-- 指定された四点Source。 -/
abbrev Source := Bool × Bool
/-- 第一座標を読む粗reading。 -/
abbrev qc : Reading Source where
  Target := Bool
  read := Prod.fst
  surjective x := ⟨(x, false), rfl⟩
/-- 同じSourceの恒等reading。 -/
abbrev qf : Reading Source where
  Target := Source
  read := id
  surjective := Function.surjective_id
/-- 原始reading評価からの粗細順序。 -/
theorem coarser : qc.CoarserThan qf := by
  intro x y h
  exact congrArg Prod.fst h
/-- 同じSourceの二点が真の細分化を証明する。 -/
theorem not_coarser : ¬ qf.CoarserThan qc := by
  intro h
  exact Bool.false_ne_true (congrArg Prod.snd
    (h (x := (false, false)) (y := (false, true)) rfl))
/-- 比較因子は実際に第一座標射影。 -/
theorem factor : comparisonFactor qc qf coarser = Prod.fst := by
  symm
  exact comparisonFactor_unique qc qf coarser Prod.fst (fun _ => rfl)
/-- 指定された一つの非定数Law。 -/
def laws : FiniteLawFamily Source where
  Law := Unit
  lawFintype := inferInstance
  Value _ := Bool
  valueDecidableEq _ := inferInstance
  eval _ := Prod.fst
/-- 粗readingのadequacyを原始評価から生成する。 -/
theorem adequate_coarse : laws.Adequate qc := fun _ => ⟨id, fun _ => rfl⟩
/-- 細readingのadequacyを同じ原始Law評価から生成する。 -/
theorem adequate_fine : laws.Adequate qf :=
  fun _ => ⟨Prod.fst, fun _ => rfl⟩
/-- Law非定数性の同じSource上の証人。 -/
theorem law_nonconstant : ∃ l s t, laws.eval l s ≠ laws.eval l t :=
  ⟨(), (false, false), (true, false), by decide⟩
/-- 各実Sourceから二つの発生ラベルを保持する。 -/
def label (a : Bool) : LawValueLabel laws := LawValueLabel.ofSource laws () (a, false)
/-- 実際のLaw値が異なる発生ラベルは異なる。 -/
theorem labels_ne : label false ≠ label true := by
  intro h
  have hv := congrArg LawValueLabel.value h
  exact Bool.false_ne_true hv

end AAT.AG.AtlasCoefficientFiber.WitnessCommon
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessCommon.Source
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessCommon.qc
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessCommon.qf
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessCommon.coarser
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessCommon.not_coarser
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessCommon.factor
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessCommon.laws
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessCommon.adequate_coarse
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessCommon.adequate_fine
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessCommon.law_nonconstant
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessCommon.label
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessCommon.labels_ne
#assert_standard_axioms_only AAT.AG.AtlasCoefficientFiber.WitnessCommon
