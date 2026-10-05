import ResearchLean.AG.AtlasDefectComposition.SupportReconstruction
import ResearchLean.AG.AtlasDefectComposition.GeneratedDefect
import Mathlib.Data.Fin.VecNotation
import Formal.Util.AssertStandardAxioms
/-! # W2 の同一原始入力

三点 Source の恒等 reading と Law、二つの名付き孤立 chart を固定する。
chart の支持は {a,b} と {c} であり、比較も原始恒等である。
-/
noncomputable section
namespace AAT.AG.AtlasDefectComposition.WitnessTwo
open CanonicalResolution ResolutionInvariance Cohomology TwoPhase
/-- W2 の原始三点 Source。 -/
abbrev Source := Fin 3
/-- W2 の reading は Source の恒等写像である。 -/
abbrev q : Reading Source where
  Target := Source
  read := id
  surjective := Function.surjective_id
/-- W2 の比較は同じ reading を読む。 -/
theorem coarser : q.CoarserThan q := by
  intro x y h
  exact h
/-- 二つの名付き chart と空 edge・face からなる原始 nerve。 -/
abbrev nerve : CoverNerve where
  Chart := Bool
  EdgeComponent := Empty
  FaceComponent := Empty
  edgeLeft := Empty.elim
  edgeRight := Empty.elim
  faceEdge0 := Empty.elim
  faceEdge1 := Empty.elim
  faceEdge2 := Empty.elim
  edgeOverlapComponent := Empty.elim
  faceTripleOverlapComponent := Empty.elim
  edgeOverlapComponent_holds := fun e => e.elim
  faceTripleOverlapComponent_holds := fun f => f.elim
/-- false chart は {a,b}、true chart は {c} を支持する。 -/
abbrev support (c : Bool) : Set Source := if c then {2} else {0,1}
/-- 指定二 chart の支持入力。支持の非空性は原始点で証明する。 -/
abbrev N : TargetSupportedNerve q where
  nerve := nerve
  chartSupport := support
  chartSupport_nonempty c := by cases c; exact ⟨0,by simp [support]⟩; exact ⟨2,by simp [support]⟩
  faceEdge0_left := fun f => f.elim
  faceEdge0_right := fun f => f.elim
  faceEdge1_right := fun f => f.elim
/-- W2 の原始恒等セル比較。 -/
def M : TargetSupportedNerveMorphism q q coarser N N :=
  TargetSupportedNerveMorphism.identityMorphism q N
/-- W2 の一つの Law は恒等評価で、三つの値は実 Source から発生する。 -/
def laws : FiniteLawFamily Source where
  Law := Unit
  lawFintype := inferInstance
  Value _ := Source
  valueDecidableEq _ := inferInstance
  eval _ x := x
/-- 恒等 Law の adequacy は原始恒等因子化から得られる。 -/
theorem adequate : laws.Adequate q := fun _ => ⟨id,fun _ => rfl⟩
/-- 同じ reading の因子は実 Source の恒等写像である。 -/
@[simp] theorem factor_self (t : Source) : comparisonFactor q q coarser t = t :=
  comparisonFactor_commutes q q coarser t
/-- W2 の粗細全六種類の実セル族。 -/
abbrev family := SupportSignature.family N N coarser
/-- W2 の実全セル選択。 -/
abbrev alpha := SupportSignature.alpha N N coarser
/-- W2 の全名付きセル署名。 -/
abbrev sigma := SupportSignature.sigma N N coarser
end AAT.AG.AtlasDefectComposition.WitnessTwo
#assert_standard_axioms_only AAT.AG.AtlasDefectComposition.WitnessTwo
