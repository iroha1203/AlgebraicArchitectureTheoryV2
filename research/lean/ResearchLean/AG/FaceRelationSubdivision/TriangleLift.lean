import ResearchLean.AG.FaceRelationSubdivision.TriangleContraction
import ResearchLean.AG.FaceRelationSubdivision.LiftVariation

/-!
# 三角形追加で指定した二つの道の持ち上げ

## Implementation notes

原始補正は旧eを追加fへ送るだけ。支持はK1の同じ辺・面台から導く。
新sectionは原始有限和で定め、既存収縮からの補正式と全Aで一致させる。
-/
noncomputable section
open scoped Classical
namespace AAT.AG.FaceRelationSubdivision
open CanonicalResolution ResolutionInvariance TwoPhase AtlasDefectComposition
universe u
variable {Source : Type u} {q : Reading Source}
namespace TriangleAddition
variable (N : TargetSupportedNerve q) (e : N.nerve.EdgeComponent)

/-- 旧eの補正を新fへ送る原始像。他の旧辺では零。 -/
def liftT : SupportedBasisMap N.edgeSupport (supported N e).faceSupport := by
  classical
  exact SupportedBasisMap.ofOption
    (fun a => if a = e then some (.inr PUnit.unit) else none) (by
      intro a F h t ht
      dsimp only at h
      split_ifs at h with ha
      · subst a; cases Option.some.inj h
        rw [faceSupport_new]; exact ht
      )

/-- 指定した補正基底像。 -/
@[simp] theorem liftT_basis (a : N.nerve.EdgeComponent) :
    (liftT N e).basisImage a = if a = e then (Finsupp.single (.inr PUnit.unit) 1 :
      (supported N e).nerve.FaceComponent →₀ ℚ) else 0 := by
  classical
  simp only [liftT, SupportedBasisMap.ofOption_basis]
  split_ifs <;> rfl

/-- 変更sectionの辺の原始有限和。 -/
def liftedS1 := (s1 N e).add ((liftT N e).comp (TargetSupportedNerve.rawD2 (supported N e)))
/-- 変更sectionの面の原始有限和。 -/
def liftedS2 := (s2 N e).add ((TargetSupportedNerve.rawD2 N).comp (liftT N e))

/-- 辺sectionは指定したs+∂tそのもの。 -/
theorem liftedS1_raw : (liftedS1 N e).raw = (s1 N e).raw +
    (TargetSupportedNerve.rawD2 (supported N e)).raw.comp (liftT N e).raw := by
  rw [liftedS1, SupportedBasisMap.raw_add, SupportedBasisMap.raw_comp]
/-- 面sectionは指定したs+t∂そのもの。 -/
theorem liftedS2_raw : (liftedS2 N e).raw = (s2 N e).raw +
    (liftT N e).raw.comp (TargetSupportedNerve.rawD2 N).raw := by
  rw [liftedS2, SupportedBasisMap.raw_add, SupportedBasisMap.raw_comp]

/-- 辺の変更sectionの基底像は原始二射の和。 -/
@[simp] theorem liftedS1_basis (a : N.nerve.EdgeComponent) :
    (liftedS1 N e).basisImage a = (s1 N e).basisImage a +
      (TargetSupportedNerve.rawD2 (supported N e)).raw ((liftT N e).basisImage a) := rfl
/-- 面の変更sectionの基底像は原始二射の和。 -/
@[simp] theorem liftedS2_basis_image (F : N.nerve.FaceComponent) :
    (liftedS2 N e).basisImage F = (s2 N e).basisImage F +
      (liftT N e).raw ((TargetSupportedNerve.rawD2 N).basisImage F) := rfl

/-- 辺sectionの支持制限も原始二射の和。 -/
@[simp] theorem liftedS1_selected (A : Set q.Target) :
    (liftedS1 N e).selected A = (s1 N e).selected A +
      (chainD2 (supported N e) A).comp ((liftT N e).selected A) := by
  simp only [liftedS1, SupportedBasisMap.selected_add, SupportedBasisMap.selected_comp,
    TargetSupportedNerve.selected_rawD2]
/-- 面sectionの支持制限も原始二射の和。 -/
@[simp] theorem liftedS2_selected (A : Set q.Target) :
    (liftedS2 N e).selected A = (s2 N e).selected A +
      ((liftT N e).selected A).comp (chainD2 N A) := by
  simp only [liftedS2, SupportedBasisMap.selected_add, SupportedBasisMap.selected_comp,
    TargetSupportedNerve.selected_rawD2]

/-- 指定旧辺の原始sectionはc+e2。 -/
theorem liftedS1_target_basis : (liftedS1 N e).basisImage e =
    Finsupp.single (.inr false) 1 + Finsupp.single (.inr true) 1 := by
  rw [liftedS1_basis, s1_basis, liftT_basis]
  simp only
  let old : (supported N e).nerve.EdgeComponent →₀ ℚ := Finsupp.single (.inl e) 1
  let c : (supported N e).nerve.EdgeComponent →₀ ℚ := Finsupp.single (.inr false) 1
  let b : (supported N e).nerve.EdgeComponent →₀ ℚ := Finsupp.single (.inr true) 1
  have h := SupportedBasisMap.raw_single (TargetSupportedNerve.rawD2 (supported N e))
    (.inr PUnit.unit) (1 : ℚ)
  simp only [one_smul, TargetSupportedNerve.rawD2_basis, faceEdge0_new, faceEdge1_new,
    faceEdge2_new] at h
  change old + (TargetSupportedNerve.rawD2 (supported N e)).raw
    (Finsupp.single (.inr PUnit.unit) 1) = c + b
  calc
    _ = old + (c - old + b) := congrArg (fun x => old + x) h
    _ = _ := by abel

/-- 旧面上のsectionは三つの符号位置の指定補正。重複も三回評価する。 -/
theorem liftedS2_basis (F : N.nerve.FaceComponent) :
    (liftedS2 N e).basisImage F = Finsupp.single (.inl F) 1 +
      (liftT N e).basisImage (N.nerve.faceEdge0 F) -
      (liftT N e).basisImage (N.nerve.faceEdge1 F) +
      (liftT N e).basisImage (N.nerve.faceEdge2 F) := by
  simp only [liftedS2_basis_image,
    s2_basis, TargetSupportedNerve.rawD2_basis, map_add, map_sub,
    SupportedBasisMap.raw_single, one_smul]
  abel

/-- 補正fはcollapseで零へ写る。 -/
theorem liftT_r2_zero : (r2 N e).raw.comp (liftT N e).raw = 0 := by
  classical
  apply Finsupp.lhom_ext
  intro a x
  simp only [LinearMap.comp_apply, SupportedBasisMap.raw_single, liftT_basis]
  split_ifs <;> simp [SupportedBasisMap.raw_single, Finsupp.smul_single]

/-- 同じ零式を任意支持へ制限する。 -/
theorem liftT_selected_r2_zero (A : Set q.Target) :
    ((chainContraction N e A).r2).comp ((liftT N e).selected A) = 0 := by
  rw [chainContraction_r2]
  apply LinearMap.ext
  intro x
  apply selectedEmbed_injective N.faceSupport A
  change selectedEmbed N.faceSupport A ((r2 N e).selected A ((liftT N e).selected A x)) =
    selectedEmbed N.faceSupport A 0
  rw [SupportedBasisMap.selectedEmbed_apply, SupportedBasisMap.selectedEmbed_apply, map_zero]
  exact LinearMap.congr_fun (liftT_r2_zero N e) (selectedEmbed N.edgeSupport A x)

/-- 原始支持補正から生成した新sectionを持つ収縮。 -/
def liftedContraction (A : Set q.Target) :=
  (chainContraction N e A).varyLift ((liftT N e).selected A) (liftT_selected_r2_zero N e A)

/-- 変更収縮の構成式。 -/
@[simp] theorem liftedContraction_eq (A : Set q.Target) :
    liftedContraction N e A = (chainContraction N e A).varyLift
      ((liftT N e).selected A) (liftT_selected_r2_zero N e A) := rfl

/-- 変更収縮の辺sectionは同じ原始有限和の支持制限。 -/
theorem liftedContraction_s1 (A : Set q.Target) :
    (liftedContraction N e A).s1 = (liftedS1 N e).selected A := by
  rw [liftedContraction_eq, SubsetChainContraction.varyLift_s1, chainContraction_s1]
  rw [liftedS1_selected]
/-- 変更収縮の面sectionも同じ原始有限和の支持制限。 -/
theorem liftedContraction_s2 (A : Set q.Target) :
    (liftedContraction N e A).s2 = (liftedS2 N e).selected A := by
  rw [liftedContraction_eq, SubsetChainContraction.varyLift_s2, chainContraction_s2]
  rw [liftedS2_selected]

/-- 持ち上げ変更は同じ実収縮比較を保持する。 -/
@[simp] theorem liftedContraction_rHom (A : Set q.Target) :
    (liftedContraction N e A).rHom = rHom N e A := by
  rw [liftedContraction_eq, SubsetChainContraction.varyLift_rHom, chainContraction_rHom]

/-- 指定持ち上げ間の標準ホモトピーは同じ二つの実section Homを結ぶ。 -/
def liftedHomotopy (A : Set q.Target) : Homotopy
    (zeroExtensionMap (liftedContraction N e A).sHom) (zeroExtensionMap (sHom N e A)) := by
  rw [liftedContraction_eq, ← chainContraction_sHom]
  exact (chainContraction N e A).liftHomotopy ((liftT N e).selected A)
    (liftT_selected_r2_zero N e A)

/-- 指定持ち上げの実読み戻しは全標準次数で元のsectionと同じ。 -/
theorem liftedContraction_homologyMap (A : Set q.Target) (n : ℤ) :
    HomologicalComplex.homologyMap (zeroExtensionMap (liftedContraction N e A).sHom) n =
      HomologicalComplex.homologyMap (zeroExtensionMap (sHom N e A)) n := by
  rw [liftedContraction_eq, SubsetChainContraction.varyLift_homologyMap, chainContraction_sHom]

/-- 変更した実sectionのH1読み戻しは同じ旧包含sHomの射。 -/
theorem liftedContraction_h1Map (A : Set q.Target) :
    (liftedContraction N e A).sHom.h1Map = (sHom N e A).h1Map := by
  rw [liftedContraction_eq, SubsetChainContraction.varyLift_h1Map, chainContraction_sHom]

end TriangleAddition
end AAT.AG.FaceRelationSubdivision
#assert_standard_axioms_only AAT.AG.FaceRelationSubdivision
