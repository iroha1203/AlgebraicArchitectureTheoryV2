import ResearchLean.AG.AtlasDefectComposition.SupportReconstruction
import ResearchLean.AG.AtlasDefectComposition.EmptySubset
import Formal.Util.AssertStandardAxioms
/-! # 零署名からの実 block 零性

Implementation notes: 全六種類のセル署名が空という結論を各実 subtype へ評価する。
元の target subset が空という仮定は置かず、非空の unsupported subset も扱う。
-/
noncomputable section
open CategoryTheory CategoryTheory.Limits HomologicalComplex CochainComplex
namespace AAT.AG.AtlasDefectComposition.SupportZeroBlock
open CanonicalResolution ResolutionInvariance TwoPhase
universe u
variable {Source : Type u} {q r : Reading Source}
variable (N : TargetSupportedNerve q) (E : TargetSupportedNerve r) (h : q.CoarserThan r)
variable {A : Set q.Target} (hz : SupportSignature.sigma N E h A = ⊥)
include hz
/-- 零署名は全粗細セル選択が空であることを意味する。 -/
theorem alpha_empty : SupportSignature.alpha N E h A = ∅ := by
  have hh := congrArg Subtype.val hz
  simpa only [SignatureGeometry.sigma_val,SignatureGeometry.signature_bot_val] using hh
/-- 零署名は coarse chart の実選択 subtype が空であることを放電する。 -/
theorem coarseChartIsEmpty : IsEmpty (N.ChartInTargetSubset A) := ⟨fun c => by
  have hc := (SupportSignature.mem_alpha_coarseChart N E h A c.1).mpr c.2
  rw [alpha_empty N E h hz] at hc
  exact hc⟩
/-- 零署名は coarse edge の実選択 subtype が空であることを放電する。 -/
theorem coarseEdgeIsEmpty : IsEmpty (N.EdgeInTargetSubset A) := ⟨fun c => by
  have hc := (SupportSignature.mem_alpha_coarseEdge N E h A c.1).mpr c.2
  rw [alpha_empty N E h hz] at hc
  exact hc⟩
/-- 零署名は coarse face の実選択 subtype が空であることを放電する。 -/
theorem coarseFaceIsEmpty : IsEmpty (N.FaceInTargetSubset A) := ⟨fun c => by
  have hc := (SupportSignature.mem_alpha_coarseFace N E h A c.1).mpr c.2
  rw [alpha_empty N E h hz] at hc
  exact hc⟩
/-- 零署名は fine chart の実選択 subtype が空であることを放電する。 -/
theorem fineChartIsEmpty : IsEmpty (E.ChartInTargetSubset (comparisonFactor q r h ⁻¹' A)) := ⟨fun c => by
  have hc := (SupportSignature.mem_alpha_fineChart N E h A c.1).mpr c.2
  rw [alpha_empty N E h hz] at hc
  exact hc⟩
/-- 零署名は fine edge の実選択 subtype が空であることを放電する。 -/
theorem fineEdgeIsEmpty : IsEmpty (E.EdgeInTargetSubset (comparisonFactor q r h ⁻¹' A)) := ⟨fun c => by
  have hc := (SupportSignature.mem_alpha_fineEdge N E h A c.1).mpr c.2
  rw [alpha_empty N E h hz] at hc
  exact hc⟩
/-- 零署名は fine face の実選択 subtype が空であることを放電する。 -/
theorem fineFaceIsEmpty : IsEmpty (E.FaceInTargetSubset (comparisonFactor q r h ⁻¹' A)) := ⟨fun c => by
  have hc := (SupportSignature.mem_alpha_fineFace N E h A c.1).mpr c.2
  rw [alpha_empty N E h hz] at hc
  exact hc⟩
/-- 零署名は coarse の実標準零延長が全整数次数で零であることを放電する。 -/
theorem coarse_isZero_X (m : ℤ) : IsZero ((zeroExtension (N.targetSubsetComplex A)).X m) := by
  letI := coarseChartIsEmpty N E h hz
  letI := coarseEdgeIsEmpty N E h hz
  letI := coarseFaceIsEmpty N E h hz
  letI : Subsingleton (N.targetSubsetComplex A).C0 := by
    change Subsingleton (N.ChartInTargetSubset A → ℚ)
    infer_instance
  letI : Subsingleton (N.targetSubsetComplex A).C1 := by
    change Subsingleton (N.EdgeInTargetSubset A → ℚ)
    infer_instance
  letI : Subsingleton (N.targetSubsetComplex A).C2 := by
    change Subsingleton (N.FaceInTargetSubset A → ℚ)
    infer_instance
  exact zeroExtension_isZero_X m
/-- 零署名の coarse 各次数加群の実零性。 -/
theorem coarse_subsingleton_X (m : ℤ) : Subsingleton ((zeroExtension (N.targetSubsetComplex A)).X m) :=
  ModuleCat.subsingleton_of_isZero (coarse_isZero_X N E h hz m)
/-- 零署名は fine の実標準零延長が全整数次数で零であることを放電する。 -/
theorem fine_isZero_X (m : ℤ) : IsZero ((zeroExtension (E.targetSubsetComplex (comparisonFactor q r h ⁻¹' A))).X m) := by
  letI := fineChartIsEmpty N E h hz
  letI := fineEdgeIsEmpty N E h hz
  letI := fineFaceIsEmpty N E h hz
  letI : Subsingleton (E.targetSubsetComplex (comparisonFactor q r h ⁻¹' A)).C0 := by
    change Subsingleton (E.ChartInTargetSubset (comparisonFactor q r h ⁻¹' A) → ℚ)
    infer_instance
  letI : Subsingleton (E.targetSubsetComplex (comparisonFactor q r h ⁻¹' A)).C1 := by
    change Subsingleton (E.EdgeInTargetSubset (comparisonFactor q r h ⁻¹' A) → ℚ)
    infer_instance
  letI : Subsingleton (E.targetSubsetComplex (comparisonFactor q r h ⁻¹' A)).C2 := by
    change Subsingleton (E.FaceInTargetSubset (comparisonFactor q r h ⁻¹' A) → ℚ)
    infer_instance
  exact zeroExtension_isZero_X m
/-- 零署名の fine 各次数加群の実零性。 -/
theorem fine_subsingleton_X (m : ℤ) : Subsingleton ((zeroExtension (E.targetSubsetComplex (comparisonFactor q r h ⁻¹' A))).X m) :=
  ModuleCat.subsingleton_of_isZero (fine_isZero_X N E h hz m)
variable (M : TargetSupportedNerveMorphism q r h N E)
/-- 零署名の実比較錐も全整数次数で零である。 -/
theorem cone_isZero_X (m : ℤ) : IsZero ((mappingCone (zeroExtensionMap (M.aSubnerveComparisonHom A))).X m) :=
  (mappingCone.isZero_X_iff _ m).mpr ⟨coarse_isZero_X N E h hz (m+1),fine_isZero_X N E h hz m⟩
/-- 零署名の実比較錐の各次数加群の零性。 -/
theorem cone_subsingleton_X (m : ℤ) : Subsingleton ((mappingCone (zeroExtensionMap (M.aSubnerveComparisonHom A))).X m) :=
  ModuleCat.subsingleton_of_isZero (cone_isZero_X N E h hz M m)
end AAT.AG.AtlasDefectComposition.SupportZeroBlock
#assert_standard_axioms_only AAT.AG.AtlasDefectComposition.SupportZeroBlock
