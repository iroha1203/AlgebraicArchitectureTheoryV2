import ResearchLean.AG.FaceRelationSubdivision.IncidenceComparison
import ResearchLean.AG.ResolutionInvariance.DegenerateFaceComm1Obstruction
import Formal.Util.AssertStandardAxioms

/-!
# 端点条件だけでは原始incidenceを満たさない

G-134 Aの指定失敗例。既存comm1反例と同じセル表を自由ℤ加群で評価する。
-/

noncomputable section
namespace AAT.AG.FaceRelationSubdivision
open ResolutionInvariance

/-- 既存comm1反例の三重loop像の符号付き和は零でない。 -/
theorem degenerateFace_primitive_incidence_fails :
    let N := DegenerateFaceComm1Obstruction.fineNerve
    let r := DegenerateFaceComm1Obstruction.edgeMap
    optionCell (r (N.faceEdge0 PUnit.unit)) -
      optionCell (r (N.faceEdge1 PUnit.unit)) +
      optionCell (r (N.faceEdge2 PUnit.unit)) ≠ 0 := by
  dsimp only
  intro h
  have he := congrArg (fun x => x PUnit.unit) h
  norm_num [DegenerateFaceComm1Obstruction.fineNerve,
    DegenerateFaceComm1Obstruction.edgeMap, optionCell] at he

/-- 同じ原始セル表を新しい比較として提示することはできない。 -/
theorem no_incidenceComparison_with_obstruction_maps :
    ¬ ∃ M : IncidenceSupportedComparison
      DegenerateFaceComm1Obstruction.coarseReading
      DegenerateFaceComm1Obstruction.fineReading
      DegenerateFaceComm1Obstruction.coarse_coarser_fine
      DegenerateFaceComm1Obstruction.coarseSupported
      DegenerateFaceComm1Obstruction.fineSupported,
      M.edgeMap = DegenerateFaceComm1Obstruction.edgeMap ∧
        M.faceMap = DegenerateFaceComm1Obstruction.faceMap := by
  rintro ⟨M, he, hf⟩
  have h := M.face_none_incidence PUnit.unit (by rw [hf]; rfl)
  rw [he] at h
  exact degenerateFace_primitive_incidence_fails h

end AAT.AG.FaceRelationSubdivision
#print axioms AAT.AG.FaceRelationSubdivision.degenerateFace_primitive_incidence_fails
#print axioms AAT.AG.FaceRelationSubdivision.no_incidenceComparison_with_obstruction_maps
#assert_standard_axioms_only AAT.AG.FaceRelationSubdivision
