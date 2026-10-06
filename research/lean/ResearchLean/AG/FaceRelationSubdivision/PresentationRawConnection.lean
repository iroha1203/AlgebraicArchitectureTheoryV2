import ResearchLean.AG.FaceRelationSubdivision.PresentationRawEquivalence
import ResearchLean.AG.FaceRelationSubdivision.RawLawHomotopy
import ResearchLean.AG.FaceRelationSubdivision.LawFiniteOption
import ResearchLean.AG.FaceRelationSubdivision.LawPresentation

/-!
# 有限列表示の同じ原始実Law比較と新混在比較

## Implementation notes

原始名前全単射の単一非零項を評価し、同じセル・発生ラベルで
候補08の独立生成比較と全三成分で照合する。表示の存在だけを根拠にはしない。
-/
noncomputable section
open CategoryTheory
namespace AAT.AG.FaceRelationSubdivision
open CanonicalResolution ResolutionInvariance TwoPhase AtlasDefectComposition
universe u
variable {Source : Type u} [Fintype Source] {qc qf : Reading Source} {h : qc.CoarserThan qf}
variable {Nc : TargetSupportedNerve qc} {Nf : TargetSupportedNerve qf}
namespace CellPresentationEquiv
variable (E : CellPresentationEquiv qc qf h Nc Nf)
variable (laws : FiniteLawFamily Source) (hc : laws.Adequate qc)

/-- 原始表示の独立Law有限和は同じ新混在比較の実Hom。 -/
theorem rawEquivalence_lawR_eq_generated :
    E.rawEquivalence.lawR laws hc (fineAdequate (h := h) laws hc) =
      E.comparison.generatedComparisonHom laws hc (fineAdequate (h := h) laws hc) := by
  apply cochain_ext
  · apply LinearMap.ext; intro z
    funext x
    rw [RawChainEquivalence.lawR_f0, E.rawEquivalence_r0]
    refine (E.sourceR0.mixedLawDual_apply_single (qi := qf) (qj := qc)
        (si := Nf.chartSupport) (sj := Nc.chartSupport) laws (fineAdequate (h := h) laws hc) hc z x
        (E.chartEquiv x.cell) (E.sourceR0_basis x.cell)).trans ?_
    rw [IncidenceSupportedComparison.generatedComparisonHom_f0]
    refine Eq.trans ?_ (E.comparison.generatedPullback0_apply laws hc (fineAdequate (h := h) laws hc) z x).symm
    apply congrArg z
    apply coordinate_eq_of_cell_label laws hc
    · rw [SupportedBasisMap.mixedLawCoordinate_cell,
        IncidenceSupportedComparison.chartCoordinateMap_cell, E.comparison_chart]
    · exact (E.sourceR0.mixedLawCoordinate_label (qi := qf) (qj := qc)
        (si := Nf.chartSupport) (sj := Nc.chartSupport) laws (fineAdequate (h := h) laws hc) hc x _ _).trans
        (E.comparison.chartCoordinateMap_lawValueLabel laws hc (fineAdequate (h := h) laws hc) x).symm
  · apply LinearMap.ext; intro z
    funext x
    rw [RawChainEquivalence.lawR_f1, E.rawEquivalence_r1]
    refine (E.sourceR1.mixedLawDual_apply_single (qi := qf) (qj := qc)
        (si := Nf.edgeSupport) (sj := Nc.edgeSupport) laws (fineAdequate (h := h) laws hc) hc z x
        (E.edgeEquiv x.cell) (E.sourceR1_basis x.cell)).trans ?_
    rw [IncidenceSupportedComparison.generatedComparisonHom_f1]
    refine Eq.trans ?_ (E.comparison.generatedPullback1_apply laws hc (fineAdequate (h := h) laws hc) z x).symm
    rw [E.comparison.edgeCoordinateMapOption_eq_some laws hc (fineAdequate (h := h) laws hc)
      x (E.edgeEquiv x.cell) (E.comparison_edge x.cell), Option.elim_some]
    apply congrArg z
    apply coordinate_eq_of_cell_label laws hc
    · rw [SupportedBasisMap.mixedLawCoordinate_cell,
        IncidenceSupportedComparison.edgeCoordinateMap_cell]
    · exact (E.sourceR1.mixedLawCoordinate_label (qi := qf) (qj := qc)
        (si := Nf.edgeSupport) (sj := Nc.edgeSupport) laws (fineAdequate (h := h) laws hc) hc x _ _).trans
        (E.comparison.edgeCoordinateMap_lawValueLabel laws hc (fineAdequate (h := h) laws hc) x (E.edgeEquiv x.cell) (E.comparison_edge x.cell)).symm
  · apply LinearMap.ext; intro z
    funext x
    rw [RawChainEquivalence.lawR_f2, E.rawEquivalence_r2]
    refine (E.sourceR2.mixedLawDual_apply_single (qi := qf) (qj := qc)
        (si := Nf.faceSupport) (sj := Nc.faceSupport) laws (fineAdequate (h := h) laws hc) hc z x
        (E.faceEquiv x.cell) (E.sourceR2_basis x.cell)).trans ?_
    rw [IncidenceSupportedComparison.generatedComparisonHom_f2]
    refine Eq.trans ?_ (E.comparison.generatedPullback2_apply laws hc (fineAdequate (h := h) laws hc) z x).symm
    rw [E.comparison.faceCoordinateMapOption_eq_some laws hc (fineAdequate (h := h) laws hc)
      x (E.faceEquiv x.cell) (E.comparison_face x.cell), Option.elim_some]
    apply congrArg z
    apply coordinate_eq_of_cell_label laws hc
    · rw [SupportedBasisMap.mixedLawCoordinate_cell,
        IncidenceSupportedComparison.faceCoordinateMap_cell]
    · exact (E.sourceR2.mixedLawCoordinate_label (qi := qf) (qj := qc)
        (si := Nf.faceSupport) (sj := Nc.faceSupport) laws (fineAdequate (h := h) laws hc) hc x _ _).trans
        (E.comparison.faceCoordinateMap_lawValueLabel laws hc (fineAdequate (h := h) laws hc) x (E.faceEquiv x.cell) (E.comparison_face x.cell)).symm

/-- 同じ表示有限列順射の零延長は受理済み実表示同型の順射。 -/
theorem rawEquivalence_lawR_zeroExtension :
    zeroExtensionMap (E.rawEquivalence.lawR laws hc (fineAdequate (h := h) laws hc)) =
      (E.lawZeroExtensionIso laws hc).hom := by
  rw [rawEquivalence_lawR_eq_generated, E.lawZeroExtensionIso_hom]

/-- 原始表示有限和の同じ実Law順逆往復は粗側恒等。 -/
theorem rawEquivalence_lawRS :
    cochainComp (E.rawEquivalence.lawR laws hc (fineAdequate (h := h) laws hc))
      (E.rawEquivalence.lawS laws hc (fineAdequate (h := h) laws hc)) =
        cochainId (Nc.lawGeneratedComplex laws hc) := by
  apply cochain_ext
  · apply LinearMap.ext; intro z
    rw [cochainComp_f0, cochainId_f0, RawChainEquivalence.lawR_f0, RawChainEquivalence.lawS_f0,
      E.rawEquivalence_r0, E.rawEquivalence_s0]
    have he := (E.sourceS0.comp E.sourceR0).mixedLawDual_eq_of_raw_eq
      (qi := qc) (qj := qc) (si := Nc.chartSupport) (sj := Nc.chartSupport)
      laws hc hc (SupportedBasisMap.identity (sourceSupport qc Nc.chartSupport)) (by
        rw [SupportedBasisMap.raw_comp, SupportedBasisMap.raw_identity]
        exact E.sourceRS0)
    rw [E.sourceS0.mixedLawDual_comp laws hc (fineAdequate (h := h) laws hc) E.sourceR0 hc,
      SupportedBasisMap.mixedLawDual_identity] at he
    exact LinearMap.congr_fun he z
  · apply LinearMap.ext; intro z
    rw [cochainComp_f1, cochainId_f1, RawChainEquivalence.lawR_f1, RawChainEquivalence.lawS_f1,
      E.rawEquivalence_r1, E.rawEquivalence_s1]
    have he := (E.sourceS1.comp E.sourceR1).mixedLawDual_eq_of_raw_eq
      (qi := qc) (qj := qc) (si := Nc.edgeSupport) (sj := Nc.edgeSupport)
      laws hc hc (SupportedBasisMap.identity (sourceSupport qc Nc.edgeSupport)) (by
        rw [SupportedBasisMap.raw_comp, SupportedBasisMap.raw_identity]
        exact E.sourceRS1)
    rw [E.sourceS1.mixedLawDual_comp laws hc (fineAdequate (h := h) laws hc) E.sourceR1 hc,
      SupportedBasisMap.mixedLawDual_identity] at he
    exact LinearMap.congr_fun he z
  · apply LinearMap.ext; intro z
    rw [cochainComp_f2, cochainId_f2, RawChainEquivalence.lawR_f2, RawChainEquivalence.lawS_f2,
      E.rawEquivalence_r2, E.rawEquivalence_s2]
    have he := (E.sourceS2.comp E.sourceR2).mixedLawDual_eq_of_raw_eq
      (qi := qc) (qj := qc) (si := Nc.faceSupport) (sj := Nc.faceSupport)
      laws hc hc (SupportedBasisMap.identity (sourceSupport qc Nc.faceSupport)) (by
        rw [SupportedBasisMap.raw_comp, SupportedBasisMap.raw_identity]
        exact E.sourceRS2)
    rw [E.sourceS2.mixedLawDual_comp laws hc (fineAdequate (h := h) laws hc) E.sourceR2 hc,
      SupportedBasisMap.mixedLawDual_identity] at he
    exact LinearMap.congr_fun he z

/-- 同じ独立実Law逆射の零延長は受理済み表示同型の逆そのもの。 -/
theorem rawEquivalence_lawS_zeroExtension :
    zeroExtensionMap (E.rawEquivalence.lawS laws hc (fineAdequate (h := h) laws hc)) =
      (E.lawZeroExtensionIso laws hc).inv := by
  apply (cancel_epi (E.lawZeroExtensionIso laws hc).hom).mp
  rw [Iso.hom_inv_id, ← rawEquivalence_lawR_zeroExtension, ← zeroExtensionMap_comp,
    E.rawEquivalence_lawRS, zeroExtensionMap_id]

end CellPresentationEquiv
end AAT.AG.FaceRelationSubdivision
#assert_standard_axioms_only AAT.AG.FaceRelationSubdivision
