import ResearchLean.AG.FaceRelationSubdivision.OperationPathComposition
import ResearchLean.AG.FaceRelationSubdivision.OperationPathMaps
import ResearchLean.AG.FaceRelationSubdivision.RawMapComposition
import ResearchLean.AG.AtlasDefectComposition.ConeCompositionTriangle

/-!
# 原始有限列の実射恒等・連結と同じ合成錐triangle

## Implementation notes

原始有限列の直接出力から実射を生成した後で段階射の合成等号を証明する。
空列も全三成分で同じ実恒等へ接続する。合成錐のmiddleはこの直接射を保持する。
-/
noncomputable section
open CategoryTheory Limits CochainComplex Pretriangulated
namespace AAT.AG.FaceRelationSubdivision
open CanonicalResolution ResolutionInvariance TwoPhase AtlasDefectComposition
universe u
variable {Source : Type u} {qc qm qf : Reading Source}
variable {Nc : TargetSupportedNerve qc} {Nm : TargetSupportedNerve qm} {Nf : TargetSupportedNerve qf}
namespace PrimitiveOperationPath

/-- 空列の全A選択は元のA。 -/
@[simp] theorem targetSubset_nil (N : TargetSupportedNerve qc) (A : Set qc.Target) :
    (nil N).targetSubset A = A := by
  ext t
  obtain ⟨x, rfl⟩ := qc.surjective t
  simp only [targetSubset_eq_preimage, Set.mem_preimage, comparisonFactor_commutes]

/-- 任意二列の支持選択は同じ因子逆像の合成。 -/
theorem targetSubset_append (P : PrimitiveOperationPath qc Nc qm Nm)
    (Q : PrimitiveOperationPath qm Nm qf Nf) (A : Set qc.Target) :
    (P.append Q).targetSubset A = Q.targetSubset (P.targetSubset A) := by
  ext t
  obtain ⟨x, rfl⟩ := qf.surjective t
  simp only [targetSubset_eq_preimage, Set.mem_preimage, comparisonFactor_commutes]

variable (P : PrimitiveOperationPath qc Nc qm Nm) (Q : PrimitiveOperationPath qm Nm qf Nf)
variable [Fintype Source] (laws : FiniteLawFamily Source) (ha : laws.Adequate qc)

/-- 連結列の直接Law順射は全三成分で段階射の同じ合成。 -/
theorem lawR_append : (P.append Q).lawR laws ha =
    cochainComp (P.lawR laws ha) (Q.lawR laws (P.adequate laws ha)) := by
  rw [lawR_eq_raw, rawEquivalence_append, lawR_eq_raw, lawR_eq_raw]
  exact P.rawEquivalence.lawR_trans Q.rawEquivalence laws ha
    (P.adequate laws ha) ((P.append Q).adequate laws ha)

/-- 連結列の直接Law逆射は全三成分で逆順合成。 -/
theorem lawS_append : (P.append Q).lawS laws ha =
    cochainComp (Q.lawS laws (P.adequate laws ha)) (P.lawS laws ha) := by
  rw [lawS_eq_raw, rawEquivalence_append, lawS_eq_raw, lawS_eq_raw]
  exact P.rawEquivalence.lawS_trans Q.rawEquivalence laws ha
    (P.adequate laws ha) ((P.append Q).adequate laws ha)

/-- 同じ直接Law順射の既存H1は段階射の合成。 -/
theorem lawR_append_h1 : ((P.append Q).lawR laws ha).h1Map =
    (Q.lawR laws (P.adequate laws ha)).h1Map.comp (P.lawR laws ha).h1Map := by
  rw [lawR_append, cochainComp_h1Map]
/-- 同じ直接Law逆射の既存H1は逆順合成。 -/
theorem lawS_append_h1 : ((P.append Q).lawS laws ha).h1Map =
    (P.lawS laws ha).h1Map.comp (Q.lawS laws (P.adequate laws ha)).h1Map := by
  rw [lawS_append, cochainComp_h1Map]

/-- 同じ直接Law順射の標準零延長は段階射の合成。 -/
theorem lawR_append_zeroExtension : zeroExtensionMap ((P.append Q).lawR laws ha) =
    zeroExtensionMap (P.lawR laws ha) ≫ zeroExtensionMap (Q.lawR laws (P.adequate laws ha)) := by
  rw [lawR_append, zeroExtensionMap_comp]

/-- 原始二列の同じ直接実射をmiddleに持つG133合成錐triangle。 -/
def lawCompositionTriangle := compositionTriangle
  (zeroExtensionMap (P.lawR laws ha)) (zeroExtensionMap (Q.lawR laws (P.adequate laws ha)))
  (zeroExtensionMap ((P.append Q).lawR laws ha)) (P.lawR_append_zeroExtension Q laws ha)

/-- 同じ直接実射の錐をmiddleに持つtriangleは標準homotopy圏でdistinguished。 -/
theorem lawCompositionTriangle_distinguished :
    (HomotopyCategory.quotient (ModuleCat.{u} ℚ) (ComplexShape.up ℤ)).mapTriangle.obj
      (P.lawCompositionTriangle Q laws ha) ∈
      distTriang (HomotopyCategory (ModuleCat.{u} ℚ) (ComplexShape.up ℤ)) :=
  compositionTriangle_distinguished _ _ _ (P.lawR_append_zeroExtension Q laws ha)

/-- 空列の同じ独立Law順射は実恒等。 -/
theorem lawR_nil (N : TargetSupportedNerve qc) :
    (nil N).lawR laws ha = cochainId (N.lawGeneratedComplex laws ha) := by
  rw [lawR_eq_raw, rawEquivalence_nil]
  exact RawChainEquivalence.lawR_refl laws ha N
/-- 空列の同じ独立Law逆射は実恒等。 -/
theorem lawS_nil (N : TargetSupportedNerve qc) :
    (nil N).lawS laws ha = cochainId (N.lawGeneratedComplex laws ha) := by
  rw [lawS_eq_raw, rawEquivalence_nil]
  exact RawChainEquivalence.lawS_refl laws ha N

end PrimitiveOperationPath
end AAT.AG.FaceRelationSubdivision
#assert_standard_axioms_only AAT.AG.FaceRelationSubdivision
