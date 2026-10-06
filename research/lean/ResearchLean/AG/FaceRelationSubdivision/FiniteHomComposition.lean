import ResearchLean.AG.FaceRelationSubdivision.LawFiniteOption
import ResearchLean.AG.FaceRelationSubdivision.GeneratedComposition

/-!
# 原始有限基底射のchain式と同じLaw合成

## Implementation notes

Option比較のchain式を全セル基底から証明する。合成の方向仮定は各原始射の
式であり、具体操作の適用では構成済みの式を渡す。Law射は合成有限和から生成する。
-/
noncomputable section
namespace AAT.AG.FaceRelationSubdivision
open CanonicalResolution ResolutionInvariance TwoPhase AtlasDefectComposition
universe u
variable {Source : Type u} {q : Reading Source}
namespace IncidenceSupportedComparison
variable {Nc Nf : TargetSupportedNerve q}
variable (M : IncidenceSupportedComparison q q (Reading.coarserThan_refl q) Nc Nf)

/-- 原始端点表は全セルの同じd1と可換。空台のセルも含む。 -/
theorem basis_comm01 : (TargetSupportedNerve.rawD1 Nc).raw.comp M.basis1.raw =
    M.basis0.raw.comp (TargetSupportedNerve.rawD1 Nf).raw := by
  apply Finsupp.lhom_ext
  intro e a
  simp only [LinearMap.comp_apply, SupportedBasisMap.raw_single, TargetSupportedNerve.rawD1_basis,
    basis0_image, basis1_image, map_sub, map_smul, one_smul]
  cases he : M.edgeMap e with
  | none =>
    rw [rationalOptionCell_none, map_zero, M.edge_none_fiber e he]
    simp
  | some b =>
    rw [rationalOptionCell_some, SupportedBasisMap.raw_single,
      TargetSupportedNerve.rawD1_basis, one_smul,
      M.edge_some_left e b he, M.edge_some_right e b he]

/-- 原始三辺表・混在退化零和は全セルの同じd2と可換。 -/
theorem basis_comm12 : (TargetSupportedNerve.rawD2 Nc).raw.comp M.basis2.raw =
    M.basis1.raw.comp (TargetSupportedNerve.rawD2 Nf).raw := by
  apply Finsupp.lhom_ext
  intro f a
  simp only [LinearMap.comp_apply, SupportedBasisMap.raw_single, TargetSupportedNerve.rawD2_basis,
    basis1_image, basis2_image, map_add, map_sub, map_smul, one_smul]
  cases hf : M.faceMap f with
  | none =>
    rw [rationalOptionCell_none, map_zero]
    rcases (optionCell_incidence_iff _ _ _).mp (M.face_none_incidence f hf) with
      ⟨h0, h12⟩ | ⟨h2, h01⟩
    · rw [h0, h12, rationalOptionCell_none]; simp
    · rw [h2, h01, rationalOptionCell_none]; simp
  | some b =>
    rw [rationalOptionCell_some, SupportedBasisMap.raw_single,
      TargetSupportedNerve.rawD2_basis, one_smul,
      M.face_some_edge0 f b hf, M.face_some_edge1 f b hf, M.face_some_edge2 f b hf,
      rationalOptionCell_some, rationalOptionCell_some, rationalOptionCell_some]

/-- 同じ原始有限和Homは、同じOption生成subset射に一致する。 -/
theorem basisSubsetFiniteHom_eq (A : Set q.Target) :
    subsetFiniteHom M.basis0 M.basis1 M.basis2 M.basis_comm01 M.basis_comm12 A =
      M.targetSubsetComparisonHom A A (selfSubsetMapsTo A) := by
  rw [← M.basisHom_eq_generated]
  apply cochain_ext
  · rw [subsetFiniteHom_f0, basisHom_f0]
  · rw [subsetFiniteHom_f1, basisHom_f1]
  · rw [subsetFiniteHom_f2, basisHom_f2]

end IncidenceSupportedComparison

/-- 二つの原始chain正方形は合成した有限和の同じ正方形を生成する。 -/
theorem raw_square_comp {I0 I1 J0 J1 K0 K1 : Type u}
    (di : (I1 →₀ ℚ) →ₗ[ℚ] (I0 →₀ ℚ))
    (dj : (J1 →₀ ℚ) →ₗ[ℚ] (J0 →₀ ℚ))
    (dk : (K1 →₀ ℚ) →ₗ[ℚ] (K0 →₀ ℚ))
    (m0 : (I0 →₀ ℚ) →ₗ[ℚ] (J0 →₀ ℚ)) (m1 : (I1 →₀ ℚ) →ₗ[ℚ] (J1 →₀ ℚ))
    (n0 : (J0 →₀ ℚ) →ₗ[ℚ] (K0 →₀ ℚ)) (n1 : (J1 →₀ ℚ) →ₗ[ℚ] (K1 →₀ ℚ))
    (hm : dj.comp m1 = m0.comp di) (hn : dk.comp n1 = n0.comp dj) :
    dk.comp (n1.comp m1) = (n0.comp m0).comp di := by
  rw [← LinearMap.comp_assoc, hn, LinearMap.comp_assoc, hm, ← LinearMap.comp_assoc]

variable {N0 N1 N2 : TargetSupportedNerve q}
variable (m0 : SupportedBasisMap N1.chartSupport N0.chartSupport)
variable (m1 : SupportedBasisMap N1.edgeSupport N0.edgeSupport)
variable (m2 : SupportedBasisMap N1.faceSupport N0.faceSupport)
variable (n0 : SupportedBasisMap N2.chartSupport N1.chartSupport)
variable (n1 : SupportedBasisMap N2.edgeSupport N1.edgeSupport)
variable (n2 : SupportedBasisMap N2.faceSupport N1.faceSupport)
variable (hm0 : (TargetSupportedNerve.rawD1 N0).raw.comp m1.raw = m0.raw.comp (TargetSupportedNerve.rawD1 N1).raw)
variable (hm1 : (TargetSupportedNerve.rawD2 N0).raw.comp m2.raw = m1.raw.comp (TargetSupportedNerve.rawD2 N1).raw)
variable (hn0 : (TargetSupportedNerve.rawD1 N1).raw.comp n1.raw = n0.raw.comp (TargetSupportedNerve.rawD1 N2).raw)
variable (hn1 : (TargetSupportedNerve.rawD2 N1).raw.comp n2.raw = n1.raw.comp (TargetSupportedNerve.rawD2 N2).raw)

include hm0 hn0 in
/-- 直接有限和の次数0/1 chain式。 -/
theorem finiteComp_comm01 : (TargetSupportedNerve.rawD1 N0).raw.comp (n1.comp m1).raw =
    (n0.comp m0).raw.comp (TargetSupportedNerve.rawD1 N2).raw := by
  simp only [SupportedBasisMap.raw_comp]
  exact raw_square_comp _ _ _ _ _ _ _ hn0 hm0
include hm1 hn1 in
/-- 直接有限和の次数1/2 chain式。 -/
theorem finiteComp_comm12 : (TargetSupportedNerve.rawD2 N0).raw.comp (n2.comp m2).raw =
    (n1.comp m1).raw.comp (TargetSupportedNerve.rawD2 N2).raw := by
  simp only [SupportedBasisMap.raw_comp]
  exact raw_square_comp _ _ _ _ _ _ _ hn1 hm1

/-- 合成原始有限和から独立生成したLaw射は同じ実三成分合成。 -/
theorem lawFiniteHom_comp [Fintype Source] (laws : FiniteLawFamily Source) (ha : laws.Adequate q) :
    lawFiniteHom (n0.comp m0) (n1.comp m1) (n2.comp m2)
      (finiteComp_comm01 m0 m1 n0 n1 hm0 hn0) (finiteComp_comm12 m1 m2 n1 n2 hm1 hn1) laws ha =
      cochainComp (lawFiniteHom m0 m1 m2 hm0 hm1 laws ha)
        (lawFiniteHom n0 n1 n2 hn0 hn1 laws ha) := by
  apply cochain_ext
  · apply LinearMap.ext; intro z
    rw [cochainComp_f0, lawFiniteHom_f0, lawFiniteHom_f0, lawFiniteHom_f0,
      SupportedBasisMap.lawDual_comp]
    rfl
  · apply LinearMap.ext; intro z
    rw [cochainComp_f1, lawFiniteHom_f1, lawFiniteHom_f1, lawFiniteHom_f1,
      SupportedBasisMap.lawDual_comp]
    rfl
  · apply LinearMap.ext; intro z
    rw [cochainComp_f2, lawFiniteHom_f2, lawFiniteHom_f2, lawFiniteHom_f2,
      SupportedBasisMap.lawDual_comp]
    rfl

end AAT.AG.FaceRelationSubdivision
#assert_standard_axioms_only AAT.AG.FaceRelationSubdivision
