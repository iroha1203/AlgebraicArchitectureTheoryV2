import ResearchLean.AG.AtlasCoefficientFiber.SupportDegenerate
import ResearchLean.AG.AtlasCoefficientFiber.DualRestriction

/-!
# G-135 D：原L包含の双対が生成するQの台制限

## Implementation notes

Qの射は同じ原L₀・L₁・L₂包含のmathlib dualMapである。
元細cochainの制限を同じ自由chain双対で評価し、実制限射の全Hom正方形へ接続する。
R上の写像を先に選ぶ案は、原短完全列のQ射を構成しないため採らない。
-/
noncomputable section
namespace AAT.AG.AtlasCoefficientFiber
open CategoryTheory CanonicalResolution ResolutionInvariance FaceRelationSubdivision TwoPhase
universe u
variable {Source : Type u} {qc qf : Reading Source} {h : qc.CoarserThan qf}
variable {Nc : TargetSupportedNerve.{u,u} qc} {Nf : TargetSupportedNerve.{u,u} qf}
variable (M : IncidenceSupportedComparison qc qf h Nc Nf) {A B : Set qc.Target} (hab : A ⊆ B)

/-- 原L0の実包含を双対化する同じQ次数0制限。 -/
def supportQ0 : (restrictionComplex M B).C0 →ₗ[ℚ] (restrictionComplex M A).C0 :=
  (supportL0Include M hab).dualMap

/-- Q次数0制限の全原Lchain評価。 -/
theorem supportQ0_apply (z : (restrictionComplex M B).C0) (x : degenerateL0 M A) :
    supportQ0 M hab z x = z (supportL0Include M hab x) := rfl

/-- 原L1の実包含を双対化する同じQ次数1制限。 -/
def supportQ1 : (restrictionComplex M B).C1 →ₗ[ℚ] (restrictionComplex M A).C1 :=
  (supportL1Include M hab).dualMap

/-- Q次数1制限の全原Lchain評価。 -/
theorem supportQ1_apply (z : (restrictionComplex M B).C1) (x : degenerateL1 M A) :
    supportQ1 M hab z x = z (supportL1Include M hab x) := rfl

/-- 原L2の実包含を双対化する同じQ次数2制限。 -/
def supportQ2 : (restrictionComplex M B).C2 →ₗ[ℚ] (restrictionComplex M A).C2 :=
  (supportL2Include M hab).dualMap

/-- Q次数2制限の全原Lchain評価。 -/
theorem supportQ2_apply (z : (restrictionComplex M B).C2) (x : degenerateL2 M A) :
    supportQ2 M hab z x = z (supportL2Include M hab x) := rfl

/-- Qの微分0は同じL微分の可換式の実双対で制限と可換。 -/
theorem supportQ_comm0 (z : (restrictionComplex M B).C0) :
    supportQ1 M hab ((restrictionComplex M B).d0 z) =
      (restrictionComplex M A).d0 (supportQ0 M hab z) := by
  apply LinearMap.ext
  intro x
  rw [supportQ1_apply, restrictionComplex_d0_apply,
    restrictionComplex_d0_apply, supportQ0_apply, supportLInclude_boundary1]

/-- Qの微分1は同じL微分の可換式の実双対で制限と可換。 -/
theorem supportQ_comm1 (z : (restrictionComplex M B).C1) :
    supportQ2 M hab ((restrictionComplex M B).d1 z) =
      (restrictionComplex M A).d1 (supportQ1 M hab z) := by
  apply LinearMap.ext
  intro x
  rw [supportQ2_apply, restrictionComplex_d1_apply,
    restrictionComplex_d1_apply, supportQ1_apply, supportLInclude_boundary2]

/-- 原Q=L*の全三次数実cochain制限。 -/
def supportQHom : ThreeCochainComplex.Hom (restrictionComplex M B) (restrictionComplex M A) where
  f0 := supportQ0 M hab
  f1 := supportQ1 M hab
  f2 := supportQ2 M hab
  comm0 := supportQ_comm0 M hab
  comm1 := supportQ_comm1 M hab

/-- Q制限の次数0を読む所有者API。 -/
@[simp] theorem supportQHom_f0 : (supportQHom M hab).f0 = supportQ0 M hab := rfl

/-- 原細cochain→Qの次数0制限は同じ台制限と全chainで可換。 -/
theorem supportRestriction0
    (z : (Nf.targetSubsetComplex (comparisonFactor qc qf h ⁻¹' B)).C0) :
    supportQ0 M hab (restriction0 M B z) =
      restriction0 M A (selectedRestrict Nf.chartSupport (fun _ ht => hab ht) z) := by
  apply LinearMap.ext
  intro x
  rw [supportQ0_apply, restriction0_apply, restriction0_apply, supportL0Include_val, selectedRestrict_eq_dual]
  exact (dualCellMap_dual (selectedInclude Nf.chartSupport (fun _ ht => hab ht)) z x.1).symm

/-- 原Q次数0制限の恒等則。 -/
theorem supportQ0_refl (A : Set qc.Target) : supportQ0 M (Set.Subset.refl A) = LinearMap.id := by
  apply LinearMap.ext
  intro z
  apply LinearMap.ext
  intro x
  rw [supportQ0_apply, supportL0Include_refl]
  rfl

/-- 原Q次数0制限の合成則。 -/
theorem supportQ0_comp {C : Set qc.Target} (hbc : B ⊆ C) :
    (supportQ0 M hab).comp (supportQ0 M hbc) = supportQ0 M (hab.trans hbc) := by
  apply LinearMap.ext
  intro z
  apply LinearMap.ext
  intro x
  change supportQ0 M hab (supportQ0 M hbc z) x = supportQ0 M (hab.trans hbc) z x
  rw [supportQ0_apply, supportQ0_apply, supportQ0_apply]
  exact congrArg z (LinearMap.congr_fun (supportL0Include_comp M hab hbc) x)

/-- Q制限の次数1を読む所有者API。 -/
@[simp] theorem supportQHom_f1 : (supportQHom M hab).f1 = supportQ1 M hab := rfl

/-- 原細cochain→Qの次数1制限は同じ台制限と全chainで可換。 -/
theorem supportRestriction1
    (z : (Nf.targetSubsetComplex (comparisonFactor qc qf h ⁻¹' B)).C1) :
    supportQ1 M hab (restriction1 M B z) =
      restriction1 M A (selectedRestrict Nf.edgeSupport (fun _ ht => hab ht) z) := by
  apply LinearMap.ext
  intro x
  rw [supportQ1_apply, restriction1_apply, restriction1_apply, supportL1Include_val, selectedRestrict_eq_dual]
  exact (dualCellMap_dual (selectedInclude Nf.edgeSupport (fun _ ht => hab ht)) z x.1).symm

/-- 原Q次数1制限の恒等則。 -/
theorem supportQ1_refl (A : Set qc.Target) : supportQ1 M (Set.Subset.refl A) = LinearMap.id := by
  apply LinearMap.ext
  intro z
  apply LinearMap.ext
  intro x
  rw [supportQ1_apply, supportL1Include_refl]
  rfl

/-- 原Q次数1制限の合成則。 -/
theorem supportQ1_comp {C : Set qc.Target} (hbc : B ⊆ C) :
    (supportQ1 M hab).comp (supportQ1 M hbc) = supportQ1 M (hab.trans hbc) := by
  apply LinearMap.ext
  intro z
  apply LinearMap.ext
  intro x
  change supportQ1 M hab (supportQ1 M hbc z) x = supportQ1 M (hab.trans hbc) z x
  rw [supportQ1_apply, supportQ1_apply, supportQ1_apply]
  exact congrArg z (LinearMap.congr_fun (supportL1Include_comp M hab hbc) x)

/-- Q制限の次数2を読む所有者API。 -/
@[simp] theorem supportQHom_f2 : (supportQHom M hab).f2 = supportQ2 M hab := rfl

/-- 原細cochain→Qの次数2制限は同じ台制限と全chainで可換。 -/
theorem supportRestriction2
    (z : (Nf.targetSubsetComplex (comparisonFactor qc qf h ⁻¹' B)).C2) :
    supportQ2 M hab (restriction2 M B z) =
      restriction2 M A (selectedRestrict Nf.faceSupport (fun _ ht => hab ht) z) := by
  apply LinearMap.ext
  intro x
  rw [supportQ2_apply, restriction2_apply, restriction2_apply, supportL2Include_val, selectedRestrict_eq_dual]
  exact (dualCellMap_dual (selectedInclude Nf.faceSupport (fun _ ht => hab ht)) z x.1).symm

/-- 原Q次数2制限の恒等則。 -/
theorem supportQ2_refl (A : Set qc.Target) : supportQ2 M (Set.Subset.refl A) = LinearMap.id := by
  apply LinearMap.ext
  intro z
  apply LinearMap.ext
  intro x
  rw [supportQ2_apply, supportL2Include_refl]
  rfl

/-- 原Q次数2制限の合成則。 -/
theorem supportQ2_comp {C : Set qc.Target} (hbc : B ⊆ C) :
    (supportQ2 M hab).comp (supportQ2 M hbc) = supportQ2 M (hab.trans hbc) := by
  apply LinearMap.ext
  intro z
  apply LinearMap.ext
  intro x
  change supportQ2 M hab (supportQ2 M hbc z) x = supportQ2 M (hab.trans hbc) z x
  rw [supportQ2_apply, supportQ2_apply, supportQ2_apply]
  exact congrArg z (LinearMap.congr_fun (supportL2Include_comp M hab hbc) x)

/-- 原細cochain→Q射の全三次数正方形。 -/
theorem supportRestrictionHom :
    AtlasDefectComposition.cochainComp (restrictionHom M B) (supportQHom M hab) =
      AtlasDefectComposition.cochainComp (subsetRestrictHom Nf (fun _ ht => hab ht))
        (restrictionHom M A) := by
  apply AtlasDefectComposition.cochain_ext
  · apply LinearMap.ext
    intro z
    simpa only [AtlasDefectComposition.cochainComp_f0, restrictionHom_f0, supportQHom_f0,
      subsetRestrictHom_f0, LinearMap.comp_apply] using supportRestriction0 M hab z
  · apply LinearMap.ext
    intro z
    simpa only [AtlasDefectComposition.cochainComp_f1, restrictionHom_f1, supportQHom_f1,
      subsetRestrictHom_f1, LinearMap.comp_apply] using supportRestriction1 M hab z
  · apply LinearMap.ext
    intro z
    simpa only [AtlasDefectComposition.cochainComp_f2, restrictionHom_f2, supportQHom_f2,
      subsetRestrictHom_f2, LinearMap.comp_apply] using supportRestriction2 M hab z

/-- 同じQ全Homの恒等則。 -/
theorem supportQHom_refl (A : Set qc.Target) :
    supportQHom M (Set.Subset.refl A) = AtlasDefectComposition.cochainId (restrictionComplex M A) := by
  apply AtlasDefectComposition.cochain_ext
  · apply LinearMap.ext
    intro z
    rw [supportQHom_f0, AtlasDefectComposition.cochainId_f0]
    exact LinearMap.congr_fun (supportQ0_refl M A) z
  · apply LinearMap.ext
    intro z
    rw [supportQHom_f1, AtlasDefectComposition.cochainId_f1]
    exact LinearMap.congr_fun (supportQ1_refl M A) z
  · apply LinearMap.ext
    intro z
    rw [supportQHom_f2, AtlasDefectComposition.cochainId_f2]
    exact LinearMap.congr_fun (supportQ2_refl M A) z

/-- 同じQ全Homの合成則。 -/
theorem supportQHom_comp {C : Set qc.Target} (hbc : B ⊆ C) :
    AtlasDefectComposition.cochainComp (supportQHom M hbc) (supportQHom M hab) =
      supportQHom M (hab.trans hbc) := by
  apply AtlasDefectComposition.cochain_ext
  · apply LinearMap.ext
    intro z
    rw [AtlasDefectComposition.cochainComp_f0, supportQHom_f0, supportQHom_f0, supportQHom_f0]
    exact LinearMap.congr_fun (supportQ0_comp M hab hbc) z
  · apply LinearMap.ext
    intro z
    rw [AtlasDefectComposition.cochainComp_f1, supportQHom_f1, supportQHom_f1, supportQHom_f1]
    exact LinearMap.congr_fun (supportQ1_comp M hab hbc) z
  · apply LinearMap.ext
    intro z
    rw [AtlasDefectComposition.cochainComp_f2, supportQHom_f2, supportQHom_f2, supportQHom_f2]
    exact LinearMap.congr_fun (supportQ2_comp M hab hbc) z

end AAT.AG.AtlasCoefficientFiber
#print axioms AAT.AG.AtlasCoefficientFiber.supportQ0
#print axioms AAT.AG.AtlasCoefficientFiber.supportQ0_apply
#print axioms AAT.AG.AtlasCoefficientFiber.supportQ1
#print axioms AAT.AG.AtlasCoefficientFiber.supportQ1_apply
#print axioms AAT.AG.AtlasCoefficientFiber.supportQ2
#print axioms AAT.AG.AtlasCoefficientFiber.supportQ2_apply
#print axioms AAT.AG.AtlasCoefficientFiber.supportQ_comm0
#print axioms AAT.AG.AtlasCoefficientFiber.supportQ_comm1
#print axioms AAT.AG.AtlasCoefficientFiber.supportQHom
#print axioms AAT.AG.AtlasCoefficientFiber.supportQHom_f0
#print axioms AAT.AG.AtlasCoefficientFiber.supportRestriction0
#print axioms AAT.AG.AtlasCoefficientFiber.supportQ0_refl
#print axioms AAT.AG.AtlasCoefficientFiber.supportQ0_comp
#print axioms AAT.AG.AtlasCoefficientFiber.supportQHom_f1
#print axioms AAT.AG.AtlasCoefficientFiber.supportRestriction1
#print axioms AAT.AG.AtlasCoefficientFiber.supportQ1_refl
#print axioms AAT.AG.AtlasCoefficientFiber.supportQ1_comp
#print axioms AAT.AG.AtlasCoefficientFiber.supportQHom_f2
#print axioms AAT.AG.AtlasCoefficientFiber.supportRestriction2
#print axioms AAT.AG.AtlasCoefficientFiber.supportQ2_refl
#print axioms AAT.AG.AtlasCoefficientFiber.supportQ2_comp
#print axioms AAT.AG.AtlasCoefficientFiber.supportRestrictionHom
#print axioms AAT.AG.AtlasCoefficientFiber.supportQHom_refl
#print axioms AAT.AG.AtlasCoefficientFiber.supportQHom_comp
#print axioms AAT.AG.AtlasCoefficientFiber.supportQ0.congr_simp
#print axioms AAT.AG.AtlasCoefficientFiber.supportQ1.congr_simp
#print axioms AAT.AG.AtlasCoefficientFiber.supportQ2.congr_simp
#print axioms AAT.AG.AtlasCoefficientFiber.supportQHom.congr_simp
#assert_standard_axioms_only AAT.AG.AtlasCoefficientFiber
