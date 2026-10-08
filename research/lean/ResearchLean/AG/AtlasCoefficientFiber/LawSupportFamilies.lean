import ResearchLean.AG.AtlasCoefficientFiber.LawSupportConnecting

/-!
# G-135 D：ラベルごとに異なる原部分台の全族図式

## Implementation notes

発生ラベルを保持した元SES族へprimitive支持制限を成分ごとに作用させる。
全族の射・native連結射と直接Phi R射を同じ原Law入力から生成する。
-/
noncomputable section
namespace AAT.AG.AtlasCoefficientFiber
open CategoryTheory HomologicalComplex CanonicalResolution ResolutionInvariance
open FaceRelationSubdivision AtlasDefectComposition
universe u

/-- 元short complex族の三成分射を同じ実族射へ集める。 -/
def coefficientShortComplexFamily_map {J : Type u}
    {S T : J → ShortComplex (CochainComplex (ModuleCat.{u} ℚ) ℤ)}
    (φ : ∀ j, S j ⟶ T j) : coefficientShortComplexFamily S ⟶ coefficientShortComplexFamily T where
  τ₁ := FiniteComplexFamily.map _ _ (fun j => (φ j).τ₁)
  τ₂ := FiniteComplexFamily.map _ _ (fun j => (φ j).τ₂)
  τ₃ := FiniteComplexFamily.map _ _ (fun j => (φ j).τ₃)
  comm₁₂ := by
    change FiniteComplexFamily.map _ _ (fun j => (φ j).τ₁) ≫
      FiniteComplexFamily.map _ _ (fun j => (T j).f) =
        FiniteComplexFamily.map _ _ (fun j => (S j).f) ≫
          FiniteComplexFamily.map _ _ (fun j => (φ j).τ₂)
    rw [← FiniteComplexFamily.map_comp, ← FiniteComplexFamily.map_comp]
    congr 1
    funext j
    exact (φ j).comm₁₂
  comm₂₃ := by
    change FiniteComplexFamily.map _ _ (fun j => (φ j).τ₂) ≫
      FiniteComplexFamily.map _ _ (fun j => (T j).g) =
        FiniteComplexFamily.map _ _ (fun j => (S j).g) ≫
          FiniteComplexFamily.map _ _ (fun j => (φ j).τ₃)
    rw [← FiniteComplexFamily.map_comp, ← FiniteComplexFamily.map_comp]
    congr 1
    funext j
    exact (φ j).comm₂₃

/-- 同じ族の三成分射影は族射と全体で可換。 -/
theorem coefficientShortComplexFamily_map_projection {J : Type u}
    {S T : J → ShortComplex (CochainComplex (ModuleCat.{u} ℚ) ℤ)}
    (φ : ∀ j, S j ⟶ T j) (j : J) :
    coefficientShortComplexFamily_map φ ≫ coefficientShortComplexFamily_projection T j =
      coefficientShortComplexFamily_projection S j ≫ φ j := by
  apply ShortComplex.Hom.ext
  · exact FiniteComplexFamily.map_projection _ _ (fun j => (φ j).τ₁) j
  · exact FiniteComplexFamily.map_projection _ _ (fun j => (φ j).τ₂) j
  · exact FiniteComplexFamily.map_projection _ _ (fun j => (φ j).τ₃) j

variable {Source : Type u} [finiteSource : Fintype Source]
variable {qc qf : Reading Source} {h : qc.CoarserThan qf}
variable {Nc : TargetSupportedNerve.{u,u} qc} {Nf : TargetSupportedNerve.{u,u} qf}
variable (M : IncidenceSupportedComparison qc qf h Nc Nf)
variable (laws : FiniteLawFamily Source) (ha : laws.Adequate qc)
variable {A : LawValueLabel laws → Set qc.Target}
variable (hA : ∀ l, A l ⊆ labelValueFiber laws qc ha l)

/-- 原Law SESを同じラベル別原部分台SES族へ送る全三射。 -/
def lawSupportFamilyMorphism : lawEvaluationRestrictionShortComplex M laws ha ⟶
    coefficientShortComplexFamily (fun l => evaluationRestrictionShortComplex M (A l)) :=
  (lawEvaluationRestrictionFamilyIso M laws ha).hom ≫
    coefficientShortComplexFamily_map (fun l => supportEvaluationRestrictionMorphism M (hA l))

/-- 元Pのラベル別部分台族への全次数射。 -/
def lawSupportFamilyP := (lawSupportFamilyMorphism M laws ha hA).τ₁
/-- 元細cochainのラベル別部分台族への全次数射。 -/
def lawSupportFamilyFine := (lawSupportFamilyMorphism M laws ha hA).τ₂
/-- 原L双対Qのラベル別部分台族への全次数射。 -/
def lawSupportFamilyQ := (lawSupportFamilyMorphism M laws ha hA).τ₃

/-- 原粗Lawを同じ原粗部分台族へ送る全次数射。 -/
def lawSupportFamilyCoarse : zeroExtension (Nc.lawGeneratedComplex laws ha) ⟶
    FiniteComplexFamily.complex (fun l => zeroExtension (Nc.targetSubsetComplex (A l))) :=
  (lawCoarseStandardIso (Nc := Nc) laws ha).hom ≫
    FiniteComplexFamily.map _ _ (fun l => zeroExtensionMap (subsetRestrictHom Nc (hA l)))

/-- 全族SES射の各ラベル値は同じprimitive部分台SES射。 -/
theorem lawSupportFamilyMorphism_projection (l : LawValueLabel laws) :
    lawSupportFamilyMorphism M laws ha hA ≫ coefficientShortComplexFamily_projection _ l =
      lawSupportMorphism M laws ha l (hA l) := by
  dsimp only [lawSupportFamilyMorphism]
  rw [lawSupportMorphism_eq, lawEvaluationRestrictionProjection_eq]
  rw [Category.assoc, coefficientShortComplexFamily_map_projection, ← Category.assoc]

/-- 原P全族射は元canonical族同型と同じprimitive制限族。 -/
theorem lawSupportFamilyP_eq : lawSupportFamilyP M laws ha hA =
    (lawPushforwardStandardIso M laws ha).hom ≫
      FiniteComplexFamily.map _ _ (fun l => zeroExtensionMap (supportPushforwardHom M (hA l))) := rfl
/-- 原細全族射は元canonical族同型と同じ細支持制限族。 -/
theorem lawSupportFamilyFine_eq : lawSupportFamilyFine M laws ha hA =
    (lawFineStandardIso (Nf := Nf) (h := h) laws ha).hom ≫
      FiniteComplexFamily.map _ _ (fun l => zeroExtensionMap (subsetRestrictHom Nf (fun _ ht => hA l ht))) := rfl
/-- 原Q全族射は元canonical族同型と同じ原L双対支持制限族。 -/
theorem lawSupportFamilyQ_eq : lawSupportFamilyQ M laws ha hA =
    (lawRestrictionStandardIso M laws ha).hom ≫
      FiniteComplexFamily.map _ _ (fun l => zeroExtensionMap (supportQHom M (hA l))) := rfl
/-- 原粗全族射のprimitive生成式。 -/
theorem lawSupportFamilyCoarse_eq : lawSupportFamilyCoarse (Nc := Nc) laws ha hA =
    (lawCoarseStandardIso (Nc := Nc) laws ha).hom ≫
      FiniteComplexFamily.map _ _ (fun l => zeroExtensionMap (subsetRestrictHom Nc (hA l))) := rfl

/-- 全族P射の同じ原ラベル射影。 -/
theorem lawSupportFamilyP_projection (l : LawValueLabel laws) :
    lawSupportFamilyP M laws ha hA ≫ FiniteComplexFamily.projection _ l =
      lawSupportP M laws ha l (hA l) :=
  congrArg ShortComplex.Hom.τ₁ (lawSupportFamilyMorphism_projection M laws ha hA l)
/-- 全族細射の同じ原ラベル射影。 -/
theorem lawSupportFamilyFine_projection (l : LawValueLabel laws) :
    lawSupportFamilyFine M laws ha hA ≫ FiniteComplexFamily.projection _ l =
      lawSupportFine M laws ha l (hA l) :=
  congrArg ShortComplex.Hom.τ₂ (lawSupportFamilyMorphism_projection M laws ha hA l)
/-- 全族Q射の同じ原ラベル射影。 -/
theorem lawSupportFamilyQ_projection (l : LawValueLabel laws) :
    lawSupportFamilyQ M laws ha hA ≫ FiniteComplexFamily.projection _ l =
      lawSupportQ M laws ha l (hA l) :=
  congrArg ShortComplex.Hom.τ₃ (lawSupportFamilyMorphism_projection M laws ha hA l)
/-- 全族粗射の同じ原ラベル射影。 -/
theorem lawSupportFamilyCoarse_projection (l : LawValueLabel laws) :
    lawSupportFamilyCoarse (Nc := Nc) laws ha hA ≫ FiniteComplexFamily.projection _ l =
      lawSupportCoarse (Nc := Nc) laws ha l (hA l) := by
  rw [lawSupportFamilyCoarse_eq, lawSupportCoarse_eq, Category.assoc,
    FiniteComplexFamily.map_projection, ← Category.assoc]

/-- 原Law全族P射の全次数・全元・全ラベル値。 -/
theorem lawSupportFamilyP_apply (n : ℤ)
    (z : (zeroExtension (lawPushforwardComplex M laws ha)).X n) (l : LawValueLabel laws) :
    (lawSupportFamilyP M laws ha hA).f n z l = (lawSupportP M laws ha l (hA l)).f n z := by
  have hh := congrArg (fun f => f.f n z) (lawSupportFamilyP_projection M laws ha hA l)
  simpa only [HomologicalComplex.comp_f, ModuleCat.comp_apply, FiniteComplexFamily.projection_apply] using hh

/-- 原Law全族Fine射の全次数・全元・全ラベル値。 -/
theorem lawSupportFamilyFine_apply (n : ℤ)
    (z : (zeroExtension (Nf.lawGeneratedComplex laws (lawFineAdequate (h := h) laws ha))).X n) (l : LawValueLabel laws) :
    (lawSupportFamilyFine M laws ha hA).f n z l = (lawSupportFine M laws ha l (hA l)).f n z := by
  have hh := congrArg (fun f => f.f n z) (lawSupportFamilyFine_projection M laws ha hA l)
  simpa only [HomologicalComplex.comp_f, ModuleCat.comp_apply, FiniteComplexFamily.projection_apply] using hh

/-- 原Law全族Q射の全次数・全元・全ラベル値。 -/
theorem lawSupportFamilyQ_apply (n : ℤ)
    (z : (zeroExtension (lawRestrictionComplex M laws ha)).X n) (l : LawValueLabel laws) :
    (lawSupportFamilyQ M laws ha hA).f n z l = (lawSupportQ M laws ha l (hA l)).f n z := by
  have hh := congrArg (fun f => f.f n z) (lawSupportFamilyQ_projection M laws ha hA l)
  simpa only [HomologicalComplex.comp_f, ModuleCat.comp_apply, FiniteComplexFamily.projection_apply] using hh

/-- 原Law全族Coarse射の全次数・全元・全ラベル値。 -/
theorem lawSupportFamilyCoarse_apply (n : ℤ)
    (z : (zeroExtension (Nc.lawGeneratedComplex laws ha)).X n) (l : LawValueLabel laws) :
    (lawSupportFamilyCoarse (Nc := Nc) laws ha hA).f n z l = (lawSupportCoarse (Nc := Nc) laws ha l (hA l)).f n z := by
  have hh := congrArg (fun f => f.f n z) (lawSupportFamilyCoarse_projection (Nc := Nc) laws ha hA l)
  simpa only [HomologicalComplex.comp_f, ModuleCat.comp_apply, FiniteComplexFamily.projection_apply] using hh

/-- 元ηは全ラベル別原部分台族への射と全Homで可換。 -/
theorem lawSupportFamilyUnit : zeroExtensionMap (lawUnitHom M laws ha) ≫ lawSupportFamilyP M laws ha hA =
    lawSupportFamilyCoarse (Nc := Nc) laws ha hA ≫
      FiniteComplexFamily.map _ _ (fun l => zeroExtensionMap (unitHom M (A l))) := by
  rw [lawSupportFamilyP_eq, lawSupportFamilyCoarse_eq, ← Category.assoc, lawUnitStandard_square]
  simp only [Category.assoc]
  rw [← FiniteComplexFamily.map_comp, ← FiniteComplexFamily.map_comp]
  congr 2
  funext l
  exact supportStandardUnit M (hA l)

/-- 元εは全ラベル別原部分台族への射と全Homで可換。 -/
theorem lawSupportFamilyEvaluation : zeroExtensionMap (lawEvaluationHom M laws ha) ≫
    lawSupportFamilyFine M laws ha hA = lawSupportFamilyP M laws ha hA ≫
      FiniteComplexFamily.map _ _ (fun l => zeroExtensionMap (evaluationHom M (A l))) :=
  (lawSupportFamilyMorphism M laws ha hA).comm₁₂.symm
/-- 原L制限は全ラベル別原部分台族への射と全Homで可換。 -/
theorem lawSupportFamilyRestriction : zeroExtensionMap (lawRestrictionHom M laws ha) ≫
    lawSupportFamilyQ M laws ha hA = lawSupportFamilyFine M laws ha hA ≫
      FiniteComplexFamily.map _ _ (fun l => zeroExtensionMap (restrictionHom M (A l))) :=
  (lawSupportFamilyMorphism M laws ha hA).comm₂₃.symm
/-- 独立生成原uは全ラベル別原部分台族への射と全Homで可換。 -/
theorem lawSupportFamilyDirect :
    zeroExtensionMap (M.generatedComparisonHom laws ha (lawFineAdequate (h := h) laws ha)) ≫
      lawSupportFamilyFine M laws ha hA = lawSupportFamilyCoarse (Nc := Nc) laws ha hA ≫
        FiniteComplexFamily.map _ _ (fun l => zeroExtensionMap (M.aSubnerveComparisonHom (A l))) := by
  apply HomologicalComplex.Hom.ext
  funext n
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  funext l
  change (lawSupportFamilyFine M laws ha hA).f n
      ((zeroExtensionMap (M.generatedComparisonHom laws ha (lawFineAdequate (h := h) laws ha))).f n x) l =
    (zeroExtensionMap (M.aSubnerveComparisonHom (A l))).f n
      ((lawSupportFamilyCoarse (Nc := Nc) laws ha hA).f n x l)
  rw [lawSupportFamilyFine_apply, lawSupportFamilyCoarse_apply]
  exact congrArg (fun f => f.f n x) (lawSupportDirect M laws ha l (hA l))

omit finiteSource in
/-- ラベル別原部分台SES族の短完全性は同じ入力から生成される。 -/
theorem lawSupportFamily_shortExact :
    (coefficientShortComplexFamily (fun l => evaluationRestrictionShortComplex M (A l))).ShortExact :=
  coefficientShortComplexFamily_shortExact _ (fun l => evaluationRestriction_shortExact M (A l))
/-- 同じ原Law native deltaの全族・全整数次数の可換式。 -/
theorem lawSupportFamily_delta (n : ℤ)
    (z : (zeroExtension (lawRestrictionComplex M laws ha)).homology n) :
    homologyMap (lawSupportFamilyP M laws ha hA) (n+1)
      ((lawEvaluationRestriction_shortExact M laws ha).δ n (n+1) rfl z) =
    (lawSupportFamily_shortExact M (A := A)).δ n (n+1) rfl
      (homologyMap (lawSupportFamilyQ M laws ha hA) n z) :=
  congrArg (fun f => f z) (HomologicalComplex.HomologySequence.δ_naturality
    (lawSupportFamilyMorphism M laws ha hA) (lawEvaluationRestriction_shortExact M laws ha)
    (lawSupportFamily_shortExact M (A := A)) n (n+1) rfl)

/-- 原Law literal Rを重複ラベルを保った原部分台R族へ直接制限する。 -/
def lawSupportFamilyR : lawR M laws ha →ₗ[ℚ] ((l : LawValueLabel laws) → R M (A l)) :=
  LinearMap.pi (fun l => lawSupportR M laws ha l (hA l))
omit finiteSource in
/-- 全族R射の各値は同じ直接Phi制限。 -/
theorem lawSupportFamilyR_apply (z : lawR M laws ha) (l : LawValueLabel laws) :
    lawSupportFamilyR M laws ha hA z l = lawSupportR M laws ha l (hA l) z := rfl

end AAT.AG.AtlasCoefficientFiber
#print axioms AAT.AG.AtlasCoefficientFiber.coefficientShortComplexFamily_map
#print axioms AAT.AG.AtlasCoefficientFiber.coefficientShortComplexFamily_map_projection
#print axioms AAT.AG.AtlasCoefficientFiber.lawSupportFamilyMorphism
#print axioms AAT.AG.AtlasCoefficientFiber.lawSupportFamilyP
#print axioms AAT.AG.AtlasCoefficientFiber.lawSupportFamilyFine
#print axioms AAT.AG.AtlasCoefficientFiber.lawSupportFamilyQ
#print axioms AAT.AG.AtlasCoefficientFiber.lawSupportFamilyCoarse
#print axioms AAT.AG.AtlasCoefficientFiber.lawSupportFamilyMorphism_projection
#print axioms AAT.AG.AtlasCoefficientFiber.lawSupportFamilyP_eq
#print axioms AAT.AG.AtlasCoefficientFiber.lawSupportFamilyFine_eq
#print axioms AAT.AG.AtlasCoefficientFiber.lawSupportFamilyQ_eq
#print axioms AAT.AG.AtlasCoefficientFiber.lawSupportFamilyCoarse_eq
#print axioms AAT.AG.AtlasCoefficientFiber.lawSupportFamilyP_projection
#print axioms AAT.AG.AtlasCoefficientFiber.lawSupportFamilyFine_projection
#print axioms AAT.AG.AtlasCoefficientFiber.lawSupportFamilyQ_projection
#print axioms AAT.AG.AtlasCoefficientFiber.lawSupportFamilyCoarse_projection
#print axioms AAT.AG.AtlasCoefficientFiber.lawSupportFamilyP_apply
#print axioms AAT.AG.AtlasCoefficientFiber.lawSupportFamilyFine_apply
#print axioms AAT.AG.AtlasCoefficientFiber.lawSupportFamilyQ_apply
#print axioms AAT.AG.AtlasCoefficientFiber.lawSupportFamilyCoarse_apply
#print axioms AAT.AG.AtlasCoefficientFiber.lawSupportFamilyUnit
#print axioms AAT.AG.AtlasCoefficientFiber.lawSupportFamilyEvaluation
#print axioms AAT.AG.AtlasCoefficientFiber.lawSupportFamilyRestriction
#print axioms AAT.AG.AtlasCoefficientFiber.lawSupportFamilyDirect
#print axioms AAT.AG.AtlasCoefficientFiber.lawSupportFamily_shortExact
#print axioms AAT.AG.AtlasCoefficientFiber.lawSupportFamily_delta
#print axioms AAT.AG.AtlasCoefficientFiber.lawSupportFamilyR
#print axioms AAT.AG.AtlasCoefficientFiber.lawSupportFamilyR_apply
#print axioms AAT.AG.AtlasCoefficientFiber.lawSupportFamilyCoarse.congr_simp
#print axioms AAT.AG.AtlasCoefficientFiber.lawSupportFamilyFine.congr_simp
#print axioms AAT.AG.AtlasCoefficientFiber.lawSupportFamilyP.congr_simp
#print axioms AAT.AG.AtlasCoefficientFiber.lawSupportFamilyQ.congr_simp
#assert_standard_axioms_only AAT.AG.AtlasCoefficientFiber
