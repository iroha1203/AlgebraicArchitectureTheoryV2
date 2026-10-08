import ResearchLean.AG.AtlasCoefficientFiber.ThirdGradedComplex

/-!
# G-135 B：原F³零対象とnative cone座標

## Implementation notes

原F³零性を全次数で証明する。零始点のconeと対象との同型は、同じ零包含・恒等射
の標準短完全列を通してhomology上に生成する。補助の零性を入力に置かない。
-/
noncomputable section
namespace AAT.AG.AtlasCoefficientFiber
open CategoryTheory Limits CanonicalResolution ResolutionInvariance FaceRelationSubdivision TwoPhase
open AtlasDefectComposition
universe u

/-- 原F³の全零延長次数は零対象。 -/
theorem zeroFiltrationDegree_isZero (n : ℤ) :
    IsZero ((zeroExtension (zeroFiltrationComplex : ThreeCochainComplex.{0,u} ℚ)).X n) := by
  by_cases h0 : n = 0
  · subst n; change IsZero (ModuleCat.of ℚ PUnit.{u+1}); exact ModuleCat.isZero_of_subsingleton _
  · by_cases h1 : n = 1
    · subst n; change IsZero (ModuleCat.of ℚ PUnit.{u+1}); exact ModuleCat.isZero_of_subsingleton _
    · by_cases h2 : n = 2
      · subst n; change IsZero (ModuleCat.of ℚ PUnit.{u+1}); exact ModuleCat.isZero_of_subsingleton _
      · exact degreeObject_isZero zeroFiltrationComplex n h0 h1 h2

/-- 原F³は標準complex圏でも零対象。 -/
theorem zeroFiltration_isZero :
    IsZero (zeroExtension (zeroFiltrationComplex : ThreeCochainComplex.{0,u} ℚ)) := by
  apply (IsZero.iff_id_eq_zero _).mpr
  apply HomologicalComplex.Hom.ext
  funext n
  exact (zeroFiltrationDegree_isZero n).eq_of_src _ _

variable {K : CochainComplex (ModuleCat.{u} ℚ) ℤ}
variable (f : zeroExtension (zeroFiltrationComplex : ThreeCochainComplex.{0,u} ℚ) ⟶ K)

/-- 原零始点からの同じ射は零射。 -/
theorem zeroFiltrationMap_eq_zero : f = 0 := zeroFiltration_isZero.eq_of_src _ _

/-- 原零始点から同じ対象へのconeに対応する標準短複体。 -/
def zeroFiltrationConeShortComplex : ShortComplex (CochainComplex (ModuleCat.{u} ℚ) ℤ) :=
  ShortComplex.mk f (𝟙 K) (by rw [Category.comp_id]; exact zeroFiltrationMap_eq_zero f)

/-- 原零包含と恒等射の列は、補助条件なしに短完全。 -/
theorem zeroFiltrationConeShortExact : (zeroFiltrationConeShortComplex f).ShortExact := by
  apply ShortComplex.ShortExact.mk' _ (zeroFiltration_isZero.mono f) (inferInstanceAs (Epi (𝟙 K)))
  exact ((zeroFiltrationConeShortComplex f).exact_iff_mono (zeroFiltrationMap_eq_zero f)).mpr
    (inferInstanceAs (Mono (𝟙 K)))

/-- 原零始点coneの対象評価。 -/
def zeroFiltrationConeDesc : CochainComplex.mappingCone f ⟶ K :=
  CochainComplex.mappingCone.descShortComplex (zeroFiltrationConeShortComplex f)

/-- 原零始点coneの評価は全次数で擬同型。 -/
instance zeroFiltrationConeDesc_quasiIso : QuasiIso (zeroFiltrationConeDesc f) :=
  CochainComplex.mappingCone.quasiIso_descShortComplex (zeroFiltrationConeShortExact f)

/-- 原inrと評価は元対象で恒等射になる。 -/
theorem zeroFiltration_inr_desc : CochainComplex.mappingCone.inr f ≫ zeroFiltrationConeDesc f = 𝟙 K :=
  CochainComplex.mappingCone.inr_descShortComplex (zeroFiltrationConeShortComplex f)

/-- 原零始点からのinrも全次数で擬同型。 -/
instance zeroFiltration_inr_quasiIso : QuasiIso (CochainComplex.mappingCone.inr f) := by
  haveI : QuasiIso (CochainComplex.mappingCone.inr f ≫ zeroFiltrationConeDesc f) := by
    rw [zeroFiltration_inr_desc]
    infer_instance
  exact quasiIso_of_comp_right _ (zeroFiltrationConeDesc f)

end AAT.AG.AtlasCoefficientFiber
#print axioms AAT.AG.AtlasCoefficientFiber.zeroFiltrationDegree_isZero
#print axioms AAT.AG.AtlasCoefficientFiber.zeroFiltration_isZero
#print axioms AAT.AG.AtlasCoefficientFiber.zeroFiltrationMap_eq_zero
#print axioms AAT.AG.AtlasCoefficientFiber.zeroFiltrationConeShortComplex
#print axioms AAT.AG.AtlasCoefficientFiber.zeroFiltrationConeShortExact
#print axioms AAT.AG.AtlasCoefficientFiber.zeroFiltrationConeDesc
#print axioms AAT.AG.AtlasCoefficientFiber.zeroFiltrationConeDesc_quasiIso
#print axioms AAT.AG.AtlasCoefficientFiber.zeroFiltration_inr_desc
#print axioms AAT.AG.AtlasCoefficientFiber.zeroFiltration_inr_quasiIso
#assert_standard_axioms_only AAT.AG.AtlasCoefficientFiber
