import ResearchLean.AG.AtlasCoefficientFiber.LawSupportCones
import ResearchLean.AG.AtlasCoefficientFiber.LawSupportComposition

/-!
# G-135 D：原Law三錐の任意ラベル別部分台族

## Implementation notes

元Law錐のcanonical族同型に、同じprimitive支持錐射を全成分で合成する。
各射影が元native Law錐射と一致することを両座標で示す。
ラベルの集合圧縮や錐homologyだけの置換を行わない。
-/
noncomputable section
namespace AAT.AG.AtlasCoefficientFiber
open CategoryTheory Limits CochainComplex HomologicalComplex
open CanonicalResolution ResolutionInvariance FaceRelationSubdivision AtlasDefectComposition
universe u

variable {Source : Type u} [Fintype Source]
variable {qc qf : Reading Source} {h : qc.CoarserThan qf}
variable {Nc : TargetSupportedNerve.{u,u} qc} {Nf : TargetSupportedNerve.{u,u} qf}
variable (M : IncidenceSupportedComparison qc qf h Nc Nf)
variable (laws : FiniteLawFamily Source) (ha : laws.Adequate qc)
variable {A : LawValueLabel laws → Set qc.Target}
variable (hA : ∀ l, A l ⊆ labelValueFiber laws qc ha l)

/-- 元LawCoefficient錐から同じ原部分台錐の全族への実射。 -/
def lawSupportCoefficientConeFamily : lawCoefficientCone M laws ha ⟶
    FiniteComplexFamily.complex (fun l => coefficientCone M (A l)) :=
  (lawCoefficientConeFamilyIso M laws ha).hom ≫
    FiniteComplexFamily.map _ _ (fun l => supportCoefficientCone M (hA l))

/-- 元LawCoefficient錐族射の全次数・全元・全ラベル値。 -/
theorem lawSupportCoefficientConeFamily_apply (n : ℤ) (z : (lawCoefficientCone M laws ha).X n)
    (l : LawValueLabel laws) :
    (lawSupportCoefficientConeFamily M laws ha hA).f n z l =
      (supportCoefficientCone M (hA l)).f n ((lawCoefficientConeFamilyIso M laws ha).hom.f n z l) := rfl

/-- 元LawCoefficient錐族射の各射影は同じnative部分台錐射。 -/
theorem lawSupportCoefficientConeFamily_projection (l : LawValueLabel laws) :
    lawSupportCoefficientConeFamily M laws ha hA ≫ FiniteComplexFamily.projection _ l =
      lawSupportCoefficientCone M laws ha l (hA l) := by
  apply HomologicalComplex.Hom.ext
  funext n
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro z
  simp only [HomologicalComplex.comp_f, ModuleCat.comp_apply, FiniteComplexFamily.projection_apply]
  apply (coneCoordinateEquiv (zeroExtensionMap (unitHom M (A l))) n).injective
  rw [lawSupportCoefficientConeFamily_apply, supportCoefficientCone_apply,
    lawCoefficientConeFamilyIso_component, lawSupportCoefficientCone_apply,
    lawSupportP_component_apply, lawSupportCoarse_component_apply]

/-- 元LawFiber錐から同じ原部分台錐の全族への実射。 -/
def lawSupportFiberConeFamily : lawFiberCone M laws ha ⟶
    FiniteComplexFamily.complex (fun l => fiberCone M (A l)) :=
  (lawFiberConeFamilyIso M laws ha).hom ≫
    FiniteComplexFamily.map _ _ (fun l => supportFiberCone M (hA l))

/-- 元LawFiber錐族射の全次数・全元・全ラベル値。 -/
theorem lawSupportFiberConeFamily_apply (n : ℤ) (z : (lawFiberCone M laws ha).X n)
    (l : LawValueLabel laws) :
    (lawSupportFiberConeFamily M laws ha hA).f n z l =
      (supportFiberCone M (hA l)).f n ((lawFiberConeFamilyIso M laws ha).hom.f n z l) := rfl

/-- 元LawFiber錐族射の各射影は同じnative部分台錐射。 -/
theorem lawSupportFiberConeFamily_projection (l : LawValueLabel laws) :
    lawSupportFiberConeFamily M laws ha hA ≫ FiniteComplexFamily.projection _ l =
      lawSupportFiberCone M laws ha l (hA l) := by
  apply HomologicalComplex.Hom.ext
  funext n
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro z
  simp only [HomologicalComplex.comp_f, ModuleCat.comp_apply, FiniteComplexFamily.projection_apply]
  apply (coneCoordinateEquiv (zeroExtensionMap (evaluationHom M (A l))) n).injective
  rw [lawSupportFiberConeFamily_apply, supportFiberCone_apply,
    lawFiberConeFamilyIso_component, lawSupportFiberCone_apply,
    lawSupportFine_component_apply, lawSupportP_component_apply]

/-- 元LawTotal錐から同じ原部分台錐の全族への実射。 -/
def lawSupportTotalConeFamily : lawTotalCone M laws ha ⟶
    FiniteComplexFamily.complex (fun l => totalCone M (A l)) :=
  (lawTotalConeFamilyIso M laws ha).hom ≫
    FiniteComplexFamily.map _ _ (fun l => supportTotalCone M (hA l))

/-- 元LawTotal錐族射の全次数・全元・全ラベル値。 -/
theorem lawSupportTotalConeFamily_apply (n : ℤ) (z : (lawTotalCone M laws ha).X n)
    (l : LawValueLabel laws) :
    (lawSupportTotalConeFamily M laws ha hA).f n z l =
      (supportTotalCone M (hA l)).f n ((lawTotalConeFamilyIso M laws ha).hom.f n z l) := rfl

/-- 元LawTotal錐族射の各射影は同じnative部分台錐射。 -/
theorem lawSupportTotalConeFamily_projection (l : LawValueLabel laws) :
    lawSupportTotalConeFamily M laws ha hA ≫ FiniteComplexFamily.projection _ l =
      lawSupportTotalCone M laws ha l (hA l) := by
  apply HomologicalComplex.Hom.ext
  funext n
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro z
  simp only [HomologicalComplex.comp_f, ModuleCat.comp_apply, FiniteComplexFamily.projection_apply]
  apply (coneCoordinateEquiv (zeroExtensionMap (M.aSubnerveComparisonHom (A l))) n).injective
  rw [lawSupportTotalConeFamily_apply, supportTotalCone_apply,
    lawTotalConeFamilyIso_component, lawSupportTotalCone_apply,
    lawSupportFine_component_apply, lawSupportCoarse_component_apply]

/-- 全族Coefficient錐射の全整数次数値は同じnative部分台錐射。 -/
theorem lawSupportCoefficientConeFamily_value (n : ℤ) (z : (lawCoefficientCone M laws ha).X n)
    (l : LawValueLabel laws) :
    (lawSupportCoefficientConeFamily M laws ha hA).f n z l = (lawSupportCoefficientCone M laws ha l (hA l)).f n z := by
  have hh := congrArg (fun f => f.f n z) (lawSupportCoefficientConeFamily_projection M laws ha hA l)
  simpa only [HomologicalComplex.comp_f, ModuleCat.comp_apply, FiniteComplexFamily.projection_apply] using hh

/-- 全族Fiber錐射の全整数次数値は同じnative部分台錐射。 -/
theorem lawSupportFiberConeFamily_value (n : ℤ) (z : (lawFiberCone M laws ha).X n)
    (l : LawValueLabel laws) :
    (lawSupportFiberConeFamily M laws ha hA).f n z l = (lawSupportFiberCone M laws ha l (hA l)).f n z := by
  have hh := congrArg (fun f => f.f n z) (lawSupportFiberConeFamily_projection M laws ha hA l)
  simpa only [HomologicalComplex.comp_f, ModuleCat.comp_apply, FiniteComplexFamily.projection_apply] using hh

/-- 全族Total錐射の全整数次数値は同じnative部分台錐射。 -/
theorem lawSupportTotalConeFamily_value (n : ℤ) (z : (lawTotalCone M laws ha).X n)
    (l : LawValueLabel laws) :
    (lawSupportTotalConeFamily M laws ha hA).f n z l = (lawSupportTotalCone M laws ha l (hA l)).f n z := by
  have hh := congrArg (fun f => f.f n z) (lawSupportTotalConeFamily_projection M laws ha hA l)
  simpa only [HomologicalComplex.comp_f, ModuleCat.comp_apply, FiniteComplexFamily.projection_apply] using hh

/-- 原Law triangleのfirst射は同じ原部分台全族射と全Homで可換。 -/
theorem lawSupportConeFamilyTriangle_first :
    (lawCoefficientCompositionTriangle M laws ha).mor₁ ≫ lawSupportTotalConeFamily M laws ha hA =
      lawSupportCoefficientConeFamily M laws ha hA ≫
        FiniteComplexFamily.map _ _ (fun l => (coefficientCompositionTriangle M (A l)).mor₁) := by
  apply HomologicalComplex.Hom.ext
  funext n
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro z
  funext l
  change (lawSupportTotalConeFamily M laws ha hA).f n
      ((lawCoefficientCompositionTriangle M laws ha).mor₁.f n z) l =
    (coefficientCompositionTriangle M (A l)).mor₁.f n
      ((lawSupportCoefficientConeFamily M laws ha hA).f n z l)
  rw [lawSupportTotalConeFamily_value, lawSupportCoefficientConeFamily_value]
  exact congrArg (fun f => f.f n z) (lawSupportConeTriangle_first M laws ha l (hA l))

/-- 原Law triangleのsecond射は同じ原部分台全族射と全Homで可換。 -/
theorem lawSupportConeFamilyTriangle_second :
    (lawCoefficientCompositionTriangle M laws ha).mor₂ ≫ lawSupportFiberConeFamily M laws ha hA =
      lawSupportTotalConeFamily M laws ha hA ≫
        FiniteComplexFamily.map _ _ (fun l => (coefficientCompositionTriangle M (A l)).mor₂) := by
  apply HomologicalComplex.Hom.ext
  funext n
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro z
  funext l
  change (lawSupportFiberConeFamily M laws ha hA).f n
      ((lawCoefficientCompositionTriangle M laws ha).mor₂.f n z) l =
    (coefficientCompositionTriangle M (A l)).mor₂.f n
      ((lawSupportTotalConeFamily M laws ha hA).f n z l)
  rw [lawSupportFiberConeFamily_value, lawSupportTotalConeFamily_value]
  exact congrArg (fun f => f.f n z) (lawSupportConeTriangle_second M laws ha l (hA l))

/-- 元Law Q評価は同じ原部分台Q評価族と全次数のHomで可換。 -/
theorem lawSupportFiberConeFamilyDesc : lawFiberConeDesc M laws ha ≫ lawSupportFamilyQ M laws ha hA =
    lawSupportFiberConeFamily M laws ha hA ≫
      FiniteComplexFamily.map _ _ (fun l => fiberConeDesc M (A l)) := by
  apply HomologicalComplex.Hom.ext
  funext n
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro z
  funext l
  change (lawSupportFamilyQ M laws ha hA).f n ((lawFiberConeDesc M laws ha).f n z) l =
    (fiberConeDesc M (A l)).f n ((lawSupportFiberConeFamily M laws ha hA).f n z l)
  rw [lawSupportFamilyQ_apply, lawSupportFiberConeFamily_value]
  exact congrArg (fun f => f.f n z) (lawSupportFiberConeDesc M laws ha l (hA l))

/-- 元ラベル台を保つCoefficient錐全族射は元canonical族同型。 -/
theorem lawSupportCoefficientConeFamily_refl :
    lawSupportCoefficientConeFamily M laws ha (fun l => Set.Subset.refl (labelValueFiber laws qc ha l)) =
      (lawCoefficientConeFamilyIso M laws ha).hom := by
  dsimp only [lawSupportCoefficientConeFamily]
  simp only [supportCoefficientCone_refl, FiniteComplexFamily.map_id, Category.comp_id]

/-- 原LawCoefficient錐の任意ラベル別入れ子台射を全族で合成する。 -/
theorem lawSupportCoefficientConeFamily_comp {B : LawValueLabel laws → Set qc.Target}
    (hab : ∀ l, A l ⊆ B l) (hb : ∀ l, B l ⊆ labelValueFiber laws qc ha l) :
    lawSupportCoefficientConeFamily M laws ha hb ≫
      FiniteComplexFamily.map _ _ (fun l => supportCoefficientCone M (hab l)) =
        lawSupportCoefficientConeFamily M laws ha (fun l => (hab l).trans (hb l)) := by
  dsimp only [lawSupportCoefficientConeFamily]
  rw [Category.assoc, ← FiniteComplexFamily.map_comp]
  congr 2
  funext l
  exact supportCoefficientCone_comp M (hab l) (hb l)

/-- 元ラベル台を保つFiber錐全族射は元canonical族同型。 -/
theorem lawSupportFiberConeFamily_refl :
    lawSupportFiberConeFamily M laws ha (fun l => Set.Subset.refl (labelValueFiber laws qc ha l)) =
      (lawFiberConeFamilyIso M laws ha).hom := by
  dsimp only [lawSupportFiberConeFamily]
  simp only [supportFiberCone_refl, FiniteComplexFamily.map_id, Category.comp_id]

/-- 原LawFiber錐の任意ラベル別入れ子台射を全族で合成する。 -/
theorem lawSupportFiberConeFamily_comp {B : LawValueLabel laws → Set qc.Target}
    (hab : ∀ l, A l ⊆ B l) (hb : ∀ l, B l ⊆ labelValueFiber laws qc ha l) :
    lawSupportFiberConeFamily M laws ha hb ≫
      FiniteComplexFamily.map _ _ (fun l => supportFiberCone M (hab l)) =
        lawSupportFiberConeFamily M laws ha (fun l => (hab l).trans (hb l)) := by
  dsimp only [lawSupportFiberConeFamily]
  rw [Category.assoc, ← FiniteComplexFamily.map_comp]
  congr 2
  funext l
  exact supportFiberCone_comp M (hab l) (hb l)

/-- 元ラベル台を保つTotal錐全族射は元canonical族同型。 -/
theorem lawSupportTotalConeFamily_refl :
    lawSupportTotalConeFamily M laws ha (fun l => Set.Subset.refl (labelValueFiber laws qc ha l)) =
      (lawTotalConeFamilyIso M laws ha).hom := by
  dsimp only [lawSupportTotalConeFamily]
  simp only [supportTotalCone_refl, FiniteComplexFamily.map_id, Category.comp_id]

/-- 原LawTotal錐の任意ラベル別入れ子台射を全族で合成する。 -/
theorem lawSupportTotalConeFamily_comp {B : LawValueLabel laws → Set qc.Target}
    (hab : ∀ l, A l ⊆ B l) (hb : ∀ l, B l ⊆ labelValueFiber laws qc ha l) :
    lawSupportTotalConeFamily M laws ha hb ≫
      FiniteComplexFamily.map _ _ (fun l => supportTotalCone M (hab l)) =
        lawSupportTotalConeFamily M laws ha (fun l => (hab l).trans (hb l)) := by
  dsimp only [lawSupportTotalConeFamily]
  rw [Category.assoc, ← FiniteComplexFamily.map_comp]
  congr 2
  funext l
  exact supportTotalCone_comp M (hab l) (hb l)

end AAT.AG.AtlasCoefficientFiber
#print axioms AAT.AG.AtlasCoefficientFiber.lawSupportCoefficientConeFamily
#print axioms AAT.AG.AtlasCoefficientFiber.lawSupportCoefficientConeFamily_apply
#print axioms AAT.AG.AtlasCoefficientFiber.lawSupportCoefficientConeFamily_projection
#print axioms AAT.AG.AtlasCoefficientFiber.lawSupportFiberConeFamily
#print axioms AAT.AG.AtlasCoefficientFiber.lawSupportFiberConeFamily_apply
#print axioms AAT.AG.AtlasCoefficientFiber.lawSupportFiberConeFamily_projection
#print axioms AAT.AG.AtlasCoefficientFiber.lawSupportTotalConeFamily
#print axioms AAT.AG.AtlasCoefficientFiber.lawSupportTotalConeFamily_apply
#print axioms AAT.AG.AtlasCoefficientFiber.lawSupportTotalConeFamily_projection
#print axioms AAT.AG.AtlasCoefficientFiber.lawSupportCoefficientConeFamily_value
#print axioms AAT.AG.AtlasCoefficientFiber.lawSupportFiberConeFamily_value
#print axioms AAT.AG.AtlasCoefficientFiber.lawSupportTotalConeFamily_value
#print axioms AAT.AG.AtlasCoefficientFiber.lawSupportConeFamilyTriangle_first
#print axioms AAT.AG.AtlasCoefficientFiber.lawSupportConeFamilyTriangle_second
#print axioms AAT.AG.AtlasCoefficientFiber.lawSupportFiberConeFamilyDesc
#print axioms AAT.AG.AtlasCoefficientFiber.lawSupportCoefficientConeFamily_refl
#print axioms AAT.AG.AtlasCoefficientFiber.lawSupportCoefficientConeFamily_comp
#print axioms AAT.AG.AtlasCoefficientFiber.lawSupportFiberConeFamily_refl
#print axioms AAT.AG.AtlasCoefficientFiber.lawSupportFiberConeFamily_comp
#print axioms AAT.AG.AtlasCoefficientFiber.lawSupportTotalConeFamily_refl
#print axioms AAT.AG.AtlasCoefficientFiber.lawSupportTotalConeFamily_comp
#print axioms AAT.AG.AtlasCoefficientFiber.lawSupportCoefficientCone.congr_simp
#print axioms AAT.AG.AtlasCoefficientFiber.lawSupportCoefficientConeFamily.congr_simp
#print axioms AAT.AG.AtlasCoefficientFiber.lawSupportFiberCone.congr_simp
#print axioms AAT.AG.AtlasCoefficientFiber.lawSupportFiberConeFamily.congr_simp
#print axioms AAT.AG.AtlasCoefficientFiber.lawSupportTotalCone.congr_simp
#print axioms AAT.AG.AtlasCoefficientFiber.lawSupportTotalConeFamily.congr_simp
#print axioms AAT.AG.AtlasCoefficientFiber.supportCoefficientCone.congr_simp
#print axioms AAT.AG.AtlasCoefficientFiber.supportFiberCone.congr_simp
#print axioms AAT.AG.AtlasCoefficientFiber.supportTotalCone.congr_simp
#assert_standard_axioms_only AAT.AG.AtlasCoefficientFiber
