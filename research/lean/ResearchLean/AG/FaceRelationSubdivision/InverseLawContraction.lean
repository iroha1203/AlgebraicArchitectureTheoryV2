import ResearchLean.AG.FaceRelationSubdivision.PresentationLawInverse
import ResearchLean.AG.FaceRelationSubdivision.TriangleInverseContraction
import ResearchLean.AG.FaceRelationSubdivision.SubdivisionInverseContraction
import ResearchLean.AG.FaceRelationSubdivision.ElementaryDiagnostics

/-!
# 原始逆patternの同じ実Law収縮

## Implementation notes

復元した正操作の原始表と原始表示表から比較・逆有限和を生成する。
標準同値の射は独立生成した同じ比較へ等号で接続し、旧H1と標準錐へ渡す。
-/
noncomputable section
open CategoryTheory CategoryTheory.Limits
namespace AAT.AG.FaceRelationSubdivision
open CanonicalResolution ResolutionInvariance TwoPhase AtlasDefectComposition
universe u
variable {Source : Type u} [Fintype Source] {q : Reading Source}

namespace TriangleInversePattern
variable {N : TargetSupportedNerve.{u,u} q} (P : TriangleInversePattern N)
variable (laws : FiniteLawFamily Source) (ha : laws.Adequate q)

/-- 原始collapse Option表から独立生成した同じ実Law比較。 -/
def lawR := P.collapse.generatedComparisonHom laws ha ha
/-- 復元正操作のsection有限和と原始表示から独立生成したLaw逆射。 -/
def lawS := presentationLawSection P.presentation
  (TriangleAddition.s0 P.restored P.restoredBase) (TriangleAddition.s1 P.restored P.restoredBase)
  (TriangleAddition.s2 P.restored P.restoredBase) (TriangleAddition.s_comm01 P.restored P.restoredBase)
  (TriangleAddition.s_comm12 P.restored P.restoredBase) laws ha

/-- 同じ原始比較への着地を公開する。 -/
@[simp] theorem lawR_eq_generated : P.lawR laws ha =
    P.collapse.generatedComparisonHom laws ha ha := rfl
/-- 同じ原始逆有限和の構成式。 -/
@[simp] theorem lawS_eq_finite : P.lawS laws ha =
    presentationLawSection P.presentation
      (TriangleAddition.s0 P.restored P.restoredBase) (TriangleAddition.s1 P.restored P.restoredBase)
      (TriangleAddition.s2 P.restored P.restoredBase) (TriangleAddition.s_comm01 P.restored P.restoredBase)
      (TriangleAddition.s_comm12 P.restored P.restoredBase) laws ha := rfl

/-- 原始rの直接生成は復元正操作と原始逆表示の同じLaw合成。 -/
theorem lawR_comp : P.lawR laws ha =
    cochainComp (TriangleAddition.lawR P.restored P.restoredBase laws ha)
      (P.presentation.symmSelf.comparison.generatedComparisonHom laws ha ha) := by
  rw [lawR_eq_generated, collapse_eq, generatedComparisonHom_comp,
    ← TriangleAddition.lawR_eq_generated]
/-- 原始section有限和も表示と復元正sectionの同じ合成へ着地。 -/
theorem lawS_comp : P.lawS laws ha =
    cochainComp (P.presentation.comparison.generatedComparisonHom laws ha ha)
      (TriangleAddition.lawS P.restored P.restoredBase laws ha) := by
  rw [lawS_eq_finite, presentationLawSection_eq]
  apply cochain_ext
  · apply LinearMap.ext; intro z
    rw [cochainComp_f0, cochainComp_f0, lawFiniteHom_f0, TriangleAddition.lawS_f0]
  · apply LinearMap.ext; intro z
    rw [cochainComp_f1, cochainComp_f1, lawFiniteHom_f1, TriangleAddition.lawS_f1]
  · apply LinearMap.ext; intro z
    rw [cochainComp_f2, cochainComp_f2, lawFiniteHom_f2, TriangleAddition.lawS_f2]

omit [Fintype Source] in
/-- 同じ原始collapse有限和の支持選択は受理済み逆pattern rHom。 -/
theorem rSubsetFiniteHom_eq (A : Set q.Target) :
    subsetFiniteHom P.collapse.basis0 P.collapse.basis1 P.collapse.basis2
      P.collapse.basis_comm01 P.collapse.basis_comm12 A = P.rHom A := by
  rw [P.collapse.basisSubsetFiniteHom_eq, P.rHom_eq_generated]

omit [Fintype Source] in
/-- 同じ原始section有限和の支持選択は受理済み逆pattern sHom。 -/
theorem sSubsetFiniteHom_eq (A : Set q.Target) :
    subsetFiniteHom ((TriangleAddition.s0 P.restored P.restoredBase).comp P.presentation.comparison.basis0)
      ((TriangleAddition.s1 P.restored P.restoredBase).comp P.presentation.comparison.basis1)
      ((TriangleAddition.s2 P.restored P.restoredBase).comp P.presentation.comparison.basis2)
      (finiteComp_comm01 _ _ _ _ P.presentation.comparison.basis_comm01
        (TriangleAddition.s_comm01 P.restored P.restoredBase))
      (finiteComp_comm12 _ _ _ _ P.presentation.comparison.basis_comm12
        (TriangleAddition.s_comm12 P.restored P.restoredBase)) A = P.sHom A := by
  apply cochain_ext
  · rw [subsetFiniteHom_f0, sHom_f0, chainContraction_s0, SupportedBasisMap.selected_comp,
      IncidenceSupportedComparison.selected_basis0_eq, ← CellPresentationEquiv.sameR0_eq_generated]
  · rw [subsetFiniteHom_f1, sHom_f1, chainContraction_s1, SupportedBasisMap.selected_comp,
      IncidenceSupportedComparison.selected_basis1_eq, ← CellPresentationEquiv.sameR1_eq_generated]
  · rw [subsetFiniteHom_f2, sHom_f2, chainContraction_s2, SupportedBasisMap.selected_comp,
      IncidenceSupportedComparison.selected_basis2_eq, ← CellPresentationEquiv.sameR2_eq_generated]

/-- 同じ原始Law collapseは全三成分で受理済み実fiber rへ着地。 -/
theorem lawR_fiber (l : LawValueLabel laws) :
    cochainComp (P.lawR laws ha) (lawFiberHom laws ha N l) =
      cochainComp (lawFiberHom laws ha P.restored l)
        (P.rHom (labelValueFiber laws q ha l)) := by
  rw [lawR_eq_generated, ← P.collapse.basisLawHom_eq_generated laws ha
    P.collapse.basis_comm01 P.collapse.basis_comm12]
  have h := lawFiniteFiber_square P.collapse.basis0 P.collapse.basis1 P.collapse.basis2
    P.collapse.basis_comm01 P.collapse.basis_comm12 laws ha l
  rw [rSubsetFiniteHom_eq] at h
  exact h

/-- 同じ独立Law section有限和も全三成分で同じ実fiber sへ着地。 -/
theorem lawS_fiber (l : LawValueLabel laws) :
    cochainComp (P.lawS laws ha) (lawFiberHom laws ha P.restored l) =
      cochainComp (lawFiberHom laws ha N l)
        (P.sHom (labelValueFiber laws q ha l)) := by
  rw [lawS_eq_finite, presentationLawSection_eq_finite]
  have h := lawFiniteFiber_square
    ((TriangleAddition.s0 P.restored P.restoredBase).comp P.presentation.comparison.basis0)
    ((TriangleAddition.s1 P.restored P.restoredBase).comp P.presentation.comparison.basis1)
    ((TriangleAddition.s2 P.restored P.restoredBase).comp P.presentation.comparison.basis2)
    (finiteComp_comm01 _ _ _ _ P.presentation.comparison.basis_comm01
      (TriangleAddition.s_comm01 P.restored P.restoredBase))
    (finiteComp_comm12 _ _ _ _ P.presentation.comparison.basis_comm12
      (TriangleAddition.s_comm12 P.restored P.restoredBase)) laws ha l
  rw [sSubsetFiniteHom_eq] at h
  exact h

/-- 原始逆patternから生成した二射とホモトピーの標準同値。 -/
def lawHomotopyEquiv :=
  (TriangleAddition.lawHomotopyEquiv P.restored P.restoredBase laws ha).trans
    (HomotopyEquiv.ofIso (P.presentation.lawZeroExtensionIso laws ha).symm)
/-- この同値の順射の構成式を公開する。 -/
@[simp] theorem lawHomotopyEquiv_hom_formula : (P.lawHomotopyEquiv laws ha).hom =
    (TriangleAddition.lawHomotopyEquiv P.restored P.restoredBase laws ha).hom ≫
      (P.presentation.lawZeroExtensionIso laws ha).inv := rfl
/-- この同値の逆射の構成式を公開する。 -/
@[simp] theorem lawHomotopyEquiv_inv_formula : (P.lawHomotopyEquiv laws ha).inv =
    (P.presentation.lawZeroExtensionIso laws ha).hom ≫
      (TriangleAddition.lawHomotopyEquiv P.restored P.restoredBase laws ha).inv := rfl
/-- 標準同値の射は同じ独立原始Law比較。 -/
theorem lawHomotopyEquiv_hom : (P.lawHomotopyEquiv laws ha).hom =
    zeroExtensionMap (P.lawR laws ha) := by
  rw [lawHomotopyEquiv_hom_formula, TriangleAddition.lawHomotopyEquiv_hom,
    CellPresentationEquiv.lawZeroExtensionIso_inv, ← zeroExtensionMap_comp, ← lawR_comp]
/-- 標準同値の逆も同じ独立有限和Law射。 -/
theorem lawHomotopyEquiv_inv : (P.lawHomotopyEquiv laws ha).inv =
    zeroExtensionMap (P.lawS laws ha) := by
  rw [lawHomotopyEquiv_inv_formula, TriangleAddition.lawHomotopyEquiv_inv,
    CellPresentationEquiv.lawZeroExtensionIso_hom, ← zeroExtensionMap_comp, ← lawS_comp]

/-- 逆縮約では同じ二射を逆向きに使用する標準同値。 -/
def inverseLawHomotopyEquiv := (P.lawHomotopyEquiv laws ha).symm
/-- 逆縮約の実順射は原始section有限和。 -/
@[simp] theorem inverseLawHomotopyEquiv_hom : (P.inverseLawHomotopyEquiv laws ha).hom =
    zeroExtensionMap (P.lawS laws ha) := by
  exact P.lawHomotopyEquiv_inv laws ha
/-- 逆縮約の実逆射は原始collapse。 -/
@[simp] theorem inverseLawHomotopyEquiv_inv : (P.inverseLawHomotopyEquiv laws ha).inv =
    zeroExtensionMap (P.lawR laws ha) := by
  exact P.lawHomotopyEquiv_hom laws ha

/-- 同じ原始Law二射の全整数次数同型。 -/
def lawHomologyIso (n : ℤ) := (P.lawHomotopyEquiv laws ha).toHomologyIso n
/-- 全次数順射は同じ原始比較のhomologyMap。 -/
theorem lawHomologyIso_hom (n : ℤ) : (P.lawHomologyIso laws ha n).hom =
    HomologicalComplex.homologyMap (zeroExtensionMap (P.lawR laws ha)) n := by
  change HomologicalComplex.homologyMap (P.lawHomotopyEquiv laws ha).hom n = _
  rw [lawHomotopyEquiv_hom]
/-- 全次数逆射は同じ原始sectionのhomologyMap。 -/
theorem lawHomologyIso_inv (n : ℤ) : (P.lawHomologyIso laws ha n).inv =
    HomologicalComplex.homologyMap (zeroExtensionMap (P.lawS laws ha)) n := by
  change HomologicalComplex.homologyMap (P.lawHomotopyEquiv laws ha).inv n = _
  rw [lawHomotopyEquiv_inv]

/-- 同じ二射の旧H1商同型。 -/
def lawOldH1Iso := homotopyOldH1Iso (P.lawHomotopyEquiv laws ha)
/-- 旧H1順射は同じ実h1Map。 -/
theorem lawOldH1Iso_hom : (P.lawOldH1Iso laws ha).hom = ModuleCat.ofHom (P.lawR laws ha).h1Map :=
  homotopyOldH1Iso_hom _ _ (P.lawHomotopyEquiv_hom laws ha)
/-- 旧H1逆射も同じ実h1Map。 -/
theorem lawOldH1Iso_inv : (P.lawOldH1Iso laws ha).inv = ModuleCat.ofHom (P.lawS laws ha).h1Map :=
  homotopyOldH1Iso_inv _ _ (P.lawHomotopyEquiv_inv laws ha)
/-- 原始collapseの実H1欠損の両成分は零。 -/
theorem lawR_blockDefect_zero : blockDefect (P.lawR laws ha).h1Map = (0,0) :=
  homotopyH1_blockDefect_zero _ _ (P.lawHomotopyEquiv_hom laws ha)
/-- 逆縮約の原始sectionの実H1欠損も零。 -/
theorem lawS_blockDefect_zero : blockDefect (P.lawS laws ha).h1Map = (0,0) :=
  homotopyH1_blockDefect_zero _ _ (P.inverseLawHomotopyEquiv_hom laws ha)
/-- 原始collapseの同じ標準錐は全整数次数で零。 -/
theorem lawR_cone_isZero (n : ℤ) : IsZero
    ((CochainComplex.mappingCone (zeroExtensionMap (P.lawR laws ha))).homology n) := by
  rw [← lawHomotopyEquiv_hom]
  exact homotopyCone_isZero (P.lawHomotopyEquiv laws ha) n
/-- 原始逆縮約の同じ標準錐も全整数次数で零。 -/
theorem lawS_cone_isZero (n : ℤ) : IsZero
    ((CochainComplex.mappingCone (zeroExtensionMap (P.lawS laws ha))).homology n) := by
  rw [← inverseLawHomotopyEquiv_hom]
  exact homotopyCone_isZero (P.inverseLawHomotopyEquiv laws ha) n

end TriangleInversePattern

namespace SubdivisionInversePattern
variable {N : TargetSupportedNerve.{u,u} q} (P : SubdivisionInversePattern N)
variable (laws : FiniteLawFamily Source) (ha : laws.Adequate q)

/-- 原始collapse Option表から独立生成した同じ実Law比較。 -/
def lawR := P.collapse.generatedComparisonHom laws ha ha
/-- 復元正操作のsection有限和と原始表示から独立生成したLaw逆射。 -/
def lawS := presentationLawSection P.presentation
  (EdgeSubdivision.s0 P.restored P.commonEdge) (EdgeSubdivision.s1 P.restored P.commonEdge)
  (EdgeSubdivision.s2 P.restored P.commonEdge) (EdgeSubdivision.s_comm01 P.restored P.commonEdge)
  (EdgeSubdivision.s_comm12 P.restored P.commonEdge) laws ha

/-- 同じ原始比較への着地を公開する。 -/
@[simp] theorem lawR_eq_generated : P.lawR laws ha =
    P.collapse.generatedComparisonHom laws ha ha := rfl
/-- 同じ原始逆有限和の構成式。 -/
@[simp] theorem lawS_eq_finite : P.lawS laws ha =
    presentationLawSection P.presentation
      (EdgeSubdivision.s0 P.restored P.commonEdge) (EdgeSubdivision.s1 P.restored P.commonEdge)
      (EdgeSubdivision.s2 P.restored P.commonEdge) (EdgeSubdivision.s_comm01 P.restored P.commonEdge)
      (EdgeSubdivision.s_comm12 P.restored P.commonEdge) laws ha := rfl

/-- 原始rの直接生成は復元正操作と原始逆表示の同じLaw合成。 -/
theorem lawR_comp : P.lawR laws ha =
    cochainComp (EdgeSubdivision.lawR P.restored P.commonEdge laws ha)
      (P.presentation.symmSelf.comparison.generatedComparisonHom laws ha ha) := by
  rw [lawR_eq_generated, collapse_eq, generatedComparisonHom_comp,
    ← EdgeSubdivision.lawR_eq_generated]
/-- 原始section有限和も表示と復元正sectionの同じ合成へ着地。 -/
theorem lawS_comp : P.lawS laws ha =
    cochainComp (P.presentation.comparison.generatedComparisonHom laws ha ha)
      (EdgeSubdivision.lawS P.restored P.commonEdge laws ha) := by
  rw [lawS_eq_finite, presentationLawSection_eq]
  apply cochain_ext
  · apply LinearMap.ext; intro z
    rw [cochainComp_f0, cochainComp_f0, lawFiniteHom_f0, EdgeSubdivision.lawS_f0]
  · apply LinearMap.ext; intro z
    rw [cochainComp_f1, cochainComp_f1, lawFiniteHom_f1, EdgeSubdivision.lawS_f1]
  · apply LinearMap.ext; intro z
    rw [cochainComp_f2, cochainComp_f2, lawFiniteHom_f2, EdgeSubdivision.lawS_f2]

omit [Fintype Source] in
/-- 同じ原始collapse有限和の支持選択は受理済み逆pattern rHom。 -/
theorem rSubsetFiniteHom_eq (A : Set q.Target) :
    subsetFiniteHom P.collapse.basis0 P.collapse.basis1 P.collapse.basis2
      P.collapse.basis_comm01 P.collapse.basis_comm12 A = P.rHom A := by
  rw [P.collapse.basisSubsetFiniteHom_eq, P.rHom_eq_generated]

omit [Fintype Source] in
/-- 同じ原始section有限和の支持選択は受理済み逆pattern sHom。 -/
theorem sSubsetFiniteHom_eq (A : Set q.Target) :
    subsetFiniteHom ((EdgeSubdivision.s0 P.restored P.commonEdge).comp P.presentation.comparison.basis0)
      ((EdgeSubdivision.s1 P.restored P.commonEdge).comp P.presentation.comparison.basis1)
      ((EdgeSubdivision.s2 P.restored P.commonEdge).comp P.presentation.comparison.basis2)
      (finiteComp_comm01 _ _ _ _ P.presentation.comparison.basis_comm01
        (EdgeSubdivision.s_comm01 P.restored P.commonEdge))
      (finiteComp_comm12 _ _ _ _ P.presentation.comparison.basis_comm12
        (EdgeSubdivision.s_comm12 P.restored P.commonEdge)) A = P.sHom A := by
  apply cochain_ext
  · rw [subsetFiniteHom_f0, sHom_f0, chainContraction_s0, SupportedBasisMap.selected_comp,
      IncidenceSupportedComparison.selected_basis0_eq, ← CellPresentationEquiv.sameR0_eq_generated]
  · rw [subsetFiniteHom_f1, sHom_f1, chainContraction_s1, SupportedBasisMap.selected_comp,
      IncidenceSupportedComparison.selected_basis1_eq, ← CellPresentationEquiv.sameR1_eq_generated]
  · rw [subsetFiniteHom_f2, sHom_f2, chainContraction_s2, SupportedBasisMap.selected_comp,
      IncidenceSupportedComparison.selected_basis2_eq, ← CellPresentationEquiv.sameR2_eq_generated]

/-- 同じ原始Law collapseは全三成分で受理済み実fiber rへ着地。 -/
theorem lawR_fiber (l : LawValueLabel laws) :
    cochainComp (P.lawR laws ha) (lawFiberHom laws ha N l) =
      cochainComp (lawFiberHom laws ha P.restored l)
        (P.rHom (labelValueFiber laws q ha l)) := by
  rw [lawR_eq_generated, ← P.collapse.basisLawHom_eq_generated laws ha
    P.collapse.basis_comm01 P.collapse.basis_comm12]
  have h := lawFiniteFiber_square P.collapse.basis0 P.collapse.basis1 P.collapse.basis2
    P.collapse.basis_comm01 P.collapse.basis_comm12 laws ha l
  rw [rSubsetFiniteHom_eq] at h
  exact h

/-- 同じ独立Law section有限和も全三成分で同じ実fiber sへ着地。 -/
theorem lawS_fiber (l : LawValueLabel laws) :
    cochainComp (P.lawS laws ha) (lawFiberHom laws ha P.restored l) =
      cochainComp (lawFiberHom laws ha N l)
        (P.sHom (labelValueFiber laws q ha l)) := by
  rw [lawS_eq_finite, presentationLawSection_eq_finite]
  have h := lawFiniteFiber_square
    ((EdgeSubdivision.s0 P.restored P.commonEdge).comp P.presentation.comparison.basis0)
    ((EdgeSubdivision.s1 P.restored P.commonEdge).comp P.presentation.comparison.basis1)
    ((EdgeSubdivision.s2 P.restored P.commonEdge).comp P.presentation.comparison.basis2)
    (finiteComp_comm01 _ _ _ _ P.presentation.comparison.basis_comm01
      (EdgeSubdivision.s_comm01 P.restored P.commonEdge))
    (finiteComp_comm12 _ _ _ _ P.presentation.comparison.basis_comm12
      (EdgeSubdivision.s_comm12 P.restored P.commonEdge)) laws ha l
  rw [sSubsetFiniteHom_eq] at h
  exact h

/-- 原始逆patternから生成した二射とホモトピーの標準同値。 -/
def lawHomotopyEquiv :=
  (EdgeSubdivision.lawHomotopyEquiv P.restored P.commonEdge laws ha).trans
    (HomotopyEquiv.ofIso (P.presentation.lawZeroExtensionIso laws ha).symm)
/-- この同値の順射の構成式を公開する。 -/
@[simp] theorem lawHomotopyEquiv_hom_formula : (P.lawHomotopyEquiv laws ha).hom =
    (EdgeSubdivision.lawHomotopyEquiv P.restored P.commonEdge laws ha).hom ≫
      (P.presentation.lawZeroExtensionIso laws ha).inv := rfl
/-- この同値の逆射の構成式を公開する。 -/
@[simp] theorem lawHomotopyEquiv_inv_formula : (P.lawHomotopyEquiv laws ha).inv =
    (P.presentation.lawZeroExtensionIso laws ha).hom ≫
      (EdgeSubdivision.lawHomotopyEquiv P.restored P.commonEdge laws ha).inv := rfl
/-- 標準同値の射は同じ独立原始Law比較。 -/
theorem lawHomotopyEquiv_hom : (P.lawHomotopyEquiv laws ha).hom =
    zeroExtensionMap (P.lawR laws ha) := by
  rw [lawHomotopyEquiv_hom_formula, EdgeSubdivision.lawHomotopyEquiv_hom,
    CellPresentationEquiv.lawZeroExtensionIso_inv, ← zeroExtensionMap_comp, ← lawR_comp]
/-- 標準同値の逆も同じ独立有限和Law射。 -/
theorem lawHomotopyEquiv_inv : (P.lawHomotopyEquiv laws ha).inv =
    zeroExtensionMap (P.lawS laws ha) := by
  rw [lawHomotopyEquiv_inv_formula, EdgeSubdivision.lawHomotopyEquiv_inv,
    CellPresentationEquiv.lawZeroExtensionIso_hom, ← zeroExtensionMap_comp, ← lawS_comp]

/-- 逆縮約では同じ二射を逆向きに使用する標準同値。 -/
def inverseLawHomotopyEquiv := (P.lawHomotopyEquiv laws ha).symm
/-- 逆縮約の実順射は原始section有限和。 -/
@[simp] theorem inverseLawHomotopyEquiv_hom : (P.inverseLawHomotopyEquiv laws ha).hom =
    zeroExtensionMap (P.lawS laws ha) := by
  exact P.lawHomotopyEquiv_inv laws ha
/-- 逆縮約の実逆射は原始collapse。 -/
@[simp] theorem inverseLawHomotopyEquiv_inv : (P.inverseLawHomotopyEquiv laws ha).inv =
    zeroExtensionMap (P.lawR laws ha) := by
  exact P.lawHomotopyEquiv_hom laws ha

/-- 同じ原始Law二射の全整数次数同型。 -/
def lawHomologyIso (n : ℤ) := (P.lawHomotopyEquiv laws ha).toHomologyIso n
/-- 全次数順射は同じ原始比較のhomologyMap。 -/
theorem lawHomologyIso_hom (n : ℤ) : (P.lawHomologyIso laws ha n).hom =
    HomologicalComplex.homologyMap (zeroExtensionMap (P.lawR laws ha)) n := by
  change HomologicalComplex.homologyMap (P.lawHomotopyEquiv laws ha).hom n = _
  rw [lawHomotopyEquiv_hom]
/-- 全次数逆射は同じ原始sectionのhomologyMap。 -/
theorem lawHomologyIso_inv (n : ℤ) : (P.lawHomologyIso laws ha n).inv =
    HomologicalComplex.homologyMap (zeroExtensionMap (P.lawS laws ha)) n := by
  change HomologicalComplex.homologyMap (P.lawHomotopyEquiv laws ha).inv n = _
  rw [lawHomotopyEquiv_inv]

/-- 同じ二射の旧H1商同型。 -/
def lawOldH1Iso := homotopyOldH1Iso (P.lawHomotopyEquiv laws ha)
/-- 旧H1順射は同じ実h1Map。 -/
theorem lawOldH1Iso_hom : (P.lawOldH1Iso laws ha).hom = ModuleCat.ofHom (P.lawR laws ha).h1Map :=
  homotopyOldH1Iso_hom _ _ (P.lawHomotopyEquiv_hom laws ha)
/-- 旧H1逆射も同じ実h1Map。 -/
theorem lawOldH1Iso_inv : (P.lawOldH1Iso laws ha).inv = ModuleCat.ofHom (P.lawS laws ha).h1Map :=
  homotopyOldH1Iso_inv _ _ (P.lawHomotopyEquiv_inv laws ha)
/-- 原始collapseの実H1欠損の両成分は零。 -/
theorem lawR_blockDefect_zero : blockDefect (P.lawR laws ha).h1Map = (0,0) :=
  homotopyH1_blockDefect_zero _ _ (P.lawHomotopyEquiv_hom laws ha)
/-- 逆縮約の原始sectionの実H1欠損も零。 -/
theorem lawS_blockDefect_zero : blockDefect (P.lawS laws ha).h1Map = (0,0) :=
  homotopyH1_blockDefect_zero _ _ (P.inverseLawHomotopyEquiv_hom laws ha)
/-- 原始collapseの同じ標準錐は全整数次数で零。 -/
theorem lawR_cone_isZero (n : ℤ) : IsZero
    ((CochainComplex.mappingCone (zeroExtensionMap (P.lawR laws ha))).homology n) := by
  rw [← lawHomotopyEquiv_hom]
  exact homotopyCone_isZero (P.lawHomotopyEquiv laws ha) n
/-- 原始逆縮約の同じ標準錐も全整数次数で零。 -/
theorem lawS_cone_isZero (n : ℤ) : IsZero
    ((CochainComplex.mappingCone (zeroExtensionMap (P.lawS laws ha))).homology n) := by
  rw [← inverseLawHomotopyEquiv_hom]
  exact homotopyCone_isZero (P.inverseLawHomotopyEquiv laws ha) n

end SubdivisionInversePattern

end AAT.AG.FaceRelationSubdivision
#assert_standard_axioms_only AAT.AG.FaceRelationSubdivision
