import ResearchLean.AG.AtlasCoefficientFiber.MappedEvaluation
import ResearchLean.AG.AtlasCoefficientFiber.FaceCloneComparison
import ResearchLean.AG.AtlasDefectComposition.ConeEquivalence

/-!
# G-135 D：面複製の原順像・二射と零fiber

## Implementation notes

元面foldの全mapped表から実ε同型を導き、自己readingの元集合へ輸送する。
この座標で同じηは元面foldの双対であり、複製した二面には同じ値を置く。
Pを細cochainから定義し直さず、原aの両逆とliteral R・τを接続する。
-/
noncomputable section
namespace AAT.AG.AtlasCoefficientFiber
open CategoryTheory Limits HomologicalComplex CochainComplex
open CanonicalResolution ResolutionInvariance FaceRelationSubdivision TwoPhase AtlasDefectComposition
universe u
namespace FaceClone
variable {Source : Type u} {q : Reading Source}
variable (N : TargetSupportedNerve.{u,u} q) (F : N.nerve.FaceComponent) (A : Set q.Target)

/-- 原面複製は全辺を同名someへ送る。 -/
theorem edge_mapped : ∀ e, (FaceDuplication.comparison N F).edgeMap e ≠ none := by
  intro e
  rw [FaceDuplication.comparison_edge]
  exact Option.some_ne_none _
/-- 原面複製は全面をfoldのsomeへ送る。 -/
theorem face_mapped : ∀ f, (FaceDuplication.comparison N F).faceMap f ≠ none := by
  intro f
  rw [FaceDuplication.comparison_face]
  exact Option.some_ne_none _
/-- 同じ原L₀は実垂直辺表から零。 -/
theorem L0_zero : degenerateL0 (FaceDuplication.comparison N F) A = ⊥ :=
  MappedCells.L0_eq_bot _ A (edge_mapped N F)
/-- 同じ原L₁は実垂直辺・混在面表から零。 -/
theorem L1_zero : degenerateL1 (FaceDuplication.comparison N F) A = ⊥ :=
  MappedCells.L1_eq_bot _ A (edge_mapped N F) (face_mapped N F)
/-- 同じ原L₂は実退化面表から零。 -/
theorem L2_zero : degenerateL2 (FaceDuplication.comparison N F) A = ⊥ :=
  MappedCells.L2_eq_bot _ A (face_mapped N F)

/-- 元Pから元canonical細複体への全次数同型、順射は原ε。 -/
def evaluationIso : zeroExtension (pushforwardComplex (FaceDuplication.comparison N F) A) ≅
    zeroExtension ((FaceDuplication.supported N F).targetSubsetComplex
      (comparisonFactor q q (Reading.coarserThan_refl q) ⁻¹' A)) :=
  MappedCells.evaluationStandardIso _ A (edge_mapped N F) (face_mapped N F)
/-- 原P評価同型の順射は独立counit評価そのもの。 -/
@[simp] theorem evaluationIso_hom : (evaluationIso N F A).hom =
    zeroExtensionMap (evaluationHom (FaceDuplication.comparison N F) A) := rfl
/-- 元自己readingの集合座標でPを細cochainへ両方向同定する。 -/
def coefficientStandardIso : zeroExtension (pushforwardComplex (FaceDuplication.comparison N F) A) ≅
    zeroExtension ((FaceDuplication.supported N F).targetSubsetComplex A) :=
  evaluationIso N F A ≪≫ fineStandardIso N F A
/-- 同型座標は同じεと元自己reading輸送の合成。 -/
@[simp] theorem coefficientStandardIso_hom : (coefficientStandardIso N F A).hom =
    zeroExtensionMap (evaluationHom (FaceDuplication.comparison N F) A) ≫
      (fineStandardIso N F A).hom := rfl
/-- 元ηはこの実ε座標で元G-134比較となる全射正方形。 -/
theorem unit_standard_square :
    zeroExtensionMap (unitHom (FaceDuplication.comparison N F) A) ≫
      (coefficientStandardIso N F A).hom = zeroExtensionMap (FaceDuplication.subsetHom N F A) := by
  rw [coefficientStandardIso_hom, ← Category.assoc, ← standardComparison_factorization]
  exact comparison_standard_square N F A
/-- 全chartで元η評価は同じchart値。 -/
theorem unit0_same (z : (N.targetSubsetComplex A).C0) :
    (coefficientStandardIso N F A).hom.f 0 (unit0 (FaceDuplication.comparison N F) A z) = z := by
  have hh := congrArg (fun φ : zeroExtension (N.targetSubsetComplex A) ⟶
    zeroExtension ((FaceDuplication.supported N F).targetSubsetComplex A) => φ.f 0 z)
      (unit_standard_square N F A)
  exact hh.trans (FaceDuplication.subsetHom_f0 N F A z)
/-- 全辺で元η評価は同じ辺値。 -/
theorem unit1_same (z : (N.targetSubsetComplex A).C1) :
    (coefficientStandardIso N F A).hom.f 1 (unit1 (FaceDuplication.comparison N F) A z) = z := by
  have hh := congrArg (fun φ : zeroExtension (N.targetSubsetComplex A) ⟶
    zeroExtension ((FaceDuplication.supported N F).targetSubsetComplex A) => φ.f 1 z)
      (unit_standard_square N F A)
  exact hh.trans (FaceDuplication.subsetHom_f1 N F A z)
/-- 全面で元η評価は同じ原始fold値、複製面には対角値を置く。 -/
theorem unit2_fold (z : (N.targetSubsetComplex A).C2)
    (f : (FaceDuplication.supported N F).FaceInTargetSubset A) :
    (coefficientStandardIso N F A).hom.f 2 (unit2 (FaceDuplication.comparison N F) A z) f =
      z (FaceDuplication.foldFace N F A f) := by
  have hh := congrArg (fun φ : zeroExtension (N.targetSubsetComplex A) ⟶
    zeroExtension ((FaceDuplication.supported N F).targetSubsetComplex A) => φ.f 2 z)
      (unit_standard_square N F A)
  exact (congrFun hh f).trans (FaceDuplication.subsetHom_f2 N F A z f)
/-- 旧選択面における原ηは元の値を回復する。 -/
theorem unit2_old (z : (N.targetSubsetComplex A).C2) (f : N.FaceInTargetSubset A) :
    (coefficientStandardIso N F A).hom.f 2 (unit2 (FaceDuplication.comparison N F) A z)
      (FaceDuplication.oldFace N F A f) = z f := by
  rw [unit2_fold, FaceDuplication.foldFace_oldFace]
/-- 選択fresh面における原ηは旧Fと同じ値となる。 -/
theorem unit2_fresh (hF : ∃ t, t ∈ N.faceSupport F ∧ t ∈ A) (z : (N.targetSubsetComplex A).C2) :
    (coefficientStandardIso N F A).hom.f 2 (unit2 (FaceDuplication.comparison N F) A z)
      (FaceDuplication.freshFace N F A hF) = z (FaceDuplication.selectedFace N F A hF) := by
  rw [unit2_fold, FaceDuplication.foldFace_fresh]

/-- 同じ原aは元H¹保存定理から両方向同型となる。 -/
def unitEquiv : (zeroExtension (N.targetSubsetComplex A)).homology (1 : ℤ) ≃ₗ[ℚ]
    (zeroExtension (pushforwardComplex (FaceDuplication.comparison N F) A)).homology (1 : ℤ) :=
  unitH1EquivOfZeroDefect _ A (defect_zero N F A)
/-- 原a同型の順射は同じηのH¹写像。 -/
@[simp] theorem unitEquiv_apply (x) : unitEquiv N F A x = unitH1 (FaceDuplication.comparison N F) A x :=
  unitH1EquivOfZeroDefect_apply _ A (defect_zero N F A) x
/-- 原aの逆座標から同じ元へ戻る。 -/
theorem unitEquiv_symm_apply (y) : unitH1 (FaceDuplication.comparison N F) A ((unitEquiv N F A).symm y) = y := by
  rw [← unitEquiv_apply, LinearEquiv.apply_symm_apply]
/-- 原aから逆に戻すと同じ粗元を回復する。 -/
theorem unitEquiv_apply_symm (x) : (unitEquiv N F A).symm (unitH1 (FaceDuplication.comparison N F) A x) = x := by
  rw [← unitEquiv_apply, LinearEquiv.symm_apply_apply]
/-- 原Φ H¹は全chartで零、mapped loopを垂直辺へ混入しない。 -/
theorem phiH1_zero (c : N.ChartInTargetSubset A) : Subsingleton (phiComplex (FaceDuplication.comparison N F) A c).H1 :=
  MappedCells.phiH1_subsingleton _ A (edge_mapped N F) c
/-- literal Rは同じ原始表から零空間となる。 -/
theorem R_zero : Subsingleton (R (FaceDuplication.comparison N F) A) :=
  MappedCells.R_subsingleton _ A (edge_mapped N F)
/-- 元τは同じliteral Rから出る零写像。 -/
theorem tau_zero : connectingTau (FaceDuplication.comparison N F) A = 0 :=
  MappedCells.tau_zero _ A (edge_mapped N F)
/-- 同じεのfiber錐は全整数次数で零。 -/
theorem fiberCone_zero (n : ℤ) : IsZero ((fiberCone (FaceDuplication.comparison N F) A).homology n) :=
  MappedCells.fiberCone_isZero _ A (edge_mapped N F) (face_mapped N F) n

/-- 同じ原η錐は実ε座標で元G-134比較錐に全複体同型。 -/
def coefficientConeIso : coefficientCone (FaceDuplication.comparison N F) A ≅
    comparisonCone (FaceDuplication.subsetHom N F A) :=
  coneMapIso _ _ (Iso.refl _) (coefficientStandardIso N F A)
    (by simpa only [Iso.refl_hom, Category.id_comp] using unit_standard_square N F A)
/-- η錐同型は元標準正方形射を使い、両錐座標を保持する。 -/
@[simp] theorem coefficientConeIso_hom : (coefficientConeIso N F A).hom =
    mappingCone.map (zeroExtensionMap (unitHom (FaceDuplication.comparison N F) A))
      (zeroExtensionMap (FaceDuplication.subsetHom N F A)) (𝟙 _)
      (coefficientStandardIso N F A).hom (by
        simpa only [Category.id_comp] using unit_standard_square N F A) := rfl

end FaceClone
end AAT.AG.AtlasCoefficientFiber

#print axioms AAT.AG.AtlasCoefficientFiber.FaceClone.edge_mapped
#print axioms AAT.AG.AtlasCoefficientFiber.FaceClone.face_mapped
#print axioms AAT.AG.AtlasCoefficientFiber.FaceClone.L0_zero
#print axioms AAT.AG.AtlasCoefficientFiber.FaceClone.L1_zero
#print axioms AAT.AG.AtlasCoefficientFiber.FaceClone.L2_zero
#print axioms AAT.AG.AtlasCoefficientFiber.FaceClone.evaluationIso
#print axioms AAT.AG.AtlasCoefficientFiber.FaceClone.evaluationIso_hom
#print axioms AAT.AG.AtlasCoefficientFiber.FaceClone.coefficientStandardIso
#print axioms AAT.AG.AtlasCoefficientFiber.FaceClone.coefficientStandardIso_hom
#print axioms AAT.AG.AtlasCoefficientFiber.FaceClone.unit_standard_square
#print axioms AAT.AG.AtlasCoefficientFiber.FaceClone.unit0_same
#print axioms AAT.AG.AtlasCoefficientFiber.FaceClone.unit1_same
#print axioms AAT.AG.AtlasCoefficientFiber.FaceClone.unit2_fold
#print axioms AAT.AG.AtlasCoefficientFiber.FaceClone.unit2_old
#print axioms AAT.AG.AtlasCoefficientFiber.FaceClone.unit2_fresh
#print axioms AAT.AG.AtlasCoefficientFiber.FaceClone.unitEquiv
#print axioms AAT.AG.AtlasCoefficientFiber.FaceClone.unitEquiv_apply
#print axioms AAT.AG.AtlasCoefficientFiber.FaceClone.unitEquiv_symm_apply
#print axioms AAT.AG.AtlasCoefficientFiber.FaceClone.unitEquiv_apply_symm
#print axioms AAT.AG.AtlasCoefficientFiber.FaceClone.phiH1_zero
#print axioms AAT.AG.AtlasCoefficientFiber.FaceClone.R_zero
#print axioms AAT.AG.AtlasCoefficientFiber.FaceClone.tau_zero
#print axioms AAT.AG.AtlasCoefficientFiber.FaceClone.fiberCone_zero
#print axioms AAT.AG.AtlasCoefficientFiber.FaceClone.coefficientConeIso
#print axioms AAT.AG.AtlasCoefficientFiber.FaceClone.coefficientConeIso_hom
#assert_standard_axioms_only AAT.AG.AtlasCoefficientFiber
