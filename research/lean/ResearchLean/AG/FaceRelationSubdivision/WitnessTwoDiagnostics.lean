import ResearchLean.AG.FaceRelationSubdivision.WitnessTwoALoop
import ResearchLean.AG.FaceRelationSubdivision.WitnessTwoBLoop
import ResearchLean.AG.FaceRelationSubdivision.WitnessTwoCInput
import ResearchLean.AG.AtlasDefectComposition.LawH1Family
import Formal.Util.AssertStandardAxioms

/-!
# W2a–c の同じ原始収縮と実診断

## Implementation notes

三つの指定原始入力を有限な場合名で参照し、すべての A に同じ一般 constructor を適用する。
支持点の有無を新しい前提にせず、空の A と空辺台も同じ式へ含める。
相同型や期待の欠損値を入力証明書として受け取る方式は採らない。
-/
noncomputable section
open CategoryTheory CategoryTheory.Limits CochainComplex
namespace AAT.AG.FaceRelationSubdivision.WitnessTwo
open CanonicalResolution ResolutionInvariance TwoPhase AtlasDefectComposition
open ConnectedFaceWitness (q laws adequate label)
/-- 固定 W2 の三つの原始入力の場合名。 -/
inductive Case | face | repeated | emptySupport
/-- 固定された同じ原始入力の参照。 -/
def old : Case → TargetSupportedNerve q
  | .face => WitnessTwoA.N
  | .repeated => WitnessTwoB.N
  | .emptySupport => WitnessTwoC.N
/-- 各指定入力で分割する同じ原始辺。 -/
def edge : (i : Case) → (old i).nerve.EdgeComponent
  | .face => (0 : Fin 4)
  | .repeated => false
  | .emptySupport => ()
/-- 各原始入力から同じ一般面付き細分で得る fine 入力。 -/
abbrev fine (i : Case) := EdgeSubdivision.supported (old i) (edge i)
/-- 同じ原始 mixed collapse。 -/
abbrev comparison (i : Case) := EdgeSubdivision.collapse (old i) (edge i)
/-- 任意 A の同じ原始 r,s,h の出力。 -/
abbrev contraction (i : Case) (A : Set Bool) := EdgeSubdivision.chainContraction (old i) (edge i) A
/-- 任意 A で原始選択 r,s の三次数往復は恒等。 -/
theorem rs_all (i : Case) (A : Set Bool) :
    ((EdgeSubdivision.r0 (old i) (edge i)).selected A).comp ((EdgeSubdivision.s0 (old i) (edge i)).selected A)=LinearMap.id ∧
    ((EdgeSubdivision.r1 (old i) (edge i)).selected A).comp ((EdgeSubdivision.s1 (old i) (edge i)).selected A)=LinearMap.id ∧
    ((EdgeSubdivision.r2 (old i) (edge i)).selected A).comp ((EdgeSubdivision.s2 (old i) (edge i)).selected A)=LinearMap.id :=
  ⟨EdgeSubdivision.selected_rs0 (old i) (edge i) A,EdgeSubdivision.selected_rs1 (old i) (edge i) A,EdgeSubdivision.selected_rs2 (old i) (edge i) A⟩
/-- 任意 A で同じ r,s,h が満たす全三次数の補正式。 -/
theorem sr_h_all (i : Case) (A : Set Bool) :
    ((EdgeSubdivision.s0 (old i) (edge i)).selected A).comp ((EdgeSubdivision.r0 (old i) (edge i)).selected A)+
      (chainD1 (fine i) A).comp ((EdgeSubdivision.h0 (old i) (edge i)).selected A)=LinearMap.id ∧
    ((EdgeSubdivision.s1 (old i) (edge i)).selected A).comp ((EdgeSubdivision.r1 (old i) (edge i)).selected A)+
      (chainD2 (fine i) A).comp ((EdgeSubdivision.h1 (old i) (edge i)).selected A)+
      ((EdgeSubdivision.h0 (old i) (edge i)).selected A).comp (chainD1 (fine i) A)=LinearMap.id ∧
    ((EdgeSubdivision.s2 (old i) (edge i)).selected A).comp ((EdgeSubdivision.r2 (old i) (edge i)).selected A)+
      ((EdgeSubdivision.h1 (old i) (edge i)).selected A).comp (chainD2 (fine i) A)=LinearMap.id :=
  ⟨EdgeSubdivision.selected_sr_h0 (old i) (edge i) A,EdgeSubdivision.selected_sr_h1 (old i) (edge i) A,EdgeSubdivision.selected_sr_h2 (old i) (edge i) A⟩
/-- 任意 A の出力 r は同じ原始比較から独立生成した全三成分 Hom。 -/
theorem subset_comparison (i : Case) (A : Set Bool) :
    (contraction i A).rHom=(comparison i).targetSubsetComparisonHom A A
      (IncidenceSupportedComparison.selfSubsetMapsTo (q := q) A) :=
  (EdgeSubdivision.chainContraction_rHom (old i) (edge i) A).trans (EdgeSubdivision.rHom_eq_generated (old i) (edge i) A)
/-- 任意 A の標準全整数次数同型は同じ生成比較の homology map。 -/
theorem subset_homology_map (i : Case) (A : Set Bool) (n : ℤ) :
    (EdgeSubdivision.homologyIso (old i) (edge i) A n).hom=
      HomologicalComplex.homologyMap (zeroExtensionMap
        ((comparison i).targetSubsetComparisonHom A A (IncidenceSupportedComparison.selfSubsetMapsTo (q := q) A))) n :=
  EdgeSubdivision.homologyIso_hom (old i) (edge i) A n
/-- 同じ実 Law r は原始 mixed 比較から独立生成した射。 -/
theorem law_comparison (i : Case) : EdgeSubdivision.lawR (old i) (edge i) laws adequate=
    (comparison i).generatedComparisonHom laws adequate adequate := EdgeSubdivision.lawR_eq_generated (old i) (edge i) laws adequate
/-- 同じ独立 block r は原始 mixed 比較から生成した Hom と全三成分一致する。 -/
theorem block_comparison (i : Case) (l : LawValueLabel laws) :
    EdgeSubdivision.blockR (old i) (edge i) laws adequate l=
      (comparison i).generatedBlockComparisonHom laws adequate adequate l :=
  EdgeSubdivision.blockR_eq_generated (old i) (edge i) laws adequate l
/-- 同じ原始 r と実 Law の元ラベル fiber 正方形。 -/
theorem law_fiber_square (i : Case) (l : LawValueLabel laws) :
    cochainComp (EdgeSubdivision.lawR (old i) (edge i) laws adequate) (lawFiberHom laws adequate (fine i) l)=
      cochainComp (lawFiberHom laws adequate (old i) l)
        (contraction i (labelValueFiber laws q adequate l)).rHom := EdgeSubdivision.lawR_fiber (old i) (edge i) laws adequate l
/-- 同じ独立生成 block r と実 singleton fiber の全三成分正方形。 -/
theorem block_fiber_square (i : Case) (l : LawValueLabel laws) :
    cochainComp (EdgeSubdivision.blockR (old i) (edge i) laws adequate l)
      ((fine i).lawValueBlockTargetSubsetComplexEquiv laws adequate l).toHom=
    cochainComp ((old i).lawValueBlockTargetSubsetComplexEquiv laws adequate l).toHom
      (contraction i (labelValueFiber laws q adequate l)).rHom := EdgeSubdivision.blockR_fiber (old i) (edge i) laws adequate l
/-- 同じ実 Law r,s を持つ標準全整数次数ホモトピー同値。 -/
def lawEquiv (i : Case) := EdgeSubdivision.lawHomotopyEquiv (old i) (edge i) laws adequate
/-- 同じ標準 Law 同値の順逆は独立実 r,s。 -/
theorem law_equiv_maps (i : Case) :
    (lawEquiv i).hom=zeroExtensionMap (EdgeSubdivision.lawR (old i) (edge i) laws adequate) ∧
    (lawEquiv i).inv=zeroExtensionMap (EdgeSubdivision.lawS (old i) (edge i) laws adequate) :=
  ⟨EdgeSubdivision.lawHomotopyEquiv_hom (old i) (edge i) laws adequate,EdgeSubdivision.lawHomotopyEquiv_inv (old i) (edge i) laws adequate⟩
/-- 元ラベルの独立実 r,s を持つ標準全整数次数同値。 -/
def blockEquiv (i : Case) (l : LawValueLabel laws) := EdgeSubdivision.blockHomotopyEquiv (old i) (edge i) laws adequate l
/-- 元ラベルを保つ標準 block 同値の順逆は同じ独立実 r,s。 -/
theorem block_equiv_maps (i : Case) (l : LawValueLabel laws) :
    (blockEquiv i l).hom=zeroExtensionMap (EdgeSubdivision.blockR (old i) (edge i) laws adequate l) ∧
    (blockEquiv i l).inv=zeroExtensionMap (EdgeSubdivision.blockS (old i) (edge i) laws adequate l) :=
  ⟨EdgeSubdivision.blockHomotopyEquiv_hom (old i) (edge i) laws adequate l,EdgeSubdivision.blockHomotopyEquiv_inv (old i) (edge i) laws adequate l⟩
/-- 同じ実 Law H¹ 写像は全単射。 -/
theorem law_h1_bijective (i : Case) : Function.Bijective (EdgeSubdivision.lawR (old i) (edge i) laws adequate).h1Map :=
  EdgeSubdivision.lawH1_bijective (old i) (edge i) laws adequate
/-- 同じ実 Law 比較の実核・実余核欠損はともに零。 -/
theorem law_defect_zero (i : Case) : blockDefect (EdgeSubdivision.lawR (old i) (edge i) laws adequate).h1Map=(0,0) :=
  EdgeSubdivision.lawH1_blockDefect_zero (old i) (edge i) laws adequate
set_option maxHeartbeats 800000 in
/-- 同じ実 Law 比較の標準錐は全整数次数で零。 -/
theorem law_cone_zero (i : Case) (n : ℤ) : IsZero
    ((mappingCone (zeroExtensionMap (EdgeSubdivision.lawR (old i) (edge i) laws adequate))).homology n) :=
  EdgeSubdivision.lawCone_isZero (old i) (edge i) laws adequate n
/-- 同じ元ラベルの独立実 block 比較の欠損は零。 -/
theorem block_defect_zero (i : Case) (l : LawValueLabel laws) :
    blockDefect (EdgeSubdivision.blockR (old i) (edge i) laws adequate l).h1Map=(0,0) :=
  EdgeSubdivision.blockH1_blockDefect_zero (old i) (edge i) laws adequate l
set_option maxHeartbeats 800000 in
/-- 同じ元ラベルの独立実 block 比較の標準錐は全整数次数で零。 -/
theorem block_cone_zero (i : Case) (l : LawValueLabel laws) (n : ℤ) : IsZero
    ((mappingCone (zeroExtensionMap (EdgeSubdivision.blockR (old i) (edge i) laws adequate l))).homology n) :=
  EdgeSubdivision.blockCone_isZero (old i) (edge i) laws adequate l n
/-- 空 A を含むすべての実 subset 比較の欠損は零。 -/
theorem subset_defect_zero (i : Case) (A : Set Bool) : blockDefect (contraction i A).rHom.h1Map=(0,0) :=
  EdgeSubdivision.subsetH1_blockDefect_zero (old i) (edge i) A
set_option maxHeartbeats 800000 in
/-- 空 A を含むすべての実 subset 比較の標準錐は全次数で零。 -/
theorem subset_cone_zero (i : Case) (A : Set Bool) (n : ℤ) : IsZero
    ((mappingCone (zeroExtensionMap (contraction i A).rHom)).homology n) :=
  EdgeSubdivision.subsetCone_isZero (old i) (edge i) A n
/-- W2c の同じ実全 Law H¹ も零。 -/
theorem empty_old_law_h1_zero : Subsingleton (WitnessTwoC.N.lawGeneratedComplex laws adequate).H1 := by
  letI (l : LawValueLabel laws) := WitnessTwoC.old_h1_zero l
  exact (lawH1FamilyEquiv WitnessTwoC.N laws adequate).toEquiv.subsingleton
/-- W2c fine の同じ実全 Law H¹ も零。 -/
theorem empty_fine_law_h1_zero : Subsingleton (WitnessTwoC.fine.lawGeneratedComplex laws adequate).H1 := by
  letI (l : LawValueLabel laws) := WitnessTwoC.fine_h1_zero l
  exact (lawH1FamilyEquiv WitnessTwoC.fine laws adequate).toEquiv.subsingleton
end AAT.AG.FaceRelationSubdivision.WitnessTwo
#assert_standard_axioms_only AAT.AG.FaceRelationSubdivision.WitnessTwo
