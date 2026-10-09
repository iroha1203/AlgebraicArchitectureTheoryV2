import ResearchLean.AG.AtlasCoefficientFiber.WitnessThreeFiber
import ResearchLean.AG.AtlasCoefficientFiber.WitnessThreeDiagnostics
import ResearchLean.AG.AtlasCoefficientFiber.TransgressionRepresentatives

/-!
# G-135 W3：元標準τと補正代表

## Implementation notes

垂直・水平cochainは同じ原細辺値から生成する。標準δの代表射公式を使用する。
期待するτ行列を写像の定義へ渡す方法は採らない。
-/
noncomputable section
namespace AAT.AG.AtlasCoefficientFiber.WitnessThree
open CategoryTheory CanonicalResolution ResolutionInvariance TwoPhase FaceRelationSubdivision
open WitnessCommon WitnessFullSupport AtlasDefectComposition

/-- 全Aの垂直面は原mixed表から空。 -/
theorem vertical_faces_empty (A : Set Bool) : IsEmpty (VerticalFace M A) where
  false f := by
    rcases f with ⟨⟨f,hf⟩,hn,h0,h1,h2⟩
    fin_cases f <;> simp [M,Nf,fineNerve] at hn h1
/-- 同じ原fine代表、kとa1で1、他辺で0。 -/
def correctedW (A : Set Bool) : (Nf.targetSubsetComplex (comparisonFactor qc qf coarser ⁻¹' A)).C1 :=
  fun e => (![0,1,0,0,0,1] : Fin 6 → ℚ) e.1
/-- 原代表の垂直制限、k値1を持つ閉cochain。 -/
def verticalZ (A : Set Bool) : VerticalCocycles M A := by
  refine ⟨(freeDualEquiv _ (correctedW A)).comp (verticalEdgeInclusion M A),?_⟩
  letI := vertical_faces_empty A
  apply LinearMap.ext
  intro x
  have hx : x = 0 := Subsingleton.elim _ _
  rw [hx,map_zero]
  rfl
/-- 原代表の水平制限。a1値1・a0値0の指定補正。 -/
def horizontalBeta (A : Set Bool) : Module.Dual ℚ (HorizontalEdge M A →₀ ℚ) :=
  (freeDualEquiv _ (correctedW A)).comp (horizontalEdgeInclusion M A)
/-- 原二block再結合から、補正cochainは同じ原代表そのもの。 -/
theorem correctedEdge_eq_W (A : Set Bool) : correctedEdgeCochain M A (verticalZ A).1 (horizontalBeta A) = correctedW A := by
  apply (freeDualEquiv _).injective
  rw [correctedEdgeCochain_dual]
  apply LinearMap.ext
  intro x
  change freeDualEquiv _ (correctedW A) (verticalEdgeInclusion M A (verticalEdgeProjection M A x)) +
    freeDualEquiv _ (correctedW A) (horizontalEdgeInclusion M A (horizontalEdgeProjection M A x)) = _
  rw [← map_add,edgeBlock_recombination]
/-- 原補正代表のm微分は1−1+0=0。 -/
theorem correctedW_mixed_zero (A : Set Bool) (f : MixedFace M A) :
    (Nf.targetSubsetComplex (comparisonFactor qc qf coarser ⁻¹' A)).d1 (correctedW A) f.1 = 0 := by
  rw [TargetSupportedNerve.targetSubsetComplex_d1_apply]
  change ![0,1,0,0,0,1] (Nf.nerve.faceEdge0 f.1.1) -
    ![0,1,0,0,0,1] (Nf.nerve.faceEdge1 f.1.1) + ![0,1,0,0,0,1] (Nf.nerve.faceEdge2 f.1.1) = (0 : ℚ)
  rw [mixed_name A f]
  change (1:ℚ)-1+0=0
  ring
/-- 元BとD上の指定補正等式βB=−zD。 -/
theorem horizontalBeta_corrects (A : Set Bool) :
    (mixedHorizontalBoundary M A).dualMap (horizontalBeta A) = -(mixedVerticalBoundary M A).dualMap (verticalZ A).1 := by
  apply Finsupp.lhom_ext
  intro f r
  have hh := correctedEdgeCochain_d1_mixed M A (verticalZ A).1 (horizontalBeta A) (Finsupp.single f r)
  rw [correctedEdge_eq_W,mixedFaceInclusion_single,freeDualEquiv_single,correctedW_mixed_zero,mul_zero] at hh
  change horizontalBeta A (mixedHorizontalBoundary M A (Finsupp.single f r)) =
    -(verticalZ A).1 (mixedVerticalBoundary M A (Finsupp.single f r))
  linarith
/-- 同じk原代表と指定a1補正からliteral R類を生成。 -/
def rK (A : Set Bool) : R M A := correctedFiberClass M A (verticalZ A) (horizontalBeta A) (horizontalBeta_corrects A)
/-- 同じ補正の微分原像は原P内の(0,1) unit値。 -/
def tauPRepresentative (A : Set Bool) : (pushforwardComplex M A).C2 :=
  (unitHom M A).f2 (fun F => (![0,1] : Fin 2 → ℚ) F.1)
/-- 元εへ戻すと同じ補正微分f0=0,f1=1,m=0。 -/
theorem tauPRepresentative_evaluation (A : Set Bool) : evaluation2 M A (tauPRepresentative A) =
    (Nf.targetSubsetComplex (comparisonFactor qc qf coarser ⁻¹' A)).d1 (correctedW A) := by
  have hh := congrArg (fun f => f.f2 (fun F => (![0,1] : Fin 2 → ℚ) F.1))
    (aSubnerveComparisonHom_factorization M A)
  change (M.aSubnerveComparisonHom A).f2 (fun F => (![0,1] : Fin 2 → ℚ) F.1) = evaluation2 M A (tauPRepresentative A) at hh
  rw [← hh]
  funext f
  rw [TargetSupportedNerve.targetSubsetComplex_d1_apply]
  rcases f with ⟨f,hf⟩
  change M.targetSubsetPullback2 A _ (fun _ ht => ht) (fun F => (![0,1] : Fin 2 → ℚ) F.1) ⟨f,hf⟩ = _
  rw [M.targetSubsetPullback2_apply]
  fin_cases f
  · rw [M.targetSubsetFaceMapOption_eq_some A _ _ _ 0 rfl]
    change (0:ℚ)=0-0+0
    ring
  · rw [M.targetSubsetFaceMapOption_eq_some A _ _ _ 1 rfl]
    change (1:ℚ)=1-0+0
    ring
  · rw [M.targetSubsetFaceMapOption_eq_none A _ _ _ rfl]
    change (0:ℚ)=1-1+0
    ring
/-- 指定R類に対する元標準δの同じ(0,1)商類。 -/
theorem tau_rK (A : Set Bool) : connectingTau M A (rK A) =
    oldH2Equiv (pushforwardComplex M A) ((LinearMap.range (pushforwardComplex M A).d1).mkQ (tauPRepresentative A)) := by
  rw [rK,← correctedRestrictionCycle_fiberClass M A (verticalZ A) (horizontalBeta A) (horizontalBeta_corrects A),
    connectingTau_restrictionStandardHomologyREquiv]
  apply evaluationRestriction_connecting_representative M A _ (correctedW A) _
  · rw [correctedRestrictionCycle_val,correctedEdge_eq_W]
  · exact tauPRepresentative_evaluation A
/-- 元τ代表の原P座標はF1−F0=1。 -/
theorem tau_rK_period (A : Set Bool) (hA : A.Nonempty) : pH2Coordinates A hA (connectingTau M A (rK A)) = 1 := by
  rw [tau_rK,pH2Coordinates_mk]
  have hs := congrArg (fun f => f.f2 (fun F => (![0,1] : Fin 2 → ℚ) F.1)) (eta_square A hA)
  change (pNamedEquiv A hA).e2 (tauPRepresentative A) = ![0,1] at hs
  rw [hs]
  change (1:ℚ)-0=1
  exact sub_zero _
/-- 同原τは非零。 -/
theorem tau_nonzero (A : Set Bool) (hA : A.Nonempty) : connectingTau M A ≠ 0 := by
  intro hh
  have he := tau_rK_period A hA
  rw [hh,LinearMap.zero_apply,map_zero] at he
  exact zero_ne_one he
/-- 同k literal R類は非零。 -/
theorem rK_nonzero (A : Set Bool) (hA : A.Nonempty) : rK A ≠ 0 := by
  intro hh
  have he := tau_rK_period A hA
  rw [hh,map_zero,map_zero] at he
  exact zero_ne_one he
/-- 原比較の全同型性から同じτは単射。 -/
theorem tau_injective (A : Set Bool) (hA : A.Nonempty) : Function.Injective (connectingTau M A) :=
  ((coefficient_zeroDefect_iff M A).mp (defect A hA)).2
/-- 細側原H²零から同じτは全射。 -/
theorem tau_surjective (A : Set Bool) (hA : A.Nonempty) : Function.Surjective (connectingTau M A) := by
  letI := fineH2_subsingleton A hA
  intro z
  exact (fiveTerm_exact_at_pushforwardH2 M A z).mp (Subsingleton.elim _ _)
/-- 同じ元標準τの両方向同型。 -/
def tauEquiv (A : Set Bool) (hA : A.Nonempty) : R M A ≃ₗ[ℚ] (zeroExtension (pushforwardComplex M A)).homology (2 : ℤ) :=
  LinearEquiv.ofBijective (connectingTau M A) ⟨tau_injective A hA,tau_surjective A hA⟩
/-- 原τ全像のrankは1。 -/
theorem tau_rank (A : Set Bool) (hA : A.Nonempty) : Module.finrank ℚ (LinearMap.range (connectingTau M A)) = 1 := by
  rw [LinearMap.range_eq_top.mpr (tau_surjective A hA)]
  exact (Submodule.topEquiv).finrank_eq.trans (pH2_dimension A hA)


/-- 元垂直cochainは同じk上で1。 -/
theorem verticalZ_single (A : Set Bool) (e : VerticalEdge M A) : (verticalZ A).1 (Finsupp.single e 1) = 1 := by
  change freeDualEquiv _ (correctedW A) (verticalEdgeInclusion M A (Finsupp.single e 1)) = 1
  rw [verticalEdgeInclusion_single,freeDualEquiv_single,one_mul]
  have he := (edgeMap_none_iff e.1.1).mp e.2
  change (![0,1,0,0,0,1] : Fin 6 → ℚ) e.1.1 = 1
  rw [he]; rfl
/-- 元水平補正は同じ細辺名の指定値、a1だけ1。 -/
theorem horizontalBeta_single (A : Set Bool) (e : HorizontalEdge M A) :
    horizontalBeta A (Finsupp.single e 1) = (![0,1,0,0,0,1] : Fin 6 → ℚ) e.1.1 := by
  change freeDualEquiv _ (correctedW A) (horizontalEdgeInclusion M A (Finsupp.single e 1)) = _
  rw [horizontalEdgeInclusion_single,freeDualEquiv_single,one_mul]
  rfl
/-- 元補正微分全三面の符号値(0,1,0)、mを保持。 -/
theorem correctedW_face_values (A : Set Bool) (hA : A.Nonempty) :
    (fullSubsetNamedEquiv Nf (fun _ => rfl) _ (fine_nonempty A hA)).e2
      ((Nf.targetSubsetComplex (comparisonFactor qc qf coarser ⁻¹' A)).d1 (correctedW A)) = ![0,1,0] := by
  funext f
  change (Nf.targetSubsetComplex (comparisonFactor qc qf coarser ⁻¹' A)).d1 (correctedW A)
    (fullSelected Nf.faceSupport (fullSupport_face Nf (fun _ => rfl)) _ (fine_nonempty A hA) f) = ![0,1,0] f
  rw [TargetSupportedNerve.targetSubsetComplex_d1_apply]
  change ![0,1,0,0,0,1] (![0,1,5] f) - ![0,1,0,0,0,1] (![2,2,1] f) +
    ![0,1,0,0,0,1] (![3,3,0] f) = (![0,1,0] : Fin 3 → ℚ) f
  fin_cases f <;> dsimp <;> ring


/-- 原k単位chainを元全台から生成。 -/
def kAt (A : Set Bool) (hA : A.Nonempty) : VerticalEdge M A :=
  ⟨fullSelected Nf.edgeSupport (fullSupport_edge Nf (fun _ => rfl)) _ (fine_nonempty A hA) 5,rfl⟩
/-- kは元垂直chain閉路、同じloop両端点差。 -/
def verticalKCycle (A : Set Bool) (hA : A.Nonempty) : verticalCycles M A :=
  ⟨Finsupp.single (kAt A hA) 1,by
    rw [LinearMap.mem_ker,verticalEdgeBoundary_single]
    have he : Nf.targetSubsetEdgeRight _ (kAt A hA).1 = Nf.targetSubsetEdgeLeft _ (kAt A hA).1 := Subtype.ext rfl
    rw [he,sub_self,smul_zero]⟩
/-- 元Rの独立k periodは同じ原垂直homology類の双対評価。 -/
def rawRPeriod (A : Set Bool) (hA : A.Nonempty) : R M A →ₗ[ℚ] ℚ :=
  (LinearMap.applyₗ (Submodule.Quotient.mk (verticalKCycle A hA))).comp
    ((LinearMap.ker (rawKappa M A).dualMap).subtype.comp (fiberRRawEquiv M A).toLinearMap)
/-- 同じk代表R類の独立periodは1。 -/
theorem rawRPeriod_rK (A : Set Bool) (hA : A.Nonempty) : rawRPeriod A hA (rK A) = 1 := by
  change (fiberRRawEquiv M A (rK A)).1 (Submodule.Quotient.mk (verticalKCycle A hA)) = 1
  rw [rK,correctedFiberClass_raw,verticalCocycleClass_mk]
  exact verticalZ_single A (kAt A hA)
/-- literal Rの全類は元k代表のスカラー倍。 -/
theorem rK_spans (A : Set Bool) (hA : A.Nonempty) (r : R M A) : ∃ q : ℚ, q • rK A = r :=
  (finrank_eq_one_iff_of_nonzero' (rK A) (rK_nonzero A hA)).mp (r_dimension A hA) r
/-- 全元の原標準τは同じ独立k periodをF1−F0へ送る。 -/
theorem tau_period (A : Set Bool) (hA : A.Nonempty) (r : R M A) :
    pH2Coordinates A hA (connectingTau M A r) = rawRPeriod A hA r := by
  obtain ⟨q,rfl⟩ := rK_spans A hA r
  rw [map_smul,map_smul,tau_rK_period,map_smul,rawRPeriod_rK]
/-- 同独立原R periodの全両逆。 -/
def rawRCoordinates (A : Set Bool) (hA : A.Nonempty) : R M A ≃ₗ[ℚ] ℚ :=
  LinearEquiv.ofBijective (rawRPeriod A hA) (by
    constructor
    · intro x y hh
      apply (tau_injective A hA)
      apply (pH2Coordinates A hA).injective
      rw [tau_period,tau_period,hh]
    · intro q
      refine ⟨q • rK A,?_⟩
      rw [map_smul,rawRPeriod_rK]
      exact mul_one q)

end AAT.AG.AtlasCoefficientFiber.WitnessThree
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessThree.vertical_faces_empty
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessThree.correctedW
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessThree.verticalZ
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessThree.horizontalBeta
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessThree.correctedEdge_eq_W
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessThree.correctedW_mixed_zero
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessThree.horizontalBeta_corrects
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessThree.rK
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessThree.tauPRepresentative
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessThree.tauPRepresentative_evaluation
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessThree.tau_rK
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessThree.tau_rK_period
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessThree.tau_nonzero
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessThree.rK_nonzero
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessThree.tau_injective
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessThree.tau_surjective
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessThree.tauEquiv
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessThree.tau_rank
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessThree.verticalZ_single
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessThree.horizontalBeta_single
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessThree.correctedW_face_values
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessThree.kAt
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessThree.verticalKCycle
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessThree.rawRPeriod
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessThree.rawRPeriod_rK
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessThree.rK_spans
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessThree.tau_period
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessThree.rawRCoordinates
#assert_standard_axioms_only AAT.AG.AtlasCoefficientFiber.WitnessThree
