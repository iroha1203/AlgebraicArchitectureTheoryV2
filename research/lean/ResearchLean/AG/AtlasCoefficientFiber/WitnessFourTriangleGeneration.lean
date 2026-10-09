import ResearchLean.AG.AtlasCoefficientFiber.WitnessFourPhi
import ResearchLean.AG.FaceRelationSubdivision.WitnessOneSubset

/-!
# W4：原三角形Pの全生成と二射

Implementation notes: plusでは原成分からη両逆を生成する。minusのP1は原εの
旧e/k/fresh e₂値を取り、垂直c零と元SES像条件から全三座標の両逆を作る。
-/
noncomputable section
namespace AAT.AG.AtlasCoefficientFiber.WitnessFourTriangleGeneration
open CanonicalResolution ResolutionInvariance FaceRelationSubdivision TwoPhase AtlasDefectComposition
open FaceRelationSubdivision.WitnessOne (N plus minus qc qf coarser rPlus rMinus)

/-- 原plusの全Φ/Γと空の粗面から、全三次数η同型を構成する。 -/
def plusEtaEquiv (A : Set Bool) : ThreeCochainComplex.CochainEquiv
    (N.targetSubsetComplex A) (pushforwardComplex rPlus A) :=
  localUnitEquiv rPlus A (WitnessFourPhi.plus_components A)
    (WitnessFourCoefficients.plus_gamma_components A) (fun F => isEmptyElim F.1)
/-- 全三次数の同型順射は原η。 -/
theorem plusEtaEquiv_toHom (A : Set Bool) : (plusEtaEquiv A).toHom = unitHom rPlus A := rfl
/-- 原Kan Pから粗原表への全三次数同定。 -/
def plusPCoarseEquiv (A : Set Bool) := (plusEtaEquiv A).symm

/-- 元minusのΦ成分から原η0の両逆を生成する。 -/
def minusEta0Equiv (A : Set Bool) : (N.targetSubsetComplex A).C0 ≃ₗ[ℚ] (pushforwardComplex rMinus A).C0 :=
  LinearEquiv.piCongrRight fun c => LinearEquiv.ofBijective _
    (chartCoefficientConstant_bijective rMinus A c
      (WitnessFourPhi.minus_components A c).1 (WitnessFourPhi.minus_components A c).2)
/-- 元minusの次数0同型の順写像は同じη0。 -/
theorem minusEta0Equiv_apply (A : Set Bool) (z) : minusEta0Equiv A z = unit0 rMinus A z := rfl

/-- 元minusの全fine辺を同じ名前で選択する。 -/
def minusFineEdge (A : Set Bool) (hA : A.Nonempty) (e : minus.nerve.EdgeComponent) :
    minus.EdgeInTargetSubset (comparisonFactor qc qf coarser ⁻¹' A) :=
  fullSelected minus.edgeSupport FaceRelationSubdivision.WitnessOne.minus_edge_full _
    (WitnessFullSupport.fine_nonempty A hA) e
/-- 原水平三辺の名前。旧e、旧k、fresh e₂を保持する。 -/
def horizontalName (i : Fin 3) : minus.nerve.EdgeComponent :=
  ![Sum.inl (0 : Fin 2), Sum.inl (1 : Fin 2), Sum.inr true] i
/-- 元P1の原εから取る三辺座標。 -/
def minusP1Period (A : Set Bool) (hA : A.Nonempty) :
    (pushforwardComplex rMinus A).C1 →ₗ[ℚ] (Fin 3 → ℚ) :=
  LinearMap.pi fun i => (LinearMap.proj (minusFineEdge A hA (horizontalName i))).comp (evaluation1 rMinus A)
/-- 同じ原cの評価値は原none条件から零となる。 -/
theorem minus_evaluation_c (A : Set Bool) (hA : A.Nonempty) (z) :
    evaluation1 rMinus A z (minusFineEdge A hA (.inr false)) = 0 :=
  evaluation1_of_none rMinus A z _ rfl
/-- 全三辺座標は、原ε単射と同じc零から単射。 -/
theorem minusP1Period_injective (A : Set Bool) (hA : A.Nonempty) :
    Function.Injective (minusP1Period A hA) := by
  intro z w hh
  apply evaluation1_injective rMinus A
  funext a
  have he : minusFineEdge A hA a.1 = a := Subtype.ext rfl
  rw [← he]
  rcases a with ⟨a,hs⟩
  rcases a with a | b
  · fin_cases a
    · exact congrFun hh 0
    · exact congrFun hh 1
  · cases b
    · rw [minus_evaluation_c, minus_evaluation_c]
    · exact congrFun hh 2
/-- 任意原三辺値はc零の同じcochainから元Kanへ持ち上がる。 -/
theorem minusP1Period_surjective (A : Set Bool) (hA : A.Nonempty) :
    Function.Surjective (minusP1Period A hA) := by
  intro z
  let w : (minus.targetSubsetComplex (comparisonFactor qc qf coarser ⁻¹' A)).C1 :=
    fun a => match a.1 with
    | .inl i => ![z 0,z 1] i
    | .inr false => 0
    | .inr true => z 2
  have hw : restriction1 rMinus A w = 0 := by
    apply (restriction1_zero_iff rMinus A w).mpr
    constructor
    · intro a
      have hm := a.2
      rw [FaceRelationSubdivision.WitnessOne.rMinus_edge] at hm
      rcases h : a.1.1 with i | b
      · rw [h, FaceRelationSubdivision.WitnessOne.rPlus_edge_old] at hm
        cases hm
      · cases b
        · change w a.1 = 0
          dsimp only [w]; rw [h]
        · rw [h, FaceRelationSubdivision.WitnessOne.rPlus_edge_e2] at hm
          cases hm
    · intro f; exact isEmptyElim f.1.1
  obtain ⟨p,hp⟩ := evaluation1_preimage_of_restriction_zero rMinus A w hw
  refine ⟨p,?_⟩
  funext i
  change evaluation1 rMinus A p (minusFineEdge A hA (horizontalName i)) = z i
  rw [hp]
  fin_cases i <;> rfl
/-- 元minus P1と全原水平三辺値の両逆。 -/
def minusP1Equiv (A : Set Bool) (hA : A.Nonempty) :
    (pushforwardComplex rMinus A).C1 ≃ₗ[ℚ] (Fin 3 → ℚ) :=
  LinearEquiv.ofBijective _ ⟨minusP1Period_injective A hA, minusP1Period_surjective A hA⟩
/-- 元minus P2は同じ原空fine面の評価同型から零。 -/
theorem minusP2_zero (A : Set Bool) : Subsingleton (pushforwardComplex rMinus A).C2 := by
  letI : Subsingleton (minus.targetSubsetComplex (comparisonFactor qc qf coarser ⁻¹' A)).C2 := by
    change Subsingleton (minus.FaceInTargetSubset _ → ℚ); infer_instance
  exact (MappedCells.evaluation2Equiv rMinus A (by intro f; exact isEmptyElim f)).toEquiv.subsingleton

/-- 原η1はeの二liftで同じ値、kの値は同じ原名に置く。 -/
theorem minus_eta1_values (A : Set Bool) (hA : A.Nonempty) (z : (N.targetSubsetComplex A).C1) :
    minusP1Equiv A hA (unit1 rMinus A z) =
      ![(FaceRelationSubdivision.WitnessOne.oldSubsetEquiv A hA).e1 z 0,
        (FaceRelationSubdivision.WitnessOne.oldSubsetEquiv A hA).e1 z 1,
        (FaceRelationSubdivision.WitnessOne.oldSubsetEquiv A hA).e1 z 0] := by
  have hs := congrArg (fun f => f.f1 z) (FaceRelationSubdivision.WitnessOne.minus_subset_square A hA)
  change (FaceRelationSubdivision.WitnessOne.minusSubsetEquiv A hA).e1
    ((rMinus.aSubnerveComparisonHom A).f1 z) =
    FaceRelationSubdivision.WitnessOne.minusNamedHom.f1
      ((FaceRelationSubdivision.WitnessOne.oldSubsetEquiv A hA).e1 z) at hs
  rw [aSubnerveComparisonHom_factorization] at hs
  funext i
  change evaluation1 rMinus A (unit1 rMinus A z) (minusFineEdge A hA (horizontalName i)) = _
  have hh := congrFun hs (horizontalName i)
  fin_cases i <;> exact hh

/-- 原minus P0の全座標は元粗chart値であり、逆も元η0である。 -/
def minusP0Equiv (A : Set Bool) (hA : A.Nonempty) :
    (pushforwardComplex rMinus A).C0 ≃ₗ[ℚ] (Fin 2 → ℚ) :=
  (minusEta0Equiv A).symm.trans (FaceRelationSubdivision.WitnessOne.oldSubsetEquiv A hA).e0
/-- 原Pの微分は全三水平辺で(y−x,0,y−x)となる。 -/
theorem minus_d0_values (A : Set Bool) (hA : A.Nonempty) (z : (pushforwardComplex rMinus A).C0) :
    minusP1Equiv A hA ((pushforwardComplex rMinus A).d0 z) =
      ![minusP0Equiv A hA z 1 - minusP0Equiv A hA z 0,0,
        minusP0Equiv A hA z 1 - minusP0Equiv A hA z 0] := by
  have hz : z = unit0 rMinus A ((minusEta0Equiv A).symm z) :=
    ((minusEta0Equiv A).apply_symm_apply z).symm
  conv_lhs => rw [hz, ← unit_comm0, minus_eta1_values]
  have hh := (FaceRelationSubdivision.WitnessOne.oldSubsetEquiv A hA).comm0 ((minusEta0Equiv A).symm z)
  rw [hh]
  funext i
  fin_cases i <;> simp only [FaceRelationSubdivision.WitnessOne.d0_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, sub_self]
  all_goals rfl
/-- 原plusの全η逆座標でεは同じ独立原比較となる。 -/
theorem plus_epsilon_square (A : Set Bool) :
    cochainComp (plusPCoarseEquiv A).toHom (rPlus.aSubnerveComparisonHom A) = evaluationHom rPlus A := by
  apply cochain_ext <;> apply LinearMap.ext <;> intro z
  · have hh := congrArg (fun f => f.f0 ((plusEtaEquiv A).e0.symm z)) (aSubnerveComparisonHom_factorization rPlus A)
    change (rPlus.aSubnerveComparisonHom A).f0 ((plusEtaEquiv A).e0.symm z) =
      (evaluationHom rPlus A).f0 ((plusEtaEquiv A).e0 ((plusEtaEquiv A).e0.symm z)) at hh
    rw [LinearEquiv.apply_symm_apply] at hh
    exact hh
  · have hh := congrArg (fun f => f.f1 ((plusEtaEquiv A).e1.symm z)) (aSubnerveComparisonHom_factorization rPlus A)
    change (rPlus.aSubnerveComparisonHom A).f1 ((plusEtaEquiv A).e1.symm z) =
      (evaluationHom rPlus A).f1 ((plusEtaEquiv A).e1 ((plusEtaEquiv A).e1.symm z)) at hh
    rw [LinearEquiv.apply_symm_apply] at hh
    exact hh
  · have hh := congrArg (fun f => f.f2 ((plusEtaEquiv A).e2.symm z)) (aSubnerveComparisonHom_factorization rPlus A)
    change (rPlus.aSubnerveComparisonHom A).f2 ((plusEtaEquiv A).e2.symm z) =
      (evaluationHom rPlus A).f2 ((plusEtaEquiv A).e2 ((plusEtaEquiv A).e2.symm z)) at hh
    rw [LinearEquiv.apply_symm_apply] at hh
    exact hh

end AAT.AG.AtlasCoefficientFiber.WitnessFourTriangleGeneration

#print axioms AAT.AG.AtlasCoefficientFiber.WitnessFourTriangleGeneration.plusEtaEquiv
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessFourTriangleGeneration.plusEtaEquiv_toHom
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessFourTriangleGeneration.plusPCoarseEquiv
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessFourTriangleGeneration.minusEta0Equiv
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessFourTriangleGeneration.minusEta0Equiv_apply
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessFourTriangleGeneration.minusFineEdge
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessFourTriangleGeneration.horizontalName
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessFourTriangleGeneration.minusP1Period
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessFourTriangleGeneration.minus_evaluation_c
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessFourTriangleGeneration.minusP1Period_injective
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessFourTriangleGeneration.minusP1Period_surjective
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessFourTriangleGeneration.minusP1Equiv
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessFourTriangleGeneration.minusP2_zero
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessFourTriangleGeneration.minus_eta1_values
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessFourTriangleGeneration.minusP0Equiv
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessFourTriangleGeneration.minus_d0_values
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessFourTriangleGeneration.plus_epsilon_square
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessFourTriangleGeneration.minusP0Equiv.congr_simp
#assert_standard_axioms_only AAT.AG.AtlasCoefficientFiber.WitnessFourTriangleGeneration
