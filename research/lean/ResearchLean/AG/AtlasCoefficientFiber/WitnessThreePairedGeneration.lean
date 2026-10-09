import ResearchLean.AG.AtlasCoefficientFiber.WitnessThreeCoefficients
import ResearchLean.AG.AtlasCoefficientFiber.WitnessThreeComparison
import ResearchLean.AG.AtlasCoefficientFiber.EvaluationAnnihilator
import ResearchLean.AG.AtlasCoefficientFiber.MappedEvaluation

/-!
# G-135 W3 paired：原Kanの独立五辺座標

## Implementation notes

原counitの全射・単射から同じ水平辺五名の両逆を生成する。
Pを任意中間複体として定義する方法は採らない。
-/
noncomputable section
namespace AAT.AG.AtlasCoefficientFiber.WitnessThree
open CategoryTheory CanonicalResolution ResolutionInvariance TwoPhase FaceRelationSubdivision
open WitnessCommon WitnessFullSupport AtlasDefectComposition

/-- mなし元Kanを表示する原水平辺名の複体。kは元none条件で除く。 -/
def pairedPNamedComplex : ThreeCochainComplex ℚ where
  C0 := Fin 3 → ℚ
  C1 := Fin 5 → ℚ
  C2 := Fin 2 → ℚ
  d0 := {
    toFun z := ![z 1-z 0,z 1-z 0,z 2-z 0,z 2-z 1,0]
    map_add' z w := by funext e; fin_cases e <;> dsimp <;> ring
    map_smul' r z := by funext e; fin_cases e <;> dsimp <;> ring }
  d1 := {
    toFun z := ![z 0-z 2+z 3,z 1-z 2+z 3]
    map_add' z w := by funext f; fin_cases f <;> dsimp <;> ring
    map_smul' r z := by funext f; fin_cases f <;> dsimp <;> ring }
  d1_comp_d0 z := by funext f; fin_cases f <;> dsimp <;> ring
/-- 元mapped五辺を原fineの先頭五名へ戻す。 -/
def pairedFineEdge (A : Set Bool) (hA : A.Nonempty) (e : Fin 6) :
    pairedNf.EdgeInTargetSubset (comparisonFactor qc qf coarser ⁻¹' A) :=
  fullSelected pairedNf.edgeSupport (fullSupport_edge pairedNf (fun _ => rfl)) _ (fine_nonempty A hA) e
/-- 元counitの先頭五辺値を取る線形写像。 -/
def pairedP1Period (A : Set Bool) (hA : A.Nonempty) : (pushforwardComplex pairedM A).C1 →ₗ[ℚ] (Fin 5 → ℚ) :=
  LinearMap.pi fun e => (LinearMap.proj (pairedFineEdge A hA e.castSucc)).comp (evaluation1 pairedM A)
/-- 原counitのk値は元none条件から零。 -/
theorem paired_evaluation_k (A : Set Bool) (hA : A.Nonempty) (z : (pushforwardComplex pairedM A).C1) :
    evaluation1 pairedM A z (pairedFineEdge A hA 5) = 0 := evaluation1_of_none pairedM A z _ rfl
/-- 全五辺periodの単射性、k零と原counitの単射性から生成。 -/
theorem pairedP1Period_injective (A : Set Bool) (hA : A.Nonempty) : Function.Injective (pairedP1Period A hA) := by
  intro z w hh
  apply evaluation1_injective pairedM A
  funext e
  have he : pairedFineEdge A hA e.1 = e := Subtype.ext rfl
  rw [← he]
  rcases e with ⟨e,hs⟩
  fin_cases e
  · exact congrFun hh 0
  · exact congrFun hh 1
  · exact congrFun hh 2
  · exact congrFun hh 3
  · exact congrFun hh 4
  · change evaluation1 pairedM A z (pairedFineEdge A hA 5) = evaluation1 pairedM A w (pairedFineEdge A hA 5)
    rw [paired_evaluation_k,paired_evaluation_k]
/-- 任意五辺値はk零の原cochainから原Kanへ持ち上がる。 -/
theorem pairedP1Period_surjective (A : Set Bool) (hA : A.Nonempty) : Function.Surjective (pairedP1Period A hA) := by
  intro z
  let w : (pairedNf.targetSubsetComplex (comparisonFactor qc qf coarser ⁻¹' A)).C1 :=
    fun e => (![z 0,z 1,z 2,z 3,z 4,0] : Fin 6 → ℚ) e.1
  have hw : restriction1 pairedM A w = 0 := by
    apply (restriction1_zero_iff pairedM A w).mpr
    constructor
    · intro e
      have he : e.1.1 = 5 := (edgeMap_none_iff e.1.1).mp e.2
      change (![z 0,z 1,z 2,z 3,z 4,0] : Fin 6 → ℚ) e.1.1 = 0
      rw [he]; rfl
    · intro f; cases f.2.1
  obtain ⟨p,hp⟩ := evaluation1_preimage_of_restriction_zero pairedM A w hw
  refine ⟨p,?_⟩
  funext e
  change evaluation1 pairedM A p (pairedFineEdge A hA e.castSucc) = z e
  rw [hp]
  fin_cases e <;> rfl
/-- 元P1全空間と原五辺値の両逆。 -/
def pairedP1Equiv (A : Set Bool) (hA : A.Nonempty) : (pushforwardComplex pairedM A).C1 ≃ₗ[ℚ] (Fin 5 → ℚ) :=
  LinearEquiv.ofBijective (pairedP1Period A hA) ⟨pairedP1Period_injective A hA,pairedP1Period_surjective A hA⟩
/-- 原k両端点同一からε0は全chart値を実現する。 -/
theorem paired_evaluation0_surjective (A : Set Bool) : Function.Surjective (evaluation0 pairedM A) := by
  intro z
  apply evaluation0_preimage_of_restriction_zero pairedM A z
  apply (restriction0_zero_iff pairedM A z).mpr
  intro e
  congr 1
  apply Subtype.ext
  have he : e.1.1 = 5 := (edgeMap_none_iff e.1.1).mp e.2
  change pairedNf.nerve.edgeRight e.1.1 = pairedNf.nerve.edgeLeft e.1.1
  rw [he]; rfl
/-- 元P0の全chart値両逆。 -/
def pairedP0Equiv (A : Set Bool) (hA : A.Nonempty) : (pushforwardComplex pairedM A).C0 ≃ₗ[ℚ] (Fin 3 → ℚ) :=
  (LinearEquiv.ofBijective (evaluation0 pairedM A) ⟨evaluation0_injective pairedM A,paired_evaluation0_surjective A⟩).trans
    (fullSubsetNamedEquiv pairedNf (fun _ => rfl) _ (fine_nonempty A hA)).e0
/-- 元P2の全二面値両逆。 -/
def pairedP2Equiv (A : Set Bool) (hA : A.Nonempty) : (pushforwardComplex pairedM A).C2 ≃ₗ[ℚ] (Fin 2 → ℚ) :=
  (MappedCells.evaluation2Equiv pairedM A (by intro f hf; cases hf)).trans
    (fullSubsetNamedEquiv pairedNf (fun _ => rfl) _ (fine_nonempty A hA)).e2
/-- 原Kanの五辺座標と同じ二微分が可換。 -/
def pairedPNamedEquiv (A : Set Bool) (hA : A.Nonempty) :
    ThreeCochainComplex.CochainEquiv (pushforwardComplex pairedM A) pairedPNamedComplex where
  e0 := pairedP0Equiv A hA
  e1 := pairedP1Equiv A hA
  e2 := pairedP2Equiv A hA
  comm0 z := by
    funext e
    have hh := congrFun (evaluation_comm0 pairedM A z) (pairedFineEdge A hA e.castSucc)
    change evaluation1 pairedM A ((pushforwardComplex pairedM A).d0 z) (pairedFineEdge A hA e.castSucc) = _
    rw [hh,TargetSupportedNerve.targetSubsetComplex_d0_apply]
    fin_cases e <;> try rfl
    exact sub_self _
  comm1 z := by
    funext f
    let F := fullSelected pairedNf.faceSupport (fullSupport_face pairedNf (fun _ => rfl)) _ (fine_nonempty A hA) f
    have hh := congrFun (evaluation_comm1 pairedM A z) F
    change evaluation2 pairedM A ((pushforwardComplex pairedM A).d1 z) F = _
    rw [hh,TargetSupportedNerve.targetSubsetComplex_d1_apply]
    fin_cases f <;> rfl

/-- 元ηP1の全五値は原a二liftで同じ粗値を取る。 -/
theorem paired_eta1_values (A : Set Bool) (hA : A.Nonempty) (z : (Nc.targetSubsetComplex A).C1) :
    (pairedPNamedEquiv A hA).e1 ((unitHom pairedM A).f1 z) =
      ![(fullSubsetNamedEquiv Nc (fun _ => rfl) A hA).e1 z 0,
        (fullSubsetNamedEquiv Nc (fun _ => rfl) A hA).e1 z 0,
        (fullSubsetNamedEquiv Nc (fun _ => rfl) A hA).e1 z 1,
        (fullSubsetNamedEquiv Nc (fun _ => rfl) A hA).e1 z 2,
        (fullSubsetNamedEquiv Nc (fun _ => rfl) A hA).e1 z 3] := by
  have hs := congrArg (fun f => f.f1 z) (paired_subset_square A hA)
  rw [aSubnerveComparisonHom_factorization] at hs
  change (fullSubsetNamedEquiv pairedNf (fun _ => rfl) _ (fine_nonempty A hA)).e1
      (evaluation1 pairedM A ((unitHom pairedM A).f1 z)) =
    (incidenceNamedHom pairedM).f1 ((fullSubsetNamedEquiv Nc (fun _ => rfl) A hA).e1 z) at hs
  funext e
  have hh := congrFun hs e.castSucc
  fin_cases e <;> exact hh
/-- 元ηP0の全chart値は原恒等chart写像。 -/
theorem paired_eta0_values (A : Set Bool) (hA : A.Nonempty) (z : (Nc.targetSubsetComplex A).C0) :
    (pairedPNamedEquiv A hA).e0 ((unitHom pairedM A).f0 z) = (fullSubsetNamedEquiv Nc (fun _ => rfl) A hA).e0 z := by
  have hs := congrArg (fun f => f.f0 z) (paired_subset_square A hA)
  rw [aSubnerveComparisonHom_factorization] at hs
  exact hs
/-- 元ηP2の全二面値は原恒等面写像。 -/
theorem paired_eta2_values (A : Set Bool) (hA : A.Nonempty) (z : (Nc.targetSubsetComplex A).C2) :
    (pairedPNamedEquiv A hA).e2 ((unitHom pairedM A).f2 z) = (fullSubsetNamedEquiv Nc (fun _ => rfl) A hA).e2 z := by
  have hs := congrArg (fun f => f.f2 z) (paired_subset_square A hA)
  rw [aSubnerveComparisonHom_factorization] at hs
  exact hs
/-- 原mなしP2微分は全二面値を実現する。 -/
theorem pairedP_d1_surjective : Function.Surjective pairedPNamedComplex.d1 := by
  intro z
  refine ⟨![z 0,z 1,0,0,0],?_⟩
  funext f
  change ![z 0-0+0,z 1-0+0] f = z f
  fin_cases f <;> dsimp <;> ring
/-- 原五辺cyclesのh period。 -/
def pairedPPeriod : LinearMap.ker pairedPNamedComplex.d1 →ₗ[ℚ] ℚ where
  toFun z := z.1 4
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
/-- 元P cycle period核は元chartd0像全像。 -/
theorem pairedPPeriod_kernel : LinearMap.ker pairedPPeriod = LinearMap.range pairedPNamedComplex.boundaryToCycles := by
  ext z
  constructor
  · intro hz
    change z.1 4 = 0 at hz
    have h0 := congrFun z.2 0
    have h1 := congrFun z.2 1
    change z.1 0-z.1 2+z.1 3=0 at h0
    change z.1 1-z.1 2+z.1 3=0 at h1
    refine ⟨![0,z.1 0,z.1 2],?_⟩
    apply Subtype.ext; funext e
    change pairedPNamedComplex.d0 ![0,z.1 0,z.1 2] e = z.1 e
    change ![z.1 0-0,z.1 0-0,z.1 2-0,z.1 2-z.1 0,0] e = z.1 e
    fin_cases e <;> dsimp <;> linarith
  · rintro ⟨z,rfl⟩
    change (0:ℚ)=0
    rfl
/-- 任意h値は同原P cycleで生成。 -/
theorem pairedPPeriod_surjective : Function.Surjective pairedPPeriod := by
  intro q
  refine ⟨⟨![0,0,0,0,q],?_⟩,rfl⟩
  funext f
  fin_cases f <;> change (0:ℚ)-0+0=0 <;> ring
/-- 原P全H¹商は同h periodと両逆。 -/
def pairedPNamedH1Coordinates : pairedPNamedComplex.H1 ≃ₗ[ℚ] ℚ :=
  periodQuotientEquiv _ pairedPPeriod pairedPPeriod_kernel pairedPPeriod_surjective
/-- 原Kan Pの全H¹商座標。 -/
def pairedPH1Coordinates (A : Set Bool) (hA : A.Nonempty) : (pushforwardComplex pairedM A).H1 ≃ₗ[ℚ] ℚ :=
  (pairedPNamedEquiv A hA).h1Equiv.trans pairedPNamedH1Coordinates
/-- 同ηの全元H¹でh periodが恒等。 -/
theorem paired_unit_coordinates (A : Set Bool) (hA : A.Nonempty) (z : (Nc.targetSubsetComplex A).H1) :
    pairedPH1Coordinates A hA ((unitHom pairedM A).h1Map z) = coarseCoordinates A hA z := by
  induction z using Submodule.Quotient.induction_on with | _ z =>
    change pairedPH1Coordinates A hA ((unitHom pairedM A).h1Map
      ((LinearMap.range (Nc.targetSubsetComplex A).boundaryToCycles).mkQ z)) = _
    rw [ThreeCochainComplex.Hom.h1Map_mk]
    change (pairedPNamedEquiv A hA).e1 ((unitHom pairedM A).f1 z.1) 4 =
      (fullSubsetNamedEquiv Nc (fun _ => rfl) A hA).e1 z.1 3
    rw [paired_eta1_values]
    rfl
/-- 原ηの元H¹商は全単射、P1対角から弱化しない。 -/
theorem paired_old_unit_bijective (A : Set Bool) (hA : A.Nonempty) : Function.Bijective (unitHom pairedM A).h1Map := by
  constructor
  · intro x y hh
    apply (coarseCoordinates A hA).injective
    rw [← paired_unit_coordinates A hA x,← paired_unit_coordinates A hA y,hh]
  · intro z
    refine ⟨(coarseCoordinates A hA).symm (pairedPH1Coordinates A hA z),?_⟩
    exact (pairedPH1Coordinates A hA).injective
      ((paired_unit_coordinates A hA _).trans ((coarseCoordinates A hA).apply_symm_apply _))
/-- 標準ηH¹の同じ全単射。 -/
theorem paired_unit_bijective (A : Set Bool) (hA : A.Nonempty) : Function.Bijective (unitH1 pairedM A) := by
  rw [unitH1_eq_standard]
  exact (LinearConjugation.bijective_iff _ _ (oldH1Equiv _) (oldH1Equiv _)
    (oldH1Equiv_natural (unitHom pairedM A))).mp (paired_old_unit_bijective A hA)
/-- 同mなし原a欠損00。 -/
theorem paired_unit_defect (A : Set Bool) (hA : A.Nonempty) : blockDefect (unitH1 pairedM A) = (0,0) :=
  (blockDefect_eq_zero_iff_bijective _).mpr (paired_unit_bijective A hA)

end AAT.AG.AtlasCoefficientFiber.WitnessThree
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessThree.pairedPNamedComplex
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessThree.pairedFineEdge
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessThree.pairedP1Period
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessThree.paired_evaluation_k
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessThree.pairedP1Period_injective
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessThree.pairedP1Period_surjective
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessThree.pairedP1Equiv
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessThree.paired_evaluation0_surjective
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessThree.pairedP0Equiv
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessThree.pairedP2Equiv
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessThree.pairedPNamedEquiv
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessThree.paired_eta1_values
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessThree.paired_eta0_values
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessThree.paired_eta2_values
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessThree.pairedP_d1_surjective
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessThree.pairedPPeriod
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessThree.pairedPPeriod_kernel
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessThree.pairedPPeriod_surjective
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessThree.pairedPNamedH1Coordinates
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessThree.pairedPH1Coordinates
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessThree.paired_unit_coordinates
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessThree.paired_old_unit_bijective
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessThree.paired_unit_bijective
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessThree.paired_unit_defect
#assert_standard_axioms_only AAT.AG.AtlasCoefficientFiber.WitnessThree
