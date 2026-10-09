import ResearchLean.AG.AtlasCoefficientFiber.WitnessOneInput
import ResearchLean.AG.AtlasCoefficientFiber.WitnessFullSupport
import ResearchLean.AG.AtlasCoefficientFiber.MappedEvaluation
import ResearchLean.AG.AtlasCoefficientFiber.NativeDegreeDifferentials

/-!
# G-135 W1：同じ原三次数比較とH¹全元

## Implementation notes

指定loopの原始端点差と面なしから零微分を証明する。
名付き座標は全三次数同型の正方形を通して元subset商へ戻す。
-/
noncomputable section
namespace AAT.AG.AtlasCoefficientFiber.WitnessOne
open CanonicalResolution ResolutionInvariance TwoPhase FaceRelationSubdivision AtlasDefectComposition
open WitnessCommon WitnessFullSupport

/-- 指定粗loopの原始d0は零。 -/
theorem coarse_d0_zero : (namedComplex Nc).d0 = 0 := by
  apply LinearMap.ext
  intro z
  funext e
  rw [namedComplex_d0_apply]
  exact sub_self _
/-- 指定粗面なしから原始d1は零。 -/
theorem coarse_d1_zero : (namedComplex Nc).d1 = 0 := by
  apply LinearMap.ext
  intro z
  funext f
  exact Fin.elim0 f
/-- 指定hだけの原始d0は零。 -/
theorem a_d0_zero : (namedComplex Na).d0 = 0 := by
  apply LinearMap.ext
  intro z
  funext e
  rw [namedComplex_d0_apply]
  exact sub_self _
/-- 指定hだけの原始d1は零。 -/
theorem a_d1_zero : (namedComplex Na).d1 = 0 := by
  apply LinearMap.ext
  intro z
  funext f
  exact Fin.elim0 f
/-- 指定e₀,e₁,hの原始d0は零。 -/
theorem b_d0_zero : (namedComplex Nb).d0 = 0 := by
  apply LinearMap.ext
  intro z
  funext e
  rw [namedComplex_d0_apply]
  exact sub_self _
/-- 指定e₀,e₁,hの原始d1は零。 -/
theorem b_d1_zero : (namedComplex Nb).d1 = 0 := by
  apply LinearMap.ext
  intro z
  funext f
  exact Fin.elim0 f

/-- 元粗H¹全体のe,h座標、両逆を持つ。 -/
def coarseNamedCoordinates : (namedComplex Nc).H1 ≃ₗ[ℚ] (Fin 2 → ℚ) :=
  zeroDifferentialH1Equiv _ coarse_d0_zero coarse_d1_zero
/-- 元W1a細H¹全体のh座標、両逆を持つ。 -/
def aNamedCoordinates : (namedComplex Na).H1 ≃ₗ[ℚ] (Fin 1 → ℚ) :=
  zeroDifferentialH1Equiv _ a_d0_zero a_d1_zero
/-- 元W1b細H¹全体のe₀,e₁,h座標、両逆を持つ。 -/
def bNamedCoordinates : (namedComplex Nb).H1 ≃ₗ[ℚ] (Fin 3 → ℚ) :=
  zeroDifferentialH1Equiv _ b_d0_zero b_d1_zero

/-- 同じ原始W1a比較は全H¹で(x,y)→y。 -/
theorem a_named_map (x : (namedComplex Nc).H1) :
    aNamedCoordinates ((incidenceNamedHom Ma).h1Map x) =
      fun _ => coarseNamedCoordinates x 1 := by
  obtain ⟨z,rfl⟩ := (LinearMap.range (namedComplex Nc).boundaryToCycles).mkQ_surjective x
  rw [ThreeCochainComplex.Hom.h1Map_mk]
  rfl
/-- 同じ原始W1b比較は全H¹で(x,y)→(x,x,y)。 -/
theorem b_named_map (x : (namedComplex Nc).H1) :
    bNamedCoordinates ((incidenceNamedHom Mb).h1Map x) =
      ![coarseNamedCoordinates x 0,coarseNamedCoordinates x 0,coarseNamedCoordinates x 1] := by
  obtain ⟨z,rfl⟩ := (LinearMap.range (namedComplex Nc).boundaryToCycles).mkQ_surjective x
  rw [ThreeCochainComplex.Hom.h1Map_mk]
  funext e
  fin_cases e <;> rfl

/-- 同じ実粗subsetの全H¹を原始e,hへ移す。 -/
def coarseCoordinates (A : Set Bool) (hA : A.Nonempty) :
    (Nc.targetSubsetComplex A).H1 ≃ₗ[ℚ] (Fin 2 → ℚ) :=
  (fullSubsetNamedEquiv Nc (fun _ => rfl) A hA).h1Equiv.trans coarseNamedCoordinates
/-- 同じ実W1a細subsetの全H¹をhへ移す。 -/
def aCoordinates (A : Set Bool) (hA : A.Nonempty) :
    (Na.targetSubsetComplex (comparisonFactor qc qf coarser ⁻¹' A)).H1 ≃ₗ[ℚ] (Fin 1 → ℚ) :=
  (fullSubsetNamedEquiv Na (fun _ => rfl) _ (fine_nonempty A hA)).h1Equiv.trans aNamedCoordinates
/-- 同じ実W1b細subsetの全H¹をe₀,e₁,hへ移す。 -/
def bCoordinates (A : Set Bool) (hA : A.Nonempty) :
    (Nb.targetSubsetComplex (comparisonFactor qc qf coarser ⁻¹' A)).H1 ≃ₗ[ℚ] (Fin 3 → ℚ) :=
  (fullSubsetNamedEquiv Nb (fun _ => rfl) _ (fine_nonempty A hA)).h1Equiv.trans bNamedCoordinates

/-- W1aは元全三次数の実比較正方形を持つ。 -/
theorem a_subset_square (A : Set Bool) (hA : A.Nonempty) :
    cochainComp (Ma.aSubnerveComparisonHom A)
      (fullSubsetNamedEquiv Na (fun _ => rfl) _ (fine_nonempty A hA)).toHom =
    cochainComp (fullSubsetNamedEquiv Nc (fun _ => rfl) A hA).toHom (incidenceNamedHom Ma) :=
  fullSubsetNamed_square Ma (fun _ => rfl) (fun _ => rfl) A _ hA
    (fine_nonempty A hA) (fun _ ht => ht)
/-- W1bは元全三次数の実比較正方形を持つ。 -/
theorem b_subset_square (A : Set Bool) (hA : A.Nonempty) :
    cochainComp (Mb.aSubnerveComparisonHom A)
      (fullSubsetNamedEquiv Nb (fun _ => rfl) _ (fine_nonempty A hA)).toHom =
    cochainComp (fullSubsetNamedEquiv Nc (fun _ => rfl) A hA).toHom (incidenceNamedHom Mb) :=
  fullSubsetNamed_square Mb (fun _ => rfl) (fun _ => rfl) A _ hA
    (fine_nonempty A hA) (fun _ ht => ht)

/-- 原実W1a H¹比較の全元式。 -/
theorem a_subset_map (A : Set Bool) (hA : A.Nonempty) (x : (Nc.targetSubsetComplex A).H1) :
    aCoordinates A hA ((Ma.aSubnerveComparisonHom A).h1Map x) =
      fun _ => coarseCoordinates A hA x 1 := by
  have hn := fun z => congrArg (fun f => f.f1 z) (a_subset_square A hA)
  have hh := ThreeCochainComplex.CochainEquiv.h1Equiv_naturality_apply
    (fullSubsetNamedEquiv Nc (fun _ => rfl) A hA)
    (fullSubsetNamedEquiv Na (fun _ => rfl) _ (fine_nonempty A hA))
    (Ma.aSubnerveComparisonHom A) (incidenceNamedHom Ma) hn x
  exact (congrArg aNamedCoordinates hh).trans (a_named_map _)
/-- 原実W1b H¹比較の全元式。 -/
theorem b_subset_map (A : Set Bool) (hA : A.Nonempty) (x : (Nc.targetSubsetComplex A).H1) :
    bCoordinates A hA ((Mb.aSubnerveComparisonHom A).h1Map x) =
      ![coarseCoordinates A hA x 0,coarseCoordinates A hA x 0,coarseCoordinates A hA x 1] := by
  have hn := fun z => congrArg (fun f => f.f1 z) (b_subset_square A hA)
  have hh := ThreeCochainComplex.CochainEquiv.h1Equiv_naturality_apply
    (fullSubsetNamedEquiv Nc (fun _ => rfl) A hA)
    (fullSubsetNamedEquiv Nb (fun _ => rfl) _ (fine_nonempty A hA))
    (Mb.aSubnerveComparisonHom A) (incidenceNamedHom Mb) hn x
  exact (congrArg bNamedCoordinates hh).trans (b_named_map _)


/-- 指定coarseの元選択loop微分は全台で零。 -/
theorem coarse_subset_d0_zero (S : Set qc.Target) : (Nc.targetSubsetComplex S).d0 = 0 := by
  apply LinearMap.ext
  intro z
  funext e
  rw [Nc.targetSubsetComplex_d0_apply]
  have he : Nc.targetSubsetEdgeRight S e = Nc.targetSubsetEdgeLeft S e := Subtype.ext rfl
  rw [he]
  exact sub_self _

/-- 指定coarse面なしから元選択微分も全台で零。 -/
theorem coarse_subset_d1_zero (S : Set qc.Target) : (Nc.targetSubsetComplex S).d1 = 0 := by
  apply LinearMap.ext
  intro z
  funext f
  exact Fin.elim0 f.1

/-- 指定coarseの同原始d0行列全entryは零。 -/
theorem coarse_primitive_D0_zero (S : Set qc.Target)
    [Fintype (Nc.ChartInTargetSubset S)] [DecidableEq (Nc.ChartInTargetSubset S)] :
    primitiveD0Matrix Nc S = 0 := by
  apply Matrix.ext
  intro e c
  rw [primitiveD0Matrix_entry]
  have he : Nc.targetSubsetEdgeRight S e = Nc.targetSubsetEdgeLeft S e := Subtype.ext rfl
  rw [he]
  exact sub_self _

/-- 指定coarse面なしから同原始d1行列全entryは零。 -/
theorem coarse_primitive_D1_zero (S : Set qc.Target)
    [Fintype (Nc.EdgeInTargetSubset S)] [DecidableEq (Nc.EdgeInTargetSubset S)] :
    primitiveD1Matrix Nc S = 0 := by
  apply Matrix.ext
  intro f e
  exact Fin.elim0 f.1

/-- 指定aの元選択loop微分は全台で零。 -/
theorem a_subset_d0_zero (S : Set qf.Target) : (Na.targetSubsetComplex S).d0 = 0 := by
  apply LinearMap.ext
  intro z
  funext e
  rw [Na.targetSubsetComplex_d0_apply]
  have he : Na.targetSubsetEdgeRight S e = Na.targetSubsetEdgeLeft S e := Subtype.ext rfl
  rw [he]
  exact sub_self _

/-- 指定a面なしから元選択微分も全台で零。 -/
theorem a_subset_d1_zero (S : Set qf.Target) : (Na.targetSubsetComplex S).d1 = 0 := by
  apply LinearMap.ext
  intro z
  funext f
  exact Fin.elim0 f.1

/-- 指定aの同原始d0行列全entryは零。 -/
theorem a_primitive_D0_zero (S : Set qf.Target)
    [Fintype (Na.ChartInTargetSubset S)] [DecidableEq (Na.ChartInTargetSubset S)] :
    primitiveD0Matrix Na S = 0 := by
  apply Matrix.ext
  intro e c
  rw [primitiveD0Matrix_entry]
  have he : Na.targetSubsetEdgeRight S e = Na.targetSubsetEdgeLeft S e := Subtype.ext rfl
  rw [he]
  exact sub_self _

/-- 指定a面なしから同原始d1行列全entryは零。 -/
theorem a_primitive_D1_zero (S : Set qf.Target)
    [Fintype (Na.EdgeInTargetSubset S)] [DecidableEq (Na.EdgeInTargetSubset S)] :
    primitiveD1Matrix Na S = 0 := by
  apply Matrix.ext
  intro f e
  exact Fin.elim0 f.1

/-- 指定bの元選択loop微分は全台で零。 -/
theorem b_subset_d0_zero (S : Set qf.Target) : (Nb.targetSubsetComplex S).d0 = 0 := by
  apply LinearMap.ext
  intro z
  funext e
  rw [Nb.targetSubsetComplex_d0_apply]
  have he : Nb.targetSubsetEdgeRight S e = Nb.targetSubsetEdgeLeft S e := Subtype.ext rfl
  rw [he]
  exact sub_self _

/-- 指定b面なしから元選択微分も全台で零。 -/
theorem b_subset_d1_zero (S : Set qf.Target) : (Nb.targetSubsetComplex S).d1 = 0 := by
  apply LinearMap.ext
  intro z
  funext f
  exact Fin.elim0 f.1

/-- 指定bの同原始d0行列全entryは零。 -/
theorem b_primitive_D0_zero (S : Set qf.Target)
    [Fintype (Nb.ChartInTargetSubset S)] [DecidableEq (Nb.ChartInTargetSubset S)] :
    primitiveD0Matrix Nb S = 0 := by
  apply Matrix.ext
  intro e c
  rw [primitiveD0Matrix_entry]
  have he : Nb.targetSubsetEdgeRight S e = Nb.targetSubsetEdgeLeft S e := Subtype.ext rfl
  rw [he]
  exact sub_self _

/-- 指定b面なしから同原始d1行列全entryは零。 -/
theorem b_primitive_D1_zero (S : Set qf.Target)
    [Fintype (Nb.EdgeInTargetSubset S)] [DecidableEq (Nb.EdgeInTargetSubset S)] :
    primitiveD1Matrix Nb S = 0 := by
  apply Matrix.ext
  intro f e
  exact Fin.elim0 f.1

end AAT.AG.AtlasCoefficientFiber.WitnessOne
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessOne.coarse_d0_zero
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessOne.coarse_d1_zero
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessOne.a_d0_zero
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessOne.a_d1_zero
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessOne.b_d0_zero
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessOne.b_d1_zero
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessOne.coarseNamedCoordinates
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessOne.aNamedCoordinates
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessOne.bNamedCoordinates
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessOne.a_named_map
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessOne.b_named_map
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessOne.coarseCoordinates
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessOne.aCoordinates
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessOne.bCoordinates
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessOne.a_subset_square
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessOne.b_subset_square
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessOne.a_subset_map
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessOne.b_subset_map
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessOne.coarse_subset_d0_zero
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessOne.coarse_subset_d1_zero
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessOne.coarse_primitive_D0_zero
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessOne.coarse_primitive_D1_zero
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessOne.a_subset_d0_zero
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessOne.a_subset_d1_zero
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessOne.a_primitive_D0_zero
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessOne.a_primitive_D1_zero
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessOne.b_subset_d0_zero
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessOne.b_subset_d1_zero
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessOne.b_primitive_D0_zero
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessOne.b_primitive_D1_zero
#assert_standard_axioms_only AAT.AG.AtlasCoefficientFiber.WitnessOne
