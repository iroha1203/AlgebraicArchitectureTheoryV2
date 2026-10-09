import ResearchLean.AG.AtlasCoefficientFiber.WitnessTwoInput
import ResearchLean.AG.AtlasCoefficientFiber.WitnessOneEvaluation
import ResearchLean.AG.AtlasCoefficientFiber.WitnessOneDiagnostics

/-!
# G-135 W2：原H¹比較と余核period

## Implementation notes

原商の全座標を生成し、同じ実比較の全元式へ戻す。
元cycles/range商の全両逆を使い、次元だけの一致で元比較を置き換える方法は採らない。
-/
noncomputable section
namespace AAT.AG.AtlasCoefficientFiber.WitnessTwo
open CanonicalResolution ResolutionInvariance TwoPhase FaceRelationSubdivision AtlasDefectComposition
open WitnessCommon WitnessFullSupport

/-- 粗h loopの原d0は端点差から零。 -/
theorem coarse_d0_zero : (namedComplex Nc).d0 = 0 := by
  apply LinearMap.ext; intro z; funext e
  rw [namedComplex_d0_apply]; exact sub_self _
/-- 粗原d1は指定面なしから零。 -/
theorem coarse_d1_zero : (namedComplex Nc).d1 = 0 := by
  apply LinearMap.ext; intro z; funext f; exact Fin.elim0 f
/-- 細h,k loopの原d0は端点差から零。 -/
theorem fine_d0_zero : (namedComplex Nf).d0 = 0 := by
  apply LinearMap.ext; intro z; funext e
  rw [namedComplex_d0_apply]; exact sub_self _
/-- 細原d1は指定面なしから零。 -/
theorem fine_d1_zero : (namedComplex Nf).d1 = 0 := by
  apply LinearMap.ext; intro z; funext f; exact Fin.elim0 f

/-- 原粗全H¹商のh座標。 -/
def coarseNamedCoordinates : (namedComplex Nc).H1 ≃ₗ[ℚ] (Fin 1 → ℚ) :=
  zeroDifferentialH1Equiv _ coarse_d0_zero coarse_d1_zero
/-- 原細全H¹商のh,k座標。 -/
def fineNamedCoordinates : (namedComplex Nf).H1 ≃ₗ[ℚ] (Fin 2 → ℚ) :=
  zeroDifferentialH1Equiv _ fine_d0_zero fine_d1_zero
/-- 原named比較の全元はhを残しkへ零を送る。 -/
theorem named_map (x : (namedComplex Nc).H1) :
    fineNamedCoordinates ((incidenceNamedHom M).h1Map x) = ![coarseNamedCoordinates x 0,0] := by
  obtain ⟨z,rfl⟩ := (LinearMap.range (namedComplex Nc).boundaryToCycles).mkQ_surjective x
  rw [ThreeCochainComplex.Hom.h1Map_mk]
  funext e; fin_cases e <;> rfl
/-- 同じ原粗subset H¹全商のh座標。 -/
def coarseCoordinates (A : Set Bool) (hA : A.Nonempty) :
    (Nc.targetSubsetComplex A).H1 ≃ₗ[ℚ] (Fin 1 → ℚ) :=
  (fullSubsetNamedEquiv Nc (fun _ => rfl) A hA).h1Equiv.trans coarseNamedCoordinates
/-- 同じ原細subset H¹全商のh,k座標。 -/
def fineCoordinates (A : Set Bool) (hA : A.Nonempty) :
    (Nf.targetSubsetComplex (comparisonFactor qc qf coarser ⁻¹' A)).H1 ≃ₗ[ℚ] (Fin 2 → ℚ) :=
  (fullSubsetNamedEquiv Nf (fun _ => rfl) _ (fine_nonempty A hA)).h1Equiv.trans fineNamedCoordinates
/-- 元全三次数uの原named比較とのsquare。 -/
theorem subset_square (A : Set Bool) (hA : A.Nonempty) :
    cochainComp (M.aSubnerveComparisonHom A)
      (fullSubsetNamedEquiv Nf (fun _ => rfl) _ (fine_nonempty A hA)).toHom =
    cochainComp (fullSubsetNamedEquiv Nc (fun _ => rfl) A hA).toHom (incidenceNamedHom M) :=
  fullSubsetNamed_square M (fun _ => rfl) (fun _ => rfl) A _ hA
    (fine_nonempty A hA) (fun _ ht => ht)
/-- 同実uの全H¹元式x→(x,0)。 -/
theorem subset_map (A : Set Bool) (hA : A.Nonempty) (x : (Nc.targetSubsetComplex A).H1) :
    fineCoordinates A hA ((M.aSubnerveComparisonHom A).h1Map x) =
      ![coarseCoordinates A hA x 0,0] := by
  have hn := fun z => congrArg (fun f => f.f1 z) (subset_square A hA)
  have hh := ThreeCochainComplex.CochainEquiv.h1Equiv_naturality_apply
    (fullSubsetNamedEquiv Nc (fun _ => rfl) A hA)
    (fullSubsetNamedEquiv Nf (fun _ => rfl) _ (fine_nonempty A hA))
    (M.aSubnerveComparisonHom A) (incidenceNamedHom M) hn x
  exact (congrArg fineNamedCoordinates hh).trans (named_map _)
/-- 全座標の表示射。元Tへの接続はsubset_map。 -/
def coordinateMap : (Fin 1 → ℚ) →ₗ[ℚ] (Fin 2 → ℚ) where
  toFun z := ![z 0,0]
  map_add' _ _ := by funext e; fin_cases e <;> simp
  map_smul' _ _ := by funext e; fin_cases e <;> simp
/-- 表示射は全元で単射。 -/
theorem coordinateMap_injective : Function.Injective coordinateMap := by
  intro x y he; have hh := congrFun he 0
  funext i; fin_cases i; exact hh
/-- 元余核の検出periodは同じk値。 -/
def kPeriod : (Fin 2 → ℚ) →ₗ[ℚ] ℚ where
  toFun z := z 1
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
/-- 元k period核は元表示射の像、双方。 -/
theorem kPeriod_kernel : LinearMap.ker kPeriod = LinearMap.range coordinateMap := by
  ext z
  constructor
  · intro hz
    have hz' : z 1 = 0 := hz
    refine ⟨fun _ => z 0,?_⟩
    funext e; fin_cases e <;> simp [coordinateMap,hz']
  · rintro ⟨x,rfl⟩; rfl
/-- k単独値から原periodは全射。 -/
theorem kPeriod_surjective : Function.Surjective kPeriod := fun q => ⟨![0,q],rfl⟩
/-- 原表示余核の全商とk値の両逆。 -/
def coordinateCokernelEquiv : ((Fin 2 → ℚ) ⧸ LinearMap.range coordinateMap) ≃ₗ[ℚ] ℚ :=
  (Submodule.quotEquivOfEq _ _ kPeriod_kernel.symm).trans
    (LinearMap.quotKerEquivOfSurjective kPeriod kPeriod_surjective)
/-- 表示余核同値は同じk cochain値を保持。 -/
@[simp] theorem coordinateCokernelEquiv_mk (z : Fin 2 → ℚ) :
    coordinateCokernelEquiv ((LinearMap.range coordinateMap).mkQ z) = z 1 := rfl
/-- 同実Tの元余核全商とk値の両逆。 -/
def cokernelEquiv (A : Set Bool) (hA : A.Nonempty) :
    ((Nf.targetSubsetComplex (comparisonFactor qc qf coarser ⁻¹' A)).H1 ⧸
      LinearMap.range (M.aSubnerveComparisonHom A).h1Map) ≃ₗ[ℚ] ℚ :=
  (LinearConjugation.cokernelEquiv (M.aSubnerveComparisonHom A).h1Map coordinateMap
    (coarseCoordinates A hA) (fineCoordinates A hA) (subset_map A hA)).trans coordinateCokernelEquiv
/-- 同実T余核同値は元全H¹のk値を読む。 -/
@[simp] theorem cokernelEquiv_mk (A : Set Bool) (hA : A.Nonempty)
    (z : (Nf.targetSubsetComplex (comparisonFactor qc qf coarser ⁻¹' A)).H1) :
    cokernelEquiv A hA ((LinearMap.range (M.aSubnerveComparisonHom A).h1Map).mkQ z) =
      fineCoordinates A hA z 1 := rfl
/-- 同実Tは全H¹で単射。 -/
theorem comparison_injective (A : Set Bool) (hA : A.Nonempty) :
    Function.Injective (M.aSubnerveComparisonHom A).h1Map := by
  intro x y h
  apply (coarseCoordinates A hA).injective
  apply coordinateMap_injective
  exact (subset_map A hA x).symm.trans ((congrArg (fineCoordinates A hA) h).trans (subset_map A hA y))
/-- 同実Tの欠損は非空全Aで01。 -/
theorem defect (A : Set Bool) (hA : A.Nonempty) :
    blockDefect (M.aSubnerveComparisonHom A).h1Map = (0,1) := by
  apply Prod.ext
  · rw [blockDefect_kernel_dimension,LinearMap.ker_eq_bot.mpr (comparison_injective A hA)]
    exact Module.finrank_zero_of_subsingleton
  · exact (cokernelEquiv A hA).finrank_eq.trans (Module.finrank_self ℚ)
/-- 同原producer Jは同実欠損01。 -/
theorem primitive_J (A : Set Bool) (hA : A.Nonempty) : primitiveDiagnostic M A = (0,1) :=
  (primitiveDiagnostic_eq_blockDefect M A).trans (defect A hA)
/-- 空Aも同原商から欠損零。 -/
theorem empty_defect : blockDefect (M.aSubnerveComparisonHom ∅).h1Map = (0,0) := by
  letI := WitnessOne.empty_H1_subsingleton qc Nc
  letI : Subsingleton (Nf.targetSubsetComplex (comparisonFactor qc qf coarser ⁻¹' ∅)).H1 := by
    simpa only [Set.preimage_empty] using WitnessOne.empty_H1_subsingleton qf Nf
  exact (blockDefect_eq_zero_iff_bijective _).mpr
    ⟨fun _ _ _ => Subsingleton.elim _ _,fun y => ⟨0,Subsingleton.elim _ _⟩⟩
/-- 原producerは全Aに空と非空の実値を持つ。 -/
theorem allA_primitive_J (A : Set Bool) :
    primitiveDiagnostic M A = @ite (ℕ × ℕ) A.Nonempty (Classical.propDecidable _) (0,1) (0,0) := by
  classical
  by_cases hA : A.Nonempty
  · rw [if_pos hA]; exact primitive_J A hA
  · have ha : A = ∅ := Set.not_nonempty_iff_eq_empty.mp hA
    subst A
    rw [if_neg Set.not_nonempty_empty, primitiveDiagnostic_eq_blockDefect]
    exact empty_defect

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

/-- 指定fineの元選択loop微分は全台で零。 -/
theorem fine_subset_d0_zero (S : Set qf.Target) : (Nf.targetSubsetComplex S).d0 = 0 := by
  apply LinearMap.ext
  intro z
  funext e
  rw [Nf.targetSubsetComplex_d0_apply]
  have he : Nf.targetSubsetEdgeRight S e = Nf.targetSubsetEdgeLeft S e := Subtype.ext rfl
  rw [he]
  exact sub_self _

/-- 指定fine面なしから元選択微分も全台で零。 -/
theorem fine_subset_d1_zero (S : Set qf.Target) : (Nf.targetSubsetComplex S).d1 = 0 := by
  apply LinearMap.ext
  intro z
  funext f
  exact Fin.elim0 f.1

/-- 指定fineの同原始d0行列全entryは零。 -/
theorem fine_primitive_D0_zero (S : Set qf.Target)
    [Fintype (Nf.ChartInTargetSubset S)] [DecidableEq (Nf.ChartInTargetSubset S)] :
    primitiveD0Matrix Nf S = 0 := by
  apply Matrix.ext
  intro e c
  rw [primitiveD0Matrix_entry]
  have he : Nf.targetSubsetEdgeRight S e = Nf.targetSubsetEdgeLeft S e := Subtype.ext rfl
  rw [he]
  exact sub_self _

/-- 指定fine面なしから同原始d1行列全entryは零。 -/
theorem fine_primitive_D1_zero (S : Set qf.Target)
    [Fintype (Nf.EdgeInTargetSubset S)] [DecidableEq (Nf.EdgeInTargetSubset S)] :
    primitiveD1Matrix Nf S = 0 := by
  apply Matrix.ext
  intro f e
  exact Fin.elim0 f.1


end AAT.AG.AtlasCoefficientFiber.WitnessTwo
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessTwo.coarse_d0_zero
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessTwo.coarse_d1_zero
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessTwo.fine_d0_zero
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessTwo.fine_d1_zero
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessTwo.coarseNamedCoordinates
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessTwo.fineNamedCoordinates
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessTwo.named_map
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessTwo.coarseCoordinates
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessTwo.fineCoordinates
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessTwo.subset_square
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessTwo.subset_map
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessTwo.coordinateMap
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessTwo.coordinateMap_injective
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessTwo.kPeriod
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessTwo.kPeriod_kernel
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessTwo.kPeriod_surjective
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessTwo.coordinateCokernelEquiv
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessTwo.coordinateCokernelEquiv_mk
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessTwo.cokernelEquiv
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessTwo.cokernelEquiv_mk
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessTwo.comparison_injective
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessTwo.defect
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessTwo.primitive_J
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessTwo.empty_defect
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessTwo.allA_primitive_J
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessTwo.coarse_subset_d0_zero
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessTwo.coarse_subset_d1_zero
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessTwo.coarse_primitive_D0_zero
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessTwo.coarse_primitive_D1_zero
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessTwo.fine_subset_d0_zero
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessTwo.fine_subset_d1_zero
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessTwo.fine_primitive_D0_zero
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessTwo.fine_primitive_D1_zero
#assert_standard_axioms_only AAT.AG.AtlasCoefficientFiber.WitnessTwo
