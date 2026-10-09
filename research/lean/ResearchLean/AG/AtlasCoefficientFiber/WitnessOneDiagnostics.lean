import ResearchLean.AG.AtlasCoefficientFiber.WitnessOneEvaluation
import ResearchLean.AG.AtlasCoefficientFiber.WitnessOneFiber
import ResearchLean.AG.AtlasCoefficientFiber.FinitePreservationDecision
import ResearchLean.AG.AtlasDefectComposition.EmptySubset
import ResearchLean.AG.AtlasDefectComposition.LinearConjugation

/-!
# G-135 W1：同じ実核・余核と原始J

## Implementation notes

実H¹全元式から核・余核を両方向に運ぶ。差periodは元e₀,e₁の二値を読み、
期待rankや保存結果を前提にしない。原J producerは実blockDefectとの同定を使う。
-/
noncomputable section
namespace AAT.AG.AtlasCoefficientFiber.WitnessOne
open CanonicalResolution ResolutionInvariance TwoPhase FaceRelationSubdivision AtlasDefectComposition
open WitnessCommon

/-- 証明出力のW1a座標射。 -/
def aMap : (Fin 2 → ℚ) →ₗ[ℚ] (Fin 1 → ℚ) where
  toFun z _ := z 1
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
/-- 証明出力のW1b座標射。 -/
def bMap : (Fin 2 → ℚ) →ₗ[ℚ] (Fin 3 → ℚ) where
  toFun z := ![z 0,z 0,z 1]
  map_add' _ _ := by funext e; fin_cases e <;> rfl
  map_smul' _ _ := by funext e; fin_cases e <;> rfl

/-- 同じW1a座標核はeの値そのもの。 -/
def aMapKernelEquiv : LinearMap.ker aMap ≃ₗ[ℚ] ℚ where
  toFun z := z.1 0
  invFun q := ⟨![q,0],rfl⟩
  left_inv z := by
    apply Subtype.ext
    funext e
    have hz : z.1 1 = 0 := congrFun z.2 0
    fin_cases e
    · rfl
    · exact hz.symm
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- W1a座標射はh全体へ全射。 -/
theorem aMap_surjective : Function.Surjective aMap := by
  intro z
  refine ⟨![0,z 0],?_⟩
  funext e
  fin_cases e
  rfl

/-- W1b座標射は全e,hを区別して単射。 -/
theorem bMap_injective : Function.Injective bMap := by
  intro z w h
  funext e
  fin_cases e
  · exact congrFun h 0
  · exact congrFun h 2

/-- 元二e値の差を読む射。 -/
def differencePeriod : (Fin 3 → ℚ) →ₗ[ℚ] ℚ where
  toFun z := z 1 - z 0
  map_add' _ _ := by simp; ring
  map_smul' _ _ := by simp; ring

/-- 差零条件は同じ原重複比較の像と両方向に一致。 -/
theorem differencePeriod_kernel : LinearMap.ker differencePeriod = LinearMap.range bMap := by
  ext z
  constructor
  · intro hz
    have hv : z 1 = z 0 := sub_eq_zero.mp hz
    refine ⟨![z 0,z 2],?_⟩
    funext e
    fin_cases e
    · rfl
    · exact hv.symm
    · rfl
  · rintro ⟨z,rfl⟩
    exact sub_self _

/-- e₁単独cochainは任意差periodを実現する。 -/
theorem differencePeriod_surjective : Function.Surjective differencePeriod :=
  fun q => ⟨![0,q,0],by simp [differencePeriod]⟩

/-- 同じ重複比較の余核を差periodへ両逆同定。 -/
def bMapCokernelEquiv : ((Fin 3 → ℚ) ⧸ LinearMap.range bMap) ≃ₗ[ℚ] ℚ :=
  (Submodule.quotEquivOfEq _ _ differencePeriod_kernel.symm).trans
    (differencePeriod.quotKerEquivOfSurjective differencePeriod_surjective)

/-- 座標余核の全代表は元e₁−e₀の値を読む。 -/
theorem bMapCokernelEquiv_mk (z : Fin 3 → ℚ) :
    bMapCokernelEquiv ((LinearMap.range bMap).mkQ z) = z 1 - z 0 := rfl

/-- 全非空AのW1a実核は同じ元e値のQ。 -/
def aKernelEquiv (A : Set Bool) (hA : A.Nonempty) :
    LinearMap.ker (Ma.aSubnerveComparisonHom A).h1Map ≃ₗ[ℚ] ℚ :=
  (LinearConjugation.kernelEquiv _ aMap (coarseCoordinates A hA) (aCoordinates A hA)
    (a_subset_map A hA)).trans aMapKernelEquiv

/-- 全非空AのW1b実余核は同じ二e値の差のQ。 -/
def bCokernelEquiv (A : Set Bool) (hA : A.Nonempty) :
    ((Nb.targetSubsetComplex (comparisonFactor qc qf coarser ⁻¹' A)).H1 ⧸
      LinearMap.range (Mb.aSubnerveComparisonHom A).h1Map) ≃ₗ[ℚ] ℚ :=
  (LinearConjugation.cokernelEquiv _ bMap (coarseCoordinates A hA) (bCoordinates A hA)
    (b_subset_map A hA)).trans bMapCokernelEquiv

/-- 元実余核の全代表は同じ二e座標の差を読む。 -/
theorem bCokernelEquiv_mk (A : Set Bool) (hA : A.Nonempty)
    (z : (Nb.targetSubsetComplex (comparisonFactor qc qf coarser ⁻¹' A)).H1) :
    bCokernelEquiv A hA ((LinearMap.range (Mb.aSubnerveComparisonHom A).h1Map).mkQ z) =
      bCoordinates A hA z 1 - bCoordinates A hA z 0 := rfl

/-- W1a実比較はh全H¹へ全射。 -/
theorem a_surjective (A : Set Bool) (hA : A.Nonempty) :
    Function.Surjective (Ma.aSubnerveComparisonHom A).h1Map := by
  intro z
  obtain ⟨x,hx⟩ := aMap_surjective (aCoordinates A hA z)
  refine ⟨(coarseCoordinates A hA).symm x,?_⟩
  apply (aCoordinates A hA).injective
  rw [a_subset_map,LinearEquiv.apply_symm_apply]
  exact hx

/-- W1b実比較はe,h全H¹で単射。 -/
theorem b_injective (A : Set Bool) (hA : A.Nonempty) :
    Function.Injective (Mb.aSubnerveComparisonHom A).h1Map := by
  intro x y h
  apply (coarseCoordinates A hA).injective
  apply bMap_injective
  exact (b_subset_map A hA x).symm.trans ((congrArg (bCoordinates A hA) h).trans (b_subset_map A hA y))

/-- W1a同じ実Jは全非空Aで(1,0)。 -/
theorem a_defect (A : Set Bool) (hA : A.Nonempty) :
    blockDefect (Ma.aSubnerveComparisonHom A).h1Map = (1,0) := by
  apply Prod.ext
  · rw [blockDefect_kernel_dimension,(aKernelEquiv A hA).finrank_eq]
    exact Module.finrank_self ℚ
  · rw [blockDefect_cokernel_dimension,LinearMap.range_eq_top.mpr (a_surjective A hA)]
    exact Module.finrank_zero_of_subsingleton

/-- W1b同じ実Jは全非空Aで(0,1)。 -/
theorem b_defect (A : Set Bool) (hA : A.Nonempty) :
    blockDefect (Mb.aSubnerveComparisonHom A).h1Map = (0,1) := by
  apply Prod.ext
  · rw [blockDefect_kernel_dimension]
    letI : Subsingleton (LinearMap.ker (Mb.aSubnerveComparisonHom A).h1Map) := ⟨fun x y =>
      Subtype.ext (b_injective A hA (x.2.trans y.2.symm))⟩
    exact Module.finrank_zero_of_subsingleton
  · rw [blockDefect_cokernel_dimension,(bCokernelEquiv A hA).finrank_eq]
    exact Module.finrank_self ℚ

/-- 原始行列producerのJは同じ実削除比較で(1,0)。 -/
theorem a_primitive_J (A : Set Bool) (hA : A.Nonempty)
 :
    primitiveDiagnostic Ma A = (1,0) :=
  (primitiveDiagnostic_eq_blockDefect Ma A).trans (a_defect A hA)


/-- 元空subset H¹商の零性を全代表から証明する。 -/
theorem empty_H1_subsingleton (q : Reading WitnessCommon.Source) (N : TargetSupportedNerve q) :
    Subsingleton (N.targetSubsetComplex ∅).H1 := by
  constructor
  intro x y
  obtain ⟨z,rfl⟩ := (LinearMap.range (N.targetSubsetComplex ∅).boundaryToCycles).mkQ_surjective x
  obtain ⟨w,rfl⟩ := (LinearMap.range (N.targetSubsetComplex ∅).boundaryToCycles).mkQ_surjective y
  congr 1
  apply Subtype.ext
  exact Subsingleton.elim _ _

/-- 同じW1a原η H¹の核・余核の指定値。 -/
theorem a_unit_defect (A : Set Bool) (hA : A.Nonempty) : blockDefect (unitH1 Ma A) = (1,0) := by
  apply Prod.ext
  · rw [blockDefect_kernel_dimension]
    have h := (coefficient_kernel_dimension Ma A).symm
    rw [a_defect A hA] at h
    exact h
  · rw [blockDefect_cokernel_dimension]
    have h := coefficient_cokernel_dimension Ma A
    rw [a_defect A hA,a_tau_rank,a_R_dimension] at h
    simpa only [add_zero] using h.symm

/-- 空Aでは同じW1a実比較は零加群間の同型。 -/
theorem a_empty_defect : blockDefect (Ma.aSubnerveComparisonHom ∅).h1Map = (0,0) := by
  letI := empty_H1_subsingleton qc Nc
  letI : Subsingleton (Na.targetSubsetComplex (comparisonFactor qc qf coarser ⁻¹' ∅)).H1 := by
    simpa only [Set.preimage_empty] using empty_H1_subsingleton qf Na
  exact (blockDefect_eq_zero_iff_bijective _).mpr
    ⟨fun _ _ _ => Subsingleton.elim _ _,fun y => ⟨0,Subsingleton.elim _ _⟩⟩

/-- 空Aの原行列producerも同じ実比較の零欠損を得る。 -/
theorem a_empty_primitive_J : primitiveDiagnostic Ma ∅ = (0,0) :=
  (primitiveDiagnostic_eq_blockDefect Ma ∅).trans a_empty_defect

/-- 全Aの原行列producerを空台と非空台の双方で評価する。 -/
theorem a_allA_primitive_J (A : Set Bool) : primitiveDiagnostic Ma A =
    @ite (ℕ × ℕ) (A = ∅) (Classical.propDecidable _) (0,0) (1,0) := by
  classical
  by_cases hA : A.Nonempty
  · rw [if_neg (Set.nonempty_iff_ne_empty.mp hA)]
    exact a_primitive_J A hA
  · have he : A = ∅ := Set.not_nonempty_iff_eq_empty.mp hA
    subst A
    rw [if_pos rfl]
    exact a_empty_primitive_J

/-- 同原始producerのJは実重複比較で(0,1)。 -/
theorem b_primitive_J (A : Set Bool) (hA : A.Nonempty) : primitiveDiagnostic Mb A = (0,1) :=
  (primitiveDiagnostic_eq_blockDefect Mb A).trans (b_defect A hA)

/-- 同じW1b原η H¹の核・余核の指定値。 -/
theorem b_unit_defect (A : Set Bool) (hA : A.Nonempty) : blockDefect (unitH1 Mb A) = (0,1) := by
  apply Prod.ext
  · rw [blockDefect_kernel_dimension]
    have h := (coefficient_kernel_dimension Mb A).symm
    rw [b_defect A hA] at h
    exact h
  · rw [blockDefect_cokernel_dimension]
    have h := coefficient_cokernel_dimension Mb A
    rw [b_defect A hA,b_tau_rank,b_R_dimension] at h
    simpa only [add_zero] using h.symm

/-- 空Aでは同じW1b実比較は零加群間の同型。 -/
theorem b_empty_defect : blockDefect (Mb.aSubnerveComparisonHom ∅).h1Map = (0,0) := by
  letI := empty_H1_subsingleton qc Nc
  letI : Subsingleton (Nb.targetSubsetComplex (comparisonFactor qc qf coarser ⁻¹' ∅)).H1 := by
    simpa only [Set.preimage_empty] using empty_H1_subsingleton qf Nb
  exact (blockDefect_eq_zero_iff_bijective _).mpr
    ⟨fun _ _ _ => Subsingleton.elim _ _,fun y => ⟨0,Subsingleton.elim _ _⟩⟩

/-- 空Aの原行列producerも同じ実比較の零欠損を得る。 -/
theorem b_empty_primitive_J : primitiveDiagnostic Mb ∅ = (0,0) :=
  (primitiveDiagnostic_eq_blockDefect Mb ∅).trans b_empty_defect

/-- 全Aの原行列producerを空台と非空台の双方で評価する。 -/
theorem b_allA_primitive_J (A : Set Bool) : primitiveDiagnostic Mb A =
    @ite (ℕ × ℕ) (A = ∅) (Classical.propDecidable _) (0,0) (0,1) := by
  classical
  by_cases hA : A.Nonempty
  · rw [if_neg (Set.nonempty_iff_ne_empty.mp hA)]
    exact b_primitive_J A hA
  · have he : A = ∅ := Set.not_nonempty_iff_eq_empty.mp hA
    subst A
    rw [if_pos rfl]
    exact b_empty_primitive_J


end AAT.AG.AtlasCoefficientFiber.WitnessOne
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessOne.aMap
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessOne.bMap
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessOne.aMapKernelEquiv
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessOne.aMap_surjective
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessOne.bMap_injective
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessOne.differencePeriod
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessOne.differencePeriod_kernel
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessOne.differencePeriod_surjective
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessOne.bMapCokernelEquiv
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessOne.bMapCokernelEquiv_mk
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessOne.aKernelEquiv
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessOne.bCokernelEquiv
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessOne.bCokernelEquiv_mk
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessOne.a_surjective
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessOne.b_injective
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessOne.a_defect
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessOne.b_defect
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessOne.a_primitive_J
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessOne.empty_H1_subsingleton
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessOne.a_unit_defect
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessOne.a_empty_defect
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessOne.a_empty_primitive_J
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessOne.a_allA_primitive_J
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessOne.b_primitive_J
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessOne.b_unit_defect
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessOne.b_empty_defect
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessOne.b_empty_primitive_J
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessOne.b_allA_primitive_J
#assert_standard_axioms_only AAT.AG.AtlasCoefficientFiber.WitnessOne
