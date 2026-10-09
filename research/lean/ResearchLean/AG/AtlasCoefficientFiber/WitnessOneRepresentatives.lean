import ResearchLean.AG.AtlasCoefficientFiber.WitnessOneDiagnostics

/-!
# G-135 W1：原始e・hと二e差の実代表

## Implementation notes

元subset cochainへ同じセル名で値を与え、元cycles商で類を作る。
抽象的な非零元だけを選ぶ方式は指定代表を失うため採らない。
-/
noncomputable section
namespace AAT.AG.AtlasCoefficientFiber.WitnessOne
open CanonicalResolution ResolutionInvariance TwoPhase FaceRelationSubdivision AtlasDefectComposition
open WitnessCommon

/-- 元粗subsetの原始e,h値を持つ実cocycle。 -/
def coarseCycle (A : Set Bool) (z : Fin 2 → ℚ) : LinearMap.ker (Nc.targetSubsetComplex A).d1 :=
  ⟨fun e => z e.1,by funext f; exact Fin.elim0 f.1⟩
/-- 元W1a細subsetの原始h値を持つ実cocycle。 -/
def aFineCycle (A : Set Bool) (z : Fin 1 → ℚ) :
    LinearMap.ker (Na.targetSubsetComplex (comparisonFactor qc qf coarser ⁻¹' A)).d1 :=
  ⟨fun e => z e.1,by funext f; exact Fin.elim0 f.1⟩
/-- 元W1b細subsetの原始e₀,e₁,h値を持つ実cocycle。 -/
def bFineCycle (A : Set Bool) (z : Fin 3 → ℚ) :
    LinearMap.ker (Nb.targetSubsetComplex (comparisonFactor qc qf coarser ⁻¹' A)).d1 :=
  ⟨fun e => z e.1,by funext f; exact Fin.elim0 f.1⟩

/-- 同じ原粗cycles商の実類。 -/
def coarseClass (A : Set Bool) (z : Fin 2 → ℚ) :=
  (LinearMap.range (Nc.targetSubsetComplex A).boundaryToCycles).mkQ (coarseCycle A z)
/-- 同じ原W1a細cycles商の実類。 -/
def aFineClass (A : Set Bool) (z : Fin 1 → ℚ) :=
  (LinearMap.range (Na.targetSubsetComplex (comparisonFactor qc qf coarser ⁻¹' A)).boundaryToCycles).mkQ (aFineCycle A z)
/-- 同じ原W1b細cycles商の実類。 -/
def bFineClass (A : Set Bool) (z : Fin 3 → ℚ) :=
  (LinearMap.range (Nb.targetSubsetComplex (comparisonFactor qc qf coarser ⁻¹' A)).boundaryToCycles).mkQ (bFineCycle A z)

/-- 原粗cochain代表の全座標は指定e,h値を保持。 -/
theorem coarseClass_coordinates (A : Set Bool) (hA : A.Nonempty) (z : Fin 2 → ℚ) :
    coarseCoordinates A hA (coarseClass A z) = z := rfl
/-- 原W1a細cochain代表の全座標は指定h値を保持。 -/
theorem aFineClass_coordinates (A : Set Bool) (hA : A.Nonempty) (z : Fin 1 → ℚ) :
    aCoordinates A hA (aFineClass A z) = z := rfl
/-- 原W1b細cochain代表の全座標は指定二eとhの値を保持。 -/
theorem bFineClass_coordinates (A : Set Bool) (hA : A.Nonempty) (z : Fin 3 → ℚ) :
    bCoordinates A hA (bFineClass A z) = z := rfl

/-- 同じ実W1a比較は指定e単独1の類を零へ送る。 -/
theorem a_e_kernel (A : Set Bool) (hA : A.Nonempty) :
    (Ma.aSubnerveComparisonHom A).h1Map (coarseClass A ![1,0]) = 0 := by
  apply (aCoordinates A hA).injective
  rw [a_subset_map,coarseClass_coordinates,map_zero]
  rfl

/-- 指定e単独1は元粗H¹で非零。 -/
theorem coarse_e_nonzero (A : Set Bool) (hA : A.Nonempty) : coarseClass A ![1,0] ≠ 0 := by
  intro h
  have h := congrArg (fun z => coarseCoordinates A hA z 0) h
  dsimp only at h
  rw [coarseClass_coordinates,map_zero] at h
  exact one_ne_zero h

/-- 同じ実W1a比較は指定h単独1を指定細h単独1へ送る。 -/
theorem a_h_preserved (A : Set Bool) (hA : A.Nonempty) :
    (Ma.aSubnerveComparisonHom A).h1Map (coarseClass A ![0,1]) = aFineClass A ![1] := by
  apply (aCoordinates A hA).injective
  rw [a_subset_map,coarseClass_coordinates,aFineClass_coordinates]
  funext e
  fin_cases e
  rfl

/-- 同じ実W1b比較は指定h単独1を指定細h単独1へ送る。 -/
theorem b_h_preserved (A : Set Bool) (hA : A.Nonempty) :
    (Mb.aSubnerveComparisonHom A).h1Map (coarseClass A ![0,1]) = bFineClass A ![0,0,1] := by
  apply (bCoordinates A hA).injective
  rw [b_subset_map,coarseClass_coordinates,bFineClass_coordinates]
  rfl

/-- 指定h単独1は元粗H¹で非零。 -/
theorem coarse_h_nonzero (A : Set Bool) (hA : A.Nonempty) : coarseClass A ![0,1] ≠ 0 := by
  intro h
  have h := congrArg (fun z => coarseCoordinates A hA z 1) h
  dsimp only at h
  rw [coarseClass_coordinates,map_zero] at h
  exact one_ne_zero h

/-- W1a指定細h単独1も元細H¹で非零。 -/
theorem a_h_nonzero (A : Set Bool) (hA : A.Nonempty) : aFineClass A ![1] ≠ 0 := by
  intro h
  have h := congrArg (fun z => aCoordinates A hA z 0) h
  dsimp only at h
  rw [aFineClass_coordinates,map_zero] at h
  exact one_ne_zero h

/-- W1b指定細h単独1も元細H¹で非零。 -/
theorem b_h_nonzero (A : Set Bool) (hA : A.Nonempty) : bFineClass A ![0,0,1] ≠ 0 := by
  intro h
  have h := congrArg (fun z => bCoordinates A hA z 2) h
  dsimp only at h
  rw [bFineClass_coordinates,map_zero] at h
  exact one_ne_zero h

/-- 原e₁単独1の実余核類は同じ二e差で1。 -/
theorem b_extra_period (A : Set Bool) (hA : A.Nonempty) :
    bCokernelEquiv A hA ((LinearMap.range (Mb.aSubnerveComparisonHom A).h1Map).mkQ
      (bFineClass A ![0,1,0])) = 1 := by
  rw [bCokernelEquiv_mk,bFineClass_coordinates]
  norm_num

/-- 原e₁単独1の同じ実余核類は非零。 -/
theorem b_extra_cokernel_nonzero (A : Set Bool) (hA : A.Nonempty) :
    (LinearMap.range (Mb.aSubnerveComparisonHom A).h1Map).mkQ (bFineClass A ![0,1,0]) ≠ 0 := by
  intro h
  have h := congrArg (bCokernelEquiv A hA) h
  rw [b_extra_period,map_zero] at h
  exact one_ne_zero h

end AAT.AG.AtlasCoefficientFiber.WitnessOne
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessOne.coarseCycle
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessOne.aFineCycle
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessOne.bFineCycle
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessOne.coarseClass
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessOne.aFineClass
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessOne.bFineClass
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessOne.coarseClass_coordinates
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessOne.aFineClass_coordinates
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessOne.bFineClass_coordinates
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessOne.a_e_kernel
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessOne.coarse_e_nonzero
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessOne.a_h_preserved
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessOne.b_h_preserved
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessOne.coarse_h_nonzero
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessOne.a_h_nonzero
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessOne.b_h_nonzero
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessOne.b_extra_period
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessOne.b_extra_cokernel_nonzero
#assert_standard_axioms_only AAT.AG.AtlasCoefficientFiber.WitnessOne
