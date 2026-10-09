import ResearchLean.AG.AtlasCoefficientFiber.WitnessOneEvaluation

/-!
# G-135 W1：独立Kan Pと原η・ε・uの全三次数

## Implementation notes

Pを原細複体へ改定せず、同じ実εの三成分から両逆同型を構成する。
元unitと独立uの全Hom因子化を保持し、原始名付き表への全三成分正方形で照合する。
-/
noncomputable section
namespace AAT.AG.AtlasCoefficientFiber.WitnessOne
open CanonicalResolution ResolutionInvariance TwoPhase FaceRelationSubdivision AtlasDefectComposition
open WitnessCommon WitnessFullSupport

/-- W1a元Pから同細複体への三次数両逆は同じ実ε。 -/
def a_evaluation_equiv (A : Set Bool) : ThreeCochainComplex.CochainEquiv
    (pushforwardComplex Ma A) (Na.targetSubsetComplex (comparisonFactor qc qf coarser ⁻¹' A)) where
  e0 := MappedCells.evaluation0Equiv Ma A Ma_all_mapped
  e1 := MappedCells.evaluation1Equiv Ma A Ma_all_mapped Ma_faces_mapped
  e2 := MappedCells.evaluation2Equiv Ma A Ma_faces_mapped
  comm0 := evaluation_comm0 Ma A
  comm1 := evaluation_comm1 Ma A

/-- 元Pの三次数同値の順Homは同じ元counit。 -/
theorem a_evaluation_equiv_toHom (A : Set Bool) : (a_evaluation_equiv A).toHom = evaluationHom Ma A := by
  apply cochain_ext <;> rfl

/-- 全非空Aの元Kan P全体を同じ原始細degree表へ移す。 -/
def a_P_named_equiv (A : Set Bool) (hA : A.Nonempty) :
    ThreeCochainComplex.CochainEquiv (pushforwardComplex Ma A) (namedComplex Na) where
  e0 := (a_evaluation_equiv A).e0.trans (fullSubsetNamedEquiv Na (fun _ => rfl) _ (fine_nonempty A hA)).e0
  e1 := (a_evaluation_equiv A).e1.trans (fullSubsetNamedEquiv Na (fun _ => rfl) _ (fine_nonempty A hA)).e1
  e2 := (a_evaluation_equiv A).e2.trans (fullSubsetNamedEquiv Na (fun _ => rfl) _ (fine_nonempty A hA)).e2
  comm0 z := by rw [LinearEquiv.trans_apply,(a_evaluation_equiv A).comm0,
    (fullSubsetNamedEquiv Na (fun _ => rfl) _ (fine_nonempty A hA)).comm0]; rfl
  comm1 z := by rw [LinearEquiv.trans_apply,(a_evaluation_equiv A).comm1,
    (fullSubsetNamedEquiv Na (fun _ => rfl) _ (fine_nonempty A hA)).comm1]; rfl

/-- εの全三成分は同じ原P座標表示に可換。 -/
theorem a_epsilon_square (A : Set Bool) (hA : A.Nonempty) :
    (a_P_named_equiv A hA).toHom = cochainComp (evaluationHom Ma A)
      (fullSubsetNamedEquiv Na (fun _ => rfl) _ (fine_nonempty A hA)).toHom := by
  apply cochain_ext <;> rfl

/-- 原unit ηも同じ指定表へ全三成分で接続する。 -/
theorem a_eta_square (A : Set Bool) (hA : A.Nonempty) :
    cochainComp (unitHom Ma A) (a_P_named_equiv A hA).toHom =
    cochainComp (fullSubsetNamedEquiv Nc (fun _ => rfl) A hA).toHom (incidenceNamedHom Ma) := by
  rw [a_epsilon_square]
  change cochainComp (cochainComp (unitHom Ma A) (evaluationHom Ma A))
    (fullSubsetNamedEquiv Na (fun _ => rfl) _ (fine_nonempty A hA)).toHom = _
  rw [← aSubnerveComparisonHom_factorization]
  exact a_subset_square A hA

/-- W1b元Pから同細複体への三次数両逆は同じ実ε。 -/
def b_evaluation_equiv (A : Set Bool) : ThreeCochainComplex.CochainEquiv
    (pushforwardComplex Mb A) (Nb.targetSubsetComplex (comparisonFactor qc qf coarser ⁻¹' A)) where
  e0 := MappedCells.evaluation0Equiv Mb A Mb_all_mapped
  e1 := MappedCells.evaluation1Equiv Mb A Mb_all_mapped Mb_faces_mapped
  e2 := MappedCells.evaluation2Equiv Mb A Mb_faces_mapped
  comm0 := evaluation_comm0 Mb A
  comm1 := evaluation_comm1 Mb A

/-- 元Pの三次数同値の順Homは同じ元counit。 -/
theorem b_evaluation_equiv_toHom (A : Set Bool) : (b_evaluation_equiv A).toHom = evaluationHom Mb A := by
  apply cochain_ext <;> rfl

/-- 全非空Aの元Kan P全体を同じ原始細degree表へ移す。 -/
def b_P_named_equiv (A : Set Bool) (hA : A.Nonempty) :
    ThreeCochainComplex.CochainEquiv (pushforwardComplex Mb A) (namedComplex Nb) where
  e0 := (b_evaluation_equiv A).e0.trans (fullSubsetNamedEquiv Nb (fun _ => rfl) _ (fine_nonempty A hA)).e0
  e1 := (b_evaluation_equiv A).e1.trans (fullSubsetNamedEquiv Nb (fun _ => rfl) _ (fine_nonempty A hA)).e1
  e2 := (b_evaluation_equiv A).e2.trans (fullSubsetNamedEquiv Nb (fun _ => rfl) _ (fine_nonempty A hA)).e2
  comm0 z := by rw [LinearEquiv.trans_apply,(b_evaluation_equiv A).comm0,
    (fullSubsetNamedEquiv Nb (fun _ => rfl) _ (fine_nonempty A hA)).comm0]; rfl
  comm1 z := by rw [LinearEquiv.trans_apply,(b_evaluation_equiv A).comm1,
    (fullSubsetNamedEquiv Nb (fun _ => rfl) _ (fine_nonempty A hA)).comm1]; rfl

/-- εの全三成分は同じ原P座標表示に可換。 -/
theorem b_epsilon_square (A : Set Bool) (hA : A.Nonempty) :
    (b_P_named_equiv A hA).toHom = cochainComp (evaluationHom Mb A)
      (fullSubsetNamedEquiv Nb (fun _ => rfl) _ (fine_nonempty A hA)).toHom := by
  apply cochain_ext <;> rfl

/-- 原unit ηも同じ指定表へ全三成分で接続する。 -/
theorem b_eta_square (A : Set Bool) (hA : A.Nonempty) :
    cochainComp (unitHom Mb A) (b_P_named_equiv A hA).toHom =
    cochainComp (fullSubsetNamedEquiv Nc (fun _ => rfl) A hA).toHom (incidenceNamedHom Mb) := by
  rw [b_epsilon_square]
  change cochainComp (cochainComp (unitHom Mb A) (evaluationHom Mb A))
    (fullSubsetNamedEquiv Nb (fun _ => rfl) _ (fine_nonempty A hA)).toHom = _
  rw [← aSubnerveComparisonHom_factorization]
  exact b_subset_square A hA

end AAT.AG.AtlasCoefficientFiber.WitnessOne
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessOne.a_evaluation_equiv
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessOne.a_evaluation_equiv_toHom
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessOne.a_P_named_equiv
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessOne.a_epsilon_square
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessOne.a_eta_square
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessOne.b_evaluation_equiv
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessOne.b_evaluation_equiv_toHom
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessOne.b_P_named_equiv
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessOne.b_epsilon_square
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessOne.b_eta_square
#assert_standard_axioms_only AAT.AG.AtlasCoefficientFiber.WitnessOne
