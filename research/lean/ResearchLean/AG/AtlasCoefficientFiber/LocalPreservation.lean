import ResearchLean.AG.AtlasCoefficientFiber.LocalCoefficientSingle
import ResearchLean.AG.AtlasCoefficientFiber.DefectDiagnostics

/-!
# G-135 C：原ηの次数別同型と局所保存

## Implementation notes

原Φ・Γ・Λの単一成分から各係数写像の両逆を生成し、既存微分可換性を使う。
H¹の零性は別の方向仮定として扱い、高次fiberの仮定を追加しない。
-/
noncomputable section
namespace AAT.AG.AtlasCoefficientFiber
open CategoryTheory CanonicalResolution ResolutionInvariance FaceRelationSubdivision TwoPhase
open AtlasDefectComposition
universe u
variable {Source : Type u} {qc qf : Reading Source} {h : qc.CoarserThan qf}
variable {Nc : TargetSupportedNerve.{u,u} qc} {Nf : TargetSupportedNerve.{u,u} qf}
variable (M : IncidenceSupportedComparison qc qf h Nc Nf) (A : Set qc.Target)
variable
  (hPhi : ∀ c : Nc.ChartInTargetSubset A,
    Nonempty (ConnectedComponents (PhiInc M A c)) ∧
      Subsingleton (ConnectedComponents (PhiInc M A c)))
  (hGamma : ∀ e : Nc.EdgeInTargetSubset A,
    Nonempty (ConnectedComponents (GammaInc M A e)) ∧
      Subsingleton (ConnectedComponents (GammaInc M A e)))
  (hLambda : ∀ F : Nc.FaceInTargetSubset A,
    Nonempty (LambdaFace M A F) ∧ Subsingleton (LambdaFace M A F))

/-- 局所単一成分から原ηの全三次数同型を入力生成する。 -/
def localUnitEquiv : ThreeCochainComplex.CochainEquiv
    (Nc.targetSubsetComplex A) (pushforwardComplex M A) where
  e0 := LinearEquiv.piCongrRight fun c =>
    LinearEquiv.ofBijective _ (chartCoefficientConstant_bijective M A c
      (hPhi c).1 (hPhi c).2)
  e1 := LinearEquiv.piCongrRight fun e =>
    LinearEquiv.ofBijective _ (edgeCoefficientConstant_bijective M A e
      (hGamma e).1 (hGamma e).2)
  e2 := LinearEquiv.piCongrRight fun F =>
    LinearEquiv.ofBijective _ (faceCoefficientConstant_bijective M A F
      (hLambda F).1 (hLambda F).2)
  comm0 := unit_comm0 M A
  comm1 := unit_comm1 M A

/-- 生成同型の次数0順写像は原ηの同じ値を取る。 -/
@[simp] theorem localUnitEquiv_e0_apply (z : (Nc.targetSubsetComplex A).C0) :
    (localUnitEquiv M A hPhi hGamma hLambda).e0 z = unit0 M A z := rfl

/-- 生成同型の次数1順写像は原ηの同じ値を取る。 -/
@[simp] theorem localUnitEquiv_e1_apply (z : (Nc.targetSubsetComplex A).C1) :
    (localUnitEquiv M A hPhi hGamma hLambda).e1 z = unit1 M A z := rfl

/-- 生成同型の次数2順写像は原ηの同じ値を取る。 -/
@[simp] theorem localUnitEquiv_e2_apply (z : (Nc.targetSubsetComplex A).C2) :
    (localUnitEquiv M A hPhi hGamma hLambda).e2 z = unit2 M A z := rfl

/-- 両逆を持つ生成cochain同型の順Homは全成分で原unitHomと同じである。 -/
@[simp] theorem localUnitEquiv_toHom :
    (localUnitEquiv M A hPhi hGamma hLambda).toHom = unitHom M A := rfl

include hPhi hGamma hLambda in
/-- 局所成分条件から原標準H¹ηの同型性を生成する。 -/
theorem unitH1_bijective_of_local : Function.Bijective (unitH1 M A) := by
  have ho := (localUnitEquiv M A hPhi hGamma hLambda).toHom_h1Map_bijective
  rw [localUnitEquiv_toHom] at ho
  rw [unitH1_eq_standard]
  exact (LinearConjugation.bijective_iff _ _ (oldH1Equiv _) (oldH1Equiv _)
    (oldH1Equiv_natural (unitHom M A))).mp ho

/-- 全実Φ H¹が零なら、実κ*核Rからのτは単射となる。 -/
theorem connectingTau_injective_of_phiH1_zero
    (hz : ∀ c : Nc.ChartInTargetSubset A, Subsingleton (phiComplex M A c).H1) :
    Function.Injective (connectingTau M A) := by
  letI : ∀ c : Nc.ChartInTargetSubset A, Subsingleton (phiComplex M A c).H1 := hz
  exact Function.injective_of_subsingleton _

include hPhi hGamma hLambda in
/-- 局所成分条件と全Φ H¹零から同じ旧診断の零性を導く。 -/
theorem local_zeroDefect
    (hz : ∀ c : Nc.ChartInTargetSubset A, Subsingleton (phiComplex M A c).H1) :
    blockDefect (M.aSubnerveComparisonHom A).h1Map = (0,0) :=
  (coefficient_zeroDefect_iff M A).mpr
    ⟨unitH1_bijective_of_local M A hPhi hGamma hLambda,
      connectingTau_injective_of_phiH1_zero M A hz⟩

end AAT.AG.AtlasCoefficientFiber

#print axioms AAT.AG.AtlasCoefficientFiber.localUnitEquiv
#print axioms AAT.AG.AtlasCoefficientFiber.localUnitEquiv_e0_apply
#print axioms AAT.AG.AtlasCoefficientFiber.localUnitEquiv_e1_apply
#print axioms AAT.AG.AtlasCoefficientFiber.localUnitEquiv_e2_apply
#print axioms AAT.AG.AtlasCoefficientFiber.localUnitEquiv_toHom
#print axioms AAT.AG.AtlasCoefficientFiber.unitH1_bijective_of_local
#print axioms AAT.AG.AtlasCoefficientFiber.connectingTau_injective_of_phiH1_zero
#print axioms AAT.AG.AtlasCoefficientFiber.local_zeroDefect
#assert_standard_axioms_only AAT.AG.AtlasCoefficientFiber
