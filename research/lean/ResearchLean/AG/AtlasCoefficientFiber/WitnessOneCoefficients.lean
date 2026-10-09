import ResearchLean.AG.AtlasCoefficientFiber.WitnessOneInput
import ResearchLean.AG.AtlasCoefficientFiber.WitnessFullSupport
import ResearchLean.AG.AtlasCoefficientFiber.GammaComma
import ResearchLean.AG.AtlasCoefficientFiber.MappedEvaluation
import ResearchLean.AG.AtlasCoefficientFiber.LocalCoefficientSingle

/-!
# G-135 W1：元右Kanのe係数とmapped fiber零性

## Implementation notes

原Γの射から成分同値を生成する。期待する係数空間をKanの定義へ埋め込まない。
W1bはe₀とe₁の名前を保った二座標となる。
-/
noncomputable section
namespace AAT.AG.AtlasCoefficientFiber.WitnessOne
open CategoryTheory CanonicalResolution ResolutionInvariance TwoPhase FaceRelationSubdivision
open WitnessCommon WitnessFullSupport AtlasDefectComposition

/-- 全射が同じ対象を結ぶ圏の元成分商と元対象の両逆。 -/
def componentsEquivOfHomEq (J : Type) [Category J]
    (hd : ∀ {x y : J}, (x ⟶ y) → x = y) : ConnectedComponents J ≃ J where
  toFun := Quotient.lift id (fun _ _ h => invariant_of_zigzag id hd h)
  invFun := CategoryTheory.ConnectedComponents.mk
  left_inv x := by induction x using Quotient.inductionOn; rfl
  right_inv _ := rfl

section NoFaces
variable {N : TargetSupportedNerve qf}
variable (M : IncidenceSupportedComparison qc qf coarser Nc N) (A : Set Bool)
variable [IsEmpty N.nerve.FaceComponent]

/-- 面なしでは元Γの原射は頂点名を保つ。 -/
theorem gamma_hom_eq (e : Nc.EdgeInTargetSubset A)
    {x y : GammaInc M A e} (f : x ⟶ y) : x = y := by
  rcases x with v | r
  · rcases y with w | s
    · exact congrArg Sum.inl (Subtype.ext (incHom_edge_edge_target v.1 w.1 f.hom).symm)
    · exact isEmptyElim s.1.1
  · exact isEmptyElim r.1.1

/-- 元Γ対象は面なしで全mapped頂点名と両逆同定。 -/
def gammaObjectEquiv (e : Nc.EdgeInTargetSubset A) : GammaInc M A e ≃ GammaVertex M A e where
  toFun x := match x with | .inl v => v | .inr r => isEmptyElim r.1.1
  invFun := Sum.inl
  left_inv x := by rcases x with v | r; rfl; exact isEmptyElim r.1.1
  right_inv _ := rfl

/-- 元Γ成分は同じ全mapped頂点名を保持する。 -/
def gammaNoFaceComponentsEquiv (e : Nc.EdgeInTargetSubset A) :
    ConnectedComponents (GammaInc M A e) ≃ GammaVertex M A e :=
  (componentsEquivOfHomEq _ (gamma_hom_eq M A e)).trans (gammaObjectEquiv M A e)

/-- 元右Kan係数を原mapped辺の全関数へ移す。 -/
def gammaNoFaceCoefficientEquiv (e : Nc.EdgeInTargetSubset A) :
    (pushforwardCoefficients M A).obj (.edge e) ≃ₗ[ℚ] (GammaVertex M A e → ℚ) :=
  (gammaCoefficientEquiv M A e).trans
    (LinearEquiv.piCongrLeft' ℚ (fun _ : ConnectedComponents (GammaInc M A e) => ℚ)
      (gammaNoFaceComponentsEquiv M A e))

end NoFaces

/-- 指定全台から生成する同じ粗辺。 -/
def coarseEdge (A : Set Bool) (hA : A.Nonempty) (e : Fin 2) : Nc.EdgeInTargetSubset A :=
  fullSelected Nc.edgeSupport (fullSupport_edge Nc (fun _ => rfl)) A hA e

/-- W1a eを持ち上げる原mapped辺は存在しない。 -/
theorem a_e_vertices_empty (A : Set Bool) (hA : A.Nonempty) :
    IsEmpty (GammaVertex Ma A (coarseEdge A hA 0)) := by
  refine ⟨fun v => ?_⟩
  have h : (1 : Fin 2) = 0 := Option.some.inj v.2
  exact (by decide : (1 : Fin 2) ≠ 0) h

/-- W1aの元e順像係数は零空間である。 -/
theorem a_e_coefficient_zero (A : Set Bool) (hA : A.Nonempty) :
    Subsingleton ((pushforwardCoefficients Ma A).obj (.edge (coarseEdge A hA 0))) := by
  letI := a_e_vertices_empty A hA
  exact (gammaNoFaceCoefficientEquiv Ma A (coarseEdge A hA 0)).toEquiv.subsingleton_congr.mpr inferInstance

/-- W1b原eのmapped辺はe₀,e₁と両逆同定する。 -/
def b_e_vertices_equiv (A : Set Bool) (hA : A.Nonempty) :
    GammaVertex Mb A (coarseEdge A hA 0) ≃ Fin 2 where
  toFun v := ⟨v.1.1.val,by
    rcases v with ⟨⟨v,hs⟩,hv⟩
    fin_cases v <;> simp [Mb,coarseEdge] at hv ⊢⟩
  invFun i := ⟨fullSelected Nb.edgeSupport (fullSupport_edge Nb (fun _ => rfl))
    _ (fine_nonempty A hA) i.castSucc,by fin_cases i <;> rfl⟩
  left_inv v := by apply Subtype.ext; apply Subtype.ext; apply Fin.ext; rfl
  right_inv i := by apply Fin.ext; rfl

/-- W1b元e順像係数の二座標、両逆を持ち別名e₀,e₁を保持。 -/
def b_e_coefficient_equiv (A : Set Bool) (hA : A.Nonempty) :
    (pushforwardCoefficients Mb A).obj (.edge (coarseEdge A hA 0)) ≃ₗ[ℚ] (Fin 2 → ℚ) :=
  (gammaNoFaceCoefficientEquiv Mb A (coarseEdge A hA 0)).trans
    (LinearEquiv.piCongrLeft' ℚ (fun _ : GammaVertex Mb A (coarseEdge A hA 0) => ℚ)
      (b_e_vertices_equiv A hA))

/-- 同じ元W1b ηのe成分は二座標の対角写像。 -/
theorem b_e_unit_diagonal (A : Set Bool) (hA : A.Nonempty) (q : ℚ) :
    b_e_coefficient_equiv A hA
      (coefficientConstant (Carrier.preimageFunctor Mb A) (.edge (coarseEdge A hA 0)) q) =
      fun _ => q := by
  funext i
  exact gammaCoefficientConstant_apply Mb A (coarseEdge A hA 0) q _

end AAT.AG.AtlasCoefficientFiber.WitnessOne
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessOne.componentsEquivOfHomEq
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessOne.gamma_hom_eq
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessOne.gammaObjectEquiv
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessOne.gammaNoFaceComponentsEquiv
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessOne.gammaNoFaceCoefficientEquiv
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessOne.coarseEdge
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessOne.a_e_vertices_empty
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessOne.a_e_coefficient_zero
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessOne.b_e_vertices_equiv
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessOne.b_e_coefficient_equiv
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessOne.b_e_unit_diagonal
#assert_standard_axioms_only AAT.AG.AtlasCoefficientFiber.WitnessOne
