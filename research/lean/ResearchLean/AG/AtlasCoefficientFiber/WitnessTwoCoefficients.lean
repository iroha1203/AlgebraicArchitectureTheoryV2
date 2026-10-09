import ResearchLean.AG.AtlasCoefficientFiber.WitnessTwoInput
import ResearchLean.AG.AtlasCoefficientFiber.WitnessFullSupport
import ResearchLean.AG.AtlasCoefficientFiber.LocalPreservation
import ResearchLean.AG.AtlasCoefficientFiber.WitnessOneCoefficients

/-!
# G-135 W2：原局所成分からηの次数別同型

## Implementation notes

Φのk loopの両端点射を保持し、全対象へのzigzagから元成分商を計算する。
原induced incidence圏を採用し、セル包含半順序への置換はloopの二端点射を失うため採らない。
-/
noncomputable section
namespace AAT.AG.AtlasCoefficientFiber.WitnessTwo
open CategoryTheory CanonicalResolution ResolutionInvariance TwoPhase FaceRelationSubdivision
open WitnessCommon WitnessFullSupport AtlasDefectComposition

/-- 原Φ chartは一つの原細chartと両逆対応する。 -/
def phiChartEquiv (A : Set Bool) (c : Nc.ChartInTargetSubset A) : PhiChart M A c ≃ Fin 1 := by
  have hA : A.Nonempty := by obtain ⟨t,ht,ha⟩ := c.2; exact ⟨t,ha⟩
  exact {
    toFun v := v.1.1
    invFun i := ⟨fullSelected Nf.chartSupport (fun _ => rfl) _ (fine_nonempty A hA) i,by
      apply Subtype.ext; exact Subsingleton.elim _ _⟩
    left_inv v := by apply Subtype.ext; apply Subtype.ext; rfl
    right_inv _ := rfl }
/-- 元Φ chart名の唯一性、h loopを垂直辺に含めない。 -/
theorem phiChart_subsingleton (A : Set Bool) (c : Nc.ChartInTargetSubset A) :
    Subsingleton (PhiChart M A c) := (phiChartEquiv A c).subsingleton_congr.mpr inferInstance
/-- 元Φの全対象は同じchartから元射のzigzagで到達する。 -/
theorem phi_zigzag (A : Set Bool) (c : Nc.ChartInTargetSubset A) (x : PhiInc M A c) :
    @Zigzag (PhiInc M A c) inferInstance (Sum.inl ((phiChartEquiv A c).symm 0)) x := by
  letI : Category (PhiInc M A c) := InducedCategory.instCategory
  letI := phiChart_subsingleton A c
  rcases x with v | (e | f)
  · have he : (phiChartEquiv A c).symm 0 = v := Subsingleton.elim _ _
    rw [he]
  · have he : (phiChartEquiv A c).symm 0 = phiEndpoint M A e false := Subsingleton.elim _ _
    rw [he]
    let f : InducedCategory.Hom (F := phiCellObj M A c)
        (Sum.inl (phiEndpoint M A e false)) (Sum.inr (Sum.inl e)) :=
      ⟨IncHom.chartEdge (phiEndpoint M A e false).1 e.1 false rfl⟩
    exact @Zigzag.of_hom (PhiInc M A c) InducedCategory.instCategory _ _ f
  · exact Fin.elim0 f.1.1
/-- 原Φ成分の非空性と単一性。射を減らさず原商で計算する。 -/
theorem phi_components (A : Set Bool) (c : Nc.ChartInTargetSubset A) :
    Nonempty (ConnectedComponents (PhiInc M A c)) ∧ Subsingleton (ConnectedComponents (PhiInc M A c)) := by
  refine ⟨⟨CategoryTheory.ConnectedComponents.mk (Sum.inl ((phiChartEquiv A c).symm 0) : PhiInc M A c)⟩,?_⟩
  constructor
  intro x y
  induction x using Quotient.inductionOn with | h x =>
    induction y using Quotient.inductionOn with | h y =>
      exact Quotient.sound ((phi_zigzag A c x).symm.trans (phi_zigzag A c y))
/-- 原Γ_h頂点は指定h一本と両逆対応する。 -/
def gammaVertexEquiv (A : Set Bool) (e : Nc.EdgeInTargetSubset A) : GammaVertex M A e ≃ Fin 1 := by
  have hA : A.Nonempty := by obtain ⟨t,ht,ha⟩ := e.2; exact ⟨t,ha⟩
  exact {
    toFun _ := 0
    invFun _ := ⟨fullSelected Nf.edgeSupport (fullSupport_edge Nf (fun _ => rfl))
      _ (fine_nonempty A hA) 0, by have he : e.1 = 0 := Subsingleton.elim _ _; rw [he]; rfl⟩
    left_inv v := by
      apply Subtype.ext; apply Subtype.ext
      rcases v with ⟨⟨v,hv⟩,hm⟩
      fin_cases v
      · rfl
      · simp [M] at hm
    right_inv i := Subsingleton.elim _ _ }
/-- 面なしの原Γ対象は同じmapped辺名と両逆対応する。 -/
def gammaObjectEquiv (A : Set Bool) (e : Nc.EdgeInTargetSubset A) : GammaInc M A e ≃ GammaVertex M A e where
  toFun x := match x with | .inl v => v | .inr f => Fin.elim0 f.1.1
  invFun := Sum.inl
  left_inv x := by rcases x with v | f; rfl; exact Fin.elim0 f.1.1
  right_inv _ := rfl
/-- Γ_h原成分は一つ、面なしから全対象唯一性を生成。 -/
theorem gamma_components (A : Set Bool) (e : Nc.EdgeInTargetSubset A) :
    Nonempty (ConnectedComponents (GammaInc M A e)) ∧ Subsingleton (ConnectedComponents (GammaInc M A e)) := by
  let eqv := (gammaObjectEquiv A e).trans (gammaVertexEquiv A e)
  letI : Subsingleton (GammaInc M A e) := eqv.subsingleton_congr.mpr inferInstance
  let ecomp := WitnessOne.componentsEquivOfHomEq (GammaInc M A e) (fun _ => Subsingleton.elim _ _)
  exact ⟨⟨ecomp.symm (eqv.symm 0)⟩,ecomp.subsingleton_congr.mpr inferInstance⟩
/-- 原Λ条件は粗面なしから任意Aで生成される。 -/
theorem lambda_components (A : Set Bool) (F : Nc.FaceInTargetSubset A) :
    Nonempty (LambdaFace M A F) ∧ Subsingleton (LambdaFace M A F) := Fin.elim0 F.1
/-- 原局所Kanの単一成分から原η全三次数の両逆を構成。 -/
def etaEquiv (A : Set Bool) : ThreeCochainComplex.CochainEquiv
    (Nc.targetSubsetComplex A) (pushforwardComplex M A) :=
  localUnitEquiv M A (phi_components A) (gamma_components A) (lambda_components A)
/-- 生成η同型の全Homは独立原unitHomそのもの。 -/
@[simp] theorem etaEquiv_toHom (A : Set Bool) : (etaEquiv A).toHom = unitHom M A := rfl
/-- 元H¹ηも任意Aで同型、全次数同型から生成。 -/
theorem unit_bijective (A : Set Bool) : Function.Bijective (unitH1 M A) :=
  unitH1_bijective_of_local M A (phi_components A) (gamma_components A) (lambda_components A)
/-- 原a=ηH¹の核余核は00。実uの余核とは区別する。 -/
theorem unit_defect (A : Set Bool) : blockDefect (unitH1 M A) = (0,0) := by
  rw [blockDefect_eq_zero_iff_bijective]
  exact unit_bijective A
/-- 同原ε∘ηは独立原uの全三成分である。 -/
theorem eta_epsilon_square (A : Set Bool) : cochainComp (etaEquiv A).toHom (evaluationHom M A) =
    M.aSubnerveComparisonHom A := by
  rw [etaEquiv_toHom]
  exact (aSubnerveComparisonHom_factorization M A).symm

end AAT.AG.AtlasCoefficientFiber.WitnessTwo
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessTwo.phiChartEquiv
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessTwo.phiChart_subsingleton
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessTwo.phi_zigzag
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessTwo.phi_components
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessTwo.gammaVertexEquiv
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessTwo.gammaObjectEquiv
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessTwo.gamma_components
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessTwo.lambda_components
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessTwo.etaEquiv
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessTwo.etaEquiv_toHom
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessTwo.unit_bijective
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessTwo.unit_defect
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessTwo.eta_epsilon_square
#assert_standard_axioms_only AAT.AG.AtlasCoefficientFiber.WitnessTwo
