import ResearchLean.AG.AtlasCoefficientFiber.WitnessFiveInput
import ResearchLean.AG.AtlasCoefficientFiber.WitnessFullSupport
import ResearchLean.AG.AtlasCoefficientFiber.LocalPreservation

/-!
# G-135 W5：原incidence圏からのKan係数

## Implementation notes

loopの両chart端点射と混在面の二辺位置射を保持し、全対象のzigzagで成分を計算する。
原Γを離散頂点だけへ交換する案はmの閉路を失うため採用しない。
-/
noncomputable section
namespace AAT.AG.AtlasCoefficientFiber.WitnessFive
open CategoryTheory CanonicalResolution ResolutionInvariance TwoPhase FaceRelationSubdivision
open WitnessCommon WitnessFullSupport AtlasDefectComposition

/-- 同原chart写像のfiber chartは唯一の細chart。 -/
def phiChartEquiv (A : Set Bool) (c : Nc.ChartInTargetSubset A) : PhiChart M A c ≃ Unit := by
  have hA : A.Nonempty := by obtain ⟨t,ht,ha⟩ := c.2; exact ⟨t,ha⟩
  exact {
    toFun _ := ()
    invFun _ := ⟨fullSelected Nf.chartSupport (fun _ => rfl) _ (fine_nonempty A hA) (),by
      apply Subtype.ext; exact Subsingleton.elim _ _⟩
    left_inv v := by apply Subtype.ext; apply Subtype.ext; exact Subsingleton.elim _ _
    right_inv _ := Subsingleton.elim _ _ }
/-- 元Φ chartの唯一性。原loop辺の二端点射は保持する。 -/
theorem phiChart_subsingleton (A : Set Bool) (c : Nc.ChartInTargetSubset A) :
    Subsingleton (PhiChart M A c) := (phiChartEquiv A c).subsingleton_congr.mpr inferInstance
/-- 原mの位置1はmapped eなので垂直面にはならない。 -/
theorem phiFace_empty (A : Set Bool) (c : Nc.ChartInTargetSubset A) : IsEmpty (PhiFace M A c) where
  false f := by
    have h1 := f.2.2.2.1
    simp only [edgeMap_e,Option.some_ne_none] at h1
/-- 全Φ対象は原chartEdgeの射で唯一chartへ連結する。 -/
theorem phi_zigzag (A : Set Bool) (c : Nc.ChartInTargetSubset A) (x : PhiInc M A c) :
    @Zigzag (PhiInc M A c) inferInstance (Sum.inl ((phiChartEquiv A c).symm ())) x := by
  letI : Category (PhiInc M A c) := InducedCategory.instCategory
  letI := phiChart_subsingleton A c
  rcases x with v | (e | f)
  · have he : (phiChartEquiv A c).symm () = v := Subsingleton.elim _ _
    rw [he]
  · have he : (phiChartEquiv A c).symm () = phiEndpoint M A e false := Subsingleton.elim _ _
    rw [he]
    let f : InducedCategory.Hom (F := phiCellObj M A c)
        (Sum.inl (phiEndpoint M A e false)) (Sum.inr (Sum.inl e)) :=
      ⟨IncHom.chartEdge (phiEndpoint M A e false).1 e.1 false rfl⟩
    exact @Zigzag.of_hom (PhiInc M A c) InducedCategory.instCategory _ _ f
  · exact False.elim ((phiFace_empty A c).false f)
/-- 同原Φ成分商は非空単一。H¹の零性を主張する条件ではない。 -/
theorem phi_components (A : Set Bool) (c : Nc.ChartInTargetSubset A) :
    Nonempty (ConnectedComponents (PhiInc M A c)) ∧ Subsingleton (ConnectedComponents (PhiInc M A c)) := by
  refine ⟨⟨CategoryTheory.ConnectedComponents.mk (Sum.inl ((phiChartEquiv A c).symm ()) : PhiInc M A c)⟩,?_⟩
  constructor
  intro x y
  induction x using Quotient.inductionOn with | h x =>
    induction y using Quotient.inductionOn with | h y =>
      exact Quotient.sound ((phi_zigzag A c x).symm.trans (phi_zigzag A c y))

/-- 原Option表から各Γの同名e/h liftを全両逆で生成する。 -/
def gammaVertexEquiv (A : Set Bool) (e : Nc.EdgeInTargetSubset A) : GammaVertex M A e ≃ Unit := by
  have hA : A.Nonempty := by obtain ⟨t,ht,ha⟩ := e.2; exact ⟨t,ha⟩
  exact {
    toFun _ := ()
    invFun _ := ⟨fullSelected Nf.edgeSupport (fullSupport_edge Nf (fun _ => rfl))
      _ (fine_nonempty A hA) (Fin.castLE (by decide) e.1),
      (edgeMap_some_iff _ _).mpr rfl⟩
    left_inv v := by
      apply Subtype.ext; apply Subtype.ext
      exact ((edgeMap_some_iff _ _).mp v.2).symm
    right_inv _ := Subsingleton.elim _ _ }
/-- 元Γ頂点は唯一。混在面mやその二位置射は消去しない。 -/
theorem gammaVertex_subsingleton (A : Set Bool) (e : Nc.EdgeInTargetSubset A) :
    Subsingleton (GammaVertex M A e) := (gammaVertexEquiv A e).subsingleton_congr.mpr inferInstance
/-- Γの全関係面を原位置1のedgeFace射で同頂点に接続する。 -/
theorem gamma_zigzag (A : Set Bool) (e : Nc.EdgeInTargetSubset A) (x : GammaInc M A e) :
    @Zigzag (GammaInc M A e) inferInstance (Sum.inl ((gammaVertexEquiv A e).symm ())) x := by
  letI : Category (GammaInc M A e) := InducedCategory.instCategory
  letI := gammaVertex_subsingleton A e
  rcases x with v | f
  · have he : (gammaVertexEquiv A e).symm () = v := Subsingleton.elim _ _
    rw [he]
  · have he : (gammaVertexEquiv A e).symm () = gammaSource M A f := Subsingleton.elim _ _
    rw [he]
    let ff : InducedCategory.Hom (F := gammaCellObj M A e)
        (Sum.inl (gammaSource M A f)) (Sum.inr f) :=
      ⟨IncHom.edgeFace (gammaSource M A f).1 f.1 1 rfl⟩
    exact @Zigzag.of_hom (GammaInc M A e) InducedCategory.instCategory _ _ ff
/-- 同原Γ全成分商は各e/h上で一つ。 -/
theorem gamma_components (A : Set Bool) (e : Nc.EdgeInTargetSubset A) :
    Nonempty (ConnectedComponents (GammaInc M A e)) ∧ Subsingleton (ConnectedComponents (GammaInc M A e)) := by
  refine ⟨⟨CategoryTheory.ConnectedComponents.mk (Sum.inl ((gammaVertexEquiv A e).symm ()) : GammaInc M A e)⟩,?_⟩
  constructor
  intro x y
  induction x using Quotient.inductionOn with | h x =>
    induction y using Quotient.inductionOn with | h y =>
      exact Quotient.sound ((gamma_zigzag A e x).symm.trans (gamma_zigzag A e y))
/-- 原粗面がないのでΛ条件は全Aで生成される。 -/
theorem lambda_components (A : Set Bool) (F : Nc.FaceInTargetSubset A) :
    Nonempty (LambdaFace M A F) ∧ Subsingleton (LambdaFace M A F) := Empty.elim F.1
/-- 原Kanの局所成分から同じη全三次数の両逆を構成。 -/
def etaEquiv (A : Set Bool) : ThreeCochainComplex.CochainEquiv
    (Nc.targetSubsetComplex A) (pushforwardComplex M A) :=
  localUnitEquiv M A (phi_components A) (gamma_components A) (lambda_components A)
/-- 出力同型のHomは同じ原unitそのもの。 -/
@[simp] theorem etaEquiv_toHom (A : Set Bool) : (etaEquiv A).toHom = unitHom M A := rfl
/-- 原a=H¹ηの両方向可逆性を全Aで生成。 -/
theorem unit_bijective (A : Set Bool) : Function.Bijective (unitH1 M A) :=
  unitH1_bijective_of_local M A (phi_components A) (gamma_components A) (lambda_components A)
/-- 原aの実欠損は全Aで零。 -/
theorem unit_defect (A : Set Bool) : blockDefect (unitH1 M A) = (0,0) :=
  (blockDefect_eq_zero_iff_bijective _).mpr (unit_bijective A)
/-- 全三成分ηεは独立に生成された原u。 -/
theorem eta_epsilon_square (A : Set Bool) : cochainComp (etaEquiv A).toHom (evaluationHom M A) =
    M.aSubnerveComparisonHom A := by
  rw [etaEquiv_toHom]
  exact (aSubnerveComparisonHom_factorization M A).symm

end AAT.AG.AtlasCoefficientFiber.WitnessFive
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessFive.phiChartEquiv
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessFive.phiChart_subsingleton
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessFive.phiFace_empty
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessFive.phi_zigzag
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessFive.phi_components
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessFive.gammaVertexEquiv
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessFive.gammaVertex_subsingleton
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessFive.gamma_zigzag
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessFive.gamma_components
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessFive.lambda_components
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessFive.etaEquiv
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessFive.etaEquiv_toHom
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessFive.unit_bijective
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessFive.unit_defect
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessFive.eta_epsilon_square
#assert_standard_axioms_only AAT.AG.AtlasCoefficientFiber.WitnessFive
