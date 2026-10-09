import ResearchLean.AG.AtlasCoefficientFiber.WitnessThreeInput
import ResearchLean.AG.AtlasCoefficientFiber.WitnessOneCoefficients
import ResearchLean.AG.AtlasCoefficientFiber.LocalPreservation

/-!
# G-135 W3：元incidence圏の局所成分

## Implementation notes

元full induced圏の連結成分を原Option表とincidence射で計算する。
薄い包含半順序への交換はloop/重複incidenceを失うため採らない。
-/
noncomputable section
namespace AAT.AG.AtlasCoefficientFiber.WitnessThree
open CategoryTheory CanonicalResolution ResolutionInvariance TwoPhase FaceRelationSubdivision
open WitnessCommon WitnessFullSupport AtlasDefectComposition

/-- 面ありPhiの唯一chartは原chart恒等写像から生成する。 -/
def phiChartEquiv (A : Set Bool) (c : Nc.ChartInTargetSubset A) : PhiChart M A c ≃ Fin 1 := by
  have hA : A.Nonempty := by obtain ⟨t,ht,ha⟩ := c.2; exact ⟨t,ha⟩
  exact {
    toFun _ := 0
    invFun _ := ⟨fullSelected Nf.chartSupport (fun _ => rfl) _ (fine_nonempty A hA) c.1,by
      apply Subtype.ext; rfl⟩
    left_inv v := by
      apply Subtype.ext; apply Subtype.ext
      change c.1 = v.1.1
      have he := congrArg Subtype.val v.2
      exact he.symm
    right_inv i := Subsingleton.elim _ _ }
/-- 元Phi chartの唯一性。原辺と射を減らす条件ではない。 -/
theorem phiChart_subsingleton (A : Set Bool) (c : Nc.ChartInTargetSubset A) :
    Subsingleton (PhiChart M A c) := (phiChartEquiv A c).subsingleton_congr.mpr inferInstance
/-- 原mはmixedなので全chartで垂直面には入らない。 -/
theorem phiFace_empty (A : Set Bool) (c : Nc.ChartInTargetSubset A) : IsEmpty (PhiFace M A c) where
  false f := by
    rcases f with ⟨⟨f,hf⟩,hn,h0,h1,h2,hc⟩
    fin_cases f <;> simp [M,Nf,fineNerve] at hn h1
/-- 全元Phi対象を、元chartEdge射のzigzagで同じchartへ接続する。 -/
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
  · exact False.elim ((phiFace_empty A c).false f)
/-- 元Phiの全成分商は一成分。 -/
theorem phi_components (A : Set Bool) (c : Nc.ChartInTargetSubset A) :
    Nonempty (ConnectedComponents (PhiInc M A c)) ∧ Subsingleton (ConnectedComponents (PhiInc M A c)) := by
  refine ⟨⟨CategoryTheory.ConnectedComponents.mk (Sum.inl ((phiChartEquiv A c).symm 0) : PhiInc M A c)⟩,?_⟩
  constructor
  intro x y
  induction x using Quotient.inductionOn with | h x =>
    induction y using Quotient.inductionOn with | h y =>
      exact Quotient.sound ((phi_zigzag A c x).symm.trans (phi_zigzag A c y))

/-- mなしでも同じchart恒等写像の全両逆。 -/
def pairedPhiChartEquiv (A : Set Bool) (c : Nc.ChartInTargetSubset A) : PhiChart pairedM A c ≃ Fin 1 := by
  have hA : A.Nonempty := by obtain ⟨t,ht,ha⟩ := c.2; exact ⟨t,ha⟩
  exact {
    toFun _ := 0
    invFun _ := ⟨fullSelected pairedNf.chartSupport (fun _ => rfl) _ (fine_nonempty A hA) c.1,by
      apply Subtype.ext; rfl⟩
    left_inv v := by
      apply Subtype.ext; apply Subtype.ext
      change c.1 = v.1.1
      have he := congrArg Subtype.val v.2
      exact he.symm
    right_inv i := Subsingleton.elim _ _ }
/-- mなし元Phiのchart唯一性。 -/
theorem pairedPhiChart_subsingleton (A : Set Bool) (c : Nc.ChartInTargetSubset A) :
    Subsingleton (PhiChart pairedM A c) := (pairedPhiChartEquiv A c).subsingleton_congr.mpr inferInstance
/-- paired面は全mappedで垂直面がない。 -/
theorem pairedPhiFace_empty (A : Set Bool) (c : Nc.ChartInTargetSubset A) : IsEmpty (PhiFace pairedM A c) where
  false f := by cases f.2.1
/-- mなし原Phiも全対象が同chartからの元射で連結する。 -/
theorem paired_phi_zigzag (A : Set Bool) (c : Nc.ChartInTargetSubset A) (x : PhiInc pairedM A c) :
    @Zigzag (PhiInc pairedM A c) inferInstance (Sum.inl ((pairedPhiChartEquiv A c).symm 0)) x := by
  letI : Category (PhiInc pairedM A c) := InducedCategory.instCategory
  letI := pairedPhiChart_subsingleton A c
  rcases x with v | (e | f)
  · have he : (pairedPhiChartEquiv A c).symm 0 = v := Subsingleton.elim _ _
    rw [he]
  · have he : (pairedPhiChartEquiv A c).symm 0 = phiEndpoint pairedM A e false := Subsingleton.elim _ _
    rw [he]
    let f : InducedCategory.Hom (F := phiCellObj pairedM A c)
        (Sum.inl (phiEndpoint pairedM A e false)) (Sum.inr (Sum.inl e)) :=
      ⟨IncHom.chartEdge (phiEndpoint pairedM A e false).1 e.1 false rfl⟩
    exact @Zigzag.of_hom (PhiInc pairedM A c) InducedCategory.instCategory _ _ f
  · exact False.elim ((pairedPhiFace_empty A c).false f)
/-- mなし元Phi成分も非空単一。 -/
theorem paired_phi_components (A : Set Bool) (c : Nc.ChartInTargetSubset A) :
    Nonempty (ConnectedComponents (PhiInc pairedM A c)) ∧ Subsingleton (ConnectedComponents (PhiInc pairedM A c)) := by
  refine ⟨⟨CategoryTheory.ConnectedComponents.mk (Sum.inl ((pairedPhiChartEquiv A c).symm 0) : PhiInc pairedM A c)⟩,?_⟩
  constructor
  intro x y
  induction x using Quotient.inductionOn with | h x =>
    induction y using Quotient.inductionOn with | h y =>
      exact Quotient.sound ((paired_phi_zigzag A c x).symm.trans (paired_phi_zigzag A c y))

/-- 同粗面Fには同名細面fが唯一存在する。 -/
def lambdaFaceEquiv (A : Set Bool) (F : Nc.FaceInTargetSubset A) : LambdaFace M A F ≃ Fin 1 := by
  have hA : A.Nonempty := by obtain ⟨t,ht,ha⟩ := F.2; exact ⟨t,ha⟩
  exact {
    toFun _ := 0
    invFun _ := ⟨fullSelected Nf.faceSupport (fullSupport_face Nf (fun _ => rfl)) _
      (fine_nonempty A hA) (Fin.castLE (by decide) F.1), by rcases F with ⟨F,hF⟩; fin_cases F <;> rfl⟩
    left_inv f := by
      apply Subtype.ext; apply Subtype.ext
      rcases f with ⟨⟨f,hf⟩,hm⟩
      fin_cases f <;> simp [M] at hm
      · apply Fin.ext; exact (congrArg Fin.val hm).symm
      · apply Fin.ext; exact (congrArg Fin.val hm).symm
    right_inv i := Subsingleton.elim _ _ }
/-- mなし同粗面にも同名細面が唯一存在。 -/
def pairedLambdaFaceEquiv (A : Set Bool) (F : Nc.FaceInTargetSubset A) : LambdaFace pairedM A F ≃ Fin 1 := by
  have hA : A.Nonempty := by obtain ⟨t,ht,ha⟩ := F.2; exact ⟨t,ha⟩
  exact {
    toFun _ := 0
    invFun _ := ⟨fullSelected pairedNf.faceSupport (fullSupport_face pairedNf (fun _ => rfl)) _
      (fine_nonempty A hA) F.1,rfl⟩
    left_inv f := by
      apply Subtype.ext; apply Subtype.ext
      exact (Option.some.inj f.2).symm
    right_inv i := Subsingleton.elim _ _ }

/-- 元Gammaの各粗辺へ最初の同名fine辺を選ぶ。値は原Option表から生成。 -/
def gammaVertexChoice (A : Set Bool) (e : Nc.EdgeInTargetSubset A) : GammaVertex M A e := by
  have hA : A.Nonempty := by obtain ⟨t,ht,ha⟩ := e.2; exact ⟨t,ha⟩
  exact ⟨fullSelected Nf.edgeSupport (fullSupport_edge Nf (fun _ => rfl)) _
    (fine_nonempty A hA) (![0,2,3,4] e.1), by
      rcases e with ⟨e,he⟩; fin_cases e <;> rfl⟩
/-- a上の元混在関係m、両端点a1/a0をそのまま保持。 -/
def gammaM (A : Set Bool) (e : Nc.EdgeInTargetSubset A) (he : e.1 = 0) : GammaEdge M A e := by
  have hA : A.Nonempty := by obtain ⟨t,ht,ha⟩ := e.2; exact ⟨t,ha⟩
  exact ⟨fullSelected Nf.faceSupport (fullSupport_face Nf (fun _ => rfl)) _
    (fine_nonempty A hA) 2, by
      constructor
      · rfl
      · left; simp [M,Nf,fineNerve,he]⟩
/-- 元Gamma全頂点はmの二incidenceを使って同じ選択頂点へ連結する。 -/
theorem gamma_vertex_zigzag (A : Set Bool) (e : Nc.EdgeInTargetSubset A) (v : GammaVertex M A e) :
    @Zigzag (GammaInc M A e) inferInstance (Sum.inl (gammaVertexChoice A e)) (Sum.inl v) := by
  letI : Category (GammaInc M A e) := InducedCategory.instCategory
  rcases v with ⟨⟨v,hv⟩,hm⟩
  fin_cases v <;> simp [M] at hm
  · have heq : gammaVertexChoice A e = ⟨⟨0,hv⟩,by simpa [M] using hm⟩ := by
      apply Subtype.ext; apply Subtype.ext
      change ![0,2,3,4] e.1 = 0
      rw [← hm]; rfl
    rw [heq]
    exact Zigzag.refl _
  · let f := gammaM A e hm.symm
    let fa : InducedCategory.Hom (F := gammaCellObj M A e)
        (Sum.inl (gammaVertexChoice A e)) (Sum.inr f) :=
      ⟨IncHom.edgeFace (gammaVertexChoice A e).1 f.1 2 (by
        apply Subtype.ext
        change ![0,2,3,4] e.1 = 0
        rw [← hm]; rfl)⟩
    let fb : InducedCategory.Hom (F := gammaCellObj M A e)
        (Sum.inl (⟨⟨1,hv⟩,by simpa [M] using hm⟩ : GammaVertex M A e)) (Sum.inr f) :=
      ⟨IncHom.edgeFace _ f.1 1 rfl⟩
    exact (@Zigzag.of_hom (GammaInc M A e) InducedCategory.instCategory _ _ fa).trans
      (@Zigzag.of_hom (GammaInc M A e) InducedCategory.instCategory _ _ fb).symm
  · have heq : gammaVertexChoice A e = ⟨⟨2,hv⟩,by simpa [M] using hm⟩ := by
      apply Subtype.ext; apply Subtype.ext
      change ![0,2,3,4] e.1 = 2
      rw [← hm]; rfl
    rw [heq]
    exact Zigzag.refl _
  · have heq : gammaVertexChoice A e = ⟨⟨3,hv⟩,by simpa [M] using hm⟩ := by
      apply Subtype.ext; apply Subtype.ext
      change ![0,2,3,4] e.1 = 3
      rw [← hm]; rfl
    rw [heq]
    exact Zigzag.refl _
  · have heq : gammaVertexChoice A e = ⟨⟨4,hv⟩,by simpa [M] using hm⟩ := by
      apply Subtype.ext; apply Subtype.ext
      change ![0,2,3,4] e.1 = 4
      rw [← hm]; rfl
    rw [heq]
    exact Zigzag.refl _
/-- 元Gammaの全対象を連結する。関係faceは元edgeFace射で接続する。 -/
theorem gamma_zigzag (A : Set Bool) (e : Nc.EdgeInTargetSubset A) (x : GammaInc M A e) :
    @Zigzag (GammaInc M A e) inferInstance (Sum.inl (gammaVertexChoice A e)) x := by
  letI : Category (GammaInc M A e) := InducedCategory.instCategory
  rcases x with v | f
  · exact gamma_vertex_zigzag A e v
  · let ff : InducedCategory.Hom (F := gammaCellObj M A e)
        (Sum.inl (gammaSource M A f)) (Sum.inr f) :=
      ⟨IncHom.edgeFace (gammaSource M A f).1 f.1 1 rfl⟩
    exact (gamma_vertex_zigzag A e (gammaSource M A f)).trans
      (@Zigzag.of_hom (GammaInc M A e) InducedCategory.instCategory _ _ ff)
/-- 面あり元Gammaの全成分商は各粗辺上で一成分。 -/
theorem gamma_components (A : Set Bool) (e : Nc.EdgeInTargetSubset A) :
    Nonempty (ConnectedComponents (GammaInc M A e)) ∧ Subsingleton (ConnectedComponents (GammaInc M A e)) := by
  refine ⟨⟨CategoryTheory.ConnectedComponents.mk (Sum.inl (gammaVertexChoice A e) : GammaInc M A e)⟩,?_⟩
  constructor
  intro x y
  induction x using Quotient.inductionOn with | h x =>
    induction y using Quotient.inductionOn with | h y =>
      exact Quotient.sound ((gamma_zigzag A e x).symm.trans (gamma_zigzag A e y))
/-- 元面liftは同名唯一であり原局所単位の条件を満たす。 -/
theorem lambda_components (A : Set Bool) (F : Nc.FaceInTargetSubset A) :
    Nonempty (LambdaFace M A F) ∧ Subsingleton (LambdaFace M A F) :=
  ⟨⟨(lambdaFaceEquiv A F).symm 0⟩,(lambdaFaceEquiv A F).subsingleton_congr.mpr inferInstance⟩
/-- 元Kanの各局所単一成分から面ありη全三次数の両逆を生成。 -/
def etaEquiv (A : Set Bool) : ThreeCochainComplex.CochainEquiv
    (Nc.targetSubsetComplex A) (pushforwardComplex M A) :=
  localUnitEquiv M A (phi_components A) (gamma_components A) (lambda_components A)
/-- この同型は元unitHomそのもの。 -/
@[simp] theorem etaEquiv_toHom (A : Set Bool) : (etaEquiv A).toHom = unitHom M A := rfl
/-- 同面ありa=元ηH¹は全Aで同型。 -/
theorem unit_bijective (A : Set Bool) : Function.Bijective (unitH1 M A) :=
  unitH1_bijective_of_local M A (phi_components A) (gamma_components A) (lambda_components A)
/-- 同面ありηの実欠損00。 -/
theorem unit_defect (A : Set Bool) : blockDefect (unitH1 M A) = (0,0) :=
  (blockDefect_eq_zero_iff_bijective _).mpr (unit_bijective A)

/-- mなしΓ関係面は元some面表から空。 -/
theorem pairedGammaEdge_empty (A : Set Bool) (e : Nc.EdgeInTargetSubset A) :
    IsEmpty (GammaEdge pairedM A e) where
  false f := by cases f.2.1
/-- mなし原Γの射は元辺名を保つ。fineの二面は原Γへ入らない。 -/
theorem paired_gamma_hom_eq (A : Set Bool) (e : Nc.EdgeInTargetSubset A)
    {x y : GammaInc pairedM A e} (f : x ⟶ y) : x = y := by
  rcases x with v | r
  · rcases y with w | s
    · exact congrArg Sum.inl (Subtype.ext (incHom_edge_edge_target v.1 w.1 f.hom).symm)
    · exact False.elim ((pairedGammaEdge_empty A e).false s)
  · exact False.elim ((pairedGammaEdge_empty A e).false r)
/-- 元mなしΓ対象と原mapped辺liftの両逆。 -/
def pairedGammaObjectEquiv (A : Set Bool) (e : Nc.EdgeInTargetSubset A) :
    GammaInc pairedM A e ≃ GammaVertex pairedM A e where
  toFun x := match x with | .inl v => v | .inr r => False.elim ((pairedGammaEdge_empty A e).false r)
  invFun := Sum.inl
  left_inv x := by
    rcases x with v | r
    · rfl
    · exact False.elim ((pairedGammaEdge_empty A e).false r)
  right_inv _ := rfl
/-- 原mなしΓ成分商は同じlift名をそのまま保持。 -/
def pairedGammaComponentsEquiv (A : Set Bool) (e : Nc.EdgeInTargetSubset A) :
    ConnectedComponents (GammaInc pairedM A e) ≃ GammaVertex pairedM A e :=
  (WitnessOne.componentsEquivOfHomEq _ (paired_gamma_hom_eq A e)).trans (pairedGammaObjectEquiv A e)
/-- 原Kan辺係数と原lift全関数の両逆。 -/
def pairedGammaCoefficientEquiv (A : Set Bool) (e : Nc.EdgeInTargetSubset A) :
    (pushforwardCoefficients pairedM A).obj (.edge e) ≃ₗ[ℚ] (GammaVertex pairedM A e → ℚ) :=
  (gammaCoefficientEquiv pairedM A e).trans
    (LinearEquiv.piCongrLeft' ℚ (fun _ : ConnectedComponents (GammaInc pairedM A e) => ℚ)
      (pairedGammaComponentsEquiv A e))
/-- 原aの二lift a0/a1を両逆で区別。 -/
def pairedAVerticesEquiv (A : Set Bool) (hA : A.Nonempty) :
    GammaVertex pairedM A (fullSelected Nc.edgeSupport (fullSupport_edge Nc (fun _ => rfl)) A hA 0) ≃ Fin 2 where
  toFun v := ⟨v.1.1.val,by
    rcases v with ⟨⟨v,hs⟩,hv⟩
    fin_cases v <;> simp [pairedM,M] at hv ⊢⟩
  invFun i := ⟨fullSelected pairedNf.edgeSupport (fullSupport_edge pairedNf (fun _ => rfl))
    _ (fine_nonempty A hA) (Fin.castLE (by decide) i),by fin_cases i <;> rfl⟩
  left_inv v := by apply Subtype.ext; apply Subtype.ext; apply Fin.ext; rfl
  right_inv i := by apply Fin.ext; rfl
/-- 二原liftからの実a係数ℚ²。 -/
def pairedACoefficientEquiv (A : Set Bool) (hA : A.Nonempty) :
    (pushforwardCoefficients pairedM A).obj
      (.edge (fullSelected Nc.edgeSupport (fullSupport_edge Nc (fun _ => rfl)) A hA 0)) ≃ₗ[ℚ] (Fin 2 → ℚ) :=
  (pairedGammaCoefficientEquiv A _).trans
    (LinearEquiv.piCongrLeft' ℚ (fun _ : GammaVertex pairedM A _ => ℚ) (pairedAVerticesEquiv A hA))
/-- 原ηのa成分は同二liftで対角。 -/
theorem paired_a_unit_diagonal (A : Set Bool) (hA : A.Nonempty) (q : ℚ) :
    pairedACoefficientEquiv A hA (coefficientConstant (Carrier.preimageFunctor pairedM A)
      (.edge (fullSelected Nc.edgeSupport (fullSupport_edge Nc (fun _ => rfl)) A hA 0)) q) = fun _ => q := by
  funext i
  exact gammaCoefficientConstant_apply pairedM A _ q _

end AAT.AG.AtlasCoefficientFiber.WitnessThree
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessThree.phiChartEquiv
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessThree.phiChart_subsingleton
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessThree.phiFace_empty
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessThree.phi_zigzag
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessThree.phi_components
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessThree.pairedPhiChartEquiv
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessThree.pairedPhiChart_subsingleton
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessThree.pairedPhiFace_empty
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessThree.paired_phi_zigzag
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessThree.paired_phi_components
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessThree.lambdaFaceEquiv
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessThree.pairedLambdaFaceEquiv
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessThree.gammaVertexChoice
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessThree.gammaM
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessThree.gamma_vertex_zigzag
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessThree.gamma_zigzag
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessThree.gamma_components
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessThree.lambda_components
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessThree.etaEquiv
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessThree.etaEquiv_toHom
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessThree.unit_bijective
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessThree.unit_defect
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessThree.pairedGammaEdge_empty
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessThree.paired_gamma_hom_eq
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessThree.pairedGammaObjectEquiv
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessThree.pairedGammaComponentsEquiv
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessThree.pairedGammaCoefficientEquiv
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessThree.pairedAVerticesEquiv
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessThree.pairedACoefficientEquiv
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessThree.paired_a_unit_diagonal
#assert_standard_axioms_only AAT.AG.AtlasCoefficientFiber.WitnessThree
