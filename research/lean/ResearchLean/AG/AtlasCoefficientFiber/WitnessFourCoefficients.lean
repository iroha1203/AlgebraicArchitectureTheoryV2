import ResearchLean.AG.AtlasCoefficientFiber.WitnessFourTriangle
import ResearchLean.AG.AtlasCoefficientFiber.WitnessOneCoefficients

/-!
# W4：同じ原三角形の二持ち上げと右Kan係数

Implementation notes: 面なしΓの全射を元incidence APIで読む。
対象商を元mapped辺へ両逆同定し、原eの二つの別名を二座標に保つ。
-/
noncomputable section
namespace AAT.AG.AtlasCoefficientFiber.WitnessFourCoefficients
open CategoryTheory CanonicalResolution ResolutionInvariance TwoPhase FaceRelationSubdivision
open FaceRelationSubdivision.WitnessOne (N plus minus qc qf coarser rPlus rMinus)
open AtlasDefectComposition

/-- 面なし原Γの同じ全incidence射は頂点名を保つ。 -/
theorem minus_gamma_hom_eq (A : Set Bool) (e : N.EdgeInTargetSubset A)
    {x y : GammaInc rMinus A e} (f : x ⟶ y) : x = y := by
  rcases x with v | r
  · rcases y with w | s
    · exact congrArg Sum.inl (Subtype.ext (incHom_edge_edge_target v.1 w.1 f.hom).symm)
    · exact isEmptyElim s.1.1
  · exact isEmptyElim r.1.1

/-- 同じ面なし原Γの対象と全mapped辺の両逆。 -/
def minusGammaObjectEquiv (A : Set Bool) (e : N.EdgeInTargetSubset A) :
    GammaInc rMinus A e ≃ GammaVertex rMinus A e where
  toFun x := match x with | .inl v => v | .inr f => isEmptyElim f.1.1
  invFun := Sum.inl
  left_inv x := by rcases x with v | f; rfl; exact isEmptyElim f.1.1
  right_inv _ := rfl

/-- 原Γ商は同じ二liftを統合せず保持する。 -/
def minusGammaComponentsEquiv (A : Set Bool) (e : N.EdgeInTargetSubset A) :
    ConnectedComponents (GammaInc rMinus A e) ≃ GammaVertex rMinus A e :=
  (WitnessOne.componentsEquivOfHomEq _ (minus_gamma_hom_eq A e)).trans
    (minusGammaObjectEquiv A e)

/-- 原右Kanの辺係数を同じ全mapped辺上の関数へ移す。 -/
def minusGammaCoefficientEquiv (A : Set Bool) (e : N.EdgeInTargetSubset A) :
    (pushforwardCoefficients rMinus A).obj (.edge e) ≃ₗ[ℚ] (GammaVertex rMinus A e → ℚ) :=
  (gammaCoefficientEquiv rMinus A e).trans
    (LinearEquiv.piCongrLeft' ℚ (fun _ : ConnectedComponents (GammaInc rMinus A e) => ℚ)
      (minusGammaComponentsEquiv A e))

/-- 原全台から選択する同じ粗辺e。 -/
def coarseE (A : Set Bool) (hA : A.Nonempty) : N.EdgeInTargetSubset A :=
  fullSelected N.edgeSupport FaceRelationSubdivision.WitnessOne.edge_full A hA 0

/-- eの二liftは旧eとfresh e₂、その原Option値から両逆を構成する。 -/
def minusEVerticesEquiv (A : Set Bool) (hA : A.Nonempty) :
    GammaVertex rMinus A (coarseE A hA) ≃ Bool where
  toFun v := match v.1.1 with | .inl _ => false | .inr _ => true
  invFun b := ⟨fullSelected minus.edgeSupport FaceRelationSubdivision.WitnessOne.minus_edge_full _
    (WitnessFullSupport.fine_nonempty A hA) (if b then .inr true else .inl (0 : Fin 2)), by
      cases b <;> rfl⟩
  left_inv v := by
    apply Subtype.ext; apply Subtype.ext
    rcases v with ⟨⟨v,hv⟩,hm⟩
    rw [FaceRelationSubdivision.WitnessOne.rMinus_edge] at hm
    cases v with
    | inl a =>
      have ha : a = (0 : Fin 2) := Option.some.inj hm
      change (Sum.inl (0 : Fin 2) : minus.nerve.EdgeComponent) = .inl a
      rw [ha]
    | inr b =>
      cases b
      · cases hm
      · rfl
  right_inv b := by cases b <;> rfl

/-- 同じ原e右Kan係数の二成分、両逆を保持。 -/
def minusECoefficientEquiv (A : Set Bool) (hA : A.Nonempty) :
    (pushforwardCoefficients rMinus A).obj (.edge (coarseE A hA)) ≃ₗ[ℚ] (Bool → ℚ) :=
  (minusGammaCoefficientEquiv A (coarseE A hA)).trans
    (LinearEquiv.piCongrLeft' ℚ (fun _ : GammaVertex rMinus A (coarseE A hA) => ℚ)
      (minusEVerticesEquiv A hA))

/-- 原ηのe成分は二liftの両方へ同じ値を置く対角写像。 -/
theorem minus_e_unit_diagonal (A : Set Bool) (hA : A.Nonempty) (q : ℚ) :
    minusECoefficientEquiv A hA
      (coefficientConstant (Carrier.preimageFunctor rMinus A) (.edge (coarseE A hA)) q) =
      fun _ => q := by
  funext i
  exact gammaCoefficientConstant_apply rMinus A (coarseE A hA) q _

/-- 面あり原Γの同名old liftは全粗辺で存在する。 -/
def plusGammaChoice (A : Set Bool) (e : N.EdgeInTargetSubset A) : GammaVertex rPlus A e := by
  have hA : A.Nonempty := by obtain ⟨t,ht,ha⟩ := e.2; exact ⟨t,ha⟩
  exact ⟨fullSelected plus.edgeSupport FaceRelationSubdivision.WitnessOne.plus_edge_full _
    (WitnessFullSupport.fine_nonempty A hA) (.inl e.1), rfl⟩

/-- 原fのmixed関係は同じ粗e上の二liftを結ぶ。 -/
def plusGammaF (A : Set Bool) (e : N.EdgeInTargetSubset A) (he : e.1 = 0) :
    GammaEdge rPlus A e := by
  have hA : A.Nonempty := by obtain ⟨t,ht,ha⟩ := e.2; exact ⟨t,ha⟩
  exact ⟨fullSelected plus.faceSupport FaceRelationSubdivision.WitnessOne.plus_face_full _
    (WitnessFullSupport.fine_nonempty A hA) (.inr PUnit.unit), by
      constructor
      · rfl
      · left
        refine ⟨?_, ?_, ?_⟩
        · exact FaceRelationSubdivision.WitnessOne.rPlus_edge_c
        · change rPlus.edgeMap (.inl (0 : Fin 2)) = some e.1
          rw [FaceRelationSubdivision.WitnessOne.rPlus_edge_old, he]
        · change rPlus.edgeMap (.inr true) = some e.1
          rw [FaceRelationSubdivision.WitnessOne.rPlus_edge_e2, he]⟩

/-- 原Γの二liftは元fの二incidenceから同じ成分へ接続する。 -/
theorem plus_gamma_vertex_zigzag (A : Set Bool) (e : N.EdgeInTargetSubset A)
    (v : GammaVertex rPlus A e) :
    @Zigzag (GammaInc rPlus A e) inferInstance (Sum.inl (plusGammaChoice A e)) (Sum.inl v) := by
  letI : Category (GammaInc rPlus A e) := InducedCategory.instCategory
  rcases v with ⟨⟨v,hv⟩,hm⟩
  cases v with
  | inl a =>
    have ha : a = e.1 := Option.some.inj hm
    have heq : plusGammaChoice A e = ⟨⟨.inl a,hv⟩,hm⟩ := by
      apply Subtype.ext; apply Subtype.ext; exact congrArg Sum.inl ha.symm
    rw [heq]
  | inr b =>
    cases b
    · cases hm
    · have he : e.1 = 0 := (Option.some.inj hm).symm
      let f := plusGammaF A e he
      let fa : InducedCategory.Hom (F := gammaCellObj rPlus A e)
          (Sum.inl (plusGammaChoice A e)) (Sum.inr f) :=
        ⟨IncHom.edgeFace (plusGammaChoice A e).1 f.1 1 (by
          apply Subtype.ext; change Sum.inl e.1 = Sum.inl (0 : Fin 2); rw [he])⟩
      let fb : InducedCategory.Hom (F := gammaCellObj rPlus A e)
          (Sum.inl (⟨⟨Sum.inr true,hv⟩,hm⟩ : GammaVertex rPlus A e)) (Sum.inr f) :=
        ⟨IncHom.edgeFace _ f.1 2 rfl⟩
      exact (@Zigzag.of_hom (GammaInc rPlus A e) InducedCategory.instCategory _ _ fa).trans
        (@Zigzag.of_hom (GammaInc rPlus A e) InducedCategory.instCategory _ _ fb).symm

/-- 原Γの関係面も同じ全対象zigzagに含む。 -/
theorem plus_gamma_zigzag (A : Set Bool) (e : N.EdgeInTargetSubset A) (x : GammaInc rPlus A e) :
    @Zigzag (GammaInc rPlus A e) inferInstance (Sum.inl (plusGammaChoice A e)) x := by
  letI : Category (GammaInc rPlus A e) := InducedCategory.instCategory
  rcases x with v | f
  · exact plus_gamma_vertex_zigzag A e v
  · let ff : InducedCategory.Hom (F := gammaCellObj rPlus A e)
        (Sum.inl (gammaSource rPlus A f)) (Sum.inr f) :=
      ⟨IncHom.edgeFace (gammaSource rPlus A f).1 f.1 1 rfl⟩
    exact (plus_gamma_vertex_zigzag A e (gammaSource rPlus A f)).trans
      (@Zigzag.of_hom (GammaInc rPlus A e) InducedCategory.instCategory _ _ ff)

/-- 面ありΓは同じ原二incidenceを保った一成分。 -/
theorem plus_gamma_components (A : Set Bool) (e : N.EdgeInTargetSubset A) :
    Nonempty (ConnectedComponents (GammaInc rPlus A e)) ∧
      Subsingleton (ConnectedComponents (GammaInc rPlus A e)) := by
  refine ⟨⟨CategoryTheory.ConnectedComponents.mk (Sum.inl (plusGammaChoice A e) : GammaInc rPlus A e)⟩,?_⟩
  constructor
  intro x y
  induction x using Quotient.inductionOn with | h x =>
    induction y using Quotient.inductionOn with | h y =>
      exact Quotient.sound ((plus_gamma_zigzag A e x).symm.trans (plus_gamma_zigzag A e y))

/-- 原plus辺η係数の両方向同型はΓの一成分から生成する。 -/
def plusEdgeUnitEquiv (A : Set Bool) (e : N.EdgeInTargetSubset A) :
    ℚ ≃ₗ[ℚ] (pushforwardCoefficients rPlus A).obj (.edge e) :=
  LinearEquiv.ofBijective _ (edgeCoefficientConstant_bijective rPlus A e
    (plus_gamma_components A e).1 (plus_gamma_components A e).2)

end AAT.AG.AtlasCoefficientFiber.WitnessFourCoefficients

#print axioms AAT.AG.AtlasCoefficientFiber.WitnessFourCoefficients.minus_gamma_hom_eq
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessFourCoefficients.minusGammaObjectEquiv
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessFourCoefficients.minusGammaComponentsEquiv
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessFourCoefficients.minusGammaCoefficientEquiv
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessFourCoefficients.coarseE
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessFourCoefficients.minusEVerticesEquiv
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessFourCoefficients.minusECoefficientEquiv
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessFourCoefficients.minus_e_unit_diagonal
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessFourCoefficients.plusGammaChoice
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessFourCoefficients.plusGammaF
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessFourCoefficients.plus_gamma_vertex_zigzag
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessFourCoefficients.plus_gamma_zigzag
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessFourCoefficients.plus_gamma_components
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessFourCoefficients.plusEdgeUnitEquiv
#assert_standard_axioms_only AAT.AG.AtlasCoefficientFiber.WitnessFourCoefficients
