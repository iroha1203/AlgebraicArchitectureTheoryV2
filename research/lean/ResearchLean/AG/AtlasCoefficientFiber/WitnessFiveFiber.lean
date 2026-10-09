import ResearchLean.AG.AtlasCoefficientFiber.WitnessFiveCoefficients
import ResearchLean.AG.AtlasCoefficientFiber.FiberCohomology
import ResearchLean.AG.AtlasCoefficientFiber.WitnessFullSupport
import ResearchLean.AG.AtlasCoefficientFiber.GammaForest

/-!
# G-135 W5：原Φの円と混在閉路の原D

## Implementation notes

全Aで混在面mと垂直辺kを同じ選択支持から両方向に構成する。
空支持では両型とも空であり、期待rankを選択条件にする方法は採用しない。
-/
noncomputable section
namespace AAT.AG.AtlasCoefficientFiber.WitnessFive
open CategoryTheory CanonicalResolution ResolutionInvariance FaceRelationSubdivision TwoPhase
open WitnessCommon WitnessFullSupport AtlasDefectComposition

/-- 原selected kから粗Aの非空性を読む。 -/
theorem nonempty_of_vertical (A : Set Bool) (e : VerticalEdge M A) : A.Nonempty := by
  obtain ⟨s,_,hs⟩ := e.1.2
  exact ⟨comparisonFactor qc qf coarser s,hs⟩
/-- 原mixed mの位置0は同原none辺k。 -/
def mixedToVertical (A : Set Bool) (f : MixedFace M A) : VerticalEdge M A :=
  ⟨Nf.targetSubsetFaceEdge0 _ f.1,by
    change M.edgeMap (Nf.nerve.faceEdge0 f.1.1) = none
    rw [fine_faceEdge0,edgeMap_k]⟩
/-- selected kの支持から同原mを生成する逆方向。 -/
def verticalToMixed (A : Set Bool) (e : VerticalEdge M A) : MixedFace M A :=
  ⟨fullSelected Nf.faceSupport (fullSupport_face Nf (fun _ => rfl)) _
    (fine_nonempty A (nonempty_of_vertical A e)) (),by
    refine ⟨faceMap_apply _,0,?_⟩
    rw [fine_faceEdge1,edgeMap_e]⟩
/-- 原m↔kの両逆は全Aで同じ支持を保持する。 -/
def mixedVerticalEquiv (A : Set Bool) : MixedFace M A ≃ VerticalEdge M A where
  toFun := mixedToVertical A
  invFun := verticalToMixed A
  left_inv f := by apply Subtype.ext; apply Subtype.ext; exact Subsingleton.elim _ _
  right_inv e := by
    apply Subtype.ext; apply Subtype.ext
    change Nf.nerve.faceEdge0 () = e.1.1
    rw [fine_faceEdge0]
    exact ((edgeMap_none_iff _).mp e.2).symm
/-- 原m↔kの順写像評価。 -/
@[simp] theorem mixedVerticalEquiv_apply (A : Set Bool) (f : MixedFace M A) :
    mixedVerticalEquiv A f = mixedToVertical A f := rfl
/-- 原全選択chartは同じ唯一chart。 -/
theorem fineChart_subsingleton (S : Set qf.Target) : Subsingleton (Nf.ChartInTargetSubset S) := inferInstance
/-- 原垂直aの全列は同端点の差で零。 -/
theorem verticalEdgeBoundary_zero (A : Set Bool) : verticalEdgeBoundary M A = 0 := by
  classical
  apply Finsupp.lhom_ext
  intro e r
  rw [verticalEdgeBoundary_single]
  have he : Nf.targetSubsetEdgeRight _ e.1 = Nf.targetSubsetEdgeLeft _ e.1 := Subtype.ext rfl
  rw [he,sub_self,smul_zero]
  rfl
/-- 原mはmapped位置1を持つので垂直面は空。 -/
theorem verticalFace_empty (A : Set Bool) : IsEmpty (VerticalFace M A) where
  false f := by
    have h1 := f.2.2.2.1
    simp only [edgeMap_e,Option.some_ne_none] at h1
/-- 原Vの始域が空なので実写像は零。 -/
theorem verticalBoundary_zero (A : Set Bool) : verticalBoundary M A = 0 := by
  letI := verticalFace_empty A
  apply LinearMap.ext; intro x
  rw [Subsingleton.elim x 0,map_zero]; rfl
/-- 同mの二原水平出現は同じselected e。 -/
theorem mixed_horizontal_endpoints (A : Set Bool) (f : MixedFace M A) :
    Nf.targetSubsetFaceEdge1 _ f.1 = Nf.targetSubsetFaceEdge2 _ f.1 := Subtype.ext rfl
/-- 原Dの各列はk−e+eから同k単独chainとなる。 -/
theorem mixedVerticalBoundary_single (A : Set Bool) (f : MixedFace M A) (r : ℚ) :
    mixedVerticalBoundary M A (Finsupp.single f r) = Finsupp.single (mixedToVertical A f) r := by
  rw [mixedVerticalBoundary_apply,mixedFaceInclusion_single,chainD2_single]
  rw [mixed_horizontal_endpoints,sub_add_cancel]
  change verticalEdgeProjection M A (r • Finsupp.single (mixedToVertical A f).1 1) = _
  rw [map_smul,verticalEdgeProjection_single,Finsupp.smul_single]
  simp only [smul_eq_mul,mul_one]
/-- 原Dは同m↔kの自由chain同型の実写像と全元一致。 -/
theorem mixedVerticalBoundary_eq (A : Set Bool) :
    mixedVerticalBoundary M A = (Finsupp.domLCongr (mixedVerticalEquiv A)).toLinearMap := by
  classical
  apply Finsupp.lhom_ext
  intro f r
  rw [mixedVerticalBoundary_single]
  exact (Finsupp.domLCongr_single (mixedVerticalEquiv A) f r).symm
/-- 原Dの単射・全射は上の原セル両逆から生成。 -/
theorem mixedVerticalBoundary_bijective (A : Set Bool) : Function.Bijective (mixedVerticalBoundary M A) := by
  rw [mixedVerticalBoundary_eq]
  exact (Finsupp.domLCongr (mixedVerticalEquiv A)).bijective
/-- 原Bの全列は同eの二出現の符号で相殺する。 -/
theorem mixedHorizontalBoundary_zero (A : Set Bool) : mixedHorizontalBoundary M A = 0 := by
  classical
  apply Finsupp.lhom_ext
  intro f r
  rw [mixedHorizontalBoundary_apply,mixedFaceInclusion_single,chainD2_single]
  rw [mixed_horizontal_endpoints,sub_add_cancel]
  change horizontalEdgeProjection M A (r • Finsupp.single (mixedToVertical A f).1 1) = 0
  rw [map_smul,horizontalEdgeProjection_vertical_single,smul_zero]

/-- 元Φの唯一辺は同じ原k、同粗chartの支持から生成する。 -/
def phiEdgeEquiv (A : Set Bool) (c : Nc.ChartInTargetSubset A) : PhiEdge M A c ≃ Unit := by
  have hA : A.Nonempty := by obtain ⟨t,_,ht⟩ := c.2; exact ⟨t,ht⟩
  exact {
    toFun _ := ()
    invFun _ := ⟨fullSelected Nf.edgeSupport (fullSupport_edge Nf (fun _ => rfl)) _
      (fine_nonempty A hA) 2,edgeMap_k,by apply Subtype.ext; exact Subsingleton.elim _ _⟩
    left_inv e := by
      apply Subtype.ext; apply Subtype.ext
      exact ((edgeMap_none_iff _).mp e.2.1).symm
    right_inv _ := Subsingleton.elim _ _ }
/-- 原Φ d0は同chartのloop両端点差から零。 -/
theorem phi_d0_zero (A : Set Bool) (c : Nc.ChartInTargetSubset A) : (phiComplex M A c).d0 = 0 := by
  letI := phiChart_subsingleton A c
  apply LinearMap.ext; intro z; funext e
  change phiD0 M A c z e = (0 : ℚ)
  rw [phiD0_apply]
  rw [Subsingleton.elim (phiEndpoint M A e true) (phiEndpoint M A e false)]
  exact sub_self _
/-- 原Φ垂直面はないので同d1は零。 -/
theorem phi_d1_zero (A : Set Bool) (c : Nc.ChartInTargetSubset A) : (phiComplex M A c).d1 = 0 := by
  letI := phiFace_empty A c
  apply LinearMap.ext; intro z; funext f; exact isEmptyElim f
/-- 同原Φ H¹の全商とk cochain値の両逆。 -/
def phiH1Coordinates (A : Set Bool) (c : Nc.ChartInTargetSubset A) : (phiComplex M A c).H1 ≃ₗ[ℚ] ℚ :=
  (zeroDifferentialH1Equiv _ (phi_d0_zero A c) (phi_d1_zero A c)).trans
    ((LinearEquiv.piCongrLeft' ℚ (fun _ : PhiEdge M A c => ℚ) (phiEdgeEquiv A c)).trans
      (LinearEquiv.funUnique Unit ℚ ℚ))
/-- 元Φ H¹の実次元は粗chartが選択されると1。 -/
theorem phiH1_dimension (A : Set Bool) (c : Nc.ChartInTargetSubset A) : Module.finrank ℚ (phiComplex M A c).H1 = 1 :=
  (phiH1Coordinates A c).finrank_eq.trans (Module.finrank_self ℚ)

/-- 原mが入るΓは同粗eだけである。 -/
theorem gammaEdge_coarse_name (A : Set Bool) (e : Nc.EdgeInTargetSubset A) (f : GammaEdge M A e) : e.1 = 0 := by
  have h1 : M.edgeMap (Nf.nerve.faceEdge1 f.1.1) = some e.1 := by
    rcases f.2.2 with hl | hr
    · exact hl.2.1
    · exact hr.2.1
  have hh : (0 : Fin 2) = e.1 := Option.some.inj (edgeMap_e.symm.trans h1)
  exact hh.symm
/-- e上の元Γ関係面は同m一つ、原二出現を残す。 -/
def gammaEEdgeEquiv (A : Set Bool) (e : Nc.EdgeInTargetSubset A) (he : e.1 = 0) : GammaEdge M A e ≃ Unit := by
  have hA : A.Nonempty := by obtain ⟨t,_,ht⟩ := e.2; exact ⟨t,ht⟩
  exact {
    toFun _ := ()
    invFun _ := ⟨fullSelected Nf.faceSupport (fullSupport_face Nf (fun _ => rfl)) _ (fine_nonempty A hA) (),by
      refine ⟨faceMap_apply _,Or.inl ?_⟩
      change M.edgeMap 2 = none ∧ M.edgeMap 0 = some e.1 ∧ M.edgeMap 0 = some e.1
      exact ⟨edgeMap_k,edgeMap_e.trans (congrArg Option.some he.symm),edgeMap_e.trans (congrArg Option.some he.symm)⟩⟩
    left_inv f := by apply Subtype.ext; apply Subtype.ext; exact Subsingleton.elim _ _
    right_inv _ := Subsingleton.elim _ _ }
/-- h上の元Γは関係面を持たない点。 -/
theorem gammaHEdge_empty (A : Set Bool) (e : Nc.EdgeInTargetSubset A) (he : e.1 = 1) : IsEmpty (GammaEdge M A e) where
  false f := by
    have hh : (0 : Fin 2) = 1 := (gammaEdge_coarse_name A e f).symm.trans he
    exact (by decide : (0 : Fin 2) ≠ 1) hh
/-- 同一Γ頂点に戻る原mのincidence列は零。 -/
theorem gammaBoundary_zero (A : Set Bool) (e : Nc.EdgeInTargetSubset A) : gammaBoundary M A e = 0 := by
  letI := gammaVertex_subsingleton A e
  apply Finsupp.lhom_ext; intro f r
  rw [gammaBoundary_single,Subsingleton.elim (gammaTarget M A f) (gammaSource M A f),sub_self,smul_zero]
  rfl
/-- e上の実Γ incidence核は原m値Qと全両逆で対応。 -/
def gammaCycleCoordinates (A : Set Bool) (e : Nc.EdgeInTargetSubset A) (he : e.1 = 0) :
    LinearMap.ker (gammaBoundary M A e) ≃ₗ[ℚ] ℚ := by
  let v := (LinearMap.ker (gammaBoundary M A e)).subtype
  have hv : Function.Bijective v := by
    constructor
    · exact Subtype.val_injective
    · intro y
      exact ⟨⟨y,by rw [LinearMap.mem_ker,gammaBoundary_zero]; rfl⟩,rfl⟩
  exact (LinearEquiv.ofBijective v hv).trans
    ((Finsupp.domLCongr (gammaEEdgeEquiv A e he)).trans
      ((Finsupp.linearEquivFunOnFinite ℚ ℚ Unit).trans (LinearEquiv.funUnique Unit ℚ ℚ)))
/-- 原Γのmでは同じ細eの位置1と2が別射である。 -/
theorem gamma_parallel_incidence (A : Set Bool) (e : Nc.EdgeInTargetSubset A) (f : GammaEdge M A e) :
    IncHom.edgeFace (Nf.targetSubsetFaceEdge1 _ f.1) f.1 1 rfl ≠
      IncHom.edgeFace (Nf.targetSubsetFaceEdge1 _ f.1) f.1 2 (Subtype.ext rfl) :=
  edgeFace_ne_of_position_ne _ _ 1 2 rfl (Subtype.ext rfl) (by decide)

/-- 原Φ全商座標の公開代表評価、同k辺の元cochain値を読む。 -/
theorem phiH1Coordinates_mk (A : Set Bool) (c : Nc.ChartInTargetSubset A)
    (z : LinearMap.ker (phiComplex M A c).d1) :
    phiH1Coordinates A c ((LinearMap.range (phiComplex M A c).boundaryToCycles).mkQ z) =
      z.1 ((phiEdgeEquiv A c).symm ()) := by
  change (LinearEquiv.funUnique Unit ℚ ℚ)
    ((LinearEquiv.piCongrLeft' ℚ (fun _ : PhiEdge M A c => ℚ) (phiEdgeEquiv A c))
      (zeroDifferentialH1Equiv _ (phi_d0_zero A c) (phi_d1_zero A c)
        ((LinearMap.range (phiComplex M A c).boundaryToCycles).mkQ z))) = _
  rw [zeroDifferentialH1Equiv_mk]
  rfl

end AAT.AG.AtlasCoefficientFiber.WitnessFive
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessFive.nonempty_of_vertical
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessFive.mixedToVertical
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessFive.verticalToMixed
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessFive.mixedVerticalEquiv
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessFive.mixedVerticalEquiv_apply
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessFive.fineChart_subsingleton
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessFive.verticalEdgeBoundary_zero
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessFive.verticalFace_empty
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessFive.verticalBoundary_zero
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessFive.mixed_horizontal_endpoints
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessFive.mixedVerticalBoundary_single
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessFive.mixedVerticalBoundary_eq
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessFive.mixedVerticalBoundary_bijective
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessFive.mixedHorizontalBoundary_zero
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessFive.phiEdgeEquiv
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessFive.phi_d0_zero
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessFive.phi_d1_zero
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessFive.phiH1Coordinates
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessFive.phiH1_dimension
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessFive.gammaEdge_coarse_name
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessFive.gammaEEdgeEquiv
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessFive.gammaHEdge_empty
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessFive.gammaBoundary_zero
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessFive.gammaCycleCoordinates
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessFive.gamma_parallel_incidence
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessFive.phiH1Coordinates_mk
#assert_standard_axioms_only AAT.AG.AtlasCoefficientFiber.WitnessFive
