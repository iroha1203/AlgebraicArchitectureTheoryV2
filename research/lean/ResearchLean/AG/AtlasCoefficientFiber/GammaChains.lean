import ResearchLean.AG.AtlasCoefficientFiber.RawBlocks

/-!
# G-135 B §1：同じ原始Γの全mapped辺・混在面

関係は原面名、端点は原mapped辺名。loop・平行関係を商にしない。

## Implementation notes

原Some辺と混在面のcarrierでSigma分類し、Bを同じΓ始点・終点差へ同定する。
端点対による辺の商は、重複辺出現と平行関係を失うため採用しない。
-/
noncomputable section
namespace AAT.AG.AtlasCoefficientFiber
open CategoryTheory CanonicalResolution ResolutionInvariance FaceRelationSubdivision
universe u
variable {Source : Type u} {qc qf : Reading Source} {h : qc.CoarserThan qf}
variable {Nc : TargetSupportedNerve.{u,u} qc} {Nf : TargetSupportedNerve.{u,u} qf}
variable (M : IncidenceSupportedComparison qc qf h Nc Nf) (A : Set qc.Target)

/-- mapped辺には宣言表のsome値が存在する。 -/
theorem horizontalEdge_has_image (e : HorizontalEdge M A) : ∃ E, M.edgeMap e.1.1 = some E := by
  cases he : M.edgeMap e.1.1 with
  | none => exact False.elim (e.2 he)
  | some E => exact ⟨E, rfl⟩

/-- mapped辺の実some値をK1選択済みの粗辺へ移す。 -/
def horizontalCarrier (e : HorizontalEdge M A) : Nc.EdgeInTargetSubset A :=
  M.targetSubsetEdgeMap A (comparisonFactor qc qf h ⁻¹' A) (fun _ ht => ht) e.1
    (Classical.choose (horizontalEdge_has_image M A e))
    (Classical.choose_spec (horizontalEdge_has_image M A e))

/-- carrierは元のOption表のsame名前付き粗辺。 -/
@[simp] theorem horizontalCarrier_map (e : HorizontalEdge M A) :
    M.edgeMap e.1.1 = some (horizontalCarrier M A e).1 :=
  Classical.choose_spec (horizontalEdge_has_image M A e)

/-- 同じsome値を指定すれば実carrierと一致する。 -/
theorem horizontalCarrier_eq (e : HorizontalEdge M A) (E : Nc.EdgeInTargetSubset A)
    (he : M.edgeMap e.1.1 = some E.1) : horizontalCarrier M A e = E :=
  Subtype.ext (Option.some.inj ((horizontalCarrier_map M A e).symm.trans he))

/-- 全水平辺は同じ原Γ頂点の非交和である。 -/
def gammaVertexPartition : HorizontalEdge M A ≃ Σ E : Nc.EdgeInTargetSubset A, GammaVertex M A E where
  toFun e := ⟨horizontalCarrier M A e, ⟨e.1, horizontalCarrier_map M A e⟩⟩
  invFun e := ⟨e.2.1, by rw [e.2.2]; exact Option.some_ne_none _⟩
  left_inv e := rfl
  right_inv e := by
    rcases e with ⟨E, e, he⟩
    have hc := horizontalCarrier_eq M A ⟨e, by rw [he]; exact Option.some_ne_none _⟩ E he
    apply Sigma.ext hc
    apply (Subtype.heq_iff_coe_eq (fun x => by dsimp only; rw [hc])).mpr
    rfl

/-- 混在面の負辺は実水平辺に属する。 -/
def mixedNegativeEdge (f : MixedFace M A) : HorizontalEdge M A :=
  ⟨Nf.targetSubsetFaceEdge1 _ f.1, by
    obtain ⟨E, he⟩ := f.2.2
    change ¬ M.edgeMap (Nf.nerve.faceEdge1 f.1.1) = none
    rw [he]
    exact Option.some_ne_none _⟩

/-- 混在面の実粗辺carrier。 -/
def mixedCarrier (f : MixedFace M A) : Nc.EdgeInTargetSubset A :=
  horizontalCarrier M A (mixedNegativeEdge M A f)

/-- 原始二パターンは、この同じ粗carrierのΓ関係になる。 -/
theorem mixedCarrier_patterns (f : MixedFace M A) :
    ((M.edgeMap (Nf.nerve.faceEdge0 f.1.1) = none ∧
      M.edgeMap (Nf.nerve.faceEdge1 f.1.1) = some (mixedCarrier M A f).1 ∧
      M.edgeMap (Nf.nerve.faceEdge2 f.1.1) = some (mixedCarrier M A f).1) ∨
    (M.edgeMap (Nf.nerve.faceEdge0 f.1.1) = some (mixedCarrier M A f).1 ∧
      M.edgeMap (Nf.nerve.faceEdge1 f.1.1) = some (mixedCarrier M A f).1 ∧
      M.edgeMap (Nf.nerve.faceEdge2 f.1.1) = none)) := by
  obtain ⟨E, he, hp⟩ := mixedFace_patterns M A f
  have hc : E = (mixedCarrier M A f).1 :=
    Option.some.inj (he.symm.trans (horizontalCarrier_map M A (mixedNegativeEdge M A f)))
  subst E
  rcases hp with hl | hr
  · exact Or.inl ⟨hl.1, he, hl.2⟩
  · exact Or.inr ⟨hr.1, he, hr.2⟩

/-- 全混在面は原面名を保つ全Γ関係の非交和である。 -/
def gammaEdgePartition : MixedFace M A ≃ Σ E : Nc.EdgeInTargetSubset A, GammaEdge M A E where
  toFun f := ⟨mixedCarrier M A f, ⟨f.1, f.2.1, mixedCarrier_patterns M A f⟩⟩
  invFun f := ⟨f.2.1, f.2.2.1, by
    rcases f.2.2.2 with hl | hr
    · exact ⟨f.1.1, hl.2.1⟩
    · exact ⟨f.1.1, hr.2.1⟩⟩
  left_inv f := rfl
  right_inv f := by
    rcases f with ⟨E, f, hn, hp⟩
    have he : M.edgeMap (Nf.nerve.faceEdge1 f.1) = some E.1 := by
      rcases hp with hl | hr
      · exact hl.2.1
      · exact hr.2.1
    have hc : mixedCarrier M A ⟨f, hn, E.1, he⟩ = E :=
      horizontalCarrier_eq M A _ E he
    apply Sigma.ext hc
    apply (Subtype.heq_iff_coe_eq (fun x => by dsimp only; rw [hc])).mpr
    rfl

/-- Γ頂点の分類逆は同じ元細辺を返す。 -/
@[simp] theorem gammaVertexPartition_symm_val (E : Nc.EdgeInTargetSubset A) (e : GammaVertex M A E) :
    ((gammaVertexPartition M A).symm ⟨E, e⟩).1 = e.1 := rfl

/-- Γ関係の分類逆は同じ元細面を返す。 -/
@[simp] theorem gammaEdgePartition_symm_val (E : Nc.EdgeInTargetSubset A) (f : GammaEdge M A E) :
    ((gammaEdgePartition M A).symm ⟨E, f⟩).1 = f.1 := rfl

/-- Γ頂点を同じ名前付き水平辺として読む。 -/
def gammaHorizontalVertex {E : Nc.EdgeInTargetSubset A} (e : GammaVertex M A E) : HorizontalEdge M A :=
  ⟨e.1, by rw [e.2]; exact Option.some_ne_none _⟩

/-- Γ頂点の水平辺表示は原細辺名を保つ。 -/
@[simp] theorem gammaHorizontalVertex_val {E : Nc.EdgeInTargetSubset A} (e : GammaVertex M A E) :
    (gammaHorizontalVertex M A e).1 = e.1 := rfl

/-- 原混在面のΓ始点。全Γ非交和を水平辺名で表示する。 -/
def mixedGraphSource (f : MixedFace M A) : HorizontalEdge M A :=
  gammaHorizontalVertex M A (gammaSource M A (gammaEdgePartition M A f).2)

/-- 原混在面のΓ終点。 -/
def mixedGraphTarget (f : MixedFace M A) : HorizontalEdge M A :=
  gammaHorizontalVertex M A (gammaTarget M A (gammaEdgePartition M A f).2)

/-- Γ始点は原負符号の辺出現。 -/
@[simp] theorem mixedGraphSource_val (f : MixedFace M A) :
    (mixedGraphSource M A f).1 = Nf.targetSubsetFaceEdge1 _ f.1 := rfl

/-- 左垂直パターンのΓ終点は原第三辺出現。 -/
theorem mixedGraphTarget_val_left (f : MixedFace M A)
    (h0 : M.edgeMap (Nf.nerve.faceEdge0 f.1.1) = none) :
    (mixedGraphTarget M A f).1 = Nf.targetSubsetFaceEdge2 _ f.1 :=
  gammaTarget_val_of_left M A (gammaEdgePartition M A f).2 h0

/-- 第三辺垂直パターンのΓ終点は原第一辺出現。 -/
theorem mixedGraphTarget_val_right (f : MixedFace M A) (E : Nc.nerve.EdgeComponent)
    (h0 : M.edgeMap (Nf.nerve.faceEdge0 f.1.1) = some E) :
    (mixedGraphTarget M A f).1 = Nf.targetSubsetFaceEdge0 _ f.1 := by
  have hn : ¬ M.edgeMap (Nf.nerve.faceEdge0 f.1.1) = none := by
    rw [h0]; exact Option.some_ne_none _
  have hp := mixedCarrier_patterns M A f
  rcases hp with hl | hr
  · exact False.elim (hn hl.1)
  · exact gammaTarget_val_of_right M A (gammaEdgePartition M A f).2 hr.1

/-- 実Bの各列は全Γの実有向incidenceそのもの。重複辺も両出現として保持。 -/
@[simp] theorem mixedHorizontalBoundary_single (f : MixedFace M A) (r : ℚ) :
    mixedHorizontalBoundary M A (Finsupp.single f r) = r •
      (Finsupp.single (mixedGraphTarget M A f) 1 - Finsupp.single (mixedGraphSource M A f) 1) := by
  rw [mixedHorizontalBoundary_apply]
  rw [mixedFaceInclusion_single, chainD2_single]
  simp only [map_smul, map_sub, map_add]
  obtain ⟨E, he, hp⟩ := mixedFace_patterns M A f
  have hs : Nf.targetSubsetFaceEdge1 _ f.1 = (mixedGraphSource M A f).1 := rfl
  rcases hp with hl | hr
  · have hv : (⟨Nf.targetSubsetFaceEdge0 _ f.1, hl.1⟩ : VerticalEdge M A).1 =
        Nf.targetSubsetFaceEdge0 _ f.1 := rfl
    rw [← hv, horizontalEdgeProjection_vertical_single, hs,
      ← mixedGraphTarget_val_left M A f hl.1, horizontalEdgeProjection_single,
      horizontalEdgeProjection_single, zero_sub]
    rw [neg_add_eq_sub]
  · have hv : (⟨Nf.targetSubsetFaceEdge2 _ f.1, hr.2⟩ : VerticalEdge M A).1 =
        Nf.targetSubsetFaceEdge2 _ f.1 := rfl
    rw [← hv, horizontalEdgeProjection_vertical_single, hs,
      ← mixedGraphTarget_val_right M A f E hr.1, horizontalEdgeProjection_single,
      horizontalEdgeProjection_single, add_zero]

/-- 実Bは、同じ原Γ始点・終点の自由線形incidenceとして全chain上で一致する。 -/
theorem mixedHorizontalBoundary_eq_incidence : mixedHorizontalBoundary M A =
    freeMap (fun f => Finsupp.single (mixedGraphTarget M A f) 1 -
      Finsupp.single (mixedGraphSource M A f) 1) := by
  apply Finsupp.lhom_ext
  intro f r
  rw [mixedHorizontalBoundary_single, freeMap_single]

/-- 全Γ頂点分類の逆は同じ水平辺表示。 -/
@[simp] theorem gammaVertexPartition_symm_apply (E : Nc.EdgeInTargetSubset A) (e : GammaVertex M A E) :
    (gammaVertexPartition M A).symm ⟨E, e⟩ = gammaHorizontalVertex M A e := rfl

/-- 全非交和分類は原Γの始点写像と可換。 -/
theorem gammaVertexPartition_mixed_source (f : MixedFace M A) :
    gammaVertexPartition M A (mixedGraphSource M A f) =
      ⟨(gammaEdgePartition M A f).1, gammaSource M A (gammaEdgePartition M A f).2⟩ := by
  change gammaVertexPartition M A (gammaHorizontalVertex M A _) = _
  rw [← gammaVertexPartition_symm_apply]
  exact (gammaVertexPartition M A).apply_symm_apply _

/-- 全非交和分類は原Γの終点写像と可換。loop・平行辺を忘れない。 -/
theorem gammaVertexPartition_mixed_target (f : MixedFace M A) :
    gammaVertexPartition M A (mixedGraphTarget M A f) =
      ⟨(gammaEdgePartition M A f).1, gammaTarget M A (gammaEdgePartition M A f).2⟩ := by
  change gammaVertexPartition M A (gammaHorizontalVertex M A _) = _
  rw [← gammaVertexPartition_symm_apply]
  exact (gammaVertexPartition M A).apply_symm_apply _

end AAT.AG.AtlasCoefficientFiber

#print axioms AAT.AG.AtlasCoefficientFiber.horizontalEdge_has_image
#print axioms AAT.AG.AtlasCoefficientFiber.horizontalCarrier
#print axioms AAT.AG.AtlasCoefficientFiber.horizontalCarrier_map
#print axioms AAT.AG.AtlasCoefficientFiber.horizontalCarrier_eq
#print axioms AAT.AG.AtlasCoefficientFiber.gammaVertexPartition
#print axioms AAT.AG.AtlasCoefficientFiber.mixedNegativeEdge
#print axioms AAT.AG.AtlasCoefficientFiber.mixedCarrier
#print axioms AAT.AG.AtlasCoefficientFiber.mixedCarrier_patterns
#print axioms AAT.AG.AtlasCoefficientFiber.gammaEdgePartition
#print axioms AAT.AG.AtlasCoefficientFiber.gammaVertexPartition_symm_val
#print axioms AAT.AG.AtlasCoefficientFiber.gammaEdgePartition_symm_val
#print axioms AAT.AG.AtlasCoefficientFiber.gammaHorizontalVertex
#print axioms AAT.AG.AtlasCoefficientFiber.gammaHorizontalVertex_val
#print axioms AAT.AG.AtlasCoefficientFiber.mixedGraphSource
#print axioms AAT.AG.AtlasCoefficientFiber.mixedGraphTarget
#print axioms AAT.AG.AtlasCoefficientFiber.mixedGraphSource_val
#print axioms AAT.AG.AtlasCoefficientFiber.mixedGraphTarget_val_left
#print axioms AAT.AG.AtlasCoefficientFiber.mixedGraphTarget_val_right
#print axioms AAT.AG.AtlasCoefficientFiber.mixedHorizontalBoundary_single
#print axioms AAT.AG.AtlasCoefficientFiber.mixedHorizontalBoundary_eq_incidence
#print axioms AAT.AG.AtlasCoefficientFiber.gammaVertexPartition_symm_apply
#print axioms AAT.AG.AtlasCoefficientFiber.gammaVertexPartition_mixed_source
#print axioms AAT.AG.AtlasCoefficientFiber.gammaVertexPartition_mixed_target
#assert_standard_axioms_only AAT.AG.AtlasCoefficientFiber
