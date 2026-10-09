import ResearchLean.AG.AtlasCoefficientFiber.WitnessFourCoefficients

/-!
# W4：原三角形のΦの全incidence成分

Implementation notes: old chartとfresh chartを原cの二射で接続し、原全誘導圏の
商を計算する。面あり・なしの同じ支持を全Aで保持する。
-/
noncomputable section
namespace AAT.AG.AtlasCoefficientFiber.WitnessFourPhi
open CategoryTheory CanonicalResolution ResolutionInvariance TwoPhase FaceRelationSubdivision
open FaceRelationSubdivision.WitnessOne (N plus minus qc qf coarser rPlus rMinus)
open AtlasDefectComposition

/-- 原plusのold chartは全Aの同じΦに存在する。 -/
def plusOldChart (A : Set Bool) (c : N.ChartInTargetSubset A) : PhiChart rPlus A c := by
  have hA : A.Nonempty := by obtain ⟨t,ht,ha⟩ := c.2; exact ⟨t,ha⟩
  exact ⟨fullSelected plus.chartSupport FaceRelationSubdivision.WitnessOne.plus_chart_full _
    (WitnessFullSupport.fine_nonempty A hA) (.inl c.1), by apply Subtype.ext; rfl⟩

/-- 原plusのfresh chartとold vを結ぶ同じc辺。 -/
def plusC (A : Set Bool) (c : N.ChartInTargetSubset A) (hc : c.1 = 0) :
    PhiEdge rPlus A c := by
  have hA : A.Nonempty := by obtain ⟨t,ht,ha⟩ := c.2; exact ⟨t,ha⟩
  exact ⟨fullSelected plus.edgeSupport FaceRelationSubdivision.WitnessOne.plus_edge_full _
    (WitnessFullSupport.fine_nonempty A hA) (.inr false), by
      constructor
      · rfl
      · apply Subtype.ext; exact hc.symm⟩

/-- 原plusの全Φ頂点を同じcの二incidenceで接続する。 -/
theorem plus_vertex_zigzag (A : Set Bool) (c : N.ChartInTargetSubset A) (v : PhiChart rPlus A c) :
    @Zigzag (PhiInc rPlus A c) inferInstance (Sum.inl (plusOldChart A c)) (Sum.inl v) := by
  letI : Category (PhiInc rPlus A c) := InducedCategory.instCategory
  rcases v with ⟨⟨v,hv⟩,hm⟩
  cases v with
  | inl a =>
    have ha : a = c.1 := congrArg Subtype.val hm
    have heq : plusOldChart A c = ⟨⟨.inl a,hv⟩,hm⟩ := by
      apply Subtype.ext; apply Subtype.ext; exact congrArg Sum.inl ha.symm
    rw [heq]
  | inr v =>
    cases v
    have hc : c.1 = 0 := (congrArg Subtype.val hm).symm
    let e := plusC A c hc
    let fa : InducedCategory.Hom (F := phiCellObj rPlus A c)
        (Sum.inl (plusOldChart A c)) (Sum.inr (Sum.inl e)) :=
      ⟨IncHom.chartEdge (plusOldChart A c).1 e.1 false (by
        apply Subtype.ext; change Sum.inl c.1 = Sum.inl (0 : Fin 2); rw [hc])⟩
    let fb : InducedCategory.Hom (F := phiCellObj rPlus A c)
        (Sum.inl (⟨⟨Sum.inr PUnit.unit,hv⟩,hm⟩ : PhiChart rPlus A c)) (Sum.inr (Sum.inl e)) :=
      ⟨IncHom.chartEdge _ e.1 true rfl⟩
    exact (@Zigzag.of_hom (PhiInc rPlus A c) InducedCategory.instCategory _ _ fa).trans
      (@Zigzag.of_hom (PhiInc rPlus A c) InducedCategory.instCategory _ _ fb).symm

/-- 原plusには全垂直Φ面が存在しない。 -/
theorem plus_face_empty (A : Set Bool) (c : N.ChartInTargetSubset A) : IsEmpty (PhiFace rPlus A c) where
  false f := by
    rcases h : f.1.1 with G | v
    · exact Empty.elim G
    · have hm := f.2.2.2.1
      rw [h, TriangleAddition.faceEdge1_new, FaceRelationSubdivision.WitnessOne.rPlus_edge_old] at hm
      cases hm

/-- 原plusの全対象を同じ原incidence射で接続する。 -/
theorem plus_zigzag (A : Set Bool) (c : N.ChartInTargetSubset A) (x : PhiInc rPlus A c) :
    @Zigzag (PhiInc rPlus A c) inferInstance (Sum.inl (plusOldChart A c)) x := by
  letI : Category (PhiInc rPlus A c) := InducedCategory.instCategory
  rcases x with v | (e | f)
  · exact plus_vertex_zigzag A c v
  · let ff : InducedCategory.Hom (F := phiCellObj rPlus A c)
        (Sum.inl (phiEndpoint rPlus A e false)) (Sum.inr (Sum.inl e)) :=
      ⟨IncHom.chartEdge (phiEndpoint rPlus A e false).1 e.1 false rfl⟩
    exact (plus_vertex_zigzag A c (phiEndpoint rPlus A e false)).trans
      (@Zigzag.of_hom (PhiInc rPlus A c) InducedCategory.instCategory _ _ ff)
  · exact False.elim ((plus_face_empty A c).false f)

/-- 原plusの全Φ成分は非空一成分となる。 -/
theorem plus_components (A : Set Bool) (c : N.ChartInTargetSubset A) :
    Nonempty (ConnectedComponents (PhiInc rPlus A c)) ∧
      Subsingleton (ConnectedComponents (PhiInc rPlus A c)) := by
  refine ⟨⟨CategoryTheory.ConnectedComponents.mk (Sum.inl (plusOldChart A c) : PhiInc rPlus A c)⟩,?_⟩
  constructor
  intro x y
  induction x using Quotient.inductionOn with | h x =>
    induction y using Quotient.inductionOn with | h y =>
      exact Quotient.sound ((plus_zigzag A c x).symm.trans (plus_zigzag A c y))

/-- 原minusのold chartは全Aの同じΦに存在する。 -/
def minusOldChart (A : Set Bool) (c : N.ChartInTargetSubset A) : PhiChart rMinus A c := by
  have hA : A.Nonempty := by obtain ⟨t,ht,ha⟩ := c.2; exact ⟨t,ha⟩
  exact ⟨fullSelected minus.chartSupport FaceRelationSubdivision.WitnessOne.minus_chart_full _
    (WitnessFullSupport.fine_nonempty A hA) (.inl c.1), by apply Subtype.ext; rfl⟩

/-- 原minusのfresh chartとold vを結ぶ同じc辺。 -/
def minusC (A : Set Bool) (c : N.ChartInTargetSubset A) (hc : c.1 = 0) :
    PhiEdge rMinus A c := by
  have hA : A.Nonempty := by obtain ⟨t,ht,ha⟩ := c.2; exact ⟨t,ha⟩
  exact ⟨fullSelected minus.edgeSupport FaceRelationSubdivision.WitnessOne.minus_edge_full _
    (WitnessFullSupport.fine_nonempty A hA) (.inr false), by
      constructor
      · rfl
      · apply Subtype.ext; exact hc.symm⟩

/-- 原minusの全Φ頂点を同じcの二incidenceで接続する。 -/
theorem minus_vertex_zigzag (A : Set Bool) (c : N.ChartInTargetSubset A) (v : PhiChart rMinus A c) :
    @Zigzag (PhiInc rMinus A c) inferInstance (Sum.inl (minusOldChart A c)) (Sum.inl v) := by
  letI : Category (PhiInc rMinus A c) := InducedCategory.instCategory
  rcases v with ⟨⟨v,hv⟩,hm⟩
  cases v with
  | inl a =>
    have ha : a = c.1 := congrArg Subtype.val hm
    have heq : minusOldChart A c = ⟨⟨.inl a,hv⟩,hm⟩ := by
      apply Subtype.ext; apply Subtype.ext; exact congrArg Sum.inl ha.symm
    rw [heq]
  | inr v =>
    cases v
    have hc : c.1 = 0 := (congrArg Subtype.val hm).symm
    let e := minusC A c hc
    let fa : InducedCategory.Hom (F := phiCellObj rMinus A c)
        (Sum.inl (minusOldChart A c)) (Sum.inr (Sum.inl e)) :=
      ⟨IncHom.chartEdge (minusOldChart A c).1 e.1 false (by
        apply Subtype.ext; change Sum.inl c.1 = Sum.inl (0 : Fin 2); rw [hc])⟩
    let fb : InducedCategory.Hom (F := phiCellObj rMinus A c)
        (Sum.inl (⟨⟨Sum.inr PUnit.unit,hv⟩,hm⟩ : PhiChart rMinus A c)) (Sum.inr (Sum.inl e)) :=
      ⟨IncHom.chartEdge _ e.1 true rfl⟩
    exact (@Zigzag.of_hom (PhiInc rMinus A c) InducedCategory.instCategory _ _ fa).trans
      (@Zigzag.of_hom (PhiInc rMinus A c) InducedCategory.instCategory _ _ fb).symm

/-- 原minusには全垂直Φ面が存在しない。 -/
theorem minus_face_empty (A : Set Bool) (c : N.ChartInTargetSubset A) : IsEmpty (PhiFace rMinus A c) where
  false f := by
    exact isEmptyElim f.1.1

/-- 原minusの全対象を同じ原incidence射で接続する。 -/
theorem minus_zigzag (A : Set Bool) (c : N.ChartInTargetSubset A) (x : PhiInc rMinus A c) :
    @Zigzag (PhiInc rMinus A c) inferInstance (Sum.inl (minusOldChart A c)) x := by
  letI : Category (PhiInc rMinus A c) := InducedCategory.instCategory
  rcases x with v | (e | f)
  · exact minus_vertex_zigzag A c v
  · let ff : InducedCategory.Hom (F := phiCellObj rMinus A c)
        (Sum.inl (phiEndpoint rMinus A e false)) (Sum.inr (Sum.inl e)) :=
      ⟨IncHom.chartEdge (phiEndpoint rMinus A e false).1 e.1 false rfl⟩
    exact (minus_vertex_zigzag A c (phiEndpoint rMinus A e false)).trans
      (@Zigzag.of_hom (PhiInc rMinus A c) InducedCategory.instCategory _ _ ff)
  · exact False.elim ((minus_face_empty A c).false f)

/-- 原minusの全Φ成分は非空一成分となる。 -/
theorem minus_components (A : Set Bool) (c : N.ChartInTargetSubset A) :
    Nonempty (ConnectedComponents (PhiInc rMinus A c)) ∧
      Subsingleton (ConnectedComponents (PhiInc rMinus A c)) := by
  refine ⟨⟨CategoryTheory.ConnectedComponents.mk (Sum.inl (minusOldChart A c) : PhiInc rMinus A c)⟩,?_⟩
  constructor
  intro x y
  induction x using Quotient.inductionOn with | h x =>
    induction y using Quotient.inductionOn with | h y =>
      exact Quotient.sound ((minus_zigzag A c x).symm.trans (minus_zigzag A c y))
/-- 原plusのv以外のΦはold chart一点を持つ。 -/
theorem plus_other_chart_single (A : Set Bool) (c : N.ChartInTargetSubset A) (hc : c.1 ≠ 0) :
    Subsingleton (PhiChart rPlus A c) := by
  have heq : ∀ v : PhiChart rPlus A c, v = plusOldChart A c := by
    intro v
    have hm := congrArg Subtype.val v.2
    rcases h : v.1.1 with a | u
    · apply Subtype.ext; apply Subtype.ext
      change rPlus.chartMap v.1.1 = c.1 at hm
      rw [h] at hm
      change a = c.1 at hm
      exact h.trans (congrArg Sum.inl hm)
    · change rPlus.chartMap v.1.1 = c.1 at hm
      rw [h] at hm
      exact False.elim (hc hm.symm)
  exact ⟨fun v w => (heq v).trans (heq w).symm⟩
/-- 原plusのv以外のΦには退化辺がない。 -/
theorem plus_other_edge_empty (A : Set Bool) (c : N.ChartInTargetSubset A) (hc : c.1 ≠ 0) :
    IsEmpty (PhiEdge rPlus A c) where
  false e := by
    have hm := congrArg Subtype.val e.2.2
    change rPlus.chartMap (plus.nerve.edgeLeft e.1.1) = c.1 at hm
    rw [WitnessFourTriangle.plus_vertical_name A c e] at hm
    exact hc hm.symm
/-- 原minusのv以外のΦはold chart一点を持つ。 -/
theorem minus_other_chart_single (A : Set Bool) (c : N.ChartInTargetSubset A) (hc : c.1 ≠ 0) :
    Subsingleton (PhiChart rMinus A c) := by
  have heq : ∀ v : PhiChart rMinus A c, v = minusOldChart A c := by
    intro v
    have hm := congrArg Subtype.val v.2
    rcases h : v.1.1 with a | u
    · apply Subtype.ext; apply Subtype.ext
      change rMinus.chartMap v.1.1 = c.1 at hm
      rw [h] at hm
      change a = c.1 at hm
      exact h.trans (congrArg Sum.inl hm)
    · change rMinus.chartMap v.1.1 = c.1 at hm
      rw [h] at hm
      exact False.elim (hc hm.symm)
  exact ⟨fun v w => (heq v).trans (heq w).symm⟩
/-- 原minusのv以外のΦには退化辺がない。 -/
theorem minus_other_edge_empty (A : Set Bool) (c : N.ChartInTargetSubset A) (hc : c.1 ≠ 0) :
    IsEmpty (PhiEdge rMinus A c) where
  false e := by
    have hm := congrArg Subtype.val e.2.2
    change rMinus.chartMap (minus.nerve.edgeLeft e.1.1) = c.1 at hm
    rw [WitnessFourTriangle.minus_vertical_name A c e] at hm
    exact hc hm.symm
end AAT.AG.AtlasCoefficientFiber.WitnessFourPhi

#print axioms AAT.AG.AtlasCoefficientFiber.WitnessFourPhi.plusOldChart
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessFourPhi.plusC
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessFourPhi.plus_vertex_zigzag
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessFourPhi.plus_face_empty
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessFourPhi.plus_zigzag
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessFourPhi.plus_components
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessFourPhi.minusOldChart
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessFourPhi.minusC
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessFourPhi.minus_vertex_zigzag
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessFourPhi.minus_face_empty
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessFourPhi.minus_zigzag
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessFourPhi.minus_components
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessFourPhi.plus_other_chart_single
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessFourPhi.plus_other_edge_empty
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessFourPhi.minus_other_chart_single
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessFourPhi.minus_other_edge_empty
#assert_standard_axioms_only AAT.AG.AtlasCoefficientFiber.WitnessFourPhi
