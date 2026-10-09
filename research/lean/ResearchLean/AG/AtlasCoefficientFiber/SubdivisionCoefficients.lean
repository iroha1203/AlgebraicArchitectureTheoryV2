import ResearchLean.AG.AtlasCoefficientFiber.LocalPreservation
import ResearchLean.AG.FaceRelationSubdivision.EdgeSubdivision

/-!
# 原辺分割のΦ成分とΛ持ち上げ

Implementation notes: 原支持からold chartとcを選択し、全誘導圏のincidence射で
同じ成分へ接続する。旧面の唯一center持ち上げも同じ原faceMapから生成する。
-/
noncomputable section
namespace AAT.AG.AtlasCoefficientFiber.SubdivisionCoefficients
open CategoryTheory CanonicalResolution ResolutionInvariance FaceRelationSubdivision TwoPhase
open AtlasDefectComposition
universe u
variable {Source : Type u} {q : Reading Source}
variable (N : TargetSupportedNerve.{u,u} q) (e : N.nerve.EdgeComponent) (A : Set q.Target)

/-- 原old chartは同じ台を保ったΦに存在する。 -/
def oldChart (c : N.ChartInTargetSubset A) : PhiChart (EdgeSubdivision.collapse N e) A c := by
  refine ⟨⟨.inl c.1, ?_⟩, ?_⟩
  · obtain ⟨t,ht,ha⟩ := c.2
    exact ⟨t, ht, by simpa only [Set.mem_preimage, comparisonFactor_self, id_eq] using ha⟩
  · apply Subtype.ext; rfl

/-- 原fresh/old始点を結ぶcは、始点が選択されれば元辺台によらず選択される。 -/
def cEdge (c : N.ChartInTargetSubset A) (hc : c.1 = N.nerve.edgeLeft e) :
    PhiEdge (EdgeSubdivision.collapse N e) A c := by
  refine ⟨⟨.inr (.inl false), ?_⟩, ?_, ?_⟩
  · obtain ⟨t,ht,ha⟩ := c.2
    refine ⟨t, ?_, ?_⟩
    · rw [EdgeSubdivision.edgeSupport_c, ← hc]; exact ht
    · simpa only [Set.mem_preimage, comparisonFactor_self, id_eq] using ha
  · rfl
  · apply Subtype.ext; exact hc.symm

/-- 全原Φ頂点はold/freshの元c二射で同じ成分へ接続する。 -/
theorem vertex_zigzag (c : N.ChartInTargetSubset A)
    (v : PhiChart (EdgeSubdivision.collapse N e) A c) :
    @Zigzag (PhiInc (EdgeSubdivision.collapse N e) A c) inferInstance
      (Sum.inl (oldChart N e A c)) (Sum.inl v) := by
  letI : Category (PhiInc (EdgeSubdivision.collapse N e) A c) := InducedCategory.instCategory
  rcases v with ⟨⟨v,hv⟩,hm⟩
  cases v with
  | inl a =>
    have ha : a = c.1 := congrArg Subtype.val hm
    have heq : oldChart N e A c = ⟨⟨.inl a,hv⟩,hm⟩ := by
      apply Subtype.ext; apply Subtype.ext; exact congrArg Sum.inl ha.symm
    rw [heq]
  | inr v =>
    cases v
    have hc : c.1 = N.nerve.edgeLeft e := (congrArg Subtype.val hm).symm
    let a := cEdge N e A c hc
    let fa : InducedCategory.Hom (F := phiCellObj (EdgeSubdivision.collapse N e) A c)
        (Sum.inl (oldChart N e A c)) (Sum.inr (Sum.inl a)) :=
      ⟨IncHom.chartEdge (oldChart N e A c).1 a.1 false (by
        apply Subtype.ext; change Sum.inl c.1 = Sum.inl (N.nerve.edgeLeft e); rw [hc])⟩
    let fb : InducedCategory.Hom (F := phiCellObj (EdgeSubdivision.collapse N e) A c)
        (Sum.inl (⟨⟨Sum.inr PUnit.unit,hv⟩,hm⟩ : PhiChart (EdgeSubdivision.collapse N e) A c))
        (Sum.inr (Sum.inl a)) := ⟨IncHom.chartEdge _ a.1 true rfl⟩
    exact (@Zigzag.of_hom (PhiInc (EdgeSubdivision.collapse N e) A c)
      InducedCategory.instCategory _ _ fa).trans
      (@Zigzag.of_hom (PhiInc (EdgeSubdivision.collapse N e) A c)
        InducedCategory.instCategory _ _ fb).symm

/-- 原center面はmapped、原triangle面はmixedなので垂直面はない。 -/
theorem face_empty (c : N.ChartInTargetSubset A) :
    IsEmpty (PhiFace (EdgeSubdivision.collapse N e) A c) where
  false f := by
    rcases h : f.1.1 with F | o
    · have hm := f.2.1
      change EdgeSubdivision.faceImage N e f.1.1 = none at hm
      simp [h, EdgeSubdivision.faceImage] at hm
    · have hm := f.2.2.2.1
      change EdgeSubdivision.edgeImage N e ((EdgeSubdivision.nerve N e).faceEdge1 f.1.1) = none at hm
      simp [h, EdgeSubdivision.nerve, EdgeSubdivision.edgeImage] at hm

/-- 全原Φ対象のzigzag。元面を省略する条件は入力しない。 -/
theorem zigzag (c : N.ChartInTargetSubset A) (x : PhiInc (EdgeSubdivision.collapse N e) A c) :
    @Zigzag (PhiInc (EdgeSubdivision.collapse N e) A c) inferInstance
      (Sum.inl (oldChart N e A c)) x := by
  letI : Category (PhiInc (EdgeSubdivision.collapse N e) A c) := InducedCategory.instCategory
  rcases x with v | (a | f)
  · exact vertex_zigzag N e A c v
  · let ff : InducedCategory.Hom (F := phiCellObj (EdgeSubdivision.collapse N e) A c)
        (Sum.inl (phiEndpoint (EdgeSubdivision.collapse N e) A a false)) (Sum.inr (Sum.inl a)) :=
      ⟨IncHom.chartEdge (phiEndpoint (EdgeSubdivision.collapse N e) A a false).1 a.1 false rfl⟩
    exact (vertex_zigzag N e A c (phiEndpoint (EdgeSubdivision.collapse N e) A a false)).trans
      (@Zigzag.of_hom (PhiInc (EdgeSubdivision.collapse N e) A c) InducedCategory.instCategory _ _ ff)
  · exact False.elim ((face_empty N e A c).false f)

/-- 全部分台の原Φ全成分は非空単一。 -/
theorem phi_components (c : N.ChartInTargetSubset A) :
    Nonempty (ConnectedComponents (PhiInc (EdgeSubdivision.collapse N e) A c)) ∧
      Subsingleton (ConnectedComponents (PhiInc (EdgeSubdivision.collapse N e) A c)) := by
  refine ⟨⟨CategoryTheory.ConnectedComponents.mk
    (Sum.inl (oldChart N e A c) : PhiInc (EdgeSubdivision.collapse N e) A c)⟩,?_⟩
  constructor
  intro x y
  induction x using Quotient.inductionOn with | h x =>
    induction y using Quotient.inductionOn with | h y =>
      exact Quotient.sound ((zigzag N e A c x).symm.trans (zigzag N e A c y))

/-- 同じ原Λは旧Fのcenter面を唯一のliftとして保持する。 -/
def lambdaEquiv (F : N.FaceInTargetSubset A) :
    LambdaFace (EdgeSubdivision.collapse N e) A F ≃ Fin 1 where
  toFun _ := 0
  invFun _ := ⟨⟨.inl F.1, by
    obtain ⟨t,ht,ha⟩ := F.2
    exact ⟨t, by rw [EdgeSubdivision.faceSupport_center]; exact ht,
      by simpa only [Set.mem_preimage, comparisonFactor_self, id_eq] using ha⟩⟩, rfl⟩
  left_inv f := by
    apply Subtype.ext; apply Subtype.ext
    have hm := f.2
    change EdgeSubdivision.faceImage N e f.1.1 = some F.1 at hm
    rcases h : f.1.1 with G | o
    · have he : G = F.1 := by simpa only [h, EdgeSubdivision.faceImage, Option.some.injEq] using hm
      change Sum.inl F.1 = Sum.inl G
      rw [he]
    · simp [h, EdgeSubdivision.faceImage] at hm
  right_inv i := Subsingleton.elim _ _

/-- 同じ原Λの非空・単一性を両逆から得る。 -/
theorem lambda_single (F : N.FaceInTargetSubset A) :
    Nonempty (LambdaFace (EdgeSubdivision.collapse N e) A F) ∧
      Subsingleton (LambdaFace (EdgeSubdivision.collapse N e) A F) :=
  ⟨⟨(lambdaEquiv N e A F).symm 0⟩, (lambdaEquiv N e A F).subsingleton_congr.mpr inferInstance⟩

/-- 原辺の台を保つ名前付きfine辺を、同じAの逆像で選択する。 -/
def selectedEdge (a : N.EdgeInTargetSubset A) (b : (EdgeSubdivision.supported N e).nerve.EdgeComponent)
    (hb : (EdgeSubdivision.supported N e).edgeSupport b = N.edgeSupport a.1) :
    (EdgeSubdivision.supported N e).EdgeInTargetSubset
      (comparisonFactor q q (Reading.coarserThan_refl q) ⁻¹' A) := by
  refine ⟨b, ?_⟩
  obtain ⟨t,ht,ha⟩ := a.2
  exact ⟨t, by rw [hb]; exact ht,
    by simpa only [Set.mem_preimage, comparisonFactor_self, id_eq] using ha⟩

/-- 分割辺eの同じmapped b lift。 -/
def gammaB (a : N.EdgeInTargetSubset A) (ha : a.1 = e) :
    GammaVertex (EdgeSubdivision.collapse N e) A a :=
  ⟨selectedEdge N e A a (.inr (.inl true)) (by rw [EdgeSubdivision.edgeSupport_b, ha]),
    by change some e = some a.1; rw [ha]⟩
/-- 非分割辺の同じretained lift。 -/
def gammaRetained (a : N.EdgeInTargetSubset A) (ha : a.1 ≠ e) :
    GammaVertex (EdgeSubdivision.collapse N e) A a :=
  ⟨selectedEdge N e A a (.inl ⟨a.1, ha⟩) (EdgeSubdivision.edgeSupport_old N e _), rfl⟩
/-- 各粗辺の原表から選ぶmapped lift。 -/
def gammaChoice (a : N.EdgeInTargetSubset A) : GammaVertex (EdgeSubdivision.collapse N e) A a := by
  classical
  exact if ha : a.1 = e then gammaB N e A a ha else gammaRetained N e A a ha
/-- 出現名を保った同じ対角辺lift。 -/
def gammaDiagonal (a : N.EdgeInTargetSubset A) (ha : a.1 = e) (o : EdgeSubdivision.Occurrence N e) :
    GammaVertex (EdgeSubdivision.collapse N e) A a :=
  ⟨selectedEdge N e A a (.inr (.inr o)) (by rw [EdgeSubdivision.edgeSupport_diagonal, ha]),
    by change some e = some a.1; rw [ha]⟩
/-- 各出現の原triangle関係はbと同じ名前付き対角辺を結ぶ。 -/
def gammaTriangle (a : N.EdgeInTargetSubset A) (ha : a.1 = e) (o : EdgeSubdivision.Occurrence N e) :
    GammaEdge (EdgeSubdivision.collapse N e) A a := by
  refine ⟨⟨.inr o, ?_⟩, ?_, ?_⟩
  · obtain ⟨t,ht,hA⟩ := a.2
    exact ⟨t, by rw [EdgeSubdivision.faceSupport_triangle, ← ha]; exact ht,
      by simpa only [Set.mem_preimage, comparisonFactor_self, id_eq] using hA⟩
  · rfl
  · left
    refine ⟨rfl, ?_, ?_⟩ <;> change some e = some a.1 <;> rw [ha]

/-- 原全Γ頂点は出現ごとの二incidenceで選択liftへ接続する。 -/
theorem gamma_vertex_zigzag (a : N.EdgeInTargetSubset A)
    (v : GammaVertex (EdgeSubdivision.collapse N e) A a) :
    @Zigzag (GammaInc (EdgeSubdivision.collapse N e) A a) inferInstance
      (Sum.inl (gammaChoice N e A a)) (Sum.inl v) := by
  classical
  letI : Category (GammaInc (EdgeSubdivision.collapse N e) A a) := InducedCategory.instCategory
  rcases v with ⟨⟨v,hv⟩,hm⟩
  rcases v with b | (b | o)
  · have heq : b.1 = a.1 := Option.some.inj hm
    have hne : a.1 ≠ e := by rw [← heq]; exact b.2
    have hh : gammaChoice N e A a = ⟨⟨.inl b,hv⟩,hm⟩ := by
      simp only [gammaChoice, dif_neg hne]
      apply Subtype.ext; apply Subtype.ext
      exact congrArg Sum.inl (Subtype.ext heq.symm)
    rw [hh]
  · cases b
    · cases hm
    · have ha : a.1 = e := (Option.some.inj hm).symm
      have hh : gammaChoice N e A a = ⟨⟨.inr (.inl true),hv⟩,hm⟩ := by
        simp only [gammaChoice, dif_pos ha]
        apply Subtype.ext; apply Subtype.ext; rfl
      rw [hh]
  · have ha : a.1 = e := (Option.some.inj hm).symm
    let f := gammaTriangle N e A a ha o
    let fa : InducedCategory.Hom (F := gammaCellObj (EdgeSubdivision.collapse N e) A a)
        (Sum.inl (gammaChoice N e A a)) (Sum.inr f) :=
      ⟨IncHom.edgeFace (gammaChoice N e A a).1 f.1 2 (by
        simp only [gammaChoice, dif_pos ha]
        apply Subtype.ext; rfl)⟩
    let fb : InducedCategory.Hom (F := gammaCellObj (EdgeSubdivision.collapse N e) A a)
        (Sum.inl (⟨⟨.inr (.inr o),hv⟩,hm⟩ : GammaVertex (EdgeSubdivision.collapse N e) A a))
        (Sum.inr f) := ⟨IncHom.edgeFace _ f.1 1 rfl⟩
    exact (@Zigzag.of_hom (GammaInc (EdgeSubdivision.collapse N e) A a)
      InducedCategory.instCategory _ _ fa).trans
      (@Zigzag.of_hom (GammaInc (EdgeSubdivision.collapse N e) A a)
        InducedCategory.instCategory _ _ fb).symm

/-- 元Γの全関係も同じ出現射で接続する。 -/
theorem gamma_zigzag (a : N.EdgeInTargetSubset A) (x : GammaInc (EdgeSubdivision.collapse N e) A a) :
    @Zigzag (GammaInc (EdgeSubdivision.collapse N e) A a) inferInstance
      (Sum.inl (gammaChoice N e A a)) x := by
  letI : Category (GammaInc (EdgeSubdivision.collapse N e) A a) := InducedCategory.instCategory
  rcases x with v | f
  · exact gamma_vertex_zigzag N e A a v
  · let ff : InducedCategory.Hom (F := gammaCellObj (EdgeSubdivision.collapse N e) A a)
        (Sum.inl (gammaSource (EdgeSubdivision.collapse N e) A f)) (Sum.inr f) :=
      ⟨IncHom.edgeFace (gammaSource (EdgeSubdivision.collapse N e) A f).1 f.1 1 rfl⟩
    exact (gamma_vertex_zigzag N e A a (gammaSource (EdgeSubdivision.collapse N e) A f)).trans
      (@Zigzag.of_hom (GammaInc (EdgeSubdivision.collapse N e) A a) InducedCategory.instCategory _ _ ff)

/-- 各原Γ成分は全部分台で非空一成分。 -/
theorem gamma_components (a : N.EdgeInTargetSubset A) :
    Nonempty (ConnectedComponents (GammaInc (EdgeSubdivision.collapse N e) A a)) ∧
      Subsingleton (ConnectedComponents (GammaInc (EdgeSubdivision.collapse N e) A a)) := by
  refine ⟨⟨CategoryTheory.ConnectedComponents.mk
    (Sum.inl (gammaChoice N e A a) : GammaInc (EdgeSubdivision.collapse N e) A a)⟩,?_⟩
  constructor
  intro x y
  induction x using Quotient.inductionOn with | h x =>
    induction y using Quotient.inductionOn with | h y =>
      exact Quotient.sound ((gamma_zigzag N e A a x).symm.trans (gamma_zigzag N e A a y))

/-- 原全Φ/Γ/Λからηの全三次数両逆を生成する。次数別同型を仮定しない。 -/
def etaEquiv : ThreeCochainComplex.CochainEquiv (N.targetSubsetComplex A)
    (pushforwardComplex (EdgeSubdivision.collapse N e) A) :=
  localUnitEquiv _ A (phi_components N e A) (gamma_components N e A) (lambda_single N e A)
/-- 生成同型の順Homは同じ原η。 -/
theorem etaEquiv_toHom : (etaEquiv N e A).toHom = unitHom (EdgeSubdivision.collapse N e) A := rfl

end AAT.AG.AtlasCoefficientFiber.SubdivisionCoefficients

#print axioms AAT.AG.AtlasCoefficientFiber.SubdivisionCoefficients.oldChart
#print axioms AAT.AG.AtlasCoefficientFiber.SubdivisionCoefficients.cEdge
#print axioms AAT.AG.AtlasCoefficientFiber.SubdivisionCoefficients.vertex_zigzag
#print axioms AAT.AG.AtlasCoefficientFiber.SubdivisionCoefficients.face_empty
#print axioms AAT.AG.AtlasCoefficientFiber.SubdivisionCoefficients.zigzag
#print axioms AAT.AG.AtlasCoefficientFiber.SubdivisionCoefficients.phi_components
#print axioms AAT.AG.AtlasCoefficientFiber.SubdivisionCoefficients.lambdaEquiv
#print axioms AAT.AG.AtlasCoefficientFiber.SubdivisionCoefficients.lambda_single
#print axioms AAT.AG.AtlasCoefficientFiber.SubdivisionCoefficients.selectedEdge
#print axioms AAT.AG.AtlasCoefficientFiber.SubdivisionCoefficients.gammaB
#print axioms AAT.AG.AtlasCoefficientFiber.SubdivisionCoefficients.gammaRetained
#print axioms AAT.AG.AtlasCoefficientFiber.SubdivisionCoefficients.gammaChoice
#print axioms AAT.AG.AtlasCoefficientFiber.SubdivisionCoefficients.gammaDiagonal
#print axioms AAT.AG.AtlasCoefficientFiber.SubdivisionCoefficients.gammaTriangle
#print axioms AAT.AG.AtlasCoefficientFiber.SubdivisionCoefficients.gamma_vertex_zigzag
#print axioms AAT.AG.AtlasCoefficientFiber.SubdivisionCoefficients.gamma_zigzag
#print axioms AAT.AG.AtlasCoefficientFiber.SubdivisionCoefficients.gamma_components
#print axioms AAT.AG.AtlasCoefficientFiber.SubdivisionCoefficients.etaEquiv
#print axioms AAT.AG.AtlasCoefficientFiber.SubdivisionCoefficients.etaEquiv_toHom
#print axioms AAT.AG.AtlasCoefficientFiber.SubdivisionCoefficients.gammaB.congr_simp
#print axioms AAT.AG.AtlasCoefficientFiber.SubdivisionCoefficients.gammaRetained.congr_simp
#assert_standard_axioms_only AAT.AG.AtlasCoefficientFiber.SubdivisionCoefficients
