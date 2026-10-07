import ResearchLean.AG.AtlasCoefficientFiber.PhiComma
import ResearchLean.AG.AtlasCoefficientFiber.GammaComma
import ResearchLean.AG.AtlasCoefficientFiber.CoefficientEvaluation

/-!
# G-135 A：原始fiberのincidence自然性

## Implementation notes

原始Φ・Γ・Λから実comma成分への同値を使い、incidenceの前合成を局所成分へ戻す。
その写像が細セルの指定端点・辺位置を読むことを証明する。
同値と前合成を独立に構成するため、自然性を新しい入力certificateにしない。
-/
noncomputable section
namespace AAT.AG.AtlasCoefficientFiber
open CategoryTheory CanonicalResolution ResolutionInvariance FaceRelationSubdivision
universe u
variable {Source : Type u} {qc qf : Reading Source} {h : qc.CoarserThan qf}
variable {Nc : TargetSupportedNerve.{u, u} qc} {Nf : TargetSupportedNerve.{u, u} qf}
variable (M : IncidenceSupportedComparison qc qf h Nc Nf) (A : Set qc.Target)

/-- Γの成分から指定粗端点のΦ成分への写像。実commaの前合成から生成する。 -/
def endpointComponents (e : Nc.EdgeInTargetSubset A) (s : Bool)
    (k : CategoryTheory.ConnectedComponents (GammaInc M A e)) :
    CategoryTheory.ConnectedComponents (PhiInc M A (edgeEndpoint Nc A e s)) :=
  (phiComponentsEquiv M A _).symm
    ((StructuredArrow.map (IncHom.chartEdge (edgeEndpoint Nc A e s) e s rfl)).mapConnectedComponents
      (gammaComponentsEquiv M A e k))

/-- Λの持ち上げ面から指定粗辺のΓ成分への写像。同じincidenceの前合成を読む。 -/
def faceEdgeComponents (F : Nc.FaceInTargetSubset A) (i : Fin 3)
    (f : LambdaFace M A F) :
    CategoryTheory.ConnectedComponents (GammaInc M A (faceEdge Nc A F i)) :=
  (gammaComponentsEquiv M A _).symm
    ((StructuredArrow.map (IncHom.edgeFace (faceEdge Nc A F i) F i rfl)).mapConnectedComponents
      ((lambdaComponentsEquiv M A F).symm f))

/-- Γ成分上の右Kan chart→edge係数射はendpointComponentsでの関数制限である。 -/
theorem coefficient_endpoint_naturality (e : Nc.EdgeInTargetSubset A) (s : Bool)
    (z : (pushforwardCoefficients M A).obj (.chart (edgeEndpoint Nc A e s)))
    (k : CategoryTheory.ConnectedComponents (GammaInc M A e)) :
    gammaCoefficientEquiv M A e
      ((pushforwardCoefficients M A).map (IncHom.chartEdge (edgeEndpoint Nc A e s) e s rfl) z) k =
    phiCoefficientEquiv M A (edgeEndpoint Nc A e s) z (endpointComponents M A e s k) := by
  rw [gammaCoefficientEquiv_apply, phiCoefficientEquiv_apply]
  rw [← phiComponentsEquiv_apply]
  change _ = ((coefficientCellIso (Carrier.preimageFunctor M A) _).hom z
    ((phiComponentsEquiv M A _)
      ((phiComponentsEquiv M A _).symm _))).down
  rw [Equiv.apply_symm_apply]
  exact congrArg ULift.down (coefficientPushforward_map_component_eval
    (Carrier.preimageFunctor M A) _ z ((gammaCommaFunctor M A e).mapConnectedComponents k))

/-- Λ上の右Kan edge→face係数射はfaceEdgeComponentsでの関数制限である。 -/
theorem coefficient_faceEdge_naturality (F : Nc.FaceInTargetSubset A) (i : Fin 3)
    (z : (pushforwardCoefficients M A).obj (.edge (faceEdge Nc A F i)))
    (f : LambdaFace M A F) :
    lambdaCoefficientEquiv M A F
      ((pushforwardCoefficients M A).map (IncHom.edgeFace (faceEdge Nc A F i) F i rfl) z) f =
    gammaCoefficientEquiv M A (faceEdge Nc A F i) z (faceEdgeComponents M A F i f) := by
  rw [lambdaCoefficientEquiv_apply, gammaCoefficientEquiv_apply]
  rw [← gammaComponentsEquiv_apply]
  change _ = ((coefficientCellIso (Carrier.preimageFunctor M A) _).hom z
    ((gammaComponentsEquiv M A _)
      ((gammaComponentsEquiv M A _).symm _))).down
  rw [Equiv.apply_symm_apply]
  exact congrArg ULift.down (coefficientPushforward_map_eval
    (Carrier.preimageFunctor M A) _ z (lambdaCommaObj M A F f))

/-- Γの原始mapped辺の指定端点を、同じ粗端点上のΦ chartとして生成する。 -/
def gammaEndpointChart (e : Nc.EdgeInTargetSubset A) (s : Bool) (v : GammaVertex M A e) :
    PhiChart M A (edgeEndpoint Nc A e s) :=
  ⟨edgeEndpoint Nf (comparisonFactor qc qf h ⁻¹' A) v.1 s,
    (Carrier.preimageFunctor_edge_endpoint_of_some M A v.1 e.1 v.2 s).trans
      (congrArg (fun a => edgeEndpoint Nc A a s) (Subtype.ext rfl))⟩

/-- 原始mapped端点の細chart名。定義所有者API。 -/
@[simp] theorem gammaEndpointChart_val (e : Nc.EdgeInTargetSubset A) (s : Bool)
    (v : GammaVertex M A e) :
    (gammaEndpointChart M A e s v).1 = edgeEndpoint Nf (comparisonFactor qc qf h ⁻¹' A) v.1 s := rfl

/-- mapped細辺の指定端点から、Γ包含の前合成comma対象への実incidence射。 -/
def gammaEndpointCommaArrow (e : Nc.EdgeInTargetSubset A) (s : Bool)
    (v : GammaVertex M A e) :
    (phiCommaFunctor M A _).obj (.inl (gammaEndpointChart M A e s v)) ⟶
      (StructuredArrow.map (IncHom.chartEdge (edgeEndpoint Nc A e s) e s rfl)).obj
        ((gammaCommaFunctor M A e).obj (.inl v)) :=
  StructuredArrow.homMk
    (IncHom.chartEdge (edgeEndpoint Nf (comparisonFactor qc qf h ⁻¹' A) v.1 s) v.1 s rfl) (by
      change ((phiCommaFunctor M A _).obj (.inl (gammaEndpointChart M A e s v))).hom ≫
          (Carrier.preimageFunctor M A).map
            (IncHom.chartEdge (edgeEndpoint Nf (comparisonFactor qc qf h ⁻¹' A) v.1 s) v.1 s rfl) =
        IncHom.chartEdge (edgeEndpoint Nc A e s) e s rfl ≫
          ((gammaCommaFunctor M A e).obj (.inl v)).hom
      rw [phiCommaFunctor_obj_hom, gammaCommaFunctor_obj_hom]
      apply incHomCode_injective
      rw [incHomCode_eqToHom_comp, incHomCode_comp_eqToHom,
        Carrier.preimageFunctor_map_chartEdge_code_of_some M A _ v.1 e.1 v.2 s rfl]
      rfl)

/-- endpointComponentsは、原始mapped辺の指定端点が属するΦ成分を返す。 -/
theorem endpointComponents_vertex (e : Nc.EdgeInTargetSubset A) (s : Bool)
    (v : GammaVertex M A e) :
    endpointComponents M A e s (CategoryTheory.ConnectedComponents.mk (.inl v)) =
      CategoryTheory.ConnectedComponents.mk (.inl (gammaEndpointChart M A e s v)) := by
  apply (phiComponentsEquiv M A _).injective
  simp only [endpointComponents, Equiv.apply_symm_apply, phiComponentsEquiv_apply,
    gammaComponentsEquiv_apply, Functor.mapConnectedComponents_mk]
  exact Quotient.sound (Zigzag.of_hom (gammaEndpointCommaArrow M A e s v)).symm

/-- Λの持ち上げ面の指定細辺を、同じ粗辺上の原始Γ頂点として生成する。 -/
def lambdaEdgeVertex (F : Nc.FaceInTargetSubset A) (i : Fin 3) (f : LambdaFace M A F) :
    GammaVertex M A (faceEdge Nc A F i) :=
  ⟨faceEdge Nf (comparisonFactor qc qf h ⁻¹' A) f.1 i, by
    have hF : M.targetSubsetFaceMap A _ (fun _ ht => ht) f.1 F.1 f.2 = F := Subtype.ext rfl
    simpa only [hF] using Carrier.preimageFunctor_face_edgeMap_of_some M A f.1 F.1 f.2 i⟩

/-- 原始持ち上げの指定細辺名。定義所有者API。 -/
@[simp] theorem lambdaEdgeVertex_val (F : Nc.FaceInTargetSubset A) (i : Fin 3)
    (f : LambdaFace M A F) :
    (lambdaEdgeVertex M A F i f).1 = faceEdge Nf (comparisonFactor qc qf h ⁻¹' A) f.1 i := rfl

/-- 指定細辺から、Λ包含の前合成comma対象への同じ原始edgeFace射。 -/
def lambdaEdgeCommaArrow (F : Nc.FaceInTargetSubset A) (i : Fin 3)
    (f : LambdaFace M A F) :
    (gammaCommaFunctor M A _).obj (.inl (lambdaEdgeVertex M A F i f)) ⟶
      (StructuredArrow.map (IncHom.edgeFace (faceEdge Nc A F i) F i rfl)).obj
        (lambdaCommaObj M A F f) :=
  StructuredArrow.homMk
    (IncHom.edgeFace (faceEdge Nf (comparisonFactor qc qf h ⁻¹' A) f.1 i) f.1 i rfl) (by
      change ((gammaCommaFunctor M A _).obj (.inl (lambdaEdgeVertex M A F i f))).hom ≫
          (Carrier.preimageFunctor M A).map
            (IncHom.edgeFace (faceEdge Nf (comparisonFactor qc qf h ⁻¹' A) f.1 i) f.1 i rfl) =
        IncHom.edgeFace (faceEdge Nc A F i) F i rfl ≫ (lambdaCommaObj M A F f).hom
      rw [gammaCommaFunctor_obj_hom, lambdaCommaObj_hom]
      apply incHomCode_injective
      rw [incHomCode_eqToHom_comp, incHomCode_comp_eqToHom,
        Carrier.preimageFunctor_map_edgeFace_code_of_some M A _ f.1 F.1 f.2 i rfl]
      rfl)

/-- faceEdgeComponentsは、原始持ち上げ面の指定細辺が属するΓ成分を返す。 -/
theorem faceEdgeComponents_lift (F : Nc.FaceInTargetSubset A) (i : Fin 3)
    (f : LambdaFace M A F) :
    faceEdgeComponents M A F i f =
      CategoryTheory.ConnectedComponents.mk (.inl (lambdaEdgeVertex M A F i f)) := by
  apply (gammaComponentsEquiv M A _).injective
  simp only [faceEdgeComponents, Equiv.apply_symm_apply, gammaComponentsEquiv_apply,
    lambdaComponentsEquiv_symm_apply, Functor.mapConnectedComponents_mk]
  exact Quotient.sound (Zigzag.of_hom (lambdaEdgeCommaArrow M A F i f)).symm

/-- 原始Γ関係の負符号端点から同じmixed面へのincidence射。 -/
def gammaSourceIncidence (e : Nc.EdgeInTargetSubset A) (m : GammaEdge M A e) :
    InducedCategory.Hom (F := gammaCellObj M A e) (.inl (gammaSource M A m)) (.inr m) :=
  InducedCategory.homMk (IncHom.edgeFace (gammaSource M A m).1 m.1 1 (by rw [gammaSource_val]; rfl))

/-- 原始Γ関係の正符号端点から同じmixed面へのincidence射。二パターンをMで判別。 -/
def gammaTargetIncidence (e : Nc.EdgeInTargetSubset A) (m : GammaEdge M A e) :
    InducedCategory.Hom (F := gammaCellObj M A e) (.inl (gammaTarget M A m)) (.inr m) := by
  classical
  by_cases h0 : M.edgeMap (Nf.nerve.faceEdge0 m.1.1) = none
  · exact InducedCategory.homMk (IncHom.edgeFace (gammaTarget M A m).1 m.1 2
      (by rw [gammaTarget_val_of_left M A m h0]; rfl))
  · have hs : M.edgeMap (Nf.nerve.faceEdge0 m.1.1) = some e.1 := by
      rcases m.2.2 with hl | hr
      · exact False.elim (h0 hl.1)
      · exact hr.1
    exact InducedCategory.homMk (IncHom.edgeFace (gammaTarget M A m).1 m.1 0
      (by rw [gammaTarget_val_of_right M A m hs]; rfl))

/-- Γの原始関係の二端点は同じΓ成分を持つ。loopでも同じ原始出現射を使う。 -/
theorem gamma_relation_component (e : Nc.EdgeInTargetSubset A) (m : GammaEdge M A e) :
    (CategoryTheory.ConnectedComponents.mk (.inl (gammaSource M A m)) : CategoryTheory.ConnectedComponents (GammaInc M A e)) =
      (CategoryTheory.ConnectedComponents.mk (.inl (gammaTarget M A m)) : CategoryTheory.ConnectedComponents (GammaInc M A e)) :=
  Quotient.sound ((Zigzag.of_hom (gammaSourceIncidence M A e m)).trans
    (Zigzag.of_hom (gammaTargetIncidence M A e m)).symm)

/-- 全Γ成分は原始mapped辺頂点を代表元に持つ。mixed面は負符号端点と連結する。 -/
theorem gammaComponent_vertex_representative (e : Nc.EdgeInTargetSubset A)
    (k : CategoryTheory.ConnectedComponents (GammaInc M A e)) :
    ∃ v : GammaVertex M A e, CategoryTheory.ConnectedComponents.mk (.inl v) = k := by
  induction k using Quotient.inductionOn with
  | h x =>
    rcases x with v | m
    · exact ⟨v, rfl⟩
    · exact ⟨gammaSource M A m, Quotient.sound (Zigzag.of_hom (gammaSourceIncidence M A e m))⟩

/-- mixed原始関係の二端点は、指定粗端点上でも同じΦ成分を持つ。 -/
theorem gamma_endpoint_relation (e : Nc.EdgeInTargetSubset A) (s : Bool) (m : GammaEdge M A e) :
    (CategoryTheory.ConnectedComponents.mk (.inl (gammaEndpointChart M A e s (gammaSource M A m))) :
      CategoryTheory.ConnectedComponents (PhiInc M A (edgeEndpoint Nc A e s))) =
      CategoryTheory.ConnectedComponents.mk (.inl (gammaEndpointChart M A e s (gammaTarget M A m))) := by
  have hh := congrArg (endpointComponents M A e s) (gamma_relation_component M A e m)
  simpa only [endpointComponents_vertex] using hh

/-- 粗端点等号を含むincidenceから生成したΓ→Φ成分写像。面の二経路を同じchartで読む。 -/
def endpointComponentsAt (c : Nc.ChartInTargetSubset A) (e : Nc.EdgeInTargetSubset A)
    (s : Bool) (hc : c = edgeEndpoint Nc A e s)
    (k : CategoryTheory.ConnectedComponents (GammaInc M A e)) :
    CategoryTheory.ConnectedComponents (PhiInc M A c) :=
  (phiComponentsEquiv M A c).symm
    ((StructuredArrow.map (IncHom.chartEdge c e s hc)).mapConnectedComponents
      (gammaComponentsEquiv M A e k))

/-- 持ち上げ面の頂点出現に沿うΦ成分。同じchartFace射の前合成から生成する。 -/
def faceVertexComponents (F : Nc.FaceInTargetSubset A) (i : Fin 3) (f : LambdaFace M A F) :
    CategoryTheory.ConnectedComponents (PhiInc M A (faceVertex Nc A F i)) :=
  (phiComponentsEquiv M A _).symm
    ((StructuredArrow.map (IncHom.chartFace (faceVertex Nc A F i) F i rfl)).mapConnectedComponents
      ((lambdaComponentsEquiv M A F).symm f))

/-- 成分incidenceは、元の三角形の同じ頂点へ至る二経路を保持する。 -/
theorem endpoint_faceEdge_components (F : Nc.FaceInTargetSubset A) (i : Fin 3) (s : Bool)
    (f : LambdaFace M A F) :
    endpointComponentsAt M A (faceVertex Nc A F (endpointPosition i s)) (faceEdge Nc A F i) s
      (edgeEndpoint_faceEdge Nc A F i s).symm (faceEdgeComponents M A F i f) =
      faceVertexComponents M A F (endpointPosition i s) f := by
  apply (phiComponentsEquiv M A _).injective
  simp only [endpointComponentsAt, faceEdgeComponents, faceVertexComponents, Equiv.apply_symm_apply,
    lambdaComponentsEquiv_symm_apply, Functor.mapConnectedComponents_mk]
  rw [← StructuredArrow.map_comp, chartEdge_edgeFace_comp]

/-- Φ辺の原始端点から同じ垂直辺へのincidence。 -/
def phiEndpointIncidence (c : Nc.ChartInTargetSubset A) (e : PhiEdge M A c) (s : Bool) :
    InducedCategory.Hom (F := phiCellObj M A c) (.inl (phiEndpoint M A e s)) (.inr (.inl e)) :=
  InducedCategory.homMk (IncHom.chartEdge (phiEndpoint M A e s).1 e.1 s (phiEndpoint_val M A e s))

/-- 垂直Φ面の第一頂点を原始端点から生成する。 -/
def phiFaceChart (c : Nc.ChartInTargetSubset A) (f : PhiFace M A c) : PhiChart M A c :=
  phiEndpoint M A (phiFaceEdge M A f 0) false

/-- Φ面の原始第一頂点から同じ垂直面へのincidence。 -/
def phiFaceChartIncidence (c : Nc.ChartInTargetSubset A) (f : PhiFace M A c) :
    InducedCategory.Hom (F := phiCellObj M A c) (.inl (phiFaceChart M A c f)) (.inr (.inr f)) :=
  InducedCategory.homMk (IncHom.chartFace (phiFaceChart M A c f).1 f.1 0 (by
    rw [phiFaceChart, phiEndpoint_val, phiFaceEdge_val]
    exact edgeEndpoint_faceEdge Nf _ f.1 0 false))

/-- 全Φ成分は原始細chartを代表元に持つ。垂直辺・面は同じ原始頂点と連結する。 -/
theorem phiComponent_chart_representative (c : Nc.ChartInTargetSubset A)
    (k : CategoryTheory.ConnectedComponents (PhiInc M A c)) :
    ∃ v : PhiChart M A c, CategoryTheory.ConnectedComponents.mk (.inl v) = k := by
  induction k using Quotient.inductionOn with
  | h x =>
    rcases x with v | w
    · exact ⟨v, rfl⟩
    · rcases w with e | f
      · exact ⟨phiEndpoint M A e false, Quotient.sound (Zigzag.of_hom (phiEndpointIncidence M A c e false))⟩
      · exact ⟨phiFaceChart M A c f, Quotient.sound (Zigzag.of_hom (phiFaceChartIncidence M A c f))⟩

end AAT.AG.AtlasCoefficientFiber
#print axioms AAT.AG.AtlasCoefficientFiber.endpointComponents
#print axioms AAT.AG.AtlasCoefficientFiber.faceEdgeComponents
#print axioms AAT.AG.AtlasCoefficientFiber.coefficient_endpoint_naturality
#print axioms AAT.AG.AtlasCoefficientFiber.coefficient_faceEdge_naturality
#print axioms AAT.AG.AtlasCoefficientFiber.gammaEndpointChart
#print axioms AAT.AG.AtlasCoefficientFiber.gammaEndpointChart_val
#print axioms AAT.AG.AtlasCoefficientFiber.gammaEndpointCommaArrow
#print axioms AAT.AG.AtlasCoefficientFiber.endpointComponents_vertex
#print axioms AAT.AG.AtlasCoefficientFiber.lambdaEdgeVertex
#print axioms AAT.AG.AtlasCoefficientFiber.lambdaEdgeVertex_val
#print axioms AAT.AG.AtlasCoefficientFiber.lambdaEdgeCommaArrow
#print axioms AAT.AG.AtlasCoefficientFiber.faceEdgeComponents_lift
#print axioms AAT.AG.AtlasCoefficientFiber.gammaSourceIncidence
#print axioms AAT.AG.AtlasCoefficientFiber.gammaTargetIncidence
#print axioms AAT.AG.AtlasCoefficientFiber.gamma_relation_component
#print axioms AAT.AG.AtlasCoefficientFiber.gammaComponent_vertex_representative
#print axioms AAT.AG.AtlasCoefficientFiber.gamma_endpoint_relation
#print axioms AAT.AG.AtlasCoefficientFiber.endpointComponentsAt
#print axioms AAT.AG.AtlasCoefficientFiber.faceVertexComponents
#print axioms AAT.AG.AtlasCoefficientFiber.endpoint_faceEdge_components
#print axioms AAT.AG.AtlasCoefficientFiber.phiEndpointIncidence
#print axioms AAT.AG.AtlasCoefficientFiber.phiFaceChart
#print axioms AAT.AG.AtlasCoefficientFiber.phiFaceChartIncidence
#print axioms AAT.AG.AtlasCoefficientFiber.phiComponent_chart_representative
#assert_standard_axioms_only AAT.AG.AtlasCoefficientFiber
