import ResearchLean.AG.AtlasCoefficientFiber.SupportCoefficients
import ResearchLean.AG.AtlasCoefficientFiber.LocalEvaluation
import ResearchLean.AG.FaceRelationSubdivision.ComparisonRestriction

/-!
# G-135 D：元の順像複体と二射の台制限

## Implementation notes

各粗セルの実comma前合成を直積し、元の右Kan Pの制限を作る。
原incidence自然性を微分可換性に使い、定数係数とcounitの同じ値へ戻す。
商双対をPの定義へ交換する案は、元の順像との同定義務を失うため採らない。
-/
noncomputable section
namespace AAT.AG.AtlasCoefficientFiber
open CategoryTheory CanonicalResolution ResolutionInvariance FaceRelationSubdivision TwoPhase
universe u
variable {Source : Type u} {qc qf : Reading Source} {h : qc.CoarserThan qf}
variable {Nc : TargetSupportedNerve.{u,u} qc} {Nf : TargetSupportedNerve.{u,u} qf}
variable (M : IncidenceSupportedComparison qc qf h Nc Nf) {A B : Set qc.Target} (hab : A ⊆ B)

/-- 元のPのchart直積を同じcomma制限で読む。 -/
def supportPushforward0 : (pushforwardComplex M B).C0 →ₗ[ℚ] (pushforwardComplex M A).C0 :=
  LinearMap.pi fun c => (supportCoefficientRestrict M hab (.chart c)).comp
    (LinearMap.proj (supportCellInclude Nc.chartSupport hab c))

/-- 元のPの辺直積を同じcomma制限で読む。 -/
def supportPushforward1 : (pushforwardComplex M B).C1 →ₗ[ℚ] (pushforwardComplex M A).C1 :=
  LinearMap.pi fun e => (supportCoefficientRestrict M hab (.edge e)).comp
    (LinearMap.proj (supportCellInclude Nc.edgeSupport hab e))

/-- 元のPの面直積を同じcomma制限で読む。 -/
def supportPushforward2 : (pushforwardComplex M B).C2 →ₗ[ℚ] (pushforwardComplex M A).C2 :=
  LinearMap.pi fun f => (supportCoefficientRestrict M hab (.face f)).comp
    (LinearMap.proj (supportCellInclude Nc.faceSupport hab f))

/-- chart値は元の係数制限の値。 -/
theorem supportPushforward0_apply (z : (pushforwardComplex M B).C0) (c : Nc.ChartInTargetSubset A) :
    supportPushforward0 M hab z c =
      supportCoefficientRestrict M hab (.chart c) (z (supportCellInclude Nc.chartSupport hab c)) := rfl

/-- 辺値は元の係数制限の値。 -/
theorem supportPushforward1_apply (z : (pushforwardComplex M B).C1) (e : Nc.EdgeInTargetSubset A) :
    supportPushforward1 M hab z e =
      supportCoefficientRestrict M hab (.edge e) (z (supportCellInclude Nc.edgeSupport hab e)) := rfl

/-- 面値は元の係数制限の値。 -/
theorem supportPushforward2_apply (z : (pushforwardComplex M B).C2) (f : Nc.FaceInTargetSubset A) :
    supportPushforward2 M hab z f =
      supportCoefficientRestrict M hab (.face f) (z (supportCellInclude Nc.faceSupport hab f)) := rfl

/-- 同じ左右出現の係数射と制限は、元の端点名の輸送を含め可換。 -/
theorem supportCoefficientRestrict_endpoint (z : (pushforwardComplex M B).C0)
    (e : Nc.EdgeInTargetSubset A) (s : Bool) :
    supportCoefficientRestrict M hab (.edge e)
      ((pushforwardCoefficients M B).map
        (IncHom.chartEdge (edgeEndpoint Nc B (supportCellInclude Nc.edgeSupport hab e) s)
          (supportCellInclude Nc.edgeSupport hab e) s rfl)
        (z (edgeEndpoint Nc B (supportCellInclude Nc.edgeSupport hab e) s))) =
      (pushforwardCoefficients M A).map
        (IncHom.chartEdge (edgeEndpoint Nc A e s) e s rfl)
        (supportCoefficientRestrict M hab (.chart (edgeEndpoint Nc A e s))
          (z (supportCellInclude Nc.chartSupport hab (edgeEndpoint Nc A e s)))) := by
  have hn := supportCoefficientRestrict_natural M hab
    (IncHom.chartEdge (edgeEndpoint Nc A e s) e s rfl)
    (z (supportCellInclude Nc.chartSupport hab (edgeEndpoint Nc A e s)))
  rw [supportIncFunctor_map_chartEdge] at hn
  erw [coefficient_endpoint_chart_eval Nc B (pushforwardCoefficients M B) z
    (supportCellInclude Nc.edgeSupport hab e) s _ (supportCellInclude_endpoint Nc hab e s)] at hn
  exact hn

/-- 同じ三辺出現の係数射と制限は、原辺名の輸送を含め可換。 -/
theorem supportCoefficientRestrict_faceEdge (z : (pushforwardComplex M B).C1)
    (f : Nc.FaceInTargetSubset A) (i : Fin 3) :
    supportCoefficientRestrict M hab (.face f)
      ((pushforwardCoefficients M B).map
        (IncHom.edgeFace (faceEdge Nc B (supportCellInclude Nc.faceSupport hab f) i)
          (supportCellInclude Nc.faceSupport hab f) i rfl)
        (z (faceEdge Nc B (supportCellInclude Nc.faceSupport hab f) i))) =
      (pushforwardCoefficients M A).map
        (IncHom.edgeFace (faceEdge Nc A f i) f i rfl)
        (supportCoefficientRestrict M hab (.edge (faceEdge Nc A f i))
          (z (supportCellInclude Nc.edgeSupport hab (faceEdge Nc A f i)))) := by
  have hn := supportCoefficientRestrict_natural M hab
    (IncHom.edgeFace (faceEdge Nc A f i) f i rfl)
    (z (supportCellInclude Nc.edgeSupport hab (faceEdge Nc A f i)))
  rw [supportIncFunctor_map_edgeFace] at hn
  erw [coefficient_face_edge_eval Nc B (pushforwardCoefficients M B) z
    (supportCellInclude Nc.faceSupport hab f) i _ (supportCellInclude_faceEdge Nc hab f i)] at hn
  exact hn

/-- 元Pの第一微分は左右出現の自然性で制限と可換。 -/
theorem supportPushforward_comm0 (z : (pushforwardComplex M B).C0) :
    supportPushforward1 M hab ((pushforwardComplex M B).d0 z) =
      (pushforwardComplex M A).d0 (supportPushforward0 M hab z) := by
  funext e
  rw [supportPushforward1_apply, pushforwardComplex_d0_apply,
    pushforwardComplex_d0_apply, map_sub, supportPushforward0_apply, supportPushforward0_apply]
  exact congrArg₂ (fun x y => x - y)
    (supportCoefficientRestrict_endpoint M hab z e true)
    (supportCoefficientRestrict_endpoint M hab z e false)

/-- 元Pの第二微分は三辺出現と同じ符号を保って制限と可換。 -/
theorem supportPushforward_comm1 (z : (pushforwardComplex M B).C1) :
    supportPushforward2 M hab ((pushforwardComplex M B).d1 z) =
      (pushforwardComplex M A).d1 (supportPushforward1 M hab z) := by
  funext f
  rw [supportPushforward2_apply, pushforwardComplex_d1_apply,
    pushforwardComplex_d1_apply, map_add, map_sub,
    supportPushforward1_apply, supportPushforward1_apply, supportPushforward1_apply]
  exact congrArg₂ (fun x y => x + y)
    (congrArg₂ (fun x y => x - y)
      (supportCoefficientRestrict_faceEdge M hab z f 0)
      (supportCoefficientRestrict_faceEdge M hab z f 1))
    (supportCoefficientRestrict_faceEdge M hab z f 2)

/-- 全三次数の原右Kan Pを制限する実cochain Hom。 -/
def supportPushforwardHom : ThreeCochainComplex.Hom (pushforwardComplex M B) (pushforwardComplex M A) where
  f0 := supportPushforward0 M hab
  f1 := supportPushforward1 M hab
  f2 := supportPushforward2 M hab
  comm0 := supportPushforward_comm0 M hab
  comm1 := supportPushforward_comm1 M hab

/-- P制限の次数0を読む所有者API。 -/
@[simp] theorem supportPushforwardHom_f0 : (supportPushforwardHom M hab).f0 = supportPushforward0 M hab := rfl
/-- P制限の次数1を読む所有者API。 -/
@[simp] theorem supportPushforwardHom_f1 : (supportPushforwardHom M hab).f1 = supportPushforward1 M hab := rfl
/-- P制限の次数2を読む所有者API。 -/
@[simp] theorem supportPushforwardHom_f2 : (supportPushforwardHom M hab).f2 = supportPushforward2 M hab := rfl

/-- comma前合成は元の定数係数値を保存する。 -/
theorem supportCoefficientRestrict_constant (σ : Inc Nc A) (q : ℚ) :
    supportCoefficientRestrict M hab σ
      (coefficientConstant (Carrier.preimageFunctor M B) ((supportIncFunctor Nc hab).obj σ) q) =
      coefficientConstant (Carrier.preimageFunctor M A) σ q := by
  apply (coefficientCellIso (Carrier.preimageFunctor M A) σ).toLinearEquiv.injective
  change (coefficientCellIso (Carrier.preimageFunctor M A) σ).hom (_) =
    (coefficientCellIso (Carrier.preimageFunctor M A) σ).hom (_)
  funext c
  rw [supportCoefficientRestrict_component, coefficientConstant_eval, coefficientConstant_eval]

/-- 元ηのchart値と台制限は全cochainで可換。 -/
theorem supportUnit0 (z : (Nc.targetSubsetComplex B).C0) :
    supportPushforward0 M hab (unit0 M B z) =
      unit0 M A (selectedRestrict Nc.chartSupport hab z) := by
  funext c
  rw [supportPushforward0_apply, unit0_apply, unit0_apply, selectedRestrict_apply]
  exact supportCoefficientRestrict_constant M hab (.chart c) _

/-- 元ηの辺値と台制限も全cochainで可換。 -/
theorem supportUnit1 (z : (Nc.targetSubsetComplex B).C1) :
    supportPushforward1 M hab (unit1 M B z) =
      unit1 M A (selectedRestrict Nc.edgeSupport hab z) := by
  funext e
  rw [supportPushforward1_apply, unit1_apply, unit1_apply, selectedRestrict_apply]
  exact supportCoefficientRestrict_constant M hab (.edge e) _

/-- 元ηの面値と台制限も全cochainで可換。 -/
theorem supportUnit2 (z : (Nc.targetSubsetComplex B).C2) :
    supportPushforward2 M hab (unit2 M B z) =
      unit2 M A (selectedRestrict Nc.faceSupport hab z) := by
  funext f
  rw [supportPushforward2_apply, unit2_apply, unit2_apply, selectedRestrict_apply]
  exact supportCoefficientRestrict_constant M hab (.face f) _

/-- 原unit ηの台自然性を全三次数の同じcochain Homへ接続する。 -/
theorem supportUnitHom :
    AtlasDefectComposition.cochainComp (unitHom M B) (supportPushforwardHom M hab) =
      AtlasDefectComposition.cochainComp (subsetRestrictHom Nc hab) (unitHom M A) := by
  apply AtlasDefectComposition.cochain_ext
  · ext z
    simpa only [AtlasDefectComposition.cochainComp_f0, unitHom_f0, supportPushforwardHom_f0,
      subsetRestrictHom_f0, LinearMap.comp_apply] using supportUnit0 M hab z
  · ext z
    simpa only [AtlasDefectComposition.cochainComp_f1, unitHom_f1, supportPushforwardHom_f1,
      subsetRestrictHom_f1, LinearMap.comp_apply] using supportUnit1 M hab z
  · ext z
    simpa only [AtlasDefectComposition.cochainComp_f2, unitHom_f2, supportPushforwardHom_f2,
      subsetRestrictHom_f2, LinearMap.comp_apply] using supportUnit2 M hab z

/-- 元counitの輸送comma対象も同じ台包含の対象になる。 -/
theorem supportCommaFunctor_transport (j : Inc Nf (comparisonFactor qc qf h ⁻¹' A))
    {σ : Inc Nc A} (hj : (Carrier.preimageFunctor M A).obj j = σ)
    (hjB : (Carrier.preimageFunctor M B).obj
      ((supportIncFunctor Nf (supportPreimageInclude (h := h) hab)).obj j) =
        (supportIncFunctor Nc hab).obj σ) :
    (supportCommaFunctor M hab σ).obj (StructuredArrow.mk (eqToHom hj.symm)) =
      StructuredArrow.mk (eqToHom hjB.symm) := by
  apply StructuredArrow.obj_ext _ _ (show
    ((supportCommaFunctor M hab σ).obj (StructuredArrow.mk (eqToHom hj.symm))).right =
      (StructuredArrow.mk (eqToHom hjB.symm)).right from rfl)
  rw [supportCommaFunctor_obj_hom, supportCarrierIso_hom_app]
  simp only [StructuredArrow.mk_hom_eq_self, eqToHom_map,
    eqToHom_refl, CategoryTheory.Functor.map_id, Category.comp_id]
  rw [eqToHom_trans]

/-- 原counit有理評価は同じ台制限と全細セルで可換。 -/
theorem supportCoefficientEvaluationAt (j : Inc Nf (comparisonFactor qc qf h ⁻¹' A))
    {σ : Inc Nc A} (hj : (Carrier.preimageFunctor M A).obj j = σ)
    (hjB : (Carrier.preimageFunctor M B).obj
      ((supportIncFunctor Nf (supportPreimageInclude (h := h) hab)).obj j) =
        (supportIncFunctor Nc hab).obj σ)
    (z : (pushforwardCoefficients M B).obj ((supportIncFunctor Nc hab).obj σ)) :
    coefficientEvaluationAt (Carrier.preimageFunctor M A) j hj
      (supportCoefficientRestrict M hab σ z) =
    coefficientEvaluationAt (Carrier.preimageFunctor M B)
      ((supportIncFunctor Nf (supportPreimageInclude (h := h) hab)).obj j) hjB z := by
  rw [coefficientEvaluationAt_cellIso, coefficientEvaluationAt_cellIso,
    supportCoefficientRestrict_eval, supportCommaFunctor_transport M hab j hj hjB]

/-- 原εの次数0評価と元細セルの台制限は全値で可換。 -/
theorem supportEvaluation0 (z : (pushforwardComplex M B).C0) :
    evaluation0 M A (supportPushforward0 M hab z) =
      selectedRestrict Nf.chartSupport (fun _ ht => hab ht) (evaluation0 M B z) := by
  funext c
  rw [selectedRestrict_apply]
  rw [evaluation0_apply, evaluation0_apply, supportPushforward0_apply]
  have hc : supportCellInclude Nc.chartSupport hab (Carrier.chart M A _ (fun _ ht => ht) c) =
      Carrier.chart M B _ (fun _ ht => ht) (supportCellInclude Nf.chartSupport (fun _ ht => hab ht) c) := by
    apply Subtype.ext
    rfl
  have hjB : (Carrier.preimageFunctor M B).obj
      ((supportIncFunctor Nf (supportPreimageInclude (h := h) hab)).obj (.chart c)) =
        (supportIncFunctor Nc hab).obj (.chart (Carrier.chart M A _ (fun _ ht => ht) c)) :=
    (Carrier.preimageFunctor_obj_chart M B _).trans (congrArg Inc.chart hc.symm)
  have hh := supportCoefficientEvaluationAt M hab (.chart c)
    (Carrier.preimageFunctor_obj_chart M A c) hjB (z (supportCellInclude Nc.chartSupport hab (Carrier.chart M A _ (fun _ ht => ht) c)))
  simpa only [supportIncFunctor_obj_chart, hc] using hh

/-- 原εの次数1評価と元細セルの台制限は全値で可換。 -/
theorem supportEvaluation1 (z : (pushforwardComplex M B).C1) :
    evaluation1 M A (supportPushforward1 M hab z) =
      selectedRestrict Nf.edgeSupport (fun _ ht => hab ht) (evaluation1 M B z) := by
  funext e
  rw [supportSelectedRestrict_apply]
  cases he : M.edgeMap e.1 with
  | none =>
      rw [evaluation1_of_none M A _ e he, evaluation1_of_none M B _ _ he]
  | some a =>
      rw [evaluation1_of_some M A _ e a he,
        evaluation1_of_some M B z (supportCellInclude Nf.edgeSupport (fun _ ht => hab ht) e) a he,
        supportPushforward1_apply]
      have hc : supportCellInclude Nc.edgeSupport hab (M.targetSubsetEdgeMap A _ (fun _ ht => ht) e a he) =
          M.targetSubsetEdgeMap B _ (fun _ ht => ht) (supportCellInclude Nf.edgeSupport (fun _ ht => hab ht) e) a he := by
        apply Subtype.ext
        rfl
      have hjB : (Carrier.preimageFunctor M B).obj
          ((supportIncFunctor Nf (supportPreimageInclude (h := h) hab)).obj (.edge e)) =
            (supportIncFunctor Nc hab).obj (.edge (M.targetSubsetEdgeMap A _ (fun _ ht => ht) e a he)) :=
        (Carrier.preimageFunctor_obj_edge_of_some M B _ a he).trans (congrArg Inc.edge hc.symm)
      have hh := supportCoefficientEvaluationAt M hab (.edge e)
        (Carrier.preimageFunctor_obj_edge_of_some M A e a he) hjB (z (supportCellInclude Nc.edgeSupport hab (M.targetSubsetEdgeMap A _ (fun _ ht => ht) e a he)))
      simpa only [supportIncFunctor_obj_edge, hc] using hh

/-- 原εの次数2評価と元細セルの台制限は全値で可換。 -/
theorem supportEvaluation2 (z : (pushforwardComplex M B).C2) :
    evaluation2 M A (supportPushforward2 M hab z) =
      selectedRestrict Nf.faceSupport (fun _ ht => hab ht) (evaluation2 M B z) := by
  funext f
  rw [supportSelectedRestrict_apply]
  cases he : M.faceMap f.1 with
  | none =>
      rw [evaluation2_of_none M A _ f he, evaluation2_of_none M B _ _ he]
  | some a =>
      rw [evaluation2_of_some M A _ f a he,
        evaluation2_of_some M B z (supportCellInclude Nf.faceSupport (fun _ ht => hab ht) f) a he,
        supportPushforward2_apply]
      have hc : supportCellInclude Nc.faceSupport hab (M.targetSubsetFaceMap A _ (fun _ ht => ht) f a he) =
          M.targetSubsetFaceMap B _ (fun _ ht => ht) (supportCellInclude Nf.faceSupport (fun _ ht => hab ht) f) a he := by
        apply Subtype.ext
        rfl
      have hjB : (Carrier.preimageFunctor M B).obj
          ((supportIncFunctor Nf (supportPreimageInclude (h := h) hab)).obj (.face f)) =
            (supportIncFunctor Nc hab).obj (.face (M.targetSubsetFaceMap A _ (fun _ ht => ht) f a he)) :=
        (Carrier.preimageFunctor_obj_face_of_some M B _ a he).trans (congrArg Inc.face hc.symm)
      have hh := supportCoefficientEvaluationAt M hab (.face f)
        (Carrier.preimageFunctor_obj_face_of_some M A f a he) hjB (z (supportCellInclude Nc.faceSupport hab (M.targetSubsetFaceMap A _ (fun _ ht => ht) f a he)))
      simpa only [supportIncFunctor_obj_face, hc] using hh

/-- 原評価εの全三次数Homは同じ細cochain制限と可換。 -/
theorem supportEvaluationHom :
    AtlasDefectComposition.cochainComp (supportPushforwardHom M hab) (evaluationHom M A) =
      AtlasDefectComposition.cochainComp (evaluationHom M B)
        (subsetRestrictHom Nf (fun _ ht => hab ht)) := by
  apply AtlasDefectComposition.cochain_ext
  · ext z
    simpa only [AtlasDefectComposition.cochainComp_f0, evaluationHom_f0, supportPushforwardHom_f0,
      subsetRestrictHom_f0, LinearMap.comp_apply] using supportEvaluation0 M hab z
  · ext z
    simpa only [AtlasDefectComposition.cochainComp_f1, evaluationHom_f1, supportPushforwardHom_f1,
      subsetRestrictHom_f1, LinearMap.comp_apply] using supportEvaluation1 M hab z
  · ext z
    simpa only [AtlasDefectComposition.cochainComp_f2, evaluationHom_f2, supportPushforwardHom_f2,
      subsetRestrictHom_f2, LinearMap.comp_apply] using supportEvaluation2 M hab z

/-- 元P次数0制限の恒等則は実評価の単射性で同じ細制限の恒等へ戻る。 -/
theorem supportPushforward0_refl (A : Set qc.Target) :
    supportPushforward0 M (Set.Subset.refl A) = LinearMap.id := by
  apply LinearMap.ext
  intro z
  apply evaluation0_injective M A
  rw [supportEvaluation0, selectedRestrict_refl]
  rfl

/-- 元P次数0制限の合成則は実評価の単射性で同じ細制限の合成へ戻る。 -/
theorem supportPushforward0_comp {C : Set qc.Target} (hbc : B ⊆ C) :
    (supportPushforward0 M hab).comp (supportPushforward0 M hbc) =
      supportPushforward0 M (hab.trans hbc) := by
  apply LinearMap.ext
  intro z
  apply evaluation0_injective M A
  change evaluation0 M A (supportPushforward0 M hab (supportPushforward0 M hbc z)) = _
  rw [supportEvaluation0, supportEvaluation0, supportEvaluation0]
  exact (LinearMap.congr_fun (selectedRestrict_comp Nf.chartSupport
    (fun _ ht => hab ht) (fun _ ht => hbc ht)) (evaluation0 M C z)).symm

/-- 元P次数1制限の恒等則は実評価の単射性で同じ細制限の恒等へ戻る。 -/
theorem supportPushforward1_refl (A : Set qc.Target) :
    supportPushforward1 M (Set.Subset.refl A) = LinearMap.id := by
  apply LinearMap.ext
  intro z
  apply evaluation1_injective M A
  rw [supportEvaluation1, selectedRestrict_refl]
  rfl

/-- 元P次数1制限の合成則は実評価の単射性で同じ細制限の合成へ戻る。 -/
theorem supportPushforward1_comp {C : Set qc.Target} (hbc : B ⊆ C) :
    (supportPushforward1 M hab).comp (supportPushforward1 M hbc) =
      supportPushforward1 M (hab.trans hbc) := by
  apply LinearMap.ext
  intro z
  apply evaluation1_injective M A
  change evaluation1 M A (supportPushforward1 M hab (supportPushforward1 M hbc z)) = _
  rw [supportEvaluation1, supportEvaluation1, supportEvaluation1]
  exact (LinearMap.congr_fun (selectedRestrict_comp Nf.edgeSupport
    (fun _ ht => hab ht) (fun _ ht => hbc ht)) (evaluation1 M C z)).symm

/-- 元P次数2制限の恒等則は実評価の単射性で同じ細制限の恒等へ戻る。 -/
theorem supportPushforward2_refl (A : Set qc.Target) :
    supportPushforward2 M (Set.Subset.refl A) = LinearMap.id := by
  apply LinearMap.ext
  intro z
  apply evaluation2_injective M A
  rw [supportEvaluation2, selectedRestrict_refl]
  rfl

/-- 元P次数2制限の合成則は実評価の単射性で同じ細制限の合成へ戻る。 -/
theorem supportPushforward2_comp {C : Set qc.Target} (hbc : B ⊆ C) :
    (supportPushforward2 M hab).comp (supportPushforward2 M hbc) =
      supportPushforward2 M (hab.trans hbc) := by
  apply LinearMap.ext
  intro z
  apply evaluation2_injective M A
  change evaluation2 M A (supportPushforward2 M hab (supportPushforward2 M hbc z)) = _
  rw [supportEvaluation2, supportEvaluation2, supportEvaluation2]
  exact (LinearMap.congr_fun (selectedRestrict_comp Nf.faceSupport
    (fun _ ht => hab ht) (fun _ ht => hbc ht)) (evaluation2 M C z)).symm

/-- 元Pの全cochain Hom制限の恒等則。 -/
theorem supportPushforwardHom_refl (A : Set qc.Target) :
    supportPushforwardHom M (Set.Subset.refl A) = AtlasDefectComposition.cochainId (pushforwardComplex M A) := by
  apply AtlasDefectComposition.cochain_ext
  · apply LinearMap.ext
    intro z
    rw [supportPushforwardHom_f0, AtlasDefectComposition.cochainId_f0]
    exact LinearMap.congr_fun (supportPushforward0_refl M A) z
  · apply LinearMap.ext
    intro z
    rw [supportPushforwardHom_f1, AtlasDefectComposition.cochainId_f1]
    exact LinearMap.congr_fun (supportPushforward1_refl M A) z
  · apply LinearMap.ext
    intro z
    rw [supportPushforwardHom_f2, AtlasDefectComposition.cochainId_f2]
    exact LinearMap.congr_fun (supportPushforward2_refl M A) z

/-- 元Pの全cochain Hom制限の合成則。 -/
theorem supportPushforwardHom_comp {C : Set qc.Target} (hbc : B ⊆ C) :
    AtlasDefectComposition.cochainComp (supportPushforwardHom M hbc) (supportPushforwardHom M hab) =
      supportPushforwardHom M (hab.trans hbc) := by
  apply AtlasDefectComposition.cochain_ext
  · apply LinearMap.ext
    intro z
    rw [AtlasDefectComposition.cochainComp_f0, supportPushforwardHom_f0, supportPushforwardHom_f0,
      supportPushforwardHom_f0]
    exact LinearMap.congr_fun (supportPushforward0_comp M hab hbc) z
  · apply LinearMap.ext
    intro z
    rw [AtlasDefectComposition.cochainComp_f1, supportPushforwardHom_f1, supportPushforwardHom_f1,
      supportPushforwardHom_f1]
    exact LinearMap.congr_fun (supportPushforward1_comp M hab hbc) z
  · apply LinearMap.ext
    intro z
    rw [AtlasDefectComposition.cochainComp_f2, supportPushforwardHom_f2, supportPushforwardHom_f2,
      supportPushforwardHom_f2]
    exact LinearMap.congr_fun (supportPushforward2_comp M hab hbc) z

/-- 独立原始比較uの全台自然性はG-134の同じ生成比較正方形へ戻る。 -/
theorem supportDirectHom :
    AtlasDefectComposition.cochainComp (M.aSubnerveComparisonHom B)
      (subsetRestrictHom Nf (fun _ ht => hab ht)) =
    AtlasDefectComposition.cochainComp (subsetRestrictHom Nc hab) (M.aSubnerveComparisonHom A) :=
  M.subset_restrict_square A B (comparisonFactor qc qf h ⁻¹' A)
    (comparisonFactor qc qf h ⁻¹' B) hab (fun _ ht => hab ht)
    (fun _ ht => ht) (fun _ ht => ht)

end AAT.AG.AtlasCoefficientFiber
#print axioms AAT.AG.AtlasCoefficientFiber.supportPushforward0
#print axioms AAT.AG.AtlasCoefficientFiber.supportPushforward1
#print axioms AAT.AG.AtlasCoefficientFiber.supportPushforward2
#print axioms AAT.AG.AtlasCoefficientFiber.supportPushforward0_apply
#print axioms AAT.AG.AtlasCoefficientFiber.supportPushforward1_apply
#print axioms AAT.AG.AtlasCoefficientFiber.supportPushforward2_apply
#print axioms AAT.AG.AtlasCoefficientFiber.supportCoefficientRestrict_endpoint
#print axioms AAT.AG.AtlasCoefficientFiber.supportCoefficientRestrict_faceEdge
#print axioms AAT.AG.AtlasCoefficientFiber.supportPushforward_comm0
#print axioms AAT.AG.AtlasCoefficientFiber.supportPushforward_comm1
#print axioms AAT.AG.AtlasCoefficientFiber.supportPushforwardHom
#print axioms AAT.AG.AtlasCoefficientFiber.supportPushforwardHom_f0
#print axioms AAT.AG.AtlasCoefficientFiber.supportPushforwardHom_f1
#print axioms AAT.AG.AtlasCoefficientFiber.supportPushforwardHom_f2
#print axioms AAT.AG.AtlasCoefficientFiber.supportCoefficientRestrict_constant
#print axioms AAT.AG.AtlasCoefficientFiber.supportUnit0
#print axioms AAT.AG.AtlasCoefficientFiber.supportUnit1
#print axioms AAT.AG.AtlasCoefficientFiber.supportUnit2
#print axioms AAT.AG.AtlasCoefficientFiber.supportUnitHom
#print axioms AAT.AG.AtlasCoefficientFiber.supportCommaFunctor_transport
#print axioms AAT.AG.AtlasCoefficientFiber.supportCoefficientEvaluationAt
#print axioms AAT.AG.AtlasCoefficientFiber.supportEvaluation0
#print axioms AAT.AG.AtlasCoefficientFiber.supportEvaluation1
#print axioms AAT.AG.AtlasCoefficientFiber.supportEvaluation2
#print axioms AAT.AG.AtlasCoefficientFiber.supportEvaluationHom
#print axioms AAT.AG.AtlasCoefficientFiber.supportPushforward0_refl
#print axioms AAT.AG.AtlasCoefficientFiber.supportPushforward0_comp
#print axioms AAT.AG.AtlasCoefficientFiber.supportPushforward1_refl
#print axioms AAT.AG.AtlasCoefficientFiber.supportPushforward1_comp
#print axioms AAT.AG.AtlasCoefficientFiber.supportPushforward2_refl
#print axioms AAT.AG.AtlasCoefficientFiber.supportPushforward2_comp
#print axioms AAT.AG.AtlasCoefficientFiber.supportPushforwardHom_refl
#print axioms AAT.AG.AtlasCoefficientFiber.supportPushforwardHom_comp
#print axioms AAT.AG.AtlasCoefficientFiber.supportDirectHom
#print axioms AAT.AG.AtlasCoefficientFiber.supportPushforward2.congr_simp
#print axioms AAT.AG.AtlasCoefficientFiber.supportIncFunctor.congr_simp
#print axioms AAT.AG.AtlasCoefficientFiber.supportPushforward1.congr_simp
#print axioms AAT.AG.AtlasCoefficientFiber.supportCellInclude.congr_simp
#print axioms AAT.AG.AtlasCoefficientFiber.supportPushforward0.congr_simp
#print axioms AAT.AG.AtlasCoefficientFiber.supportPushforwardHom.congr_simp
#assert_standard_axioms_only AAT.AG.AtlasCoefficientFiber
