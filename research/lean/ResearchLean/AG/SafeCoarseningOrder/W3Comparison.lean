import ResearchLean.AG.SafeCoarseningOrder.W3Input
import ResearchLean.AG.SafeCoarseningOrder.IsomorphismCochains
import ResearchLean.AG.AtlasGluingWidth.WidthObservation
import ResearchLean.AG.AtlasDefectComposition.LinearConjugation

/-! # W3 の元セル同型と実比較の可換同定

新しく生成する商比較を旧Width比較へ全三次数と同じ実H¹写像で接続する。

## Implementation notes

元選択セルの全単射から関数再添字線形同型を生成する。両実比較をcanonical逆像の等号で同じ領域へ移し全三次数図式を示す。同次元H¹同型を任意に選ぶ代替は実比較を失うため採らない。具体商の型照合のheartbeat上限を拡げる。
-/
set_option maxHeartbeats 1200000
noncomputable section
namespace AAT.AG.SafeCoarseningOrder.W3
open CanonicalResolution ResolutionInvariance TwoPhase AtlasGluingWidth AtlasDefectComposition

/-- 旧fineと新T0の選択chart対応。元台と領域を保持する。 -/
def fineChartEquiv (cut : Bool) (B : Set Point) :
    (Width.fine 2 cut).ChartInTargetSubset B ≃ (input cut).supported.ChartInTargetSubset B :=
  Equiv.refl _
/-- 旧fineと新T0の選択辺対応。K1交差を元端点で照合する。 -/
def fineEdgeEquiv (cut : Bool) (B : Set Point) :
    (Width.fine 2 cut).EdgeInTargetSubset B ≃ (input cut).supported.EdgeInTargetSubset B :=
  Equiv.subtypeEquiv (edgeEquiv cut) (fun e => by
    change (∃ t, t ∈ Width.support 2 (Width.left 2 e.1) ∩
      Width.support 2 (Width.right 2 e.1) ∧ t ∈ B) ↔
      (∃ t, t ∈ Width.support 2 e.1 ∩ Width.support 2 (Width.right 2 e.1) ∧ t ∈ B)
    rw [old_left])
/-- 両側の空面型の選択セル対応。 -/
def fineFaceEquiv (cut : Bool) (B : Set Point) :
    (Width.fine 2 cut).FaceInTargetSubset B ≃ (input cut).supported.FaceInTargetSubset B where
  toFun f := f.1.elim
  invFun f := f.1.elim
  left_inv f := f.1.elim
  right_inv f := f.1.elim
/-- 旧fineから新fineへの三次数同型。元セル全単射から実d0/d1を保存する。 -/
def fineCochainEquiv (cut : Bool) (B : Set Point) : ThreeCochainComplex.CochainEquiv
    ((Width.fine 2 cut).targetSubsetComplex B) ((input cut).supported.targetSubsetComplex B) where
  e0 := LinearEquiv.funCongrLeft ℚ ℚ (fineChartEquiv cut B).symm
  e1 := LinearEquiv.funCongrLeft ℚ ℚ (fineEdgeEquiv cut B).symm
  e2 := LinearEquiv.funCongrLeft ℚ ℚ (fineFaceEquiv cut B).symm
  comm0 x := by
    funext e
    change ((Width.fine 2 cut).targetSubsetComplex B).d0 x
      ((fineEdgeEquiv cut B).symm e) =
      ((input cut).supported.targetSubsetComplex B).d0
      (LinearEquiv.funCongrLeft ℚ ℚ (fineChartEquiv cut B).symm x) e
    rw [TargetSupportedNerve.targetSubsetComplex_d0_apply,
      TargetSupportedNerve.targetSubsetComplex_d0_apply]
    change x ⟨Width.right 2 e.1.1.1,_⟩ - x ⟨Width.left 2 e.1.1.1,_⟩ =
      x ⟨e.1.1.2,_⟩ - x ⟨e.1.1.1,_⟩
    congr 1
    · apply congrArg x
      apply Subtype.ext
      exact e.1.2.2.symm
    · apply congrArg x
      apply Subtype.ext
      exact old_left _
  comm1 x := by funext f; exact f.1.elim
/-- 新商と旧coarseの選択chart対応。元商target領域を保持する。 -/
def coarseChartEquiv (cut : Bool) (X : Set (Width.Concept 2)) :
    ((input cut).quotientSupported coarsening).ChartInTargetSubset (region X) ≃
      (Width.coarse 2).ChartInTargetSubset X where
  toFun c := ⟨chartEquiv c.1, by
    obtain ⟨t,_,hx⟩ := c.2
    exact ⟨targetEquiv t, Set.mem_univ _,(mem_region X t).mp hx⟩⟩
  invFun c := ⟨chartEquiv.symm c.1,by
    obtain ⟨i,_,hx⟩ := c.2
    refine ⟨targetEquiv.symm i,quotient_support_all cut _ _,?_⟩
    simpa only [region,Set.mem_preimage,Equiv.apply_symm_apply] using hx⟩
  left_inv c := Subtype.ext (chartEquiv.symm_apply_apply c.1)
  right_inv c := Subtype.ext (chartEquiv.apply_symm_apply c.1)
/-- 新商と旧coarseの空辺対応。空性を元商辺式から導く。 -/
def coarseEdgeEquiv (cut : Bool) (X : Set (Width.Concept 2)) :
    ((input cut).quotientSupported coarsening).EdgeInTargetSubset (region X) ≃
      (Width.coarse 2).EdgeInTargetSubset X where
  toFun e := False.elim (quotient_no_edge cut _ _ e.1.2)
  invFun e := e.1.elim
  left_inv e := False.elim (quotient_no_edge cut _ _ e.1.2)
  right_inv e := e.1.elim
/-- 新商と旧coarseの空面対応。 -/
def coarseFaceEquiv (cut : Bool) (X : Set (Width.Concept 2)) :
    ((input cut).quotientSupported coarsening).FaceInTargetSubset (region X) ≃
      (Width.coarse 2).FaceInTargetSubset X where
  toFun f := f.1.elim
  invFun f := f.1.elim
  left_inv f := f.1.elim
  right_inv f := f.1.elim
/-- 新商から旧coarseへの三次数同型。元支持台から選択セルを生成する。 -/
def coarseCochainEquiv (cut : Bool) (X : Set (Width.Concept 2)) :
    ThreeCochainComplex.CochainEquiv
      (((input cut).quotientSupported coarsening).targetSubsetComplex (region X))
      ((Width.coarse 2).targetSubsetComplex X) where
  e0 := LinearEquiv.funCongrLeft ℚ ℚ (coarseChartEquiv cut X).symm
  e1 := LinearEquiv.funCongrLeft ℚ ℚ (coarseEdgeEquiv cut X).symm
  e2 := LinearEquiv.funCongrLeft ℚ ℚ (coarseFaceEquiv cut X).symm
  comm0 x := by funext e; exact e.1.elim
  comm1 x := by funext f; exact f.1.elim
open AtlasDefectComposition
/-- newHomの領域条件を元canonical因子から放電する。 -/
theorem newMapsTo (cut : Bool) (X : Set (Width.Concept 2)) :
    ∀ t, t ∈ Width.region 2 X → comparisonFactor
      ((input cut).quotientReading coarsening) (input cut).reading
      ((input cut).quotient_coarser coarsening) t ∈ region X := by
  intro t ht
  rw [PrimitiveInput.quotient_factor]
  exact ht
/-- oldHomの領域条件を旧fst因子の公開APIから放電する。 -/
theorem oldMapsTo (X : Set (Width.Concept 2)) :
    ∀ t, t ∈ Width.region 2 X → comparisonFactor
      (Width.coarseReading 2) (Width.fineReading 2) (Width.coarser 2) t ∈ X := by
  intro t ht
  rw [Width.factor]
  exact ht
/-- 同じ新生成比較を指定細領域へ再表示した実Hom。 -/
def newHom (cut : Bool) (X : Set (Width.Concept 2)) :=
    ((input cut).quotientMorphism coarsening).targetSubsetComparisonHom
      (region X) (Width.region 2 X) (newMapsTo cut X)
/-- 同じ旧Width比較を同じ指定細領域へ再表示した実Hom。 -/
def oldHom (cut : Bool) (X : Set (Width.Concept 2)) :=
    (Width.hereditary 2 cut).targetSubsetComparisonHom
      X (Width.region 2 X) (oldMapsTo X)
/-- newHomの次数0を同じ公開subset pullbackへ評価する基本API。 -/
theorem newHom_f0_apply (cut : Bool) (X : Set (Width.Concept 2))
    (x : (((input cut).quotientSupported coarsening).targetSubsetComplex (region X)).C0) :
    (newHom cut X).f0 x = ((input cut).quotientMorphism coarsening).targetSubsetPullback0
      (region X) (Width.region 2 X) (newMapsTo cut X) x := rfl
/-- newHomの次数1を元有向部分像の公開pullbackへ評価する基本API。 -/
theorem newHom_f1_apply (cut : Bool) (X : Set (Width.Concept 2))
    (x : (((input cut).quotientSupported coarsening).targetSubsetComplex (region X)).C1) :
    (newHom cut X).f1 x = ((input cut).quotientMorphism coarsening).targetSubsetPullback1
      (region X) (Width.region 2 X) (newMapsTo cut X) x := rfl
/-- oldHomの次数0を同じ旧比較の公開pullbackへ評価する基本API。 -/
theorem oldHom_f0_apply (cut : Bool) (X : Set (Width.Concept 2))
    (x : ((Width.coarse 2).targetSubsetComplex X).C0) :
    (oldHom cut X).f0 x = (Width.hereditary 2 cut).targetSubsetPullback0
      X (Width.region 2 X) (oldMapsTo X) x := rfl
/-- oldHomの次数1を同じ旧比較の公開pullbackへ評価する基本API。 -/
theorem oldHom_f1_apply (cut : Bool) (X : Set (Width.Concept 2))
    (x : ((Width.coarse 2).targetSubsetComplex X).C1) :
    (oldHom cut X).f1 x = (Width.hereditary 2 cut).targetSubsetPullback1
      X (Width.region 2 X) (oldMapsTo X) x := rfl
/-- fineCochainEquivの逆Homの次数0を元chart全単射で評価する。 -/
theorem fine_symm_f0_apply (cut : Bool) (B : Set Point)
    (x : ((input cut).supported.targetSubsetComplex B).C0)
    (v : (Width.fine 2 cut).ChartInTargetSubset B) :
    (fineCochainEquiv cut B).symm.toHom.f0 x v = x (fineChartEquiv cut B v) := rfl
/-- fineCochainEquivの逆Homの次数1を元辺全単射で評価する。 -/
theorem fine_symm_f1_apply (cut : Bool) (B : Set Point)
    (x : ((input cut).supported.targetSubsetComplex B).C1)
    (e : (Width.fine 2 cut).EdgeInTargetSubset B) :
    (fineCochainEquiv cut B).symm.toHom.f1 x e = x (fineEdgeEquiv cut B e) := rfl
/-- coarseCochainEquivの次数0を元商chart対応で評価する。 -/
theorem coarse_f0_apply (cut : Bool) (X : Set (Width.Concept 2))
    (x : (((input cut).quotientSupported coarsening).targetSubsetComplex (region X)).C0)
    (v : (Width.coarse 2).ChartInTargetSubset X) :
    (coarseCochainEquiv cut X).toHom.f0 x v = x ((coarseChartEquiv cut X).symm v) := rfl
/-- newHomは新canonical比較の全Hom等号transportである。 -/
theorem newHom_eq_transport (cut : Bool) (X : Set (Width.Concept 2)) :
    newHom cut X = transportHom
      (congrArg (input cut).supported.targetSubsetComplex (factor_region cut X))
      (((input cut).quotientMorphism coarsening).aSubnerveComparisonHom (region X)) := by
  symm
  exact targetSubsetComparisonHom_transport _ _ _ _ (factor_region cut X) _ _
/-- oldHomは旧canonical比較の全Hom等号transportである。 -/
theorem oldHom_eq_transport (cut : Bool) (X : Set (Width.Concept 2)) :
    oldHom cut X = transportHom
      (congrArg (Width.fine 2 cut).targetSubsetComplex (Width.factor_region 2 X))
      ((Width.hereditary 2 cut).aSubnerveComparisonHom X) := by
  symm
  exact targetSubsetComparisonHom_transport _ _ _ _ (Width.factor_region 2 X) _ _
/-- 指定Rで全原始辺の部分像はnone。旧比較の縮約と同じ。 -/
theorem quotient_edge_none (cut : Bool) (e : (input cut).Edge) :
    (input cut).quotientEdgeMap coarsening e = none :=
  (PrimitiveInput.quotientEdgeMap_eq_none _ _ _).mpr (coarsening_chart_rel _ _)
/-- 新商readingの元Source評価は商target同定後に旧fst readingと一致。 -/
theorem reading_comm (cut : Bool) (p : Point) :
    targetEquiv (((input cut).quotientReading coarsening).read p) =
      (Width.coarseReading 2).read p := rfl
/-- 新m_Rの元chart像は商chart同定後に同じ旧mのchart像と一致。 -/
theorem morphism_chart_comm (cut : Bool) (v : Chart) :
    chartEquiv (((input cut).quotientMorphism coarsening).chartMap v) =
      (Width.hereditary 2 cut).chartMap v := rfl
/-- 同じ旧辺と新辺の部分像は両方none。内部辺縮約の元セル同定。 -/
theorem morphism_edge_comm (cut : Bool) (e : Width.Edge 2 cut) :
    (input cut).quotientEdgeMap coarsening (edgeEquiv cut e) = none ∧
      (Width.hereditary 2 cut).edgeMap e = none :=
  ⟨quotient_edge_none cut _,rfl⟩
/-- 新商と旧Width比較の全三次数可換図式。元セルと実部分像を保持する。 -/
theorem cochain_square (cut : Bool) (X : Set (Width.Concept 2)) :
    cochainComp (newHom cut X) (fineCochainEquiv cut (Width.region 2 X)).symm.toHom =
      cochainComp (coarseCochainEquiv cut X).toHom (oldHom cut X) := by
  apply cochain_ext
  · apply LinearMap.ext; intro x; funext v
    rw [cochainComp_f0,cochainComp_f0,fine_symm_f0_apply,
      newHom_f0_apply,oldHom_f0_apply,
      TargetSupportedNerveMorphism.targetSubsetPullback0_apply,
      TargetSupportedNerveMorphism.targetSubsetPullback0_apply,coarse_f0_apply]
    congr 1
    apply Subtype.ext
    exact (chartEquiv.symm_apply_apply _).symm
  · apply LinearMap.ext; intro x; funext e
    rw [cochainComp_f1,cochainComp_f1,fine_symm_f1_apply,
      newHom_f1_apply,oldHom_f1_apply,
      TargetSupportedNerveMorphism.targetSubsetPullback1_apply,
      TargetSupportedNerveMorphism.targetSubsetPullback1_apply,
      TargetSupportedNerveMorphism.targetSubsetEdgeMapOption_eq_none _ _ _ _ _
        (quotient_edge_none cut _),
      TargetSupportedNerveMorphism.targetSubsetEdgeMapOption_eq_none _ _ _ _ _ rfl]
    rfl
  · apply LinearMap.ext; intro x; funext f; exact f.1.elim
/-- 全cochain図式を同じ実H¹商へ降ろした可換図式。 -/
theorem reindexed_h1_square (cut : Bool) (X : Set (Width.Concept 2))
    (x : (((input cut).quotientSupported coarsening).targetSubsetComplex (region X)).H1) :
    (fineCochainEquiv cut (Width.region 2 X)).symm.h1Equiv ((newHom cut X).h1Map x) =
      (oldHom cut X).h1Map ((coarseCochainEquiv cut X).h1Equiv x) := by
  apply ThreeCochainComplex.CochainEquiv.h1Equiv_naturality_apply
  intro z
  exact congrArg (fun h => h.f1 z) (cochain_square cut X)
/-- 同じH¹可換図式から生成する実核同型。 -/
def reindexedKernelEquiv (cut : Bool) (X : Set (Width.Concept 2)) :=
  LinearConjugation.kernelEquiv (newHom cut X).h1Map (oldHom cut X).h1Map
    (coarseCochainEquiv cut X).h1Equiv
    (fineCochainEquiv cut (Width.region 2 X)).symm.h1Equiv (reindexed_h1_square cut X)
/-- 同じH¹可換図式から生成するliteral余核同型。 -/
def reindexedCokernelEquiv (cut : Bool) (X : Set (Width.Concept 2)) :=
  LinearConjugation.cokernelEquiv (newHom cut X).h1Map (oldHom cut X).h1Map
    (coarseCochainEquiv cut X).h1Equiv
    (fineCochainEquiv cut (Width.region 2 X)).symm.h1Equiv (reindexed_h1_square cut X)
/-- 実核/余核同型から両J成分を保存する。 -/
theorem reindexed_defect (cut : Bool) (X : Set (Width.Concept 2)) :
    blockDefect (newHom cut X).h1Map = blockDefect (oldHom cut X).h1Map := by
  exact Prod.ext (reindexedKernelEquiv cut X).finrank_eq
    (reindexedCokernelEquiv cut X).finrank_eq
/-- 新canonical実比較のJを同じWidth.actualMapへ戻す。 -/
theorem actual_defect (cut : Bool) (X : Set (Width.Concept 2)) :
    blockDefect (((input cut).quotientComparison coarsening).aSubnerveComparisonHom
      (region X)).h1Map = blockDefect (Width.actualMap 2 cut X) := by
  rw [PrimitiveInput.quotient_actualHom_old]
  rw [← transportHom_defect (congrArg (input cut).supported.targetSubsetComplex
    (factor_region cut X)),← newHom_eq_transport,reindexed_defect,oldHom_eq_transport,
    transportHom_defect]
  exact congrArg blockDefect
    (FaceRelationSubdivision.ofHereditary_aSubnerveComparisonHom_h1Map
      (Width.hereditary 2 cut) X).symm
/-- 両canonical比較の逆像transportを明示した実H¹可換図式。 -/
theorem actual_h1_square (cut : Bool) (X : Set (Width.Concept 2))
    (x : (((input cut).quotientSupported coarsening).targetSubsetComplex (region X)).H1) :
    (fineCochainEquiv cut (Width.region 2 X)).symm.h1Equiv
      ((transportHom (congrArg (input cut).supported.targetSubsetComplex
        (factor_region cut X))
        (((input cut).quotientComparison coarsening).aSubnerveComparisonHom (region X))).h1Map x) =
      (transportHom (congrArg (Width.fine 2 cut).targetSubsetComplex
        (Width.factor_region 2 X))
        ((Width.comparison 2 cut).aSubnerveComparisonHom X)).h1Map
          ((coarseCochainEquiv cut X).h1Equiv x) := by
  have ho : (Width.comparison 2 cut).aSubnerveComparisonHom X =
      (Width.hereditary 2 cut).aSubnerveComparisonHom X :=
    FaceRelationSubdivision.ofHereditary_aSubnerveComparisonHom _ _
  rw [PrimitiveInput.quotient_actualHom_old,ho,
    ← newHom_eq_transport,← oldHom_eq_transport]
  exact reindexed_h1_square cut X x
/-- canonical逆像で選ぶ新fine/旧fineの元セル生成三次数同型。 -/
def actualFineCochainEquiv (cut : Bool) (X : Set (Width.Concept 2)) :
    ThreeCochainComplex.CochainEquiv
      ((input cut).supported.targetSubsetComplex
        (comparisonFactor ((input cut).quotientReading coarsening) (input cut).reading
          ((input cut).quotient_coarser coarsening) ⁻¹' region X))
      ((Width.fine 2 cut).targetSubsetComplex
        (comparisonFactor (Width.coarseReading 2) (Width.fineReading 2)
          (Width.coarser 2) ⁻¹' X)) := by
  rw [factor_region,Width.factor_region]
  exact (fineCochainEquiv cut (Width.region 2 X)).symm
/-- 同じcanonical実H¹射と元セル同型の可換性。旧coarse零商を公開APIから用いる。 -/
theorem actual_h1_square_direct (cut : Bool) (X : Set (Width.Concept 2))
    (x : (((input cut).quotientSupported coarsening).targetSubsetComplex (region X)).H1) :
    (actualFineCochainEquiv cut X).h1Equiv
      ((((input cut).quotientComparison coarsening).aSubnerveComparisonHom (region X)).h1Map x) =
      Width.actualMap 2 cut X ((coarseCochainEquiv cut X).h1Equiv x) := by
  letI := Width.coarse_H1_zero 2 X
  have hx : x = 0 := (coarseCochainEquiv cut X).h1Equiv.injective (Subsingleton.elim _ _)
  rw [hx,map_zero,map_zero,map_zero,map_zero]
/-- 新canonical比較のliteral余核を同じ旧actualMap余核へ同定する。 -/
def actualCokernelEquiv (cut : Bool) (X : Set (Width.Concept 2)) :=
  LinearConjugation.cokernelEquiv
    ((((input cut).quotientComparison coarsening).aSubnerveComparisonHom (region X)).h1Map)
    (Width.actualMap 2 cut X) (coarseCochainEquiv cut X).h1Equiv
    (actualFineCochainEquiv cut X).h1Equiv (actual_h1_square_direct cut X)

/-- actualCokernelEquivは元fine代表を同じセル生成H¹同型で写す。 -/
theorem actualCokernelEquiv_mk (cut : Bool) (X : Set (Width.Concept 2))
    (y : ((input cut).supported.targetSubsetComplex
      (comparisonFactor ((input cut).quotientReading coarsening) (input cut).reading
        ((input cut).quotient_coarser coarsening) ⁻¹' region X)).H1) :
    actualCokernelEquiv cut X
      ((LinearMap.range (((input cut).quotientComparison coarsening).aSubnerveComparisonHom
        (region X)).h1Map).mkQ y) =
      (LinearMap.range (Width.actualMap 2 cut X)).mkQ ((actualFineCochainEquiv cut X).h1Equiv y) := rfl

end AAT.AG.SafeCoarseningOrder.W3
#assert_standard_axioms_only AAT.AG.SafeCoarseningOrder
