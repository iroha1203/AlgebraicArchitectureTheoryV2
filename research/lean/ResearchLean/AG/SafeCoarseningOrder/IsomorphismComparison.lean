import ResearchLean.AG.SafeCoarseningOrder.CoarseningTransport

/-!
# 同型輸送と元比較の実cochain図式

元原始入力と商原始入力の同型から、同じ実比較の全三次数可換図式を生成する。
canonical逆像の等号は全Homの型輸送として保持する。

## Implementation notes

商原始入力のFintypeは元のquotientSupportedのinstanceを使い、全recordの同定を保持する。
細側のsubsetを同型の逆像で再表示し、同じ生成Homの等号transportでcanonical比較へ戻す。
任意の同次元H¹同型を選ぶ方法は元比較を同定しないため用いない。
-/
noncomputable section
namespace AAT.AG.SafeCoarseningOrder
open CanonicalResolution ResolutionInvariance TwoPhase AtlasDefectComposition
variable {S T V S' T' V' : Type} [Fintype V] [Fintype V']
variable {M : PrimitiveInput S T V} {N : PrimitiveInput S' T' V'}
namespace PrimitiveIso
/-- 商原始同型から生成した選択chart全単射を独立商supportedへ接続。 -/
def quotientSubsetChartEquiv (a : PrimitiveIso M N) (R : Coarsening T V)
    (A : Set (Quotient (a.coarseningOrderIso R).1)) :
    (M.quotientSupported R).ChartInTargetSubset (a.quotientTarget R ⁻¹' A) ≃
      (N.quotientSupported (a.coarseningOrderIso R)).ChartInTargetSubset A := by
  letI : Fintype (Quotient R.2) := (M.quotientSupported R).chartFintype
  letI : Fintype (Quotient (a.coarseningOrderIso R).2) :=
    (N.quotientSupported (a.coarseningOrderIso R)).chartFintype
  exact (a.quotientIso R).subsetChartEquiv A
/-- 選択chart輸送は同じ元商chart全単射で評価する。 -/
@[simp] theorem quotientSubsetChartEquiv_val (a : PrimitiveIso M N) (R : Coarsening T V)
    (A : Set (Quotient (a.coarseningOrderIso R).1))
    (v : (M.quotientSupported R).ChartInTargetSubset (a.quotientTarget R ⁻¹' A)) :
    (a.quotientSubsetChartEquiv R A v).1 = a.quotientChart R v.1 := rfl
/-- 商原始同型から生成した選択有向辺全単射。 -/
def quotientSubsetEdgeEquiv (a : PrimitiveIso M N) (R : Coarsening T V)
    (A : Set (Quotient (a.coarseningOrderIso R).1)) :
    (M.quotientSupported R).EdgeInTargetSubset (a.quotientTarget R ⁻¹' A) ≃
      (N.quotientSupported (a.coarseningOrderIso R)).EdgeInTargetSubset A := by
  letI : Fintype (Quotient R.2) := (M.quotientSupported R).chartFintype
  letI : Fintype (Quotient (a.coarseningOrderIso R).2) :=
    (N.quotientSupported (a.coarseningOrderIso R)).chartFintype
  exact (a.quotientIso R).subsetEdgeEquiv A
/-- 選択有向辺輸送は同じ商原始同型の元辺全単射で評価する。 -/
@[simp] theorem quotientSubsetEdgeEquiv_val (a : PrimitiveIso M N) (R : Coarsening T V)
    (A : Set (Quotient (a.coarseningOrderIso R).1))
    (e : (M.quotientSupported R).EdgeInTargetSubset (a.quotientTarget R ⁻¹' A)) :
    (a.quotientSubsetEdgeEquiv R A e).1 = (a.quotientIso R).edgeEquiv e.1 := rfl
/-- 商同型の全三次数cochain同型。期待H¹同型を入力せず原始同型から作る。 -/
def quotientSubsetEquiv (a : PrimitiveIso M N) (R : Coarsening T V)
    (A : Set (Quotient (a.coarseningOrderIso R).1)) :
    ThreeCochainComplex.CochainEquiv
      ((M.quotientSupported R).targetSubsetComplex (a.quotientTarget R ⁻¹' A))
      ((N.quotientSupported (a.coarseningOrderIso R)).targetSubsetComplex A) := by
  letI : Fintype (Quotient R.2) := (M.quotientSupported R).chartFintype
  letI : Fintype (Quotient (a.coarseningOrderIso R).2) :=
    (N.quotientSupported (a.coarseningOrderIso R)).chartFintype
  exact (a.quotientIso R).subsetCochainEquiv A
/-- 逆商cochain同型の次数0評価は同じ商chart全単射。 -/
theorem quotientSubsetEquiv_symm_f0_apply (a : PrimitiveIso M N) (R : Coarsening T V)
    (A : Set (Quotient (a.coarseningOrderIso R).1))
    (x : ((N.quotientSupported (a.coarseningOrderIso R)).targetSubsetComplex A).C0)
    (v : (M.quotientSupported R).ChartInTargetSubset (a.quotientTarget R ⁻¹' A)) :
    (a.quotientSubsetEquiv R A).symm.toHom.f0 x v = x (a.quotientSubsetChartEquiv R A v) := rfl
/-- 逆商cochain同型の次数1評価は同じ商有向辺全単射。 -/
theorem quotientSubsetEquiv_symm_f1_apply (a : PrimitiveIso M N) (R : Coarsening T V)
    (A : Set (Quotient (a.coarseningOrderIso R).1))
    (x : ((N.quotientSupported (a.coarseningOrderIso R)).targetSubsetComplex A).C1)
    (e : (M.quotientSupported R).EdgeInTargetSubset (a.quotientTarget R ⁻¹' A)) :
    (a.quotientSubsetEquiv R A).symm.toHom.f1 x e = x (a.quotientSubsetEdgeEquiv R A e) := rfl
omit [Fintype V] [Fintype V'] in
/-- 元商写像の可換性からcanonical逆像の全Set等号を生成。 -/
theorem canonical_preimage (a : PrimitiveIso M N) (R : Coarsening T V)
    (A : Set (Quotient (a.coarseningOrderIso R).1)) :
    comparisonFactor (M.quotientReading R) M.reading (M.quotient_coarser R) ⁻¹'
      (a.quotientTarget R ⁻¹' A) = a.target ⁻¹'
      (comparisonFactor (N.quotientReading (a.coarseningOrderIso R)) N.reading
        (N.quotient_coarser (a.coarseningOrderIso R)) ⁻¹' A) := by
  rw [M.quotient_factor,N.quotient_factor]
  ext t
  simp only [Set.mem_preimage,quotientTarget_mk]
omit [Fintype V] [Fintype V'] in
/-- 再表示した細subsetから元商subsetへの適合を元商写像だけから生成。 -/
theorem reindexedMapsTo (a : PrimitiveIso M N) (R : Coarsening T V)
    (A : Set (Quotient (a.coarseningOrderIso R).1)) :
    ∀ t, t ∈ a.target ⁻¹' (comparisonFactor (N.quotientReading (a.coarseningOrderIso R))
      N.reading (N.quotient_coarser (a.coarseningOrderIso R)) ⁻¹' A) →
      comparisonFactor (M.quotientReading R) M.reading (M.quotient_coarser R) t ∈
        a.quotientTarget R ⁻¹' A := by
  intro t ht
  change t ∈ comparisonFactor (M.quotientReading R) M.reading (M.quotient_coarser R) ⁻¹'
    (a.quotientTarget R ⁻¹' A)
  rw [a.canonical_preimage R A]
  exact ht
/-- 同じ商比較をcanonical細subsetの原始同型逆像で再表示したHom。 -/
def reindexedComparisonHom (a : PrimitiveIso M N) (R : Coarsening T V)
    (A : Set (Quotient (a.coarseningOrderIso R).1)) :=
    (M.quotientMorphism R).targetSubsetComparisonHom (a.quotientTarget R ⁻¹' A)
      (a.target ⁻¹' (comparisonFactor (N.quotientReading (a.coarseningOrderIso R)) N.reading
        (N.quotient_coarser (a.coarseningOrderIso R)) ⁻¹' A)) (a.reindexedMapsTo R A)
omit [Fintype V'] in
/-- 再表示した同じHomの次数0を元公開subset pullbackへ評価する。 -/
theorem reindexedComparisonHom_f0_apply (a : PrimitiveIso M N) (R : Coarsening T V)
    (A : Set (Quotient (a.coarseningOrderIso R).1))
    (x : ((M.quotientSupported R).targetSubsetComplex (a.quotientTarget R ⁻¹' A)).C0) :
    (a.reindexedComparisonHom R A).f0 x =
      (M.quotientMorphism R).targetSubsetPullback0 (a.quotientTarget R ⁻¹' A)
        (a.target ⁻¹' (comparisonFactor (N.quotientReading (a.coarseningOrderIso R)) N.reading
          (N.quotient_coarser (a.coarseningOrderIso R)) ⁻¹' A)) (a.reindexedMapsTo R A) x := rfl
omit [Fintype V'] in
/-- 再表示した同じHomの次数1を元有向部分像の公開pullbackへ評価する。 -/
theorem reindexedComparisonHom_f1_apply (a : PrimitiveIso M N) (R : Coarsening T V)
    (A : Set (Quotient (a.coarseningOrderIso R).1))
    (x : ((M.quotientSupported R).targetSubsetComplex (a.quotientTarget R ⁻¹' A)).C1) :
    (a.reindexedComparisonHom R A).f1 x =
      (M.quotientMorphism R).targetSubsetPullback1 (a.quotientTarget R ⁻¹' A)
        (a.target ⁻¹' (comparisonFactor (N.quotientReading (a.coarseningOrderIso R)) N.reading
          (N.quotient_coarser (a.coarseningOrderIso R)) ⁻¹' A)) (a.reindexedMapsTo R A) x := rfl
omit [Fintype V'] in
/-- 再表示したHomは元canonical比較の全Hom等号transportである。 -/
theorem reindexedComparisonHom_eq_transport (a : PrimitiveIso M N) (R : Coarsening T V)
    (A : Set (Quotient (a.coarseningOrderIso R).1)) :
    a.reindexedComparisonHom R A = transportHom
      (congrArg M.supported.targetSubsetComplex (a.canonical_preimage R A))
      ((M.quotientMorphism R).aSubnerveComparisonHom (a.quotientTarget R ⁻¹' A)) := by
  symm
  exact targetSubsetComparisonHom_transport _ _ _ _ (a.canonical_preimage R A) _ _
/-- 元比較の全三次数可換図式。逆生成cochain同型を用い同じ有向部分像を保つ。 -/
theorem comparison_cochain_square (a : PrimitiveIso M N) (R : Coarsening T V)
    (A : Set (Quotient (a.coarseningOrderIso R).1)) :
    cochainComp ((N.quotientMorphism (a.coarseningOrderIso R)).aSubnerveComparisonHom A)
      (a.subsetCochainEquiv (comparisonFactor
        (N.quotientReading (a.coarseningOrderIso R)) N.reading
        (N.quotient_coarser (a.coarseningOrderIso R)) ⁻¹' A)).symm.toHom =
    cochainComp (a.quotientSubsetEquiv R A).symm.toHom (a.reindexedComparisonHom R A) := by
  let B := comparisonFactor (N.quotientReading (a.coarseningOrderIso R)) N.reading
    (N.quotient_coarser (a.coarseningOrderIso R)) ⁻¹' A
  apply cochain_ext
  · apply LinearMap.ext; intro x; funext v
    rw [cochainComp_f0,cochainComp_f0,subsetCochainEquiv_symm_f0_apply,
      reindexedComparisonHom_f0_apply]
    change (N.quotientMorphism (a.coarseningOrderIso R)).targetSubsetPullback0 A B _ x
      (a.subsetChartEquiv B v) = _
    rw [TargetSupportedNerveMorphism.targetSubsetPullback0_apply,
      TargetSupportedNerveMorphism.targetSubsetPullback0_apply,quotientSubsetEquiv_symm_f0_apply]
    congr 1
  · apply LinearMap.ext; intro x; funext e
    rw [cochainComp_f1,cochainComp_f1,subsetCochainEquiv_symm_f1_apply,
      reindexedComparisonHom_f1_apply]
    change (N.quotientMorphism (a.coarseningOrderIso R)).targetSubsetPullback1 A B _ x
      (a.subsetEdgeEquiv B e) = _
    rw [TargetSupportedNerveMorphism.targetSubsetPullback1_apply,
      TargetSupportedNerveMorphism.targetSubsetPullback1_apply]
    cases hm : M.quotientEdgeMap R e.1 with
    | none =>
      have hn : (N.quotientMorphism (a.coarseningOrderIso R)).edgeMap
          (a.subsetEdgeEquiv B e).1 = none := by
        have hh := (a.quotientEdgeMap_naturality R e.1).symm
        rw [hm,Option.map_none] at hh
        exact hh
      rw [TargetSupportedNerveMorphism.targetSubsetEdgeMapOption_eq_none _ _ _ _ _ hn,
        TargetSupportedNerveMorphism.targetSubsetEdgeMapOption_eq_none _ _ _ _ _ hm]
      rfl
    | some f =>
      have hn : (N.quotientMorphism (a.coarseningOrderIso R)).edgeMap
          (a.subsetEdgeEquiv B e).1 = some ((a.quotientIso R).edgeEquiv f) := by
        have hh := (a.quotientEdgeMap_naturality R e.1).symm
        rw [hm,Option.map_some] at hh
        exact hh
      rw [TargetSupportedNerveMorphism.targetSubsetEdgeMapOption_eq_some _ _ _ _ _ _ hn,
        TargetSupportedNerveMorphism.targetSubsetEdgeMapOption_eq_some _ _ _ _ _ _ hm,
        Option.elim_some,Option.elim_some,quotientSubsetEquiv_symm_f1_apply]
      congr 1
  · apply LinearMap.ext; intro x; funext f; exact f.1.elim
/-- 全cochain図式を同じ実H¹商へ降ろした比較の共役等号。 -/
theorem comparison_h1_square (a : PrimitiveIso M N) (R : Coarsening T V)
    (A : Set (Quotient (a.coarseningOrderIso R).1)) :
    (a.subsetCochainEquiv (comparisonFactor
      (N.quotientReading (a.coarseningOrderIso R)) N.reading
      (N.quotient_coarser (a.coarseningOrderIso R)) ⁻¹' A)).symm.toHom.h1Map.comp
        ((N.quotientMorphism (a.coarseningOrderIso R)).aSubnerveComparisonHom A).h1Map =
    (a.reindexedComparisonHom R A).h1Map.comp (a.quotientSubsetEquiv R A).symm.toHom.h1Map := by
  have hh := congrArg ThreeCochainComplex.Hom.h1Map (a.comparison_cochain_square R A)
  simpa only [cochainComp_h1Map] using hh
end PrimitiveIso
end AAT.AG.SafeCoarseningOrder
#assert_standard_axioms_only AAT.AG.SafeCoarseningOrder
