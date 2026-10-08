import ResearchLean.AG.AtlasCoefficientFiber.SupportPhiCells
import ResearchLean.AG.AtlasCoefficientFiber.FiberCohomology

/-!
# G-135 D：同じ原Φ cochainとH¹の台制限

## Implementation notes

原Φセル包含による前合成で三つのcochain射を生成する。
両微分の可換性は原端点と三辺出現により放電し、元のH¹商へ降りる。
H¹間の射を期待するrankから定義する案は、代表元と原微分との接続を失うため採らない。
-/
noncomputable section
namespace AAT.AG.AtlasCoefficientFiber
open CategoryTheory CanonicalResolution ResolutionInvariance FaceRelationSubdivision TwoPhase AtlasDefectComposition
universe u
variable {Source : Type u} {qc qf : Reading Source} {h : qc.CoarserThan qf}
variable {Nc : TargetSupportedNerve.{u,u} qc} {Nf : TargetSupportedNerve.{u,u} qf}
variable (M : IncidenceSupportedComparison qc qf h Nc Nf) {A B : Set qc.Target} (hab : A ⊆ B)
variable (c : Nc.ChartInTargetSubset A)

/-- 原Φ次数0cochainを同じセル包含の前合成で制限する。 -/
def supportPhi0 : (phiComplex M B (supportCellInclude Nc.chartSupport hab c)).C0 →ₗ[ℚ]
    (phiComplex M A c).C0 :=
  LinearMap.pi fun x => LinearMap.proj (supportPhiChartInclude M hab c x)

/-- 原Φ次数0制限の全セル値。 -/
theorem supportPhi0_apply
    (z : (phiComplex M B (supportCellInclude Nc.chartSupport hab c)).C0) (x : PhiChart M A c) :
    supportPhi0 M hab c z x = z (supportPhiChartInclude M hab c x) := rfl

/-- 原Φ次数0cochain制限は同じ原chain包含の実双対である。 -/
theorem supportPhi0_dual
    (z : (phiComplex M B (supportCellInclude Nc.chartSupport hab c)).C0) (x : PhiChart M A c →₀ ℚ) :
    freeDualEquiv _ (supportPhi0 M hab c z) x = freeDualEquiv _ z (supportPhiChain0 M hab c x) := by
  have hh : freeDualEquiv _ (supportPhi0 M hab c z) =
      (freeDualEquiv _ z).comp (supportPhiChain0 M hab c) := by
    apply Finsupp.lhom_ext
    intro i r
    change freeDualEquiv _ (supportPhi0 M hab c z) (Finsupp.single i r) =
      freeDualEquiv _ z (supportPhiChain0 M hab c (Finsupp.single i r))
    rw [supportPhiChain0_single, freeDualEquiv_single, freeDualEquiv_single, supportPhi0_apply]
  exact LinearMap.congr_fun hh x

/-- 原Φ次数1cochainを同じセル包含の前合成で制限する。 -/
def supportPhi1 : (phiComplex M B (supportCellInclude Nc.chartSupport hab c)).C1 →ₗ[ℚ]
    (phiComplex M A c).C1 :=
  LinearMap.pi fun x => LinearMap.proj (supportPhiEdgeInclude M hab c x)

/-- 原Φ次数1制限の全セル値。 -/
theorem supportPhi1_apply
    (z : (phiComplex M B (supportCellInclude Nc.chartSupport hab c)).C1) (x : PhiEdge M A c) :
    supportPhi1 M hab c z x = z (supportPhiEdgeInclude M hab c x) := rfl

/-- 原Φ次数1cochain制限は同じ原chain包含の実双対である。 -/
theorem supportPhi1_dual
    (z : (phiComplex M B (supportCellInclude Nc.chartSupport hab c)).C1) (x : PhiEdge M A c →₀ ℚ) :
    freeDualEquiv _ (supportPhi1 M hab c z) x = freeDualEquiv _ z (supportPhiChain1 M hab c x) := by
  have hh : freeDualEquiv _ (supportPhi1 M hab c z) =
      (freeDualEquiv _ z).comp (supportPhiChain1 M hab c) := by
    apply Finsupp.lhom_ext
    intro i r
    change freeDualEquiv _ (supportPhi1 M hab c z) (Finsupp.single i r) =
      freeDualEquiv _ z (supportPhiChain1 M hab c (Finsupp.single i r))
    rw [supportPhiChain1_single, freeDualEquiv_single, freeDualEquiv_single, supportPhi1_apply]
  exact LinearMap.congr_fun hh x

/-- 原Φ次数2cochainを同じセル包含の前合成で制限する。 -/
def supportPhi2 : (phiComplex M B (supportCellInclude Nc.chartSupport hab c)).C2 →ₗ[ℚ]
    (phiComplex M A c).C2 :=
  LinearMap.pi fun x => LinearMap.proj (supportPhiFaceInclude M hab c x)

/-- 原Φ次数2制限の全セル値。 -/
theorem supportPhi2_apply
    (z : (phiComplex M B (supportCellInclude Nc.chartSupport hab c)).C2) (x : PhiFace M A c) :
    supportPhi2 M hab c z x = z (supportPhiFaceInclude M hab c x) := rfl

/-- 原Φ次数2cochain制限は同じ原chain包含の実双対である。 -/
theorem supportPhi2_dual
    (z : (phiComplex M B (supportCellInclude Nc.chartSupport hab c)).C2) (x : PhiFace M A c →₀ ℚ) :
    freeDualEquiv _ (supportPhi2 M hab c z) x = freeDualEquiv _ z (supportPhiChain2 M hab c x) := by
  have hh : freeDualEquiv _ (supportPhi2 M hab c z) =
      (freeDualEquiv _ z).comp (supportPhiChain2 M hab c) := by
    apply Finsupp.lhom_ext
    intro i r
    change freeDualEquiv _ (supportPhi2 M hab c z) (Finsupp.single i r) =
      freeDualEquiv _ z (supportPhiChain2 M hab c (Finsupp.single i r))
    rw [supportPhiChain2_single, freeDualEquiv_single, freeDualEquiv_single, supportPhi2_apply]
  exact LinearMap.congr_fun hh x

/-- 原Φ第一微分と台制限は同じ左右端点出現により可換。 -/
theorem supportPhi_comm0 (z : (phiComplex M B (supportCellInclude Nc.chartSupport hab c)).C0) :
    supportPhi1 M hab c ((phiComplex M B (supportCellInclude Nc.chartSupport hab c)).d0 z) =
      (phiComplex M A c).d0 (supportPhi0 M hab c z) := by
  funext e
  rw [supportPhi1_apply, phiComplex_d0, phiComplex_d0]
  exact (phiD0_apply M B (supportCellInclude Nc.chartSupport hab c) z
    (supportPhiEdgeInclude M hab c e)).trans
    ((congrArg₂ (fun a b : ℚ => a - b)
      (congrArg z (supportPhiChartInclude_endpoint M hab c e true).symm)
      (congrArg z (supportPhiChartInclude_endpoint M hab c e false).symm)).trans
      (phiD0_apply M A c (supportPhi0 M hab c z) e).symm)

/-- 原Φ第二微分と台制限は同じ三辺の符号と出現により可換。 -/
theorem supportPhi_comm1 (z : (phiComplex M B (supportCellInclude Nc.chartSupport hab c)).C1) :
    supportPhi2 M hab c ((phiComplex M B (supportCellInclude Nc.chartSupport hab c)).d1 z) =
      (phiComplex M A c).d1 (supportPhi1 M hab c z) := by
  funext f
  rw [supportPhi2_apply, phiComplex_d1, phiComplex_d1]
  exact (phiD1_apply M B (supportCellInclude Nc.chartSupport hab c) z
    (supportPhiFaceInclude M hab c f)).trans
    ((congrArg₂ (fun a b : ℚ => a + b)
      (congrArg₂ (fun a b : ℚ => a - b)
        (congrArg z (supportPhiEdgeInclude_faceEdge M hab c f 0).symm)
        (congrArg z (supportPhiEdgeInclude_faceEdge M hab c f 1).symm))
      (congrArg z (supportPhiEdgeInclude_faceEdge M hab c f 2).symm)).trans
      (phiD1_apply M A c (supportPhi1 M hab c z) f).symm)

/-- 原Φの全三次数台制限を元の実cochain Homにする。 -/
def supportPhiHom : ThreeCochainComplex.Hom
    (phiComplex M B (supportCellInclude Nc.chartSupport hab c)) (phiComplex M A c) where
  f0 := supportPhi0 M hab c
  f1 := supportPhi1 M hab c
  f2 := supportPhi2 M hab c
  comm0 := supportPhi_comm0 M hab c
  comm1 := supportPhi_comm1 M hab c

/-- 元Φ制限Homのchart成分。 -/
@[simp] theorem supportPhiHom_f0 : (supportPhiHom M hab c).f0 = supportPhi0 M hab c := rfl
/-- 元Φ制限Homの辺成分。 -/
@[simp] theorem supportPhiHom_f1 : (supportPhiHom M hab c).f1 = supportPhi1 M hab c := rfl
/-- 元Φ制限Homの面成分。 -/
@[simp] theorem supportPhiHom_f2 : (supportPhiHom M hab c).f2 = supportPhi2 M hab c := rfl

/-- 全原ΦのH¹制限は同じ粗chart包含と実H¹商写像から生成する。 -/
def supportAllPhiH1 :
    ((c : Nc.ChartInTargetSubset B) → (phiComplex M B c).H1) →ₗ[ℚ]
      ((c : Nc.ChartInTargetSubset A) → (phiComplex M A c).H1) :=
  LinearMap.pi fun c => (supportPhiHom M hab c).h1Map.comp
    (LinearMap.proj (supportCellInclude Nc.chartSupport hab c))

/-- 全原Φの制限は各原cochain Homの同じH¹商写像を読む。 -/
theorem supportAllPhiH1_apply
    (z : (c : Nc.ChartInTargetSubset B) → (phiComplex M B c).H1) (c : Nc.ChartInTargetSubset A) :
    supportAllPhiH1 M hab z c = (supportPhiHom M hab c).h1Map
      (z (supportCellInclude Nc.chartSupport hab c)) := rfl

/-- 同じ原Φ H¹制限の全閉路代表式。 -/
theorem supportPhiH1_mk
    (z : LinearMap.ker (phiComplex M B (supportCellInclude Nc.chartSupport hab c)).d1) :
    (supportPhiHom M hab c).h1Map (Submodule.Quotient.mk z) =
      Submodule.Quotient.mk ((supportPhiHom M hab c).cyclesMap z) :=
  (supportPhiHom M hab c).h1Map_mk z

/-- 原Φの全cochain台制限は恒等包含で恒等射となる。 -/
theorem supportPhiHom_refl (A : Set qc.Target) (c : Nc.ChartInTargetSubset A) :
    supportPhiHom M (Set.Subset.refl A) c = cochainId (phiComplex M A c) := by
  apply cochain_ext <;> apply LinearMap.ext <;> intro z <;> funext x <;> rfl

/-- 原Φの全cochain台制限は原支持包含の合成と一致する。 -/
theorem supportPhiHom_comp {C : Set qc.Target} (hbc : B ⊆ C) :
    cochainComp (supportPhiHom M hbc (supportCellInclude Nc.chartSupport hab c))
      (supportPhiHom M hab c) = supportPhiHom M (hab.trans hbc) c := by
  apply cochain_ext <;> apply LinearMap.ext <;> intro z <;> funext x <;> rfl

/-- 全原Φ H¹台制限の恒等則。 -/
theorem supportAllPhiH1_refl (A : Set qc.Target) :
    supportAllPhiH1 M (Set.Subset.refl A) = LinearMap.id := by
  apply LinearMap.ext
  intro z
  funext c
  rw [supportAllPhiH1_apply, supportPhiHom_refl]
  exact LinearMap.congr_fun (cochainId_h1Map (phiComplex M A c)) (z c)

/-- 全原Φ H¹台制限の合成則。 -/
theorem supportAllPhiH1_comp {C : Set qc.Target} (hbc : B ⊆ C) :
    (supportAllPhiH1 M hab).comp (supportAllPhiH1 M hbc) = supportAllPhiH1 M (hab.trans hbc) := by
  apply LinearMap.ext
  intro z
  funext c
  change supportAllPhiH1 M hab (supportAllPhiH1 M hbc z) c = _
  rw [supportAllPhiH1_apply, supportAllPhiH1_apply, supportAllPhiH1_apply]
  have hh := congrArg (fun f => f.h1Map
    (z (supportCellInclude Nc.chartSupport (hab.trans hbc) c))) (supportPhiHom_comp M hab c hbc)
  dsimp only at hh
  exact (LinearMap.congr_fun (cochainComp_h1Map
    (supportPhiHom M hbc (supportCellInclude Nc.chartSupport hab c))
    (supportPhiHom M hab c)) _).symm.trans hh

end AAT.AG.AtlasCoefficientFiber
#print axioms AAT.AG.AtlasCoefficientFiber.supportPhi0
#print axioms AAT.AG.AtlasCoefficientFiber.supportPhi0_apply
#print axioms AAT.AG.AtlasCoefficientFiber.supportPhi0_dual
#print axioms AAT.AG.AtlasCoefficientFiber.supportPhi1
#print axioms AAT.AG.AtlasCoefficientFiber.supportPhi1_apply
#print axioms AAT.AG.AtlasCoefficientFiber.supportPhi1_dual
#print axioms AAT.AG.AtlasCoefficientFiber.supportPhi2
#print axioms AAT.AG.AtlasCoefficientFiber.supportPhi2_apply
#print axioms AAT.AG.AtlasCoefficientFiber.supportPhi2_dual
#print axioms AAT.AG.AtlasCoefficientFiber.supportPhi_comm0
#print axioms AAT.AG.AtlasCoefficientFiber.supportPhi_comm1
#print axioms AAT.AG.AtlasCoefficientFiber.supportPhiHom
#print axioms AAT.AG.AtlasCoefficientFiber.supportPhiHom_f0
#print axioms AAT.AG.AtlasCoefficientFiber.supportPhiHom_f1
#print axioms AAT.AG.AtlasCoefficientFiber.supportPhiHom_f2
#print axioms AAT.AG.AtlasCoefficientFiber.supportAllPhiH1
#print axioms AAT.AG.AtlasCoefficientFiber.supportAllPhiH1_apply
#print axioms AAT.AG.AtlasCoefficientFiber.supportPhiH1_mk
#print axioms AAT.AG.AtlasCoefficientFiber.supportPhiHom_refl
#print axioms AAT.AG.AtlasCoefficientFiber.supportPhiHom_comp
#print axioms AAT.AG.AtlasCoefficientFiber.supportAllPhiH1_refl
#print axioms AAT.AG.AtlasCoefficientFiber.supportAllPhiH1_comp
#assert_standard_axioms_only AAT.AG.AtlasCoefficientFiber
