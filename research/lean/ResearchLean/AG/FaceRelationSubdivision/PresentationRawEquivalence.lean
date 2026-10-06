import ResearchLean.AG.FaceRelationSubdivision.RawChainEquivalence

/-!
# reading逆像表示の原始正逆有限和

## Implementation notes

名前の全単射と支持逆像からSource支持の同じ単一基底射を作る。
両逆とchain式は端点・三辺の原始等式から証明し、補正は零とする。
cochain同型から基底射を定義する案は生成順を逆転させるため採らない。
-/
noncomputable section
namespace AAT.AG.FaceRelationSubdivision
open CanonicalResolution ResolutionInvariance
universe u
variable {Source : Type u} {qc qf : Reading Source} {h : qc.CoarserThan qf}
variable {Nc : TargetSupportedNerve qc} {Nf : TargetSupportedNerve qf}
namespace CellPresentationEquiv
variable (E : CellPresentationEquiv qc qf h Nc Nf)

/-- 原始表示等号をSource台の等号へ運ぶ。 -/
theorem source_support_eq {I J : Type u} (e : I ≃ J) (si : I → Set qf.Target)
    (sj : J → Set qc.Target) (hs : ∀ i, si i = comparisonFactor qc qf h ⁻¹' sj (e i)) (i) :
    sourceSupport qf si i = sourceSupport qc sj (e i) := by
  ext x
  simp only [mem_sourceSupport, hs, Set.mem_preimage, comparisonFactor_commutes]

/-- 原始表示の同じ単一セル正射。 -/
def sourceForward {I J : Type u} (e : I ≃ J) (si : I → Set qf.Target)
    (sj : J → Set qc.Target) (hs : ∀ i, si i = comparisonFactor qc qf h ⁻¹' sj (e i)) :
    SupportedBasisMap (sourceSupport qf si) (sourceSupport qc sj) :=
  SupportedBasisMap.ofSingle e (fun i => (source_support_eq e si sj hs i).subset)

/-- 原始表示の同じ単一セル逆射。 -/
def sourceBackward {I J : Type u} (e : I ≃ J) (si : I → Set qf.Target)
    (sj : J → Set qc.Target) (hs : ∀ i, si i = comparisonFactor qc qf h ⁻¹' sj (e i)) :
    SupportedBasisMap (sourceSupport qc sj) (sourceSupport qf si) :=
  SupportedBasisMap.ofSingle e.symm (fun j => by
    rw [source_support_eq e si sj hs, Equiv.apply_symm_apply])

/-- 正射は同じ全単射セル名の基底像。 -/
@[simp] theorem sourceForward_basis {I J : Type u} (e : I ≃ J) (si : I → Set qf.Target)
    (sj : J → Set qc.Target) (hs : ∀ i, si i = comparisonFactor qc qf h ⁻¹' sj (e i)) (i) :
    (sourceForward e si sj hs).basisImage i = Finsupp.single (e i) 1 := rfl
/-- 逆射は同じ逆全単射セル名の基底像。 -/
@[simp] theorem sourceBackward_basis {I J : Type u} (e : I ≃ J) (si : I → Set qf.Target)
    (sj : J → Set qc.Target) (hs : ∀ i, si i = comparisonFactor qc qf h ⁻¹' sj (e i)) (j) :
    (sourceBackward e si sj hs).basisImage j = Finsupp.single (e.symm j) 1 := rfl

/-- 同じ原始表示のchart正射。 -/
def sourceR0 := sourceForward E.chartEquiv Nf.chartSupport Nc.chartSupport E.chartSupport_eq
/-- 同じ原始表示の辺正射。 -/
def sourceR1 := sourceForward E.edgeEquiv Nf.edgeSupport Nc.edgeSupport E.edgeSupport_eq
/-- 同じ原始表示の面正射。 -/
def sourceR2 := sourceForward E.faceEquiv Nf.faceSupport Nc.faceSupport E.faceSupport_eq
/-- 同じ原始表示のchart逆射。 -/
def sourceS0 := sourceBackward E.chartEquiv Nf.chartSupport Nc.chartSupport E.chartSupport_eq
/-- 同じ原始表示の辺逆射。 -/
def sourceS1 := sourceBackward E.edgeEquiv Nf.edgeSupport Nc.edgeSupport E.edgeSupport_eq
/-- 同じ原始表示の面逆射。 -/
def sourceS2 := sourceBackward E.faceEquiv Nf.faceSupport Nc.faceSupport E.faceSupport_eq

/-- chart正射の公開基底式。 -/
@[simp] theorem sourceR0_basis (v) : E.sourceR0.basisImage v = Finsupp.single (E.chartEquiv v) 1 := rfl
/-- 辺正射の公開基底式。 -/
@[simp] theorem sourceR1_basis (e) : E.sourceR1.basisImage e = Finsupp.single (E.edgeEquiv e) 1 := rfl
/-- 面正射の公開基底式。 -/
@[simp] theorem sourceR2_basis (f) : E.sourceR2.basisImage f = Finsupp.single (E.faceEquiv f) 1 := rfl
/-- chart逆射の公開基底式。 -/
@[simp] theorem sourceS0_basis (v) : E.sourceS0.basisImage v = Finsupp.single (E.chartEquiv.symm v) 1 := rfl
/-- 辺逆射の公開基底式。 -/
@[simp] theorem sourceS1_basis (e) : E.sourceS1.basisImage e = Finsupp.single (E.edgeEquiv.symm e) 1 := rfl
/-- 面逆射の公開基底式。 -/
@[simp] theorem sourceS2_basis (f) : E.sourceS2.basisImage f = Finsupp.single (E.faceEquiv.symm f) 1 := rfl

/-- 原始表示正射の端点差分可換性。 -/
theorem sourceR_comm01 : (TargetSupportedNerve.rawD1 Nc).raw.comp E.sourceR1.raw =
    E.sourceR0.raw.comp (TargetSupportedNerve.rawD1 Nf).raw := by
  apply Finsupp.lhom_ext
  intro e a
  simp only [LinearMap.comp_apply, SupportedBasisMap.raw_single, sourceR0_basis,
    sourceR1_basis, TargetSupportedNerve.rawD1_basis, map_smul, map_sub,
    one_smul, E.edge_left, E.edge_right, smul_sub]

/-- 原始表示正射の三辺符号和可換性。 -/
theorem sourceR_comm12 : (TargetSupportedNerve.rawD2 Nc).raw.comp E.sourceR2.raw =
    E.sourceR1.raw.comp (TargetSupportedNerve.rawD2 Nf).raw := by
  apply Finsupp.lhom_ext
  intro f a
  simp only [LinearMap.comp_apply, SupportedBasisMap.raw_single, sourceR1_basis,
    sourceR2_basis, TargetSupportedNerve.rawD2_basis, map_smul, map_sub, map_add,
    one_smul, E.face_edge0, E.face_edge1, E.face_edge2, smul_sub, smul_add]

/-- 単一基底正逆射の粗側往復は恒等。 -/
theorem sourceForward_backward {I J : Type u} (e : I ≃ J) (si : I → Set qf.Target)
    (sj : J → Set qc.Target) (hs : ∀ i, si i = comparisonFactor qc qf h ⁻¹' sj (e i)) :
    (sourceForward e si sj hs).raw.comp (sourceBackward e si sj hs).raw = LinearMap.id := by
  apply Finsupp.lhom_ext
  intro j a
  simp only [LinearMap.comp_apply, SupportedBasisMap.raw_single, sourceForward_basis,
    sourceBackward_basis, Equiv.apply_symm_apply, Finsupp.smul_single,
    smul_eq_mul, mul_one, LinearMap.id_apply]

/-- 単一基底正逆射の細側往復も恒等。 -/
theorem sourceBackward_forward {I J : Type u} (e : I ≃ J) (si : I → Set qf.Target)
    (sj : J → Set qc.Target) (hs : ∀ i, si i = comparisonFactor qc qf h ⁻¹' sj (e i)) :
    (sourceBackward e si sj hs).raw.comp (sourceForward e si sj hs).raw = LinearMap.id := by
  apply Finsupp.lhom_ext
  intro i a
  simp only [LinearMap.comp_apply, SupportedBasisMap.raw_single, sourceForward_basis,
    sourceBackward_basis, Equiv.symm_apply_apply, Finsupp.smul_single,
    smul_eq_mul, mul_one, LinearMap.id_apply]

/-- 正射の可換式と両逆から、同じ逆射の微分可換式を導く一般補題。 -/
theorem raw_inverse_comm {I J K L : Type u} [AddCommGroup I] [Module ℚ I]
    [AddCommGroup J] [Module ℚ J] [AddCommGroup K] [Module ℚ K]
    [AddCommGroup L] [Module ℚ L]
    (r0 : I →ₗ[ℚ] J) (r1 : K →ₗ[ℚ] L) (s0 : J →ₗ[ℚ] I) (s1 : L →ₗ[ℚ] K)
    (di : K →ₗ[ℚ] I) (dj : L →ₗ[ℚ] J)
    (hsr0 : s0.comp r0 = LinearMap.id) (hrs1 : r1.comp s1 = LinearMap.id)
    (hc : dj.comp r1 = r0.comp di) : di.comp s1 = s0.comp dj := by
  apply LinearMap.ext
  intro x
  calc
    di (s1 x) = s0 (r0 (di (s1 x))) := (LinearMap.congr_fun hsr0 _).symm
    _ = s0 (dj (r1 (s1 x))) := congrArg s0 (LinearMap.congr_fun hc (s1 x)).symm
    _ = s0 (dj x) := congrArg (fun y => s0 (dj y)) (LinearMap.congr_fun hrs1 x)

/-- chartの原始粗側往復。 -/
theorem sourceRS0 : E.sourceR0.raw.comp E.sourceS0.raw = LinearMap.id :=
  sourceForward_backward E.chartEquiv Nf.chartSupport Nc.chartSupport E.chartSupport_eq

/-- chartの原始細側往復。 -/
theorem sourceSR0 : E.sourceS0.raw.comp E.sourceR0.raw = LinearMap.id :=
  sourceBackward_forward E.chartEquiv Nf.chartSupport Nc.chartSupport E.chartSupport_eq

/-- edgeの原始粗側往復。 -/
theorem sourceRS1 : E.sourceR1.raw.comp E.sourceS1.raw = LinearMap.id :=
  sourceForward_backward E.edgeEquiv Nf.edgeSupport Nc.edgeSupport E.edgeSupport_eq

/-- edgeの原始細側往復。 -/
theorem sourceSR1 : E.sourceS1.raw.comp E.sourceR1.raw = LinearMap.id :=
  sourceBackward_forward E.edgeEquiv Nf.edgeSupport Nc.edgeSupport E.edgeSupport_eq

/-- faceの原始粗側往復。 -/
theorem sourceRS2 : E.sourceR2.raw.comp E.sourceS2.raw = LinearMap.id :=
  sourceForward_backward E.faceEquiv Nf.faceSupport Nc.faceSupport E.faceSupport_eq

/-- faceの原始細側往復。 -/
theorem sourceSR2 : E.sourceS2.raw.comp E.sourceR2.raw = LinearMap.id :=
  sourceBackward_forward E.faceEquiv Nf.faceSupport Nc.faceSupport E.faceSupport_eq

/-- 原始表示逆射の同じ端点差分可換性。 -/
theorem sourceS_comm01 : (TargetSupportedNerve.rawD1 Nf).raw.comp E.sourceS1.raw =
    E.sourceS0.raw.comp (TargetSupportedNerve.rawD1 Nc).raw :=
  raw_inverse_comm E.sourceR0.raw E.sourceR1.raw E.sourceS0.raw E.sourceS1.raw
    _ _ E.sourceSR0 E.sourceRS1 E.sourceR_comm01
/-- 原始表示逆射の同じ三辺符号和可換性。 -/
theorem sourceS_comm12 : (TargetSupportedNerve.rawD2 Nf).raw.comp E.sourceS2.raw =
    E.sourceS1.raw.comp (TargetSupportedNerve.rawD2 Nc).raw :=
  raw_inverse_comm E.sourceR1.raw E.sourceR2.raw E.sourceS1.raw E.sourceS2.raw
    _ _ E.sourceSR1 E.sourceRS2 E.sourceR_comm12

/-- reading逆像/セル表示の原始両逆、零二補正を生成する。 -/
def rawEquivalence : RawChainEquivalence Nc Nf where
  r0 := E.sourceR0; r1 := E.sourceR1; r2 := E.sourceR2
  s0 := E.sourceS0; s1 := E.sourceS1; s2 := E.sourceS2
  h0 := SupportedBasisMap.zero _ _; h1 := SupportedBasisMap.zero _ _
  k0 := SupportedBasisMap.zero _ _; k1 := SupportedBasisMap.zero _ _
  r_comm01 := E.sourceR_comm01; r_comm12 := E.sourceR_comm12
  s_comm01 := E.sourceS_comm01; s_comm12 := E.sourceS_comm12
  sr_h0 := by simp only [SupportedBasisMap.raw_zero, LinearMap.comp_zero, add_zero, E.sourceSR0]
  sr_h1 := by simp only [SupportedBasisMap.raw_zero, LinearMap.comp_zero, LinearMap.zero_comp, add_zero, E.sourceSR1]
  sr_h2 := by simp only [SupportedBasisMap.raw_zero, LinearMap.zero_comp, add_zero, E.sourceSR2]
  rs_k0 := by simp only [SupportedBasisMap.raw_zero, LinearMap.comp_zero, add_zero, E.sourceRS0]
  rs_k1 := by simp only [SupportedBasisMap.raw_zero, LinearMap.comp_zero, LinearMap.zero_comp, add_zero, E.sourceRS1]
  rs_k2 := by simp only [SupportedBasisMap.raw_zero, LinearMap.zero_comp, add_zero, E.sourceRS2]

/-- 有限列表示出力の原始r0は同じ名前全単射のSource支持基底射。 -/
@[simp] theorem rawEquivalence_r0 : E.rawEquivalence.r0 = E.sourceR0 := rfl
/-- 有限列表示出力の原始r1は同じ名前全単射のSource支持基底射。 -/
@[simp] theorem rawEquivalence_r1 : E.rawEquivalence.r1 = E.sourceR1 := rfl
/-- 有限列表示出力の原始r2は同じ名前全単射のSource支持基底射。 -/
@[simp] theorem rawEquivalence_r2 : E.rawEquivalence.r2 = E.sourceR2 := rfl
/-- 有限列表示出力の原始s0は同じ名前全単射のSource支持基底射。 -/
@[simp] theorem rawEquivalence_s0 : E.rawEquivalence.s0 = E.sourceS0 := rfl
/-- 有限列表示出力の原始s1は同じ名前全単射のSource支持基底射。 -/
@[simp] theorem rawEquivalence_s1 : E.rawEquivalence.s1 = E.sourceS1 := rfl
/-- 有限列表示出力の原始s2は同じ名前全単射のSource支持基底射。 -/
@[simp] theorem rawEquivalence_s2 : E.rawEquivalence.s2 = E.sourceS2 := rfl

/-- 原始表示出力の補正h0は同じ零有限和。 -/
@[simp] theorem rawEquivalence_h0 : E.rawEquivalence.h0 = SupportedBasisMap.zero _ _ := rfl
/-- 原始表示出力の補正h1は同じ零有限和。 -/
@[simp] theorem rawEquivalence_h1 : E.rawEquivalence.h1 = SupportedBasisMap.zero _ _ := rfl
/-- 原始表示出力の補正k0は同じ零有限和。 -/
@[simp] theorem rawEquivalence_k0 : E.rawEquivalence.k0 = SupportedBasisMap.zero _ _ := rfl
/-- 原始表示出力の補正k1は同じ零有限和。 -/
@[simp] theorem rawEquivalence_k1 : E.rawEquivalence.k1 = SupportedBasisMap.zero _ _ := rfl
end CellPresentationEquiv
end AAT.AG.FaceRelationSubdivision
#assert_standard_axioms_only AAT.AG.FaceRelationSubdivision
