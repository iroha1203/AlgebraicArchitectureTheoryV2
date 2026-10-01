import ResearchLean.AG.RelativeRepairComposition.FiniteCoefficientDifferentials

/-!
# The original typed three-cell differential is linear

Both authored rewrite pastings are retained, including each orientation and
outgoing transport. The relative map is obtained by the same original restriction.
-/
namespace AAT.AG.RelativeRepairComposition
open TransportCoherence AbelianLiftingObstruction
universe uk uG uA
namespace FiniteCoefficients
variable {k : Type uk} [Field k]
variable {K : FiniteTransportPresentation.{uG}} (M : LocalCoefficients.{uG,uA} K)
variable [∀ v, Module k (M.A v)]
variable (hlinear : ∀ {i j : K.Vertex} (e : K.Edge i j) (t : k) (x : M.A i),
  M.edge e (t • x) = t • M.edge e x)

include hlinear in
/-- Each original oriented whiskered face retains its signed linear full transport. -/
theorem faceCorrection_smul (c : C2 M) (t : k) {source target : K.Vertex}
    (f : WhiskeredFace K.toFiniteTransportTwoPresentation source target) :
    faceCorrection M (t • c) f = t • faceCorrection M c f := by
  cases ho : f.orientation <;>
    simp only [faceCorrection,ho,Pi.smul_apply,pathTransport_smul M hlinear,smul_neg]

include hlinear in
/-- Every step of the original typed pasting contributes its full linear value. -/
theorem pastingCorrection_smul (c : C2 M) (t : k) {source target : K.Vertex}
    {before after : K.Path source target}
    (w : RewritePasting K.toFiniteTransportTwoPresentation before after) :
    pastingCorrection M (t • c) w = t • pastingCorrection M c w := by
  induction w with
  | nil => simp only [pastingCorrection,smul_zero]
  | cons step tail ih =>
    simp only [pastingCorrection,faceCorrection_smul M hlinear,ih,smul_add]

include hlinear in
/-- Both original three-cell routes give the same linear differential. -/
theorem d2_smul (c : C2 M) (t : k) : d2 M (t • c) = t • d2 M c := by
  funext s
  simp only [d2,Pi.smul_apply,pastingCorrection_smul M hlinear,smul_sub]

variable (U P : ClosedRegion K) [DecidablePred (· ∈ U.faces)]

/-- Extending and restricting original face values preserves the complete relative family. -/
theorem restrict_extend2 (c : RelativeCover.C2 M U P) :
    ClosedRegion.r2 M U (FiniteFamily.extend (k := k) (fun f => M.A (K.twoTarget f)) U.faces c.1) = c.1 :=
  FiniteFamily.restrict_extend (fun f => M.A (K.twoTarget f)) U.faces c.1

/-- The actual relative three-cell differential, with linearity derived from its typed pastings. -/
def differential2 : RelativeCover.C2 M U P →ₗ[k] RelativeCover.C3 M U P where
  toFun c := ⟨ClosedRegion.r3 M U (d2 M
    (FiniteFamily.extend (k := k) (fun f => M.A (K.twoTarget f)) U.faces c.1)),by
      have hh := ClosedRegion.r_d2 M U
        (FiniteFamily.extend (k := k) (fun f => M.A (K.twoTarget f)) U.faces c.1)
      rw [restrict_extend2 M U P c] at hh
      rw [hh]
      exact RelativeCover.d2_mem M U P c⟩
  map_add' c j := by
    apply Subtype.ext
    change ClosedRegion.r3 M U (d2 M
      (FiniteFamily.extend (k := k) (fun f => M.A (K.twoTarget f)) U.faces (c.1+j.1))) = _
    rw [map_add,d2_add,map_add]
    rfl
  map_smul' t c := by
    apply Subtype.ext
    change ClosedRegion.r3 M U (d2 M
      (FiniteFamily.extend (k := k) (fun f => M.A (K.twoTarget f)) U.faces (t • c.1))) = _
    rw [map_smul,d2_smul M hlinear]
    rfl

/-- The linear map is exactly the accepted full original relative d2. -/
theorem differential2_eq (c : RelativeCover.C2 M U P) :
    differential2 M hlinear U P c = RelativeCover.d2 M U P c := by
  apply Subtype.ext
  have hh := ClosedRegion.r_d2 M U
    (FiniteFamily.extend (k := k) (fun f => M.A (K.twoTarget f)) U.faces c.1)
  rw [restrict_extend2 M U P c] at hh
  exact hh

variable [DecidablePred (· ∈ U.edges)]
/-- The same original degree-one and degree-two maps have zero composition. -/
theorem differential2_differential1 (h : RelativeCover.C1 M U P) :
    differential2 M hlinear U P (differential1 M hlinear U P h) = 0 := by
  rw [differential1_eq,differential2_eq,RelativeCover.d2_d1]

end FiniteCoefficients
end AAT.AG.RelativeRepairComposition
#assert_standard_axioms_only AAT.AG.RelativeRepairComposition
