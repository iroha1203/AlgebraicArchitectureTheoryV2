import ResearchLean.AG.RepairObservationDuality.ActualAffineFamily
import ResearchLean.AG.RepairObservationDuality.ResidualDualWitness
import ResearchLean.AG.RepairObservationDuality.DualValueAcquisition

/-!
# G-131 D: the same named dual value on every original input

## Implementation notes

The physical SupportedRepair failure and negative defect are independently
constructed from the original tower. The G-130 witness descends to the same
selected native quotient without replacement. Realization of every parameter
turns acquisition on the original known fiber into the restricted-span
criterion for that particular dual value.
-/
namespace AAT.AG.RepairObservationDuality.ActualDualWitness
open CategoryTheory TransportCoherence TransportCoherence.Arbitrary
open AbelianLiftingObstruction RelativeRepairComposition PrimitiveAffineDefect
set_option autoImplicit false
universe uk uV uF uG uE uB uD vE vB vD
variable {k : Type uk} [Field k]
variable {V : Type uV} [AddCommGroup V] [Module k V]
variable {F : Type uF}
variable {K : FiniteTransportPresentation.{uG}}
variable {E : Type uE} {B : Type uB} {D : Type uD}
variable [Category.{vE} E] [Category.{vB} B] [Category.{vD} D]
variable {p : E ⥤ B} {q : B ⥤ D}
variable (T : TowerPresentation K p q)
variable [∀ v, Module k ((T.localCoefficients).A v)]
variable (edgeChange : V →ₗ[k] (C1 (T.localCoefficients)))
variable (comparisonChange : V →ₗ[k] (C2 (T.localCoefficients)))
variable (input : F → OriginalTowerPresentation K p q) (ν : F → V)
variable (hdata : ∀ X : F, (input X).toTower.toTransportData =
  data T (edgeChange (ν X)) (comparisonChange (ν X)))

variable (realize : V → F) (hrealize : ∀ v, ν (realize v) = v)
variable (P : ClosedRegion K)
variable (hfixed : ∀ X : F, ∀ f ∈ P.faces,
  (input X).toTower.upper.pathLift (K.twoLeft f) ≫
    FiberAut.hom ((input X).comparator f) =
  (input X).toTower.upper.pathLift (K.twoRight f))
variable (hlinear : ∀ {i j : K.Vertex} (e : K.Edge i j) (t : k)
  (x : (T.localCoefficients).A i),
  (T.localCoefficients).edge e (t • x) = t • (T.localCoefficients).edge e x)
variable (candidates : Set (EdgeName (K := K))) [DecidablePred (· ∈ candidates)]
variable (houtside : ∀ e ∈ candidates, e ∉ P.edges)
variable [Fintype (EdgeName (K := K))] [DecidableEq (EdgeName (K := K))]
attribute [local instance] Classical.propDecidable
local notation "D₀" => OriginalColumns.D (k := k) T.localCoefficients P candidates hlinear
local notation "C" => OriginalColumns.column (k := k) T.localCoefficients P candidates houtside hlinear
local notation "fixed" => ActualAffineFamily.model_fixed T edgeChange comparisonChange input ν hdata realize hrealize P hfixed
local notation "b₀" => RelativeAffineDefect.baseRhs T edgeChange comparisonChange P fixed
local notation "B₀" => RelativeAffineDefect.rhsLinear T hlinear edgeChange comparisonChange P fixed
local notation "DS" => SelectedCokernel.differential D₀ C
local notation "col" => CokernelNamed.column D₀ C
include hdata hrealize hfixed

/-- D's failed original repair supplies its same named dual witness on the native residual quotient. -/
theorem actual_failure (S : Set candidates) (X : F)
    (hn : ¬ Nonempty (SupportedRepair (input X)
      (fixedEdgesForRange P.edges candidates (OriginalRanges.allowed candidates S)))) :
    ∃ (phi : Module.Dual k ((RelativeCover.C2 T.localCoefficients ClosedRegion.all P) ⧸ LinearMap.range D₀))
      (hp : ∀ e ∈ S, phi.comp (col e) = 0),
      ResidualDualWitness.native D₀ C S phi hp
        ((LinearMap.range (DS S)).mkQ
          (-ActualAffineFamily.commonDefect T edgeChange comparisonChange input ν hdata P hfixed X)) ≠ 0 := by
  have he : ¬ ∃ h, DS S h = b₀ + B₀ (ν X) := by
    intro hh
    exact hn ((ActualAffineFamily.actual_affine_equation_iff T edgeChange comparisonChange
      input ν hdata realize hrealize P hfixed hlinear candidates houtside X S).mpr hh)
  obtain ⟨phi,hp,hv⟩ := ResidualDualWitness.failure D₀ C S (b₀ + B₀ (ν X)) he
  refine ⟨phi,hp,?_⟩
  rw [ActualAffineFamily.negative_defect_affine T edgeChange comparisonChange input ν hdata
    realize hrealize P hfixed hlinear X]
  exact hv

/-- D's dual value reads the identical physical negative defect with the original named witness. -/
theorem actual_value (S : Set candidates)
    (phi : Module.Dual k ((RelativeCover.C2 T.localCoefficients ClosedRegion.all P) ⧸ LinearMap.range D₀))
    (hp : ∀ e ∈ S, phi.comp (col e) = 0) (X : F) :
    ResidualDualWitness.native D₀ C S phi hp ((LinearMap.range (DS S)).mkQ
      (-ActualAffineFamily.commonDefect T edgeChange comparisonChange input ν hdata P hfixed X)) =
      phi (LinearInterface.q D₀ (b₀ + B₀ (ν X))) := by
  rw [ActualAffineFamily.negative_defect_affine T edgeChange comparisonChange input ν hdata
    realize hrealize P hfixed hlinear X, ResidualDualWitness.native_value]

variable {I J : Type*} [AddCommGroup I] [Module k I]
variable (L : V →ₗ[k] I) (s : I) (lam : J → V →ₗ[k] k) (points : Finset J)

/-- D's same failed-input dual value is acquired on all original inputs exactly under its restricted primitive-span condition. -/
theorem actual_acquisition_iff [FiniteDimensional k V] (S : Set candidates)
    (phi : Module.Dual k ((RelativeCover.C2 T.localCoefficients ClosedRegion.all P) ⧸ LinearMap.range D₀))
    (hp : ∀ e ∈ S, phi.comp (col e) = 0) {base : F} (hb : L (ν base) = s) :
    (∃ f : (points → k) → k, ∀ X : F, L (ν X) = s →
      f (observation lam points (ν X)) =
        ResidualDualWitness.native D₀ C S phi hp ((LinearMap.range (DS S)).mkQ
          (-ActualAffineFamily.commonDefect T edgeChange comparisonChange input ν hdata P hfixed X))) ↔
      ((ResidualDualWitness.native D₀ C S phi hp).comp ((LinearMap.range (DS S)).mkQ.comp B₀)).comp (LinearMap.ker L).subtype ∈
        LinearObservationDuality.evaluationSpan
          (fun j => (lam j).comp (LinearMap.ker L).subtype) points := by
  have he := DualValueAcquisition.residual_acquisition_iff (DS S) B₀ b₀ (ResidualDualWitness.native D₀ C S phi hp) L s lam points hb
  refine Iff.trans ?_ he
  constructor
  · rintro ⟨f,hf⟩
    refine ⟨f,?_⟩
    intro v hv
    have h := hf (realize v) (by simpa only [hrealize] using hv)
    simpa only [ActualAffineFamily.negative_defect_affine T edgeChange comparisonChange input ν
      hdata realize hrealize P hfixed hlinear, hrealize] using h
  · rintro ⟨f,hf⟩
    refine ⟨f,?_⟩
    intro X hx
    rw [ActualAffineFamily.negative_defect_affine T edgeChange comparisonChange input ν hdata
      realize hrealize P hfixed hlinear X]
    exact hf (ν X) hx

end AAT.AG.RepairObservationDuality.ActualDualWitness
#assert_standard_axioms_only AAT.AG.RepairObservationDuality.ActualDualWitness
