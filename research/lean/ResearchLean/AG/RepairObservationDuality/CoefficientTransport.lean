import ResearchLean.AG.RepairObservationDuality.NativeCorrectionEquation

/-!
# Complete coordinate transport along an equality of native coefficients

## Implementation notes

G-131 A / n1017 §3.5, §6.1 uses one shared whole coefficient system.
These basic constructor APIs transport the modules, relative face values and
full split sources along the coefficient equality derived from primitive data.
Every operation reduces to identity after equality elimination; no image basis
or selected quotient is substituted for the full source.
-/
namespace AAT.AG.RepairObservationDuality.CoefficientTransport
open TransportCoherence AbelianLiftingObstruction RelativeRepairComposition
set_option autoImplicit false
universe uk uG uA
variable {k : Type uk} [Field k]
variable {K : FiniteTransportPresentation.{uG}}
variable (M₁ M₂ : LocalCoefficients.{uG,uA} K)

/-- G-131 A / n1017 §3.5, §6.1 API: equality transports every whole vertex module. -/
def modules [∀ v, Module k (M₁.A v)] (hm : M₁ = M₂) :
    ∀ v, Module k (M₂.A v) := by
  cases hm
  intro v
  infer_instance

variable (P : ClosedRegion K)
/-- G-131 A / n1017 §3.5, §6.1 API: equality transports every relative face value. -/
def faces (hm : M₁ = M₂) :
    RelativeCover.C2 M₁ ClosedRegion.all P ≃+ RelativeCover.C2 M₂ ClosedRegion.all P := by
  cases hm
  exact AddEquiv.refl _

/-- G-131 A / n1017 §3.5, §6.1 API: coordinate transport retains the complete
value at every original face, with only its dependent coefficient type cast. -/
theorem faces_value (hm : M₁ = M₂)
    (r : RelativeCover.C2 M₁ ClosedRegion.all P) (f : K.TwoCell) :
    (faces M₁ M₂ P hm r).1 ⟨f,Set.mem_univ f⟩ =
      Eq.mp (congrArg (fun M : LocalCoefficients K => M.A (K.twoTarget f)) hm)
        (r.1 ⟨f,Set.mem_univ f⟩) := by
  cases hm
  rfl

/-- G-131 A / n1017 §3.5, §6.1 API: reversing the coefficient equality gives
the inverse full-face coordinate map. -/
theorem faces_symm (hm : M₁ = M₂) :
    (faces M₁ M₂ P hm).symm = faces M₂ M₁ P hm.symm := by
  cases hm
  rfl

variable [∀ v, Module k (M₁.A v)]
variable (hlinear : ∀ {i j : K.Vertex} (e : K.Edge i j) (t : k) (x : M₁.A i),
  M₁.edge e (t • x) = t • M₁.edge e x)

include hlinear in
/-- G-131 A / n1017 §3.5, §6.1 API: actual transport remains linear under the
same whole-module coordinate equality. -/
theorem linearity (hm : M₁ = M₂) :
    letI := modules (k := k) M₁ M₂ hm
    ∀ {i j : K.Vertex} (e : K.Edge i j) (t : k) (x : M₂.A i),
      M₂.edge e (t • x) = t • M₂.edge e x := by
  cases hm
  exact hlinear

variable (candidates : Set (EdgeName (K := K))) [DecidablePred (· ∈ candidates)]
attribute [local instance] Classical.propDecidable

/-- G-131 A / n1017 §3.5, §6.1 API: full always and selected candidate values
transport at the same original names, without discarding any coefficient. -/
def values (hm : M₁ = M₂) (S : Set candidates) :
    letI := modules (k := k) M₁ M₂ hm
    (OriginalColumns.alwaysSpace (k := k) M₁ P candidates ×
      (∀ e : S, M₁.A e.1.1.2.1)) ≃+
    (OriginalColumns.alwaysSpace (k := k) M₂ P candidates ×
      (∀ e : S, M₂.A e.1.1.2.1)) := by
  cases hm
  exact AddEquiv.refl _

omit [DecidablePred (· ∈ candidates)] in
/-- G-131 A / n1017 §3.5, §6.1 API: the full always value at every original
edge survives the coordinate map. -/
theorem values_always_value (hm : M₁ = M₂) (S : Set candidates)
    (h : OriginalColumns.alwaysSpace (k := k) M₁ P candidates × (∀ e : S, M₁.A e.1.1.2.1))
    (e : EdgeName (K := K)) :
    letI := modules (k := k) M₁ M₂ hm
    (values (k := k) M₁ M₂ P candidates hm S h).1.1.1 ⟨e,Set.mem_univ e⟩ =
      Eq.mp (congrArg (fun M : LocalCoefficients K => M.A e.2.1) hm)
        (h.1.1.1 ⟨e,Set.mem_univ e⟩) := by
  cases hm
  rfl

omit [DecidablePred (· ∈ candidates)] in
/-- G-131 A / n1017 §3.5, §6.1 API: every selected whole candidate value
survives at its same original name. -/
theorem values_selected_value (hm : M₁ = M₂) (S : Set candidates)
    (h : OriginalColumns.alwaysSpace (k := k) M₁ P candidates × (∀ e : S, M₁.A e.1.1.2.1))
    (e : S) :
    letI := modules (k := k) M₁ M₂ hm
    (values (k := k) M₁ M₂ P candidates hm S h).2 e =
      Eq.mp (congrArg (fun M : LocalCoefficients K => M.A e.1.1.2.1) hm) (h.2 e) := by
  cases hm
  rfl

variable (houtside : ∀ e ∈ candidates, e ∉ P.edges)
variable [Fintype (EdgeName (K := K))] [DecidableEq (EdgeName (K := K))]
/-- G-131 A / n1017 §3.5, §6.1: the entire selected native differential commutes
with the full source and face coordinate transport. -/
theorem differential (hm : M₁ = M₂) (S : Set candidates)
    (h : OriginalColumns.alwaysSpace (k := k) M₁ P candidates ×
      (∀ e : S, M₁.A e.1.1.2.1)) :
    letI := modules (k := k) M₁ M₂ hm
    faces M₁ M₂ P hm
      (SelectedCokernel.differential
        (OriginalColumns.D (k := k) M₁ P candidates hlinear)
        (OriginalColumns.column (k := k) M₁ P candidates houtside hlinear) S h) =
    SelectedCokernel.differential
      (OriginalColumns.D (k := k) M₂ P candidates (linearity M₁ M₂ hlinear hm))
      (OriginalColumns.column (k := k) M₂ P candidates houtside
        (linearity M₁ M₂ hlinear hm)) S (values (k := k) M₁ M₂ P candidates hm S h) := by
  cases hm
  rfl

/-- G-131 A / n1017 §3.5, §6.1: every solution of the transported full native
split equation corresponds to a full solution in the shared coordinates. -/
theorem equation_iff (hm : M₁ = M₂) (S : Set candidates)
    (r : RelativeCover.C2 M₂ ClosedRegion.all P) :
    (letI := modules (k := k) M₁ M₂ hm
     ∃ h, SelectedCokernel.differential
       (OriginalColumns.D (k := k) M₂ P candidates (linearity M₁ M₂ hlinear hm))
       (OriginalColumns.column (k := k) M₂ P candidates houtside
         (linearity M₁ M₂ hlinear hm)) S h = r) ↔
    ∃ h, SelectedCokernel.differential
      (OriginalColumns.D (k := k) M₁ P candidates hlinear)
      (OriginalColumns.column (k := k) M₁ P candidates houtside hlinear) S h =
      (faces M₁ M₂ P hm).symm r := by
  cases hm
  rfl

end AAT.AG.RepairObservationDuality.CoefficientTransport
#assert_standard_axioms_only AAT.AG.RepairObservationDuality.CoefficientTransport
