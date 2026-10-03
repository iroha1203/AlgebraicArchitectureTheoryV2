import ResearchLean.AG.RepairObservationDuality.PrimitiveAffineDefect

/-!
# The same physical affine defect on the original fixed-part relative faces

## Implementation notes

G-131 A / n1017 §3.5 and §6.1. Primitive tower and affine-change conditions
are the input assumptions. The main results derive the same physical defect
from accepted G-129 correction and G-130 linear-differential APIs. Fixed-part
assumptions in the relative module are actual face equalities, not defect laws.

The fixed-face input is an equality of actual paths and authored comparisons
for every parameter. It implies native vanishing through the generated raw
defect theorem. The constant and linear right-hand-side terms are constructed
on the whole original relative face space, with the required negative sign.
-/

namespace AAT.AG.RepairObservationDuality.RelativeAffineDefect
open CategoryTheory TransportCoherence TransportCoherence.Arbitrary
open AbelianLiftingObstruction RelativeRepairComposition FiniteCoefficients
open PrimitiveAffineDefect
set_option autoImplicit false
universe uk uV uG uE uB uD vE vB vD
variable {k : Type uk} [Field k]
variable {V : Type uV} [AddCommGroup V] [Module k V]
variable {K : FiniteTransportPresentation.{uG}}
variable {E : Type uE} {B : Type uB} {D : Type uD}
variable [Category.{vE} E] [Category.{vB} B] [Category.{vD} D]
variable {p : E ⥤ B} {q : B ⥤ D}
variable (T : TowerPresentation K p q)
variable [∀ v, Module k ((T.localCoefficients).A v)]
variable (hlinear : ∀ {i j : K.Vertex} (e : K.Edge i j) (t : k)
  (x : (T.localCoefficients).A i),
  (T.localCoefficients).edge e (t • x) = t • (T.localCoefficients).edge e x)
local notation "M" => T.localCoefficients
variable (edgeChange : V →ₗ[k] (C1 (T.localCoefficients)))
variable (comparisonChange : V →ₗ[k] (C2 (T.localCoefficients)))
variable (P : ClosedRegion K)
variable (hfixed : ∀ v : V, ∀ f ∈ P.faces,
  (data T (edgeChange v) (comparisonChange v)).lift.pathLift (K.twoLeft f) ≫
    FiberAut.hom ((data T (edgeChange v) (comparisonChange v)).comparator f) =
  (data T (edgeChange v) (comparisonChange v)).lift.pathLift (K.twoRight f))
attribute [local instance] Classical.propDecidable
include hfixed

/-- Fixed actual face equalities imply vanishing of every generated native value.

G-131 A / n1017 §3.5, §6.1. API lemma/constructor for the named primitive or relative construction.
Input assumptions and predecessor use are specified in the module notes.
-/
theorem fixed_defect_zero (v : V) (f : K.TwoCell) (hf : f ∈ P.faces) :
    defect T (edgeChange v) (comparisonChange v) f = 0 :=
  (defect_zero_iff T (edgeChange v) (comparisonChange v) f).mpr (hfixed v f hf)

include hlinear in
/-- The same zero parameter's original defect vanishes on the original fixed faces.

G-131 A / n1017 §3.5, §6.1. API lemma/constructor for the named primitive or relative construction.
Input assumptions and predecessor use are specified in the module notes.
-/
theorem base_defect_zero (f : K.TwoCell) (hf : f ∈ P.faces) : T.defect f = 0 := by
  have hz := fixed_defect_zero T edgeChange comparisonChange P hfixed 0 f hf
  rw [affine_defect T hlinear edgeChange comparisonChange 0,map_zero,add_zero] at hz
  exact hz

/-- Physical fixed-face coherence forces the generated linear term to vanish
there; this condition is not supplied as a separate certificate.

G-131 A / n1017 §3.5, §6.1. Main construction/theorem.
Input assumptions and predecessor use are specified in the module notes.
-/
theorem linear_term_zero (v : V) (f : K.TwoCell) (hf : f ∈ P.faces) :
    linearTerm T hlinear edgeChange comparisonChange v f = 0 := by
  have hz := fixed_defect_zero T edgeChange comparisonChange P hfixed v f hf
  rw [affine_defect T hlinear edgeChange comparisonChange v] at hz
  change T.defect f + linearTerm T hlinear edgeChange comparisonChange v f = 0 at hz
  rw [base_defect_zero T hlinear edgeChange comparisonChange P hfixed f hf,zero_add] at hz
  exact hz

/-- The actual native defect, on all original faces with fixed-face zeros.

G-131 A / n1017 §3.5, §6.1. Main construction/theorem.
Input assumptions and predecessor use are specified in the module notes.
-/
noncomputable def relativeDefect (v : V) : RelativeCover.C2 M ClosedRegion.all P :=
  ⟨fun f => defect T (edgeChange v) (comparisonChange v) f.1,
    fun f hf => fixed_defect_zero T edgeChange comparisonChange P hfixed v f.1 hf⟩

/-- Relative coordinates preserve each physical face's complete native value.

G-131 A / n1017 §3.5, §6.1. API lemma/constructor for the named primitive or relative construction.
Input assumptions and predecessor use are specified in the module notes.
-/
theorem relativeDefect_value (v : V) (f : K.TwoCell) :
    (relativeDefect T edgeChange comparisonChange P hfixed v).1 ⟨f,Set.mem_univ f⟩ =
      defect T (edgeChange v) (comparisonChange v) f := rfl

/-- The generated relative linear term retains all original face values.

G-131 A / n1017 §3.5, §6.1. Main construction/theorem.
Input assumptions and predecessor use are specified in the module notes.
-/
noncomputable def relativeLinear : V →ₗ[k] RelativeCover.C2 M ClosedRegion.all P where
  toFun v := ⟨fun f => linearTerm T hlinear edgeChange comparisonChange v f.1,
    fun f hf => linear_term_zero T hlinear edgeChange comparisonChange P hfixed v f.1 hf⟩
  map_add' v w := by
    apply Subtype.ext
    funext f
    exact congrArg (fun h : C2 M => h f.1) ((linearTerm T hlinear edgeChange comparisonChange).map_add v w)
  map_smul' t v := by
    apply Subtype.ext
    funext f
    exact congrArg (fun h : C2 M => h f.1) ((linearTerm T hlinear edgeChange comparisonChange).map_smul t v)

/-- Each relative linear coordinate is the generated original face value.

G-131 A / n1017 §3.5, §6.1. API lemma/constructor for the named primitive or relative construction.
Input assumptions and predecessor use are specified in the module notes.
-/
theorem relativeLinear_value (v : V) (f : K.TwoCell) :
    (relativeLinear T hlinear edgeChange comparisonChange P hfixed v).1
      ⟨f,Set.mem_univ f⟩ = linearTerm T hlinear edgeChange comparisonChange v f := rfl

/-- The zero input determines A's constant negative relative defect.

G-131 A / n1017 §3.5, §6.1. Main construction/theorem.
Input assumptions and predecessor use are specified in the module notes.
-/
noncomputable def baseRhs : RelativeCover.C2 M ClosedRegion.all P :=
  -relativeDefect T edgeChange comparisonChange P hfixed 0

/-- A's B is the negative of the primitive-generated relative linear term.

G-131 A / n1017 §3.5, §6.1. Main construction/theorem.
Input assumptions and predecessor use are specified in the module notes.
-/
noncomputable def rhsLinear : V →ₗ[k] RelativeCover.C2 M ClosedRegion.all P :=
  -relativeLinear T hlinear edgeChange comparisonChange P hfixed

/-- The constant coordinate is the same original zero-parameter negative defect.

G-131 A / n1017 §3.5, §6.1. API lemma/constructor for the named primitive or relative construction.
Input assumptions and predecessor use are specified in the module notes.
-/
theorem baseRhs_value (f : K.TwoCell) :
    (baseRhs T edgeChange comparisonChange P hfixed).1 ⟨f,Set.mem_univ f⟩ =
      -defect T (edgeChange 0) (comparisonChange 0) f := rfl

/-- The negative linear coordinate has the required sign of the physical update.

G-131 A / n1017 §3.5, §6.1. API lemma/constructor for the named primitive or relative construction.
Input assumptions and predecessor use are specified in the module notes.
-/
theorem rhsLinear_value (v : V) (f : K.TwoCell) :
    (rhsLinear T hlinear edgeChange comparisonChange P hfixed v).1 ⟨f,Set.mem_univ f⟩ =
      -linearTerm T hlinear edgeChange comparisonChange v f := rfl

/-- The same actual relative negative defect is exactly b0+Bv.

G-131 A / n1017 §3.5, §6.1. Main construction/theorem.
Input assumptions and predecessor use are specified in the module notes.
-/
theorem negative_defect_affine (v : V) :
    -relativeDefect T edgeChange comparisonChange P hfixed v =
      baseRhs T edgeChange comparisonChange P hfixed + rhsLinear T hlinear edgeChange comparisonChange P hfixed v := by
  apply Subtype.ext
  funext f
  change -((relativeDefect T edgeChange comparisonChange P hfixed v).1 f) =
    (baseRhs T edgeChange comparisonChange P hfixed).1 f +
      (rhsLinear T hlinear edgeChange comparisonChange P hfixed v).1 f
  rw [relativeDefect_value,baseRhs_value,rhsLinear_value]
  rw [affine_defect T hlinear edgeChange comparisonChange v,affine_defect T hlinear edgeChange comparisonChange 0,map_zero,add_zero]
  exact neg_add _ _

/-- The affine right-hand side's negative includes to the physical raw defect
of the same reference paths and comparisons.

G-131 A / n1017 §3.5, §6.1. Main construction/theorem.
Input assumptions and predecessor use are specified in the module notes.
-/
theorem rhs_physical_value (v : V) (f : K.TwoCell) :
    kernelInclusion p q _ (Additive.toMul
      (-((baseRhs T edgeChange comparisonChange P hfixed + rhsLinear T hlinear edgeChange comparisonChange P hfixed v).1
        ⟨f,Set.mem_univ f⟩))) =
      rawFaceDefect (data T (edgeChange v) (comparisonChange v)) 1 f := by
  rw [← negative_defect_affine]
  change kernelInclusion p q _ (Additive.toMul
    (-(-((relativeDefect T edgeChange comparisonChange P hfixed v).1 ⟨f,Set.mem_univ f⟩)))) = _
  rw [neg_neg,relativeDefect_value]
  exact defect_inclusion T (edgeChange v) (comparisonChange v) f

end AAT.AG.RepairObservationDuality.RelativeAffineDefect
#assert_standard_axioms_only AAT.AG.RepairObservationDuality.RelativeAffineDefect
