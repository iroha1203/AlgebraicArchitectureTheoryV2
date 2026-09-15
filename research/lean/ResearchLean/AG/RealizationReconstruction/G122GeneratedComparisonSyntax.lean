import ResearchLean.AG.RealizationReconstruction.G122FiniteCoverageBridge
import Formal.Util.AssertStandardAxioms

/-!
# Source-provenanced syntax for generated G-122 comparisons

The exhaustive point-probe route stops at infinite primitive carriers.  This
module starts the parameter-relative alternative on the comparison fragment
that G-123(D) must retain.  A typed finite term may use identities,
composition, and five source-constructed comparison leaves from an original
`G122CellInput`: the five-factor comparison and its inverse, the
cochain-selected comparison, and its source and target projectors.

No constructor accepts a completed `GeometryTotalHom`.  Evaluation invokes
the existing mathematical constructions only after the original family and
cell inputs are supplied.  The inverse, factorization, idempotence, and
absorption laws are then proved for the evaluated terms.

## Implementation notes

The syntax is indexed by its exact generated source and target objects, so
ill-typed composites cannot be formed.  Its recursive `size` counts every
constructor node; arbitrary primitive data remain parameters carried by a
leaf rather than being finitely enumerated.  This fragment does not represent
all complete morphisms, define a quotient congruence, or prove fullness.
-/

namespace AAT.AG.RealizationReconstruction

universe u v

/-- Finite typed expressions generated from the canonical comparisons,
projectors, and source-constructed inverse of `barAlpha` from original G-122
family/cell input data. -/
inductive G122GeneratedComparisonSyntax (Θ : G122FamilyInput.{u, v}) :
    G122GeneratedGeometryObject Θ → G122GeneratedGeometryObject Θ →
      Type (max (u + 2) (v + 1))
  | identity (X : G122GeneratedGeometryObject Θ) :
      G122GeneratedComparisonSyntax Θ X X
  | compose {X Y Z : G122GeneratedGeometryObject Θ}
      (first : G122GeneratedComparisonSyntax Θ X Y)
      (second : G122GeneratedComparisonSyntax Θ Y Z) :
      G122GeneratedComparisonSyntax Θ X Z
  | barAlpha (input : G122CellInput Θ) :
      G122GeneratedComparisonSyntax Θ (.direct input) (.viaBase input)
  | barAlphaInv (input : G122CellInput Θ) :
      G122GeneratedComparisonSyntax Θ (.viaBase input) (.direct input)
  | barBeta (input : G122CellInput Θ) :
      G122GeneratedComparisonSyntax Θ (.direct input) (.viaBase input)
  | barE (input : G122CellInput Θ) :
      G122GeneratedComparisonSyntax Θ (.direct input) (.direct input)
  | barD (input : G122CellInput Θ) :
      G122GeneratedComparisonSyntax Θ (.viaBase input) (.viaBase input)

namespace G122GeneratedComparisonSyntax

/-- Evaluate a finite comparison term to the independently defined complete
geometry morphism between the same generated endpoints. -/
noncomputable def evaluate {Θ : G122FamilyInput.{u, v}}
    {X Y : G122GeneratedGeometryObject Θ} :
    G122GeneratedComparisonSyntax Θ X Y →
      G122GeneratedGeometryObject.Hom Θ X Y
  | .identity X => G122GeneratedGeometryObject.id Θ X
  | .compose first second =>
      G122GeneratedGeometryObject.comp Θ first.evaluate second.evaluate
  | .barAlpha input => G122GeneratedGeometryObject.barAlpha Θ input
  | .barAlphaInv input =>
      (G122GeneratedGeometryObject.barAlphaIso Θ input).inv
  | .barBeta input => G122GeneratedGeometryObject.barBeta Θ input
  | .barE input => G122GeneratedGeometryObject.barE Θ input
  | .barD input => G122GeneratedGeometryObject.barD Θ input

/-- The number of constructor nodes in a finite comparison expression. -/
def size {Θ : G122FamilyInput.{u, v}}
    {X Y : G122GeneratedGeometryObject Θ} :
    G122GeneratedComparisonSyntax Θ X Y → Nat
  | .identity _ => 1
  | .compose first second => first.size + second.size + 1
  | .barAlpha _ => 1
  | .barAlphaInv _ => 1
  | .barBeta _ => 1
  | .barE _ => 1
  | .barD _ => 1

/-- Every comparison expression has a positive finite syntax-tree size. -/
theorem size_pos {Θ : G122FamilyInput.{u, v}}
    {X Y : G122GeneratedGeometryObject Θ}
    (term : G122GeneratedComparisonSyntax Θ X Y) : 0 < term.size := by
  induction term with
  | identity => simp [size]
  | compose first second firstPositive secondPositive =>
      simp only [size]
      omega
  | barAlpha => simp [size]
  | barAlphaInv => simp [size]
  | barBeta => simp [size]
  | barE => simp [size]
  | barD => simp [size]

/-- Evaluation of the identity constructor is the actual semantic identity. -/
@[simp] theorem evaluate_identity {Θ : G122FamilyInput.{u, v}}
    (X : G122GeneratedGeometryObject Θ) :
    evaluate (.identity X) = G122GeneratedGeometryObject.id Θ X :=
  rfl

/-- Evaluation preserves typed syntactic composition definitionally. -/
@[simp] theorem evaluate_compose {Θ : G122FamilyInput.{u, v}}
    {X Y Z : G122GeneratedGeometryObject Θ}
    (first : G122GeneratedComparisonSyntax Θ X Y)
    (second : G122GeneratedComparisonSyntax Θ Y Z) :
    evaluate (.compose first second) =
      G122GeneratedGeometryObject.comp Θ first.evaluate second.evaluate :=
  rfl

/-- Evaluation sends the `barAlpha` leaf to the actual five-factor
comparison constructed from the original input. -/
@[simp] theorem evaluate_barAlpha {Θ : G122FamilyInput.{u, v}}
    (input : G122CellInput Θ) :
    evaluate (.barAlpha input) =
      G122GeneratedGeometryObject.barAlpha Θ input :=
  rfl

/-- Evaluation sends the inverse-comparison leaf to the inverse constructed
from the original G-122 input. -/
@[simp] theorem evaluate_barAlphaInv {Θ : G122FamilyInput.{u, v}}
    (input : G122CellInput Θ) :
    evaluate (.barAlphaInv input) =
      (G122GeneratedGeometryObject.barAlphaIso Θ input).inv :=
  rfl

/-- The evaluated five-factor comparison followed by its source-constructed
inverse is the actual identity. -/
theorem evaluate_barAlpha_barAlphaInv {Θ : G122FamilyInput.{u, v}}
    (input : G122CellInput Θ) :
    evaluate (.compose (.barAlpha input) (.barAlphaInv input)) =
      evaluate (.identity (.direct input)) :=
  (G122GeneratedGeometryObject.barAlphaIso Θ input).hom_inv_id

/-- The evaluated source-constructed inverse followed by the five-factor
comparison is the actual identity. -/
theorem evaluate_barAlphaInv_barAlpha {Θ : G122FamilyInput.{u, v}}
    (input : G122CellInput Θ) :
    evaluate (.compose (.barAlphaInv input) (.barAlpha input)) =
      evaluate (.identity (.viaBase input)) :=
  (G122GeneratedGeometryObject.barAlphaIso Θ input).inv_hom_id

/-- Evaluation sends the `barBeta` leaf to the actual cochain-selected
comparison constructed from the original input. -/
@[simp] theorem evaluate_barBeta {Θ : G122FamilyInput.{u, v}}
    (input : G122CellInput Θ) :
    evaluate (.barBeta input) =
      G122GeneratedGeometryObject.barBeta Θ input :=
  rfl

/-- The evaluated cochain-selected comparison satisfies its actual
source-derived factorization through `barAlpha` and the target projector. -/
theorem evaluate_barBeta_factor {Θ : G122FamilyInput.{u, v}}
    (input : G122CellInput Θ) :
    evaluate (.barBeta input) =
      evaluate (.compose (.barAlpha input) (.barD input)) :=
  G122GeneratedGeometryObject.barBeta_factor Θ input

/-- The evaluated source-projector leaf is idempotent. -/
theorem evaluate_barE_idem {Θ : G122FamilyInput.{u, v}}
    (input : G122CellInput Θ) :
    evaluate (.compose (.barE input) (.barE input)) =
      evaluate (.barE input) :=
  G122GeneratedGeometryObject.barE_idem Θ input

/-- The evaluated target-projector leaf is idempotent. -/
theorem evaluate_barD_idem {Θ : G122FamilyInput.{u, v}}
    (input : G122CellInput Θ) :
    evaluate (.compose (.barD input) (.barD input)) =
      evaluate (.barD input) :=
  G122GeneratedGeometryObject.barD_idem Θ input

/-- Evaluation preserves the actual source-projector absorption of the
cochain-selected comparison. -/
theorem evaluate_barBeta_source_factorization
    {Θ : G122FamilyInput.{u, v}} (input : G122CellInput Θ) :
    evaluate (.compose (.barE input) (.barBeta input)) =
      evaluate (.barBeta input) :=
  G122GeneratedGeometryObject.barBeta_source_factorization Θ input

/-- Evaluation preserves the actual target-projector absorption of the
cochain-selected comparison. -/
theorem evaluate_barBeta_target_factorization
    {Θ : G122FamilyInput.{u, v}} (input : G122CellInput Θ) :
    evaluate (.compose (.barBeta input) (.barD input)) =
      evaluate (.barBeta input) :=
  G122GeneratedGeometryObject.barBeta_target_factorization Θ input

end G122GeneratedComparisonSyntax

end AAT.AG.RealizationReconstruction

#assert_standard_axioms_only AAT.AG.RealizationReconstruction
