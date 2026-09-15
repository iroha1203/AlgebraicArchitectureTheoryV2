import ResearchLean.AG.RealizationReconstruction.G122GeneratedComparisonQuotient
import ResearchLean.AG.FullGeometryNormalization.ExactNormalizationNaturality
import ResearchLean.AG.FullGeometryNormalization.AmbientKernelGeometryLift
import ResearchLean.AG.RealizationComparisonIdempotents.NormalizationComparisonGroup
import Formal.Util.AssertStandardAxioms

/-!
# Source-generated ambient-kernel recipes for the fixed G-122 input

G-123(D) must recover the information erased by canonical normalization, not
only the normalized comparison.  This file adds the first nontrivial kernel
generators on the presentation side for the card-mandated finite axis-fold
input.  Their only primitive datum is which of the two generated endpoints is
used.  Evaluation constructs the endpoint admissibility from the original
southwest package and then invokes the existing ambient-kernel construction.

No constructor accepts an automorphism, complete geometry morphism,
admissibility certificate, or element of a comparison group.  Thus the
nonidentity involutions below are finite recipes derived from the fixed input,
not renamed semantic answers.

## Implementation notes

This is deliberately a fixed-example extension of the comparison syntax.  It
does not claim that the Cycle 55 quotient already represents every element of
either G-122 comparison group.  In particular the comparison-preservation
equations relating the two endpoint involutions and `barAlpha`/`barBeta`, the
restriction homomorphism, its section, and all lift fibers remain subsequent
obligations.
-/

namespace AAT.AG.RealizationReconstruction

open CategoryTheory DoctrineFiberProduct GeometryTransport TransportCoherence
open FullGeometryNormalization
open RealizationComparisonIdempotents

local instance finiteAxisFoldAmbientKernelAtomDecidableEq :
    DecidableEq FiniteModel.carrier.Atom := by
  change DecidableEq FiniteModel.FiniteAtom
  infer_instance

/-! ## Admissibility generated from the fixed original input -/

/-- The direct endpoint is admissible because the original finite support
package is admissible and exact pull/push transport preserves admissibility. -/
theorem finiteAxisFoldDirectEndpointAdmissible :
    CanonicalObjectNormalizationAdmissible
      ((G122GeneratedGeometryObject.direct
        finiteAxisFoldG122CellInput).package
          finiteAxisFoldG122FamilyInput).core := by
  exact authoredExactDirectGeometryAt_admissible
    finiteAxisFoldBCDatumSquare
    (Discrete.mk DoubleDiamondTwoCell.second)
    Int
    (finiteAxisFoldFixedCoefficientGeometryFamily
      (Discrete.mk DoubleDiamondTwoCell.second))
    finiteCanonicalObjectNormalization_admissible

/-- The via-base endpoint is admissible by the independently constructed
exact push/pull transport of the same original finite support proof. -/
theorem finiteAxisFoldViaBaseEndpointAdmissible :
    CanonicalObjectNormalizationAdmissible
      ((G122GeneratedGeometryObject.viaBase
        finiteAxisFoldG122CellInput).package
          finiteAxisFoldG122FamilyInput).core := by
  exact authoredExactViaBaseGeometryAt_admissible
    finiteAxisFoldBCDatumSquare
    (Discrete.mk DoubleDiamondTwoCell.second)
    Int
    (finiteAxisFoldFixedCoefficientGeometryFamily
      (Discrete.mk DoubleDiamondTwoCell.second))
    finiteCanonicalObjectNormalization_admissible

/-! ## Finite source recipes and evaluation -/

/-- The two endpoint-indexed ambient-kernel generators required by the fixed
finite axis-fold comparison.  The code carries no completed semantic map. -/
inductive FiniteAxisFoldAmbientKernelCode
  | direct
  | viaBase
  deriving DecidableEq, Fintype

namespace FiniteAxisFoldAmbientKernelCode

/-- The exact generated endpoint selected by a kernel recipe. -/
noncomputable def endpoint : FiniteAxisFoldAmbientKernelCode →
    G122GeneratedGeometryObject finiteAxisFoldG122FamilyInput
  | .direct => .direct finiteAxisFoldG122CellInput
  | .viaBase => .viaBase finiteAxisFoldG122CellInput

/-- The chosen endpoint as an object of the independently defined admissible
complete-geometry category.  Its property is constructed, not accepted by the
recipe. -/
noncomputable def admissibleEndpoint
    (code : FiniteAxisFoldAmbientKernelCode) :
    CanonicalNormalizationAdmissibleGeometry.{0, 0}
      finiteAxisFoldG122FamilyInput.Carrier :=
  match code with
  | .direct =>
      ⟨direct.endpoint.package finiteAxisFoldG122FamilyInput,
        finiteAxisFoldDirectEndpointAdmissible⟩
  | .viaBase =>
      ⟨viaBase.endpoint.package finiteAxisFoldG122FamilyInput,
        finiteAxisFoldViaBaseEndpointAdmissible⟩

/-- Evaluate a code by constructing the ambient-kernel morphism from the fixed
source input and its derived endpoint admissibility. -/
noncomputable def evaluate (code : FiniteAxisFoldAmbientKernelCode) :
    G122GeneratedGeometryObject.Hom finiteAxisFoldG122FamilyInput
      code.endpoint code.endpoint :=
  match code with
  | .direct => ambientKernelGeometry _ finiteAxisFoldDirectEndpointAdmissible
  | .viaBase => ambientKernelGeometry _ finiteAxisFoldViaBaseEndpointAdmissible

/-- Each finite recipe evaluates to the hom of the corresponding constructed
ambient-kernel automorphism. -/
noncomputable def evaluateAut (code : FiniteAxisFoldAmbientKernelCode) :
    Aut code.endpoint :=
  match code with
  | .direct =>
      { hom := ambientKernelGeometry _ finiteAxisFoldDirectEndpointAdmissible
        inv := ambientKernelGeometry _ finiteAxisFoldDirectEndpointAdmissible
        hom_inv_id := ambientKernelGeometry_comp_self _
          finiteAxisFoldDirectEndpointAdmissible
        inv_hom_id := ambientKernelGeometry_comp_self _
          finiteAxisFoldDirectEndpointAdmissible }
  | .viaBase =>
      { hom := ambientKernelGeometry _ finiteAxisFoldViaBaseEndpointAdmissible
        inv := ambientKernelGeometry _ finiteAxisFoldViaBaseEndpointAdmissible
        hom_inv_id := ambientKernelGeometry_comp_self _
          finiteAxisFoldViaBaseEndpointAdmissible
        inv_hom_id := ambientKernelGeometry_comp_self _
          finiteAxisFoldViaBaseEndpointAdmissible }

@[simp] theorem evaluateAut_hom
    (code : FiniteAxisFoldAmbientKernelCode) :
    code.evaluateAut.hom = code.evaluate := by
  cases code <;> rfl

/-- Both fixed endpoint recipes evaluate to genuinely nonidentity complete
geometry morphisms. -/
theorem evaluate_ne_identity (code : FiniteAxisFoldAmbientKernelCode) :
    code.evaluate ≠
      G122GeneratedGeometryObject.id finiteAxisFoldG122FamilyInput
        code.endpoint := by
  cases code with
  | direct =>
      exact ambientKernelGeometry_ne_id _
        finiteAxisFoldDirectEndpointAdmissible
  | viaBase =>
      exact ambientKernelGeometry_ne_id _
        finiteAxisFoldViaBaseEndpointAdmissible

/-- Both generated kernel elements are involutions before normalization. -/
theorem evaluate_comp_self (code : FiniteAxisFoldAmbientKernelCode) :
    G122GeneratedGeometryObject.comp finiteAxisFoldG122FamilyInput
        code.evaluate code.evaluate =
      G122GeneratedGeometryObject.id finiteAxisFoldG122FamilyInput
        code.endpoint := by
  cases code with
  | direct =>
      exact ambientKernelGeometry_comp_self _
        finiteAxisFoldDirectEndpointAdmissible
  | viaBase =>
      exact ambientKernelGeometry_comp_self _
        finiteAxisFoldViaBaseEndpointAdmissible

/-- Canonical normalization erases each nonidentity endpoint recipe on the
right.  This is the fixed ambient-kernel information-loss equation. -/
theorem normalization_comp_evaluate (code : FiniteAxisFoldAmbientKernelCode) :
    canonicalGeometryNormalization
          (code.endpoint.package finiteAxisFoldG122FamilyInput)
          (match code with
            | .direct => finiteAxisFoldDirectEndpointAdmissible
            | .viaBase => finiteAxisFoldViaBaseEndpointAdmissible) ≫
        code.evaluate =
      canonicalGeometryNormalization
        (code.endpoint.package finiteAxisFoldG122FamilyInput)
        (match code with
          | .direct => finiteAxisFoldDirectEndpointAdmissible
          | .viaBase => finiteAxisFoldViaBaseEndpointAdmissible) := by
  cases code with
  | direct =>
      exact canonicalGeometryNormalization_comp_ambientKernelGeometry _ _
  | viaBase =>
      exact canonicalGeometryNormalization_comp_ambientKernelGeometry _ _

/-- Canonical normalization also erases each nonidentity endpoint recipe on
the left, keeping the two-sided kernel behavior distinct from merely observing
a normalized equality. -/
theorem evaluate_comp_normalization (code : FiniteAxisFoldAmbientKernelCode) :
    code.evaluate ≫
        canonicalGeometryNormalization
          (code.endpoint.package finiteAxisFoldG122FamilyInput)
          (match code with
            | .direct => finiteAxisFoldDirectEndpointAdmissible
            | .viaBase => finiteAxisFoldViaBaseEndpointAdmissible) =
      canonicalGeometryNormalization
        (code.endpoint.package finiteAxisFoldG122FamilyInput)
        (match code with
          | .direct => finiteAxisFoldDirectEndpointAdmissible
          | .viaBase => finiteAxisFoldViaBaseEndpointAdmissible) := by
  cases code with
  | direct =>
      exact ambientKernelGeometry_comp_canonicalGeometryNormalization _ _
  | viaBase =>
      exact ambientKernelGeometry_comp_canonicalGeometryNormalization _ _

/-- Positive instance: the direct code yields a nontrivial automorphism. -/
theorem direct_evaluateAut_ne_one :
    (direct.evaluateAut : Aut direct.endpoint) ≠ 1 :=
  fun equality => direct.evaluate_ne_identity
    (congrArg (fun automorphism : Aut direct.endpoint => automorphism.hom)
      equality)

/-- The same source recipe gives an automorphism in the admissible-geometry
category on which complete normalization is functorial. -/
noncomputable def admissibleEvaluateAut
    (code : FiniteAxisFoldAmbientKernelCode) :
    Aut code.admissibleEndpoint :=
  ambientKernelAdmissibleGeometryAut code.admissibleEndpoint

/-- The fixed recipe is nontrivial before normalization in the exact category
used to define the G-122 normalization homomorphism. -/
theorem admissibleEvaluateAut_ne_one
    (code : FiniteAxisFoldAmbientKernelCode) :
    code.admissibleEvaluateAut ≠ 1 :=
  ambientKernelAdmissibleGeometryAut_ne_one code.admissibleEndpoint

/-- Complete normalization maps every displayed fixed endpoint generator to
the identity automorphism. -/
theorem normalization_map_admissibleEvaluateAut
    (code : FiniteAxisFoldAmbientKernelCode) :
    (geometryNormalizationFunctor.{0, 0}
      finiteAxisFoldG122FamilyInput.Carrier).mapIso
        code.admissibleEvaluateAut = Iso.refl _ :=
  geometryNormalizationFunctor_map_ambientKernelAdmissibleGeometryAut
    code.admissibleEndpoint

/-- Hence each displayed nonidentity generator is an actual member of the
ambient observation kernel, expressed as the kernel of the endpoint
automorphism homomorphism rather than inferred from normalized data alone. -/
theorem admissibleEvaluateAut_mem_normalizationKernel
    (code : FiniteAxisFoldAmbientKernelCode) :
    code.admissibleEvaluateAut ∈ MonoidHom.ker
      (functorAutomorphismHom
        (geometryNormalizationFunctor.{0, 0}
          finiteAxisFoldG122FamilyInput.Carrier)
        code.admissibleEndpoint) := by
  change (geometryNormalizationFunctor.{0, 0}
    finiteAxisFoldG122FamilyInput.Carrier).mapIso
      code.admissibleEvaluateAut = Iso.refl _
  exact code.normalization_map_admissibleEvaluateAut

/-- Negative control: neither fixed kernel recipe evaluates to identity. -/
theorem no_code_evaluates_to_identity :
    ¬ ∃ code : FiniteAxisFoldAmbientKernelCode,
      code.evaluate =
        G122GeneratedGeometryObject.id finiteAxisFoldG122FamilyInput
          code.endpoint := by
  rintro ⟨code, equality⟩
  exact code.evaluate_ne_identity equality

end FiniteAxisFoldAmbientKernelCode

end AAT.AG.RealizationReconstruction

#assert_standard_axioms_only AAT.AG.RealizationReconstruction
