import ResearchLean.AG.RealizationReconstruction.MandatoryCEndpointPathQuotientObstruction
import Formal.Util.AssertStandardAxioms

/-!
# The currently declared closed primitive-role sum

This module combines every role actually declared in
`AATClosedFamilySignature` into one dependent tagged sum.  It then proves that
on the mandatory G-123(C) tagged-operation branch this entire current sum is
exactly the four-role `TaggedPrimitiveReference` alphabet used in Cycles
14--19: every currently declared context, Support, geometry-Axis, Observable,
context-restriction, coverage, overlap, diagnostic, signature, equation,
invariant, coordinate, and relation family has no constructor at that index.

This is a source-declaration audit, not final role exhaustion.  Among other
components, the fixed GOAL also requires complete-geometry map-side reading;
coefficient and transport;
and Atom/object/Law evaluation data not yet all declared by
`AATClosedFamilySignature`.  Consequently the equivalence below closes only
the possibility that an *already declared* role was omitted from the tagged
candidate; it does not prove that final `Sigma` has no additional legal role.

## Implementation notes

The sum is indexed by one parameter and one realization, so a reference cannot
silently change branch or owner.  Dependent endpoint, object, context, and axis
indices are retained by the corresponding constructors.  The tagged
equivalence is proved by eliminating impossible indexed constructors, rather
than assuming that their carrier types are empty through a certificate.
-/

namespace AAT.AG.RealizationReconstruction

/-- The disjoint sum of every primitive role currently present in the closed
family signature, at one fixed parameter and realization. -/
inductive ClosedPrimitiveReference
    (theta : ClosedFamilyParameter) (realization : FamilyRealization theta)
    where
  | atom (value : PrimitiveAtom theta realization)
  | source (value : PrimitiveSource theta realization)
  | object (value : PrimitiveObject theta realization)
  | operation {source target : PrimitiveObject theta realization}
      (value : PrimitiveOperation theta realization source target)
  | context {object : PrimitiveObject theta realization}
      (value : PrimitiveContext theta realization object)
  | support (value : PrimitiveSupport theta realization)
  | geometryAxis (value : PrimitiveGeometryAxis theta realization)
  | observable (value : PrimitiveObservable theta realization)
  | contextRestriction (value : PrimitiveContextRestriction theta realization)
  | coverageRequirements
      (value : PrimitiveCoverageRequirements theta realization)
  | overlapSelection (value : PrimitiveOverlapSelection theta realization)
  | diagnosticCell (value : PrimitiveDiagnosticCell theta realization)
  | signatureAxis (value : PrimitiveSignatureAxis theta realization)
  | signatureCoordinate {axis : PrimitiveSignatureAxis theta realization}
      (value : PrimitiveSignatureCoordinate theta realization axis)
  | equationIndex (value : PrimitiveEquationIndex theta realization)
  | invariantIndex (value : PrimitiveInvariantIndex theta realization)
  | coordinateIndex (value : PrimitiveCoordinateIndex theta realization)
  | relationIndex (value : PrimitiveRelationIndex theta realization)

/-- Forget the closed-sum wrapper on the tagged branch.  Indexed elimination
discharges every role that has no tagged constructor. -/
def closedTaggedPrimitiveReferenceToTagged :
    ClosedPrimitiveReference .taggedOperation .taggedOperation →
      TaggedPrimitiveReference
  | .atom (.taggedOperation value) => .atom value
  | .source (.taggedOperation value) => .source value
  | .object (.tagged value) => .object value
  | .operation (.tagged value) => .operation value
  | .context value => nomatch value
  | .support value => nomatch value
  | .geometryAxis value => nomatch value
  | .observable value => nomatch value
  | .contextRestriction value => nomatch value
  | .coverageRequirements value => nomatch value
  | .overlapSelection value => nomatch value
  | .diagnosticCell value => nomatch value
  | .signatureAxis value => nomatch value
  | .signatureCoordinate value => nomatch value
  | .equationIndex value => nomatch value
  | .invariantIndex value => nomatch value
  | .coordinateIndex value => nomatch value
  | .relationIndex value => nomatch value

/-- Include each of the four tagged roles into the complete currently declared
closed-role sum at the mandatory-C parameter. -/
def taggedPrimitiveReferenceToClosedTagged :
    TaggedPrimitiveReference →
      ClosedPrimitiveReference .taggedOperation .taggedOperation
  | .atom value => .atom (.taggedOperation value)
  | .source value => .source (.taggedOperation value)
  | .object value => .object (.tagged value)
  | .operation value => .operation (.tagged value)

/-- Reading a tagged reference after including it in the closed sum returns
the same exact role and payload. -/
@[simp] theorem closedTaggedPrimitiveReferenceToTagged_toClosedTagged
    (reference : TaggedPrimitiveReference) :
    closedTaggedPrimitiveReferenceToTagged
      (taggedPrimitiveReferenceToClosedTagged reference) = reference := by
  cases reference <;> rfl

/-- Including a closed tagged-branch reference after reading it returns the
same dependent constructor; impossible roles have already been eliminated. -/
@[simp] theorem taggedPrimitiveReferenceToClosedTagged_toTagged
    (reference : ClosedPrimitiveReference .taggedOperation .taggedOperation) :
    taggedPrimitiveReferenceToClosedTagged
      (closedTaggedPrimitiveReferenceToTagged reference) = reference := by
  cases reference with
  | atom value =>
      cases value
      rfl
  | source value =>
      cases value
      rfl
  | object value =>
      cases value
      rfl
  | operation value =>
      cases value
      rfl
  | context value => cases value
  | support value => cases value
  | geometryAxis value => cases value
  | observable value => cases value
  | contextRestriction value => cases value
  | coverageRequirements value => cases value
  | overlapSelection value => cases value
  | diagnosticCell value => cases value
  | signatureAxis value => cases value
  | signatureCoordinate value => cases value
  | equationIndex value => cases value
  | invariantIndex value => cases value
  | coordinateIndex value => cases value
  | relationIndex value => cases value

/-- On the mandatory G-123(C) branch, the complete currently declared
primitive-role sum is equivalent to the exact four-role alphabet used by the
endpoint-path quotient obstruction. -/
def closedTaggedPrimitiveReferenceEquiv :
    ClosedPrimitiveReference .taggedOperation .taggedOperation ≃
      TaggedPrimitiveReference where
  toFun := closedTaggedPrimitiveReferenceToTagged
  invFun := taggedPrimitiveReferenceToClosedTagged
  left_inv := taggedPrimitiveReferenceToClosedTagged_toTagged
  right_inv := closedTaggedPrimitiveReferenceToTagged_toClosedTagged

#assert_standard_axioms_only AAT.AG.RealizationReconstruction

end AAT.AG.RealizationReconstruction
