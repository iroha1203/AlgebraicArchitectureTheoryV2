import Formal.AG.Site.Basic
import Formal.AG.Site.ContextCategory

namespace AAT.AG
namespace Site

universe u

/--
II.定義6.1: a coverage family `{ W_i -> W }` in `ArchCtx(A)`.

Each patch is a readable local context of the selected base context. The
underlying morphism data is still supplied by the chosen context preorder; this
definition does not generate new Atom data or infer additional observations.
-/
structure CoverageFamily {U : AtomCarrier.{u}} {A : ArchitectureObject U}
    (C : ContextPreorderCategory A) where
  base : ArchCtx A
  Index : Type u
  patch : Index -> ArchCtx A
  inclusion : ∀ i : Index, C.Hom (patch i) base

namespace CoverageFamily

/-- II.定義6.1: the readable morphism represented by a patch inclusion. -/
def inclusionMorphism {U : AtomCarrier.{u}} {A : ArchitectureObject U}
    {C : ContextPreorderCategory A} (F : CoverageFamily C) (i : F.Index) :
    ContextMorphism (F.patch i) F.base :=
  C.morphism (F.inclusion i)

/-- II.定義6.1: each patch inclusion is a readable restriction. -/
theorem inclusion_isRestriction {U : AtomCarrier.{u}} {A : ArchitectureObject U}
    {C : ContextPreorderCategory A} (F : CoverageFamily C) (i : F.Index) :
    (F.inclusionMorphism i).IsRestriction :=
  C.morphism_isRestriction (F.inclusion i)

/-- II.定義7.1: readable patch inclusions do not generate atoms. -/
theorem inclusion_nonGenerating {U : AtomCarrier.{u}} {A : ArchitectureObject U}
    {C : ContextPreorderCategory A} (F : CoverageFamily C) (i : F.Index) :
    SupportMapNonGenerating (F.patch i) F.base
      (F.inclusionMorphism i).supportMap :=
  ContextMorphism.nonGenerating_of_restriction (F.inclusion_isRestriction i)

end CoverageFamily

/--
II.定義7.1 前半: selected requirements read by admissible covers.

Required equation coordinates are indexed by the required-role subtype of the
selected architectural equation system. Selected symbolic violation witnesses
use the full equation-index/Atom coordinate type. Visibility predicates remain
separate from the context data.
-/
structure CoverageRequirements {U : AtomCarrier.{u}} (A : ArchitectureObject U)
    {C : ContextPreorderCategory A} (E : ArchitecturalEquationSystem C)
    (Sig : ArchitectureSignature U) where
  requiredSupport : U.Atom -> Prop
  requiredEquationCoordinate : E.RequiredCoordinate -> Prop
  selectedViolationWitness : E.Coordinate -> Prop
  requiredAxis : Sig.Axis -> Prop
  supportVisibleOn : ArchCtx A -> U.Atom -> Prop
  equationCoordinateVisibleOn : ArchCtx A -> E.RequiredCoordinate -> Prop
  violationWitnessVisibleOn : ArchCtx A -> E.Coordinate -> Prop
  axisReadableOn : ArchCtx A -> Sig.Axis -> Prop
  boundaryVisibleOn : ArchCtx A -> ArchCtx A -> Prop

/--
II.定義7.1 前半: admissible cover conditions for a coverage family.

The six coverage fields are the selected Atom, required equation-coordinate,
symbolic violation-witness, signature-axis, overlap, and non-generation
clauses of the generated AAT coverage.
-/
structure AdmissibleCover {U : AtomCarrier.{u}} {A : ArchitectureObject U}
    {C : ContextPreorderCategory A} {E : ArchitecturalEquationSystem C}
    {Sig : ArchitectureSignature U} (R : CoverageRequirements A E Sig)
    (P : ContextOverlapPullback C) (F : CoverageFamily C) : Prop where
  atomSupportCoverage :
    ∀ atom : U.Atom, R.requiredSupport atom ->
      ∃ i : F.Index, R.supportVisibleOn (F.patch i) atom
  equationCoordinateCoverage :
    ∀ coordinate : E.RequiredCoordinate, R.requiredEquationCoordinate coordinate ->
      (∃ i : F.Index, R.equationCoordinateVisibleOn (F.patch i) coordinate) ∨
        ∃ i j : F.Index,
          R.equationCoordinateVisibleOn
            (P.overlap F.base (F.patch i) (F.patch j)) coordinate
  violationWitnessCoverage :
    ∀ witness : E.Coordinate, R.selectedViolationWitness witness ->
      (∃ i : F.Index, R.violationWitnessVisibleOn (F.patch i) witness) ∨
        ∃ i j : F.Index,
          R.violationWitnessVisibleOn
            (P.overlap F.base (F.patch i) (F.patch j)) witness
  signatureAxisCoverage :
    ∀ axis : Sig.Axis, R.requiredAxis axis ->
      ∃ i : F.Index, R.axisReadableOn (F.patch i) axis
  boundaryCoverage :
    ∀ i j : F.Index,
      R.boundaryVisibleOn (P.overlap F.base (F.patch i) (F.patch j)) F.base
  nonGeneration :
    ∀ i : F.Index, SupportMapNonGenerating (F.patch i) F.base
      (F.inclusionMorphism i).supportMap

namespace AdmissibleCover

/-- II.定義7.1: admissible covers expose required Atom support on patches. -/
theorem support {U : AtomCarrier.{u}} {A : ArchitectureObject U}
    {C : ContextPreorderCategory A} {E : ArchitecturalEquationSystem C}
    {Sig : ArchitectureSignature U} {R : CoverageRequirements A E Sig}
    {P : ContextOverlapPullback C} {F : CoverageFamily C} (h : AdmissibleCover R P F)
    {atom : U.Atom} (hreq : R.requiredSupport atom) :
    ∃ i : F.Index, R.supportVisibleOn (F.patch i) atom :=
  h.atomSupportCoverage atom hreq

/-- II.定義7.1: admissible covers expose required equation coordinates. -/
theorem equationCoordinate {U : AtomCarrier.{u}} {A : ArchitectureObject U}
    {C : ContextPreorderCategory A} {E : ArchitecturalEquationSystem C}
    {Sig : ArchitectureSignature U} {R : CoverageRequirements A E Sig}
    {P : ContextOverlapPullback C} {F : CoverageFamily C} (h : AdmissibleCover R P F)
    {coordinate : E.RequiredCoordinate}
    (hreq : R.requiredEquationCoordinate coordinate) :
    (∃ i : F.Index, R.equationCoordinateVisibleOn (F.patch i) coordinate) ∨
      ∃ i j : F.Index,
        R.equationCoordinateVisibleOn
          (P.overlap F.base (F.patch i) (F.patch j)) coordinate :=
  h.equationCoordinateCoverage coordinate hreq

/-- II.定義7.1: admissible covers expose selected symbolic violation witnesses. -/
theorem violationWitness {U : AtomCarrier.{u}} {A : ArchitectureObject U}
    {C : ContextPreorderCategory A} {E : ArchitecturalEquationSystem C}
    {Sig : ArchitectureSignature U} {R : CoverageRequirements A E Sig}
    {P : ContextOverlapPullback C} {F : CoverageFamily C} (h : AdmissibleCover R P F)
    {witness : E.Coordinate} (hreq : R.selectedViolationWitness witness) :
    (∃ i : F.Index, R.violationWitnessVisibleOn (F.patch i) witness) ∨
      ∃ i j : F.Index,
        R.violationWitnessVisibleOn
          (P.overlap F.base (F.patch i) (F.patch j)) witness :=
  h.violationWitnessCoverage witness hreq

/-- II.定義7.1: admissible covers expose required signature axes on patches. -/
theorem axis {U : AtomCarrier.{u}} {A : ArchitectureObject U}
    {C : ContextPreorderCategory A} {E : ArchitecturalEquationSystem C}
    {Sig : ArchitectureSignature U} {R : CoverageRequirements A E Sig}
    {P : ContextOverlapPullback C} {F : CoverageFamily C} (h : AdmissibleCover R P F)
    {axis : Sig.Axis} (hreq : R.requiredAxis axis) :
    ∃ i : F.Index, R.axisReadableOn (F.patch i) axis :=
  h.signatureAxisCoverage axis hreq

/-- II.定義7.1: admissible covers expose boundary readings on overlaps. -/
theorem boundary {U : AtomCarrier.{u}} {A : ArchitectureObject U}
    {C : ContextPreorderCategory A} {E : ArchitecturalEquationSystem C}
    {Sig : ArchitectureSignature U} {R : CoverageRequirements A E Sig}
    {P : ContextOverlapPullback C} {F : CoverageFamily C} (h : AdmissibleCover R P F)
    (i j : F.Index) :
    R.boundaryVisibleOn (P.overlap F.base (F.patch i) (F.patch j)) F.base :=
  h.boundaryCoverage i j

/-- II.定義7.1: admissible covers do not generate atoms along inclusions. -/
theorem nonGenerating {U : AtomCarrier.{u}} {A : ArchitectureObject U}
    {C : ContextPreorderCategory A} {E : ArchitecturalEquationSystem C}
    {Sig : ArchitectureSignature U} {R : CoverageRequirements A E Sig}
    {P : ContextOverlapPullback C} {F : CoverageFamily C} (h : AdmissibleCover R P F)
    (i : F.Index) :
    SupportMapNonGenerating (F.patch i) F.base
      (F.inclusionMorphism i).supportMap :=
  h.nonGeneration i

/--
II.定義7.1: any coverage family whose non-generation clause is inherited from
the context preorder satisfies the fifth admissibility condition.
-/
theorem nonGenerating_from_inclusions {U : AtomCarrier.{u}}
    {A : ArchitectureObject U} {C : ContextPreorderCategory A}
    {F : CoverageFamily C} :
    (∀ i : F.Index, SupportMapNonGenerating (F.patch i) F.base
      (F.inclusionMorphism i).supportMap) :=
  F.inclusion_nonGenerating

end AdmissibleCover

end Site
end AAT.AG
