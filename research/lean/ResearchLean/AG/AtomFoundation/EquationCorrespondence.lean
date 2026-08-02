import ResearchLean.AG.AtomFoundation.Transport

/-!
# Standalone equation correspondence for canonical Atom transport

This module exposes the equation-system component of `transportAlong` as a
package-level API.  The transport is generated solely from the source package
and exact doctrine morphism: no target equation system, index map, observable
equivalence, or equation certificate is supplied independently.
-/

namespace AAT.AG.AtomFoundation

universe u

/--
Canonical package-level equation-system transport generated solely from the
source package and exact doctrine morphism.
-/
def transportAlongEquationSystemExact {U : AtomCarrier.{u}}
    (P : AATCorePackage U) {E : ExtractionDoctrine U}
    (f : ExactDoctrineHom P.reading.doctrine E) :
    EquationSystemExactTransport
      P.algebra.equationSystem
      (transportAlong P f).algebra.equationSystem
      f.atomEquiv (transportArchitectureObject f.atomEquiv) :=
  transportCoreEquationSystemExact P.reading f

/-- The tautological upper hom uses exactly the standalone equation transport. -/
@[simp]
theorem transportAlongUpper_equationTransport_eq {U : AtomCarrier.{u}}
    (P : AATCorePackage U) {E : ExtractionDoctrine U}
    (f : ExactDoctrineHom P.reading.doctrine E) :
    (transportAlongUpper P f).equationTransport =
      transportAlongEquationSystemExact P f :=
  rfl

/-- Canonical package transport retains the source equation index itself. -/
@[simp]
theorem transportAlongEquationSystemExact_equationMap_heq {U : AtomCarrier.{u}}
    (P : AATCorePackage U) {E : ExtractionDoctrine U}
    (f : ExactDoctrineHom P.reading.doctrine E)
    (i : P.algebra.equationSystem.Index) :
    HEq ((transportAlongEquationSystemExact P f).equationMap i) i := by
  exact transportCoreEquationSystemExact_equationMap_heq P.reading f i

/-- Equation roles are unchanged by canonical package transport. -/
@[simp]
theorem transportAlong_equationRole_eq {U : AtomCarrier.{u}}
    (P : AATCorePackage U) {E : ExtractionDoctrine U}
    (f : ExactDoctrineHom P.reading.doctrine E)
    (i : P.algebra.equationSystem.Index) :
    (transportAlong P f).algebra.equationSystem.role
        ((transportAlongEquationSystemExact P f).equationMap i) =
      P.algebra.equationSystem.role i :=
  (transportAlongEquationSystemExact P f).role_eq i

/-- Observable-ring transport commutes with restriction along every context map. -/
theorem transportAlong_observable_naturality {U : AtomCarrier.{u}}
    (P : AATCorePackage U) {E : ExtractionDoctrine U}
    (f : ExactDoctrineHom P.reading.doctrine E)
    {W V : Site.ContextCategoryObject P.contextPreorder}
    (g : W ⟶ V) (x : P.algebra.equationSystem.Observable V) :
    (transportAlongEquationSystemExact P f).observableEquiv W
        (P.algebra.equationSystem.restrict g x) =
      (transportAlong P f).algebra.equationSystem.restrict
        ((transportAlongEquationSystemExact P f).contextFunctor.map g)
        ((transportAlongEquationSystemExact P f).observableEquiv V x) :=
  (transportAlongEquationSystemExact P f).observable_naturality g x

/-- Symbolic violation coordinates commute with canonical package transport. -/
theorem transportAlong_violationCoordinate_eq {U : AtomCarrier.{u}}
    (P : AATCorePackage U) {E : ExtractionDoctrine U}
    (f : ExactDoctrineHom P.reading.doctrine E)
    (W : Site.ContextCategoryObject P.contextPreorder)
    (i : P.algebra.equationSystem.Index) (atom : U.Atom) :
    (transportAlongEquationSystemExact P f).observableEquiv W
        (P.algebra.equationSystem.violationCoordinate W i atom) =
      (transportAlong P f).algebra.equationSystem.violationCoordinate
        ((transportAlongEquationSystemExact P f).contextFunctor.obj W)
        ((transportAlongEquationSystemExact P f).equationMap i)
        (f.atomEquiv atom) :=
  (transportAlongEquationSystemExact P f).violationCoordinate_eq W i atom

/-- Object-dependent residuals commute with canonical package transport. -/
theorem transportAlong_equationResidual_eq {U : AtomCarrier.{u}}
    (P : AATCorePackage U) {E : ExtractionDoctrine U}
    (f : ExactDoctrineHom P.reading.doctrine E)
    (W : Site.ContextCategoryObject P.contextPreorder)
    (A : ArchitectureObject U) (i : P.algebra.equationSystem.Index)
    (atom : U.Atom) :
    (transportAlongEquationSystemExact P f).observableEquiv W
        (P.algebra.equationSystem.equationResidual W A i atom) =
      (transportAlong P f).algebra.equationSystem.equationResidual
        ((transportAlongEquationSystemExact P f).contextFunctor.obj W)
        (transportArchitectureObject f.atomEquiv A)
        ((transportAlongEquationSystemExact P f).equationMap i)
        (f.atomEquiv atom) :=
  (transportAlongEquationSystemExact P f).equationResidual_eq W A i atom

/-- Detector syntax follows the same canonical equation-index correspondence. -/
theorem transportAlongEquationSystemExact_detectorCode_eq
    {U : AtomCarrier.{u}} (P : AATCorePackage U)
    {E : ExtractionDoctrine U}
    (f : ExactDoctrineHom P.reading.doctrine E)
    (i : P.algebra.equationSystem.Index) :
    (transportAlong P f).algebra.circuits.code
        ((transportAlongEquationSystemExact P f).equationMap i) =
      (P.algebra.circuits.code i).transport f.atomEquiv := by
  simpa only [transportAlongUpper_equationTransport_eq] using
    transportAlong_detectorCode_eq P f i

end AAT.AG.AtomFoundation

#assert_standard_axioms_only AAT.AG.AtomFoundation
