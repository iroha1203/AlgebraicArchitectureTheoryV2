import Formal.SHIGURE.Part1.DeclarationContexts
import Formal.SHIGURE.Part1.StructureMaps
import Mathlib.Algebra.Algebra.Defs

/-! # Coefficients chosen by a reading

Definition 1.11 records the coefficient ring and the realization scheme of
Definition 4.1. A scheme specifies its available realizations and the rules
for native inputs, primitive structure, Law interpretation, and coefficient
change. The fields specify the rules of a chosen scheme. Compatibility of an
actual reading comparison is checked on its selected realizations and inputs.

## Implementation notes

A coefficient algebra is a commutative ring with a unital map from the base
ring. To compare two choices, first apply the source scheme's coefficient
change along the declared ring map. Then transport states from that changed
realization to the selected target realization, which can use another scheme
or signature. These two steps must induce the state map of Equation (1.12).
-/

universe u

namespace SHIGURE

/-- A small commutative coefficient ring, with its named ring structure. -/
structure CoefficientRing where
  /-- The underlying scalar type. -/
  Carrier : Type u
  /-- The commutative ring of scalars. -/
  ring : CommRing Carrier

/-- Unital scalar maps between the named ring structures. -/
abbrev CoefficientRing.Hom (source target : CoefficientRing.{u}) :=
  letI := source.ring
  letI := target.ring
  source.Carrier →+* target.Carrier

/-- A commutative algebra over the chosen base ring, in its ring-map presentation. -/
structure CoefficientAlgebra (base : CoefficientRing.{u}) where
  /-- The coefficient ring at which to realize the scheme. -/
  scalars : CoefficientRing.{u}
  /-- The algebra structure map from the base ring. -/
  fromBase : base.Hom scalars

/-- Use the selected coefficient algebra through mathlib's algebra interface. -/
abbrev CoefficientAlgebra.toAlgebra {base : CoefficientRing.{u}} (R : CoefficientAlgebra base) :
    letI := base.ring
    letI := R.scalars.ring
    Algebra base.Carrier R.scalars.Carrier := by
  letI := base.ring
  letI := R.scalars.ring
  exact R.fromBase.toAlgebra

/-- Regard the target ring of a scalar map as an algebra over the same base. -/
def CoefficientAlgebra.extend {base : CoefficientRing.{u}} (R : CoefficientAlgebra base)
    {target : CoefficientRing.{u}} (f : R.scalars.Hom target) : CoefficientAlgebra base :=
  ⟨target, f.comp R.fromBase⟩

/-- The realization rules on a selected declaration context, indexed by the coefficients. -/
structure CoefficientScheme {P : PrimitivePresentation.{u}} (U : DeclarationContext P)
    (base : CoefficientRing.{u}) where
  /-- The available objects at each coefficient algebra. -/
  Realization : CoefficientAlgebra base → Type u
  /-- The carriers of designated points and the primitive maps they interpret. -/
  structureOf (R : CoefficientAlgebra base) : Realization R → Structure P.signature
  /-- The admissible structural morphisms at each coefficient algebra. -/
  Morphism (R : CoefficientAlgebra base) : Realization R → Realization R → Type u
  /-- The action of each admissible morphism on the designated points. -/
  mapPoints {R : CoefficientAlgebra base} {a b : Realization R} (f : Morphism R a b) :
    ∀ s, (structureOf R a).carrier s → (structureOf R b).carrier s
  /-- Admissible native input data for the realization scheme. -/
  Native : Type u
  /-- The native structure whose points are used in the realization rule. -/
  nativeStructure : Native → Structure P.signature
  /-- Construct a realization from the native input. -/
  realizeNative (R : CoefficientAlgebra base) : Native → Realization R
  /-- The correspondence between native and realized points. -/
  nativePoints (R : CoefficientAlgebra base) (a : Native) :
    ∀ s, (nativeStructure a).carrier s → (structureOf R (realizeNative R a)).carrier s
  /-- The interpretation rule for each retained Law. -/
  lawHolds (R : CoefficientAlgebra base) (a : Realization R)
    (name : P.laws.LawName) : Declaration.law name ∈ U.declarations → Prop
  /-- Change the realized carriers and primitive operations along the given scalar map. -/
  change {R : CoefficientAlgebra base} {target : CoefficientRing.{u}}
    (f : R.scalars.Hom target) : Realization R → Realization (R.extend f)
  /-- The map of designated states that this change induces. -/
  changePoints {R : CoefficientAlgebra base} {target : CoefficientRing.{u}}
    (f : R.scalars.Hom target) (a : Realization R) :
    ∀ s, (structureOf R a).carrier s → (structureOf (R.extend f) (change f a)).carrier s

/-- A choice of coefficients, scheme and evaluation at the actual reading structure. -/
structure CoefficientReading {P : PrimitivePresentation.{u}} (U : DeclarationContext P)
    (A : Structure P.signature) (Γ : List P.signature.SortType) where
  /-- The base ring of the chosen scheme. -/
  base : CoefficientRing.{u}
  /-- The selected coefficient algebra. -/
  algebra : CoefficientAlgebra base
  /-- The chosen realization scheme for the selected declarations. -/
  scheme : CoefficientScheme U base
  /-- The chosen realization belongs to this scheme at the selected coefficients. -/
  realization : scheme.Realization algebra
  /-- The designated points and primitive operations give the actual reading structure. -/
  realizes : scheme.structureOf algebra realization = A
  /-- Evaluate the reading on the designated states of the realizations in this scheme. -/
  evaluateOn (R : CoefficientAlgebra base) (a : scheme.Realization R) :
    Assignment (scheme.structureOf R a).carrier Γ → R.scalars.Carrier

namespace CoefficientReading

variable {P Q : PrimitivePresentation.{u}} {U : DeclarationContext P} {V : DeclarationContext Q}
  {A : Structure P.signature} {B : Structure Q.signature}
  {Γ : List P.signature.SortType} {Δ : List Q.signature.SortType}

/-- The actual coefficient ring of the reading. -/
abbrev ring (reading : CoefficientReading U A Γ) : CoefficientRing.{u} :=
  reading.algebra.scalars

/-- Evaluate the chosen realization at the supplied state of the reading. -/
def evaluate (reading : CoefficientReading U A Γ) (e : Assignment A.carrier Γ) :
    reading.ring.Carrier :=
  reading.evaluateOn reading.algebra reading.realization (reading.realizes.symm ▸ e)

/-- The changed structure comes from the selected realization by the scheme's rule. -/
def changedStructure (reading : CoefficientReading U A Γ) {target : CoefficientRing.{u}}
    (f : reading.ring.Hom target) : Structure P.signature :=
  reading.scheme.structureOf (reading.algebra.extend f) (reading.scheme.change f reading.realization)

/-- Transport the selected state's coordinates by the scheme's coefficient change. -/
def changedState (reading : CoefficientReading U A Γ) {target : CoefficientRing.{u}}
    (f : reading.ring.Hom target) (e : Assignment A.carrier Γ) :
    Assignment (reading.changedStructure f).carrier Γ :=
  (reading.realizes.symm ▸ e : Assignment (reading.scheme.structureOf _ _).carrier Γ).map
    (reading.scheme.changePoints f reading.realization)

/-- Evaluate on the actual realization and state produced by the coefficient-change rule. -/
def changedEvaluation (reading : CoefficientReading U A Γ) {target : CoefficientRing.{u}}
    (f : reading.ring.Hom target) (e : Assignment A.carrier Γ) : target.Carrier :=
  reading.evaluateOn (reading.algebra.extend f) (reading.scheme.change f reading.realization)
    (reading.changedState f e)

/-- Compare coefficient evaluation along the specified state map between two readings. -/
structure Change (source : CoefficientReading U A Γ) (target : CoefficientReading V B Δ)
    (states : Assignment A.carrier Γ → Assignment B.carrier Δ) where
  /-- The unital map on coefficients. -/
  coefficients : source.ring.Hom target.ring
  /-- Continue from the scalar-changed source realization to the selected target states. -/
  toTarget : Assignment (source.changedStructure coefficients).carrier Γ → Assignment B.carrier Δ
  /-- These two steps on states give exactly the state map of the comparison. -/
  state_commutes (e : Assignment A.carrier Γ) :
    toTarget (source.changedState coefficients e) = states e
  /-- The source scheme's change of coefficients transports the coefficient evaluation. -/
  change_commutes (e : Assignment A.carrier Γ) :
    source.changedEvaluation coefficients e = coefficients (source.evaluate e)
  /-- Transport from the changed realization agrees with the chosen target evaluation. -/
  target_commutes (e : Assignment A.carrier Γ) :
    target.evaluate (toTarget (source.changedState coefficients e)) =
      source.changedEvaluation coefficients e

/-- The chosen evaluations commute on the actual states of the comparison. -/
theorem Change.evaluate_commutes {source : CoefficientReading U A Γ} {target : CoefficientReading V B Δ}
    {states : Assignment A.carrier Γ → Assignment B.carrier Δ} (change : Change source target states)
    (e : Assignment A.carrier Γ) : target.evaluate (states e) = change.coefficients (source.evaluate e) :=
  (congrArg target.evaluate (change.state_commutes e)).symm.trans
    ((change.target_commutes e).trans (change.change_commutes e))

end CoefficientReading

end SHIGURE
