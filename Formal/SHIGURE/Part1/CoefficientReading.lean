import Formal.SHIGURE.Part1.RestrictedEvaluation
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
ring. A comparison with different coefficients tests the selected evaluations
along the scalar map and the state map of Equation (1.12). When the states
are transported using a scheme's own scalar-change rule, that rule supplies
an intermediate realization and yields the comparison by composition.
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
  structureOf (R : CoefficientAlgebra base) : Realization R → RestrictedStructure U
  /-- The admissible structural morphisms at each coefficient algebra. -/
  Morphism (R : CoefficientAlgebra base) : Realization R → Realization R → Type u
  /-- The action of each admissible morphism on the designated points. -/
  mapPoints {R : CoefficientAlgebra base} {a b : Realization R} (f : Morphism R a b) :
    RestrictedStructure.PointMap (structureOf R a) (structureOf R b)
  /-- The point map of an admissible morphism preserves the retained primitive data. -/
  mapPoints_preserves {R : CoefficientAlgebra base} {a b : Realization R} (f : Morphism R a b) :
    (structureOf R a).Preserves (structureOf R b) (mapPoints f)
  /-- Admissible native input data for the realization scheme. -/
  Native : Type u
  /-- The native structure whose points are used in the realization rule. -/
  nativeStructure : Native → RestrictedStructure U
  /-- Construct a realization from the native input. -/
  realizeNative (R : CoefficientAlgebra base) : Native → Realization R
  /-- The correspondence between native and realized points. -/
  nativePoints (R : CoefficientAlgebra base) (a : Native) :
    RestrictedStructure.PointMap (nativeStructure a) (structureOf R (realizeNative R a))
  /-- The interpretation rule for each retained Law. -/
  interpretLaw (R : CoefficientAlgebra base) (a : Realization R)
    (law : Law P.signature) : Declaration.lawBody (P := P) law ⊆ U.declarations → Prop
  /-- Change the realized carriers and primitive operations along the given scalar map. -/
  change {R : CoefficientAlgebra base} {target : CoefficientRing.{u}}
    (f : R.scalars.Hom target) : Realization R → Realization (R.extend f)
  /-- The map of designated states that this change induces. -/
  changePoints {R : CoefficientAlgebra base} {target : CoefficientRing.{u}}
    (f : R.scalars.Hom target) (a : Realization R) :
    RestrictedStructure.PointMap (structureOf R a) (structureOf (R.extend f) (change f a))

/-- Interpret a selected declaration by its written Law in the scheme. -/
def CoefficientScheme.holdsLaw {P : PrimitivePresentation.{u}} {U : DeclarationContext P}
    {base : CoefficientRing.{u}} (scheme : CoefficientScheme U base) (R : CoefficientAlgebra base)
    (realization : scheme.Realization R) (name : P.laws.LawName)
    (kept : Declaration.law name ∈ U.declarations) : Prop :=
  scheme.interpretLaw R realization (P.laws.statement name) (fun _ hd => U.closed kept (Or.inl hd))

/-- A realized model satisfies each retained required Law in its own scheme. -/
def CoefficientScheme.IsModel {P : PrimitivePresentation.{u}} {U : DeclarationContext P}
    {base : CoefficientRing.{u}} (scheme : CoefficientScheme U base) (R : CoefficientAlgebra base)
    (realization : scheme.Realization R) : Prop :=
  ∀ name : P.theory.LawName, ∀ kept : Declaration.law name.val ∈ U.declarations,
    scheme.holdsLaw R realization name.val kept

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
  /-- The positions used for coefficient evaluation. -/
  context : List P.signature.SortType
  /-- Coefficient evaluation uses only retained sort carriers. -/
  supported : Declaration.sorts (P := P) context ⊆ U.declarations
  /-- Select these inputs from the actual reading's state tuple. -/
  inputs : Renaming context Γ
  /-- Send each selected input to the designated points of the chosen realization. -/
  realizeInputs {s : P.signature.SortType} (i : Var context s) :
    A.carrier s → (scheme.structureOf algebra realization).carrier s
  /-- Evaluate on the designated states at the selected positions in the scheme. -/
  evaluateOn (R : CoefficientAlgebra base) (a : scheme.Realization R) :
    Assignment (scheme.structureOf R a).carrier context → R.scalars.Carrier

namespace CoefficientReading

variable {P Q : PrimitivePresentation.{u}} {U : DeclarationContext P} {V : DeclarationContext Q}
  {A : Structure P.signature} {B : Structure Q.signature}
  {Γ : List P.signature.SortType} {Δ : List Q.signature.SortType}

/-- The actual coefficient ring of the reading. -/
abbrev ring (reading : CoefficientReading U A Γ) : CoefficientRing.{u} :=
  reading.algebra.scalars

/-- Use the actual reading's state at the specified positions of the chosen realization. -/
def inputTuple (reading : CoefficientReading U A Γ) (e : Assignment A.carrier Γ) :
    Assignment (reading.scheme.structureOf reading.algebra reading.realization).carrier reading.context :=
  ⟨fun i => reading.realizeInputs i (e (reading.inputs i))⟩

/-- Evaluate the chosen realization at the supplied state of the reading. -/
def evaluate (reading : CoefficientReading U A Γ) (e : Assignment A.carrier Γ) :
    reading.ring.Carrier :=
  reading.evaluateOn reading.algebra reading.realization (reading.inputTuple e)

/-- Changing a state outside the chosen input positions leaves the coefficient value fixed. -/
theorem evaluate_eq_of_inputs (reading : CoefficientReading U A Γ)
    {e e' : Assignment A.carrier Γ}
    (same : ∀ {s} (i : Var reading.context s), e (reading.inputs i) = e' (reading.inputs i)) :
    reading.evaluate e = reading.evaluate e' := by
  apply congrArg (reading.evaluateOn reading.algebra reading.realization)
  exact Assignment.ext (fun i => congrArg (reading.realizeInputs i) (same i))

/-- The changed structure comes from the selected realization by the scheme's rule. -/
def changedStructure (reading : CoefficientReading U A Γ) {target : CoefficientRing.{u}}
    (f : reading.ring.Hom target) : RestrictedStructure U :=
  reading.scheme.structureOf (reading.algebra.extend f) (reading.scheme.change f reading.realization)

/-- Transport the selected state's coordinates by the scheme's coefficient change. -/
def changedState (reading : CoefficientReading U A Γ) {target : CoefficientRing.{u}}
    (f : reading.ring.Hom target) (e : Assignment A.carrier Γ) :
    Assignment (reading.changedStructure f).carrier reading.context :=
  RestrictedStructure.mapAssignment (reading.scheme.changePoints f reading.realization)
    reading.supported (reading.inputTuple e)

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
  /-- Compare the two chosen evaluations along the actual state and scalar maps. -/
  evaluate_commutes (e : Assignment A.carrier Γ) :
    target.evaluate (states e) = coefficients (source.evaluate e)

/-- Obtain the comparison by transporting first along the source scheme's scalar rule. -/
def Change.alongScheme {source : CoefficientReading U A Γ} {target : CoefficientReading V B Δ}
    {states : Assignment A.carrier Γ → Assignment B.carrier Δ}
    (f : source.ring.Hom target.ring)
    (toTarget : Assignment (source.changedStructure f).carrier source.context → Assignment B.carrier Δ)
    (state_commutes : ∀ e, toTarget (source.changedState f e) = states e)
    (change_commutes : ∀ e, source.changedEvaluation f e = f (source.evaluate e))
    (target_commutes : ∀ e, target.evaluate (toTarget (source.changedState f e)) =
      source.changedEvaluation f e) : Change source target states where
  coefficients := f
  evaluate_commutes e := (congrArg target.evaluate (state_commutes e)).symm.trans
    ((target_commutes e).trans (change_commutes e))

/-- The reading can hold its coefficient choices fixed or compare two choices by a scalar map. -/
inductive Comparison (source : CoefficientReading U A Γ) (target : CoefficientReading V B Δ)
    (states : Assignment A.carrier Γ → Assignment B.carrier Δ) where
  | fixed : source.ring = target.ring → Comparison source target states
  | changed : Change source target states → Comparison source target states

end CoefficientReading

end SHIGURE
