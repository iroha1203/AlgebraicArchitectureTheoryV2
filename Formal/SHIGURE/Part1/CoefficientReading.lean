import Formal.SHIGURE.Part1.RestrictedEvaluation
import Formal.SHIGURE.Part1.StructureMaps
import Mathlib.Algebra.Algebra.Defs
import Mathlib.CategoryTheory.Category.Basic

/-! # Coefficients chosen by a reading

Definition 1.11 records the coefficient ring and the realization scheme of
Definition 4.1. A scheme specifies its available realizations and the rules
for native inputs, primitive structure, Law interpretation, and coefficient
change. The fields specify the rules of a chosen scheme. Compatibility of an
actual reading comparison is checked on its selected realizations and inputs.

## Implementation notes

A coefficient algebra is a commutative ring with a unital map from the base
ring. A comparison that changes coefficients makes the base and scalar
maps commute, and tests the selected evaluations along the scalar map and
the state map of Equation (1.12). When the states are transported using a
scheme's own scalar-change rule, that rule supplies an intermediate
realization and yields the comparison by composition.
-/

universe u v

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
  Realization : CoefficientAlgebra base → Type v
  /-- The carriers of designated points and the primitive maps they interpret. -/
  structureOf (R : CoefficientAlgebra base) : Realization R → RestrictedStructure U
  /-- The admissible structural morphisms at each coefficient algebra, with identity and composition. -/
  category (R : CoefficientAlgebra base) : CategoryTheory.Category.{u} (Realization R)
  /-- The action of each admissible morphism on the designated points. -/
  mapPoints {R : CoefficientAlgebra base} {a b : Realization R} (f : (category R).Hom a b) :
    RestrictedStructure.PointMap (structureOf R a) (structureOf R b)
  /-- The point map of an admissible morphism preserves the retained primitive data. -/
  mapPoints_preserves {R : CoefficientAlgebra base} {a b : Realization R} (f : (category R).Hom a b) :
    (structureOf R a).Preserves (structureOf R b) (mapPoints f)
  /-- Identity acts as the identity at each retained sort. -/
  mapPoints_id {R : CoefficientAlgebra base} (a : Realization R) (s : P.signature.SortType)
    (kept : Declaration.sort s ∈ U.declarations) (x : (structureOf R a).carrier s) :
    mapPoints ((category R).id a) s kept x = x
  /-- The action on retained points respects composition. -/
  mapPoints_comp {R : CoefficientAlgebra base} {a b c : Realization R}
    (f : (category R).Hom a b) (g : (category R).Hom b c) (s : P.signature.SortType)
    (kept : Declaration.sort s ∈ U.declarations) (x : (structureOf R a).carrier s) :
    mapPoints ((category R).comp f g) s kept x = mapPoints g s kept (mapPoints f s kept x)
  /-- Point correspondences that this scheme admits from a state family on the used sorts. -/
  permitsPoints (R : CoefficientAlgebra base) (a : Realization R)
    (X : P.signature.SortType → Type u) (Γ : List P.signature.SortType)
    (points : ∀ s : P.signature.SortType, s ∈ Γ → X s → (structureOf R a).carrier s) : Prop
  /-- Admissible native input data for the realization scheme. -/
  Native : Type v
  /-- The native structure whose points are used in the realization rule. -/
  nativeStructure : Native → RestrictedStructure U
  /-- Construct a realization from the native input. -/
  realizeNative (R : CoefficientAlgebra base) : Native → Realization R
  /-- The correspondence between native and realized points. -/
  nativePoints (R : CoefficientAlgebra base) (a : Native) :
    RestrictedStructure.PointMap (nativeStructure a) (structureOf R (realizeNative R a))
  /-- The declared native correspondence is available on every selected tuple of retained sorts. -/
  nativePoints_permitted (R : CoefficientAlgebra base) (a : Native)
    (Γ : List P.signature.SortType) (kept : Declaration.sorts (P := P) Γ ⊆ U.declarations) :
    permitsPoints R (realizeNative R a) (nativeStructure a).carrier Γ
      (fun s hs => nativePoints R a s (kept ⟨s, hs, rfl⟩))
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

/-- A small indexed family of state sorts. -/
structure ObservationProduct (S : Type u) where
  /-- The positions supplied to the observation. -/
  Index : Type u
  /-- The state sort read at each position. -/
  sort : Index → S

namespace ObservationProduct

variable {S T : Type u}

/-- The dependent product of the designated carriers. -/
abbrev Values (product : ObservationProduct S) (X : S → Type u) :=
  (i : product.Index) → X (product.sort i)

/-- One position of the indicated sort. -/
def ofSort (s : S) : ObservationProduct S := ⟨PUnit, fun _ => s⟩

/-- Regard the positions of a finite typed context as an index set. -/
def ofList (Γ : List S) : ObservationProduct S :=
  ⟨Σ s : S, Var Γ s, Sigma.fst⟩

/-- The empty product of state sorts. -/
def empty : ObservationProduct S := ⟨PEmpty, fun i => nomatch i⟩

/-- Read a finite context assignment as a dependent product. -/
def ofAssignment {Γ : List S} {X : S → Type u} (e : Assignment X Γ) : (ofList Γ).Values X :=
  fun i => e i.2

/-- Read the product on a finite context as a typed assignment. -/
def toAssignment {Γ : List S} {X : S → Type u} (e : (ofList Γ).Values X) : Assignment X Γ :=
  ⟨fun {s} i => e ⟨s, i⟩⟩

/-- A common product shape with the sorts retyped by the interpretation. -/
structure Correspondence (source : ObservationProduct S) (target : ObservationProduct T)
    (onSort : S → T) where
  /-- Locate each target position in the source product. -/
  position : target.Index ≃ source.Index
  /-- The source and target positions have the prescribed corresponding sorts. -/
  sort_eq (j : target.Index) : onSort (source.sort (position j)) = target.sort j

/-- The identity sort map acts on each position of the same product. -/
def Correspondence.identity (product : ObservationProduct S) :
    Correspondence product product id := ⟨Equiv.refl _, fun _ => rfl⟩

/-- Apply the pointwise state map at the corresponding coordinates. -/
def Correspondence.mapValues {source : ObservationProduct S} {target : ObservationProduct T}
    {onSort : S → T} {X : S → Type u} {Y : T → Type u}
    (positions : Correspondence source target onSort) (h : ∀ s, X s → Y (onSort s))
    (e : source.Values X) : target.Values Y :=
  fun j => positions.sort_eq j ▸ h _ (e (positions.position j))

end ObservationProduct

/-- The positions of a product read by a selected evaluation. -/
structure InputSelection {S : Type u} (Γ : List S) where
  /-- The actual input context, allowing repeated references. -/
  context : List S
  /-- Each reference selects an original position. -/
  inputs : Renaming context Γ

namespace InputSelection

variable {S : Type u} {Γ : List S}

/-- A position is used if some input refers to it. -/
def Uses (selection : InputSelection Γ) {s : S} (i : Var Γ s) : Prop :=
  ∃ j : Var selection.context s, selection.inputs j = i

/-- States at the original positions used by the evaluation. -/
structure Values (selection : InputSelection Γ) (X : S → Type u) where
  /-- One value per used position, even when several inputs refer to it. -/
  get : ∀ {s} (i : Var Γ s), selection.Uses i → X s

/-- Restrict an assignment to the used positions. -/
def Values.restrict {selection : InputSelection Γ} {X : S → Type u} (e : Assignment X Γ) :
    selection.Values X := ⟨fun i _ => e i⟩

/-- Read the value at each selected input, repeating values as specified. -/
def Values.tuple {selection : InputSelection Γ} {X : S → Type u} (e : selection.Values X) :
    Assignment X selection.context := ⟨fun i => e.get (selection.inputs i) ⟨i, rfl⟩⟩

/-- The dependent product indexed by the used original positions. -/
def product (selection : InputSelection Γ) : ObservationProduct S :=
  ⟨Σ s : S, {i : Var Γ s // selection.Uses i}, Sigma.fst⟩

/-- The values at used positions supplied as an indexed product. -/
def Values.ofProduct {selection : InputSelection Γ} {X : S → Type u}
    (e : selection.product.Values X) : selection.Values X :=
  ⟨fun {s} i h => e ⟨s, i, h⟩⟩

/-- Which pairs of input occurrences refer to the same position. -/
def aliases (selection : InputSelection Γ) :
    (Σ s : S, Var selection.context s × Var selection.context s) → Prop :=
  fun i => selection.inputs i.2.1 = selection.inputs i.2.2

end InputSelection

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
  scheme : CoefficientScheme.{u, v} U base
  /-- The chosen realization belongs to this scheme at the selected coefficients. -/
  realization : scheme.Realization algebra
  /-- The positions used for coefficient evaluation. -/
  context : List P.signature.SortType
  /-- Coefficient evaluation uses only retained sort carriers. -/
  supported : Declaration.sorts (P := P) context ⊆ U.declarations
  /-- Select these inputs from the actual reading's state tuple. -/
  inputs : Renaming context Γ
  /-- Map points at each sort used by the coefficient inputs. -/
  realizePoint (s : P.signature.SortType) : s ∈ context →
    A.carrier s → (scheme.structureOf algebra realization).carrier s
  /-- This correspondence is one of those declared by the chosen scheme. -/
  point_permitted : scheme.permitsPoints algebra realization A.carrier context realizePoint
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

/-- The input positions selected by this reading. -/
def selection (reading : CoefficientReading U A Γ) : InputSelection Γ :=
  ⟨reading.context, reading.inputs⟩

/-- Realize the selected inputs. -/
def selectedTuple (reading : CoefficientReading U A Γ) (e : reading.selection.Values A.carrier) :
    Assignment (reading.scheme.structureOf reading.algebra reading.realization).carrier reading.context :=
  ⟨fun i => reading.realizePoint _ i.sort_mem (e.tuple i)⟩

/-- Use the actual reading's state at the specified positions of the chosen realization. -/
def inputTuple (reading : CoefficientReading U A Γ) (e : Assignment A.carrier Γ) :
    Assignment (reading.scheme.structureOf reading.algebra reading.realization).carrier reading.context :=
  reading.selectedTuple (InputSelection.Values.restrict e)

/-- Evaluate from values at the used positions. -/
def evaluateSelected (reading : CoefficientReading U A Γ) (e : reading.selection.Values A.carrier) :
    reading.ring.Carrier :=
  reading.evaluateOn reading.algebra reading.realization (reading.selectedTuple e)

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
  exact Assignment.ext (fun i => congrArg (reading.realizePoint _ i.sort_mem) (same i))

/-- Repeated references to one input have the same designated point. -/
theorem inputTuple_eq_of_same_position (reading : CoefficientReading U A Γ)
    (e : Assignment A.carrier Γ) {s : P.signature.SortType} (i j : Var reading.context s)
    (same : reading.inputs i = reading.inputs j) : reading.inputTuple e i = reading.inputTuple e j :=
  congrArg (reading.realizePoint s i.sort_mem) (congrArg (fun v => e v) same)

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

/-- Compare coefficient evaluations on one common input domain. -/
structure EvaluationComparison (source : CoefficientReading U A Γ) (target : CoefficientReading V B Δ)
    {E : Type u} (readSource : E → source.ring.Carrier) (readTarget : E → target.ring.Carrier) where
  /-- The unital map on the chosen base rings. -/
  baseMap : source.base.Hom target.base
  /-- The unital map on coefficients. -/
  coefficients : source.ring.Hom target.ring
  /-- The coefficient map respects the two algebra structure maps. -/
  algebra_commutes : coefficients.comp source.algebra.fromBase = target.algebra.fromBase.comp baseMap
  /-- Both evaluation paths give the same value at every common input. -/
  evaluate_commutes (e : E) : readTarget e = coefficients (readSource e)

/-- Compare coefficient evaluations along a map between the readings' state products. -/
abbrev Change (source : CoefficientReading U A Γ) (target : CoefficientReading V B Δ)
    (states : Assignment A.carrier Γ → Assignment B.carrier Δ) :=
  EvaluationComparison source target source.evaluate (target.evaluate ∘ states)

/-- Obtain the comparison by transporting first along the source scheme's scalar rule. -/
def Change.alongScheme {source : CoefficientReading U A Γ} {target : CoefficientReading V B Δ}
    {states : Assignment A.carrier Γ → Assignment B.carrier Δ}
    (baseMap : source.base.Hom target.base)
    (f : source.ring.Hom target.ring)
    (algebra_commutes : f.comp source.algebra.fromBase = target.algebra.fromBase.comp baseMap)
    (toTarget : Assignment (source.changedStructure f).carrier source.context → Assignment B.carrier Δ)
    (state_commutes : ∀ e, toTarget (source.changedState f e) = states e)
    (change_commutes : ∀ e, source.changedEvaluation f e = f (source.evaluate e))
    (target_commutes : ∀ e, target.evaluate (toTarget (source.changedState f e)) =
      source.changedEvaluation f e) : Change source target states where
  baseMap := baseMap
  coefficients := f
  algebra_commutes := algebra_commutes
  evaluate_commutes e := (congrArg target.evaluate (state_commutes e)).symm.trans
    ((target_commutes e).trans (change_commutes e))

/-- An unchanged choice of coefficient algebra, scheme, and evaluation rule. -/
structure SameParameters (source : CoefficientReading.{u, v} U A Γ)
    (target : CoefficientReading.{u, v} V B Δ) : Prop where
  /-- The chosen base ring is unchanged. -/
  base : source.base = target.base
  /-- The chosen algebra, including its structure map, is unchanged. -/
  algebra : (base ▸ source.algebra) = target.algebra
  /-- The same scheme is used at both endpoints. -/
  scheme : HEq source.scheme target.scheme
  /-- The same realization is selected in that scheme. -/
  realization : HEq source.realization target.realization
  /-- The evaluation uses the same sorts and order. -/
  context : HEq source.context target.context
  /-- The same input occurrences refer to shared positions. -/
  aliases : HEq source.selection.aliases target.selection.aliases
  /-- The selected point correspondence is unchanged. -/
  points : HEq source.realizePoint target.realizePoint
  /-- The rule over the selected scheme is unchanged. -/
  rule : HEq source.evaluateOn target.evaluateOn

end CoefficientReading

end SHIGURE
