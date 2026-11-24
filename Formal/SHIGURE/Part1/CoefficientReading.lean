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

Restriction fixes the selected coefficient algebra and the explicit coefficient choice
before comparing realizations. The evaluation descends through the quotient by
agreement of retained primitive structures and selected points. To produce those
points, the scheme supplies a separate rule on the two restricted structures.
Agreement with the original point map ensures this rule computes the same input
without having to extend either structure to the original context.
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
  /-- A realized structure exposes carriers only for the retained sort declarations. -/
  structure_retained (R : CoefficientAlgebra base) (a : Realization R) :
    (structureOf R a).HasOnlyRetainedSorts
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
  /-- Point correspondences that this scheme admits from the retained source structure. -/
  permitsPoints (R : CoefficientAlgebra base) (a : Realization R)
    (X : RestrictedStructure U) (sorts : Set P.signature.SortType)
    (points : ∀ s : P.signature.SortType, s ∈ sorts → X.carrier s → (structureOf R a).carrier s) : Prop
  /-- Permissions depend only on the retained source data and the selected point correspondence. -/
  permitsPoints_congr (R : CoefficientAlgebra base) (a : Realization R)
    {X Y : RestrictedStructure U} (same : X.Agrees Y)
    {sorts : Set P.signature.SortType} (kept : ∀ s ∈ sorts, Declaration.sort s ∈ U.declarations)
    (points : ∀ s : P.signature.SortType, s ∈ sorts → Y.carrier s → (structureOf R a).carrier s) :
    permitsPoints R a X sorts (fun s hs x => points s hs (same.carrier_eq s (kept s hs) ▸ x)) ↔
      permitsPoints R a Y sorts points
  /-- Admissible native input data for the realization scheme. -/
  Native : Type v
  /-- The native structure whose points are used in the realization rule. -/
  nativeStructure : Native → RestrictedStructure U
  /-- The native input uses the same retained sort declarations. -/
  native_retained (a : Native) : (nativeStructure a).HasOnlyRetainedSorts
  /-- Construct a realization from the native input. -/
  realizeNative (R : CoefficientAlgebra base) : Native → Realization R
  /-- The correspondence between native and realized points. -/
  nativePoints (R : CoefficientAlgebra base) (a : Native) :
    RestrictedStructure.PointMap (nativeStructure a) (structureOf R (realizeNative R a))
  /-- The declared native correspondence is available on every selected tuple of retained sorts. -/
  nativePoints_permitted (R : CoefficientAlgebra base) (a : Native)
    (sorts : Set P.signature.SortType) (kept : ∀ s ∈ sorts, Declaration.sort s ∈ U.declarations) :
    permitsPoints R (realizeNative R a) (nativeStructure a) sorts
      (fun s hs => nativePoints R a s (kept s hs))
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
  /-- The independently selectable data of the coefficient method. -/
  Choice : Type v := PUnit
  /-- A point correspondence computed from the retained structures and the chosen data. -/
  pointsWithin (R : CoefficientAlgebra base) (choice : Choice)
    (W : DeclarationContext P) (X Y : RestrictedStructure W)
    (s : P.signature.SortType) (kept : Declaration.sort s ∈ W.declarations) :
    Option (X.carrier s → Y.carrier s) := none

/-- A small indexed family of state sorts. -/
structure ObservationProduct (S : Type u) where
  /-- The positions supplied to the observation. -/
  Index : Type u
  /-- The state sort read at each position. -/
  sort : Index → S
  /-- Only explicitly named products identify positions across two observations. -/
  nameScope : Option String := none
  /-- The original coordinate names, with no repetitions in this product. -/
  names : Σ Name : Type u, Index ↪ Name := ⟨Index, Function.Embedding.refl Index⟩

namespace ObservationProduct

variable {S T : Type u}

/-- The dependent product of the designated carriers. -/
abbrev Values (product : ObservationProduct S) (X : S → Type u) :=
  (i : product.Index) → X (product.sort i)

/-- One position of the indicated sort. -/
def ofSort (s : S) : ObservationProduct S := { Index := PUnit, sort := fun _ => s }

/-- Regard the positions of a finite typed context as the canonical named variable positions. -/
def ofList (Γ : List S) : ObservationProduct S where
  Index := Σ s : S, Var Γ s
  sort := Sigma.fst
  nameScope := some "typed variables"
  names := ⟨ULift Nat, ⟨fun i => ⟨i.2.position⟩, by
    intro i j eq
    exact Var.position_injective Γ (congrArg ULift.down eq)⟩⟩

/-- The empty product of state sorts. -/
def empty : ObservationProduct S := { Index := PEmpty, sort := fun i => nomatch i }

/-- Name the coordinates of this product for comparisons with other products. -/
def withName (product : ObservationProduct S) (name : String) : ObservationProduct S :=
  { product with nameScope := some name }

/-- Select a subset of a product and keep the names of its original coordinates. -/
def restrict (product : ObservationProduct S) (kept : Set product.Index) : ObservationProduct S where
  Index := kept
  sort i := product.sort i.val
  nameScope := product.nameScope
  names := ⟨product.names.1, ⟨fun i => product.names.2 i.val, by
    intro i j eq
    exact Subtype.ext (product.names.2.injective eq)⟩⟩

/-- Read a finite context assignment as a dependent product. -/
def ofAssignment {Γ : List S} {X : S → Type u} (e : Assignment X Γ) : (ofList Γ).Values X :=
  fun i => e i.2

/-- Read the product on a finite context as a typed assignment. -/
def toAssignment {Γ : List S} {X : S → Type u} (e : (ofList Γ).Values X) : Assignment X Γ :=
  ⟨fun {s} i => e ⟨s, i⟩⟩

/-- A typed choice of source positions for the target observation. -/
structure Correspondence (source : ObservationProduct S) (target : ObservationProduct T)
    (onSort : S → T) where
  /-- Locate each target position in the source product. -/
  position : target.Index → source.Index
  /-- The source and target positions have the prescribed corresponding sorts. -/
  sort_eq (j : target.Index) : onSort (source.sort (position j)) = target.sort j
  /-- A compatible common name identifies the same position in both products. -/
  keepsNamed (j : target.Index) (i : source.Index) :
    source.nameScope ≠ none → source.nameScope = target.nameScope →
    HEq (source.names.2 i) (target.names.2 j) → onSort (source.sort i) = target.sort j → position j = i

/-- The identity sort map acts on each position of the same product. -/
def Correspondence.identity (product : ObservationProduct S) :
    Correspondence product product id :=
  ⟨id, fun _ => rfl, fun _ _ _ _ same _ => product.names.2.injective (eq_of_heq same.symm)⟩

/-- Apply the pointwise state map at the corresponding coordinates. -/
def Correspondence.mapValues {source : ObservationProduct S} {target : ObservationProduct T}
    {onSort : S → T} {X : S → Type u} {Y : T → Type u}
    (positions : Correspondence source target onSort) (h : ∀ s, X s → Y (onSort s))
    (e : source.Values X) : target.Values Y :=
  fun j => positions.sort_eq j ▸ h _ (e (positions.position j))

end ObservationProduct

/-- A coefficient product uses typed variable positions or a specified subset of indices.
An explicitly shared namespace identifies compatible positions across products. -/
inductive CoefficientProduct (S : Type u) where
  | ofList (context : List S) (nameScope : Option String := some "typed variables")
  | indexed (Index : Type u) (present : Set Index) (sort : present → S) (nameScope : Option String := none)
      (names : Σ Name : Type u, (present : Type u) ↪ Name :=
        ⟨Index, ⟨Subtype.val, Subtype.val_injective⟩⟩)

namespace CoefficientProduct

variable {S : Type u}

/-- The carriers supplied to the reading are indexed by the original positions. -/
def product : CoefficientProduct S → ObservationProduct S
  | .ofList Γ nameScope => { ObservationProduct.ofList Γ with nameScope := nameScope }
  | .indexed _ present sort nameScope names => ⟨present, sort, nameScope, names⟩

/-- The original slot namespace, independent of the available subset of slots. -/
abbrev Slot (raw : CoefficientProduct S) : Type u := raw.product.names.1

/-- Each original position has its actual slot, unaffected by the selected evaluation. -/
def slot (raw : CoefficientProduct S) : raw.product.Index → raw.Slot := raw.product.names.2

/-- The original product has only one position for each slot. -/
theorem slot_injective (raw : CoefficientProduct S) : Function.Injective raw.slot :=
  raw.product.names.2.injective

/-- Make all positions of a general indexed product available. -/
def all (p : ObservationProduct S) : CoefficientProduct S :=
  .indexed p.Index Set.univ (fun i => p.sort i.val) p.nameScope (p.restrict Set.univ).names

end CoefficientProduct

/-- A selection of the actual original positions used by an evaluation. -/
structure InputSelection {S : Type u} (raw : CoefficientProduct S) where
  /-- The family of actual evaluation inputs. -/
  selected : ObservationProduct S
  /-- The original position for each input. -/
  inputs : selected.Index → raw.product.Index
  /-- Selection preserves the sort of each position. -/
  sort_eq (i : selected.Index) : raw.product.sort (inputs i) = selected.sort i

namespace InputSelection

variable {S : Type u} {raw : CoefficientProduct S}

/-- The product of used original positions, with one coordinate for each shared input. -/
def used (selection : InputSelection raw) : ObservationProduct S :=
  raw.product.restrict (Set.range selection.inputs)

/-- Read each input at its selected position, preserving repeated references. -/
def tuple (selection : InputSelection raw) {X : S → Type u} (e : selection.used.Values X) :
    selection.selected.Values X :=
  fun i => selection.sort_eq i ▸ e ⟨selection.inputs i, i, rfl⟩

/-- The original slot of each selected input, in the coordinate namespace shared across products. -/
def selectedSlots (selection : InputSelection raw) : selection.selected.Index → raw.Slot :=
  raw.slot ∘ selection.inputs

/-- Select typed positions of a finite context. -/
def ofRenaming {Γ Δ : List S} {nameScope : Option String} (ρ : Renaming Δ Γ) :
    InputSelection (.ofList Γ nameScope) where
  selected := .ofList Δ
  inputs i := ⟨i.1, ρ i.2⟩
  sort_eq _ := rfl

/-- Select all positions of the indicated indexed product. -/
def all (p : ObservationProduct S) : InputSelection (CoefficientProduct.all p) where
  selected := p
  inputs i := ⟨i, Set.mem_univ i⟩
  sort_eq _ := rfl

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

/-- The designated-point map on the sorts actually evaluated. -/
abbrev CoefficientScheme.SelectedPointMap {P : PrimitivePresentation.{u}} {U : DeclarationContext P}
    {base : CoefficientRing.{u}} (scheme : CoefficientScheme.{u, v} U base)
    (R : CoefficientAlgebra base) (a : scheme.Realization R)
    (X : P.signature.SortType → Type u) (sorts : Set P.signature.SortType) :=
  ∀ s : P.signature.SortType, s ∈ sorts → X s → (scheme.structureOf R a).carrier s

/-- A selected point correspondence either uses the native rule or is explicitly permitted by the scheme. -/
inductive CoefficientScheme.PointOrigin {P : PrimitivePresentation.{u}} {U : DeclarationContext P}
    {base : CoefficientRing.{u}} (scheme : CoefficientScheme.{u, v} U base)
    (R : CoefficientAlgebra base) (a : scheme.Realization R)
    (A : Structure P.signature) (sorts : Set P.signature.SortType)
    (points : scheme.SelectedPointMap R a A.carrier sorts) where
  | declared : scheme.permitsPoints R a (RestrictedStructure.restrict U A) sorts points →
      PointOrigin scheme R a A sorts points
  | native (origin : scheme.Native) (same : scheme.realizeNative R origin = a)
      (kept : ∀ s ∈ sorts, Declaration.sort s ∈ U.declarations)
      (retained : (RestrictedStructure.restrict U A).Agrees (scheme.nativeStructure origin))
      (agrees : ∀ s hs x, points s hs x =
        (same ▸ scheme.nativePoints R origin s (kept s hs) (retained.carrier_eq s (kept s hs) ▸ x))) :
      PointOrigin scheme R a A sorts points

/-- The evaluation uses the scheme's native rule at its selected source object. -/
def CoefficientScheme.PointOrigin.isNative {P : PrimitivePresentation.{u}} {U : DeclarationContext P}
    {base : CoefficientRing.{u}} {scheme : CoefficientScheme.{u, v} U base}
    {R : CoefficientAlgebra base} {a : scheme.Realization R}
    {A : Structure P.signature} {sorts : Set P.signature.SortType}
    {points : scheme.SelectedPointMap R a A.carrier sorts} :
    scheme.PointOrigin R a A sorts points → Prop
  | .declared _ => False
  | .native .. => True

/-- Every selected point map satisfies the scheme's permission on the actual reading structure. -/
theorem CoefficientScheme.PointOrigin.permitted {P : PrimitivePresentation.{u}} {U : DeclarationContext P}
    {base : CoefficientRing.{u}} {scheme : CoefficientScheme.{u, v} U base}
    {R : CoefficientAlgebra base} {a : scheme.Realization R}
    {A : Structure P.signature} {sorts : Set P.signature.SortType}
    {points : scheme.SelectedPointMap R a A.carrier sorts}
    (origin : scheme.PointOrigin R a A sorts points) :
    scheme.permitsPoints R a (RestrictedStructure.restrict U A) sorts points := by
  cases origin with
  | declared permitted => exact permitted
  | native origin same kept retained agrees =>
    subst a
    have point_eq : points =
        (fun s hs x => scheme.nativePoints R origin s (kept s hs)
          (retained.carrier_eq s (kept s hs) ▸ x)) := funext fun s =>
      funext fun hs => funext (agrees s hs)
    rw [point_eq]
    exact (scheme.permitsPoints_congr R _ retained kept
      (fun s hs => scheme.nativePoints R origin s (kept s hs))).2
        (scheme.nativePoints_permitted R origin sorts kept)

/-- A choice of coefficients, scheme and evaluation at the actual reading structure. -/
structure CoefficientReading {P : PrimitivePresentation.{u}} (U : DeclarationContext P)
    (A : Structure P.signature) (Γ : CoefficientProduct P.signature.SortType) where
  /-- The base ring of the chosen scheme. -/
  base : CoefficientRing.{u}
  /-- The selected coefficient algebra. -/
  algebra : CoefficientAlgebra base
  /-- The chosen realization scheme for the selected declarations. -/
  scheme : CoefficientScheme.{u, v} U base
  /-- The chosen coefficient data is an input of the evaluation, independent of its realized structure. -/
  choice : scheme.Choice := by exact PUnit.unit
  /-- The chosen realization belongs to this scheme at the selected coefficients. -/
  realization : scheme.Realization algebra
  /-- The independently selected positions actually used for coefficient evaluation. -/
  selection : InputSelection Γ
  /-- Coefficient evaluation uses only retained sort carriers. -/
  supported (i : selection.selected.Index) : Declaration.sort (selection.selected.sort i) ∈ U.declarations
  /-- Map points at each sort used by the coefficient inputs. -/
  realizePoint : scheme.SelectedPointMap algebra realization A.carrier (Set.range selection.selected.sort)
  /-- The specified rule that supplies the actual correspondence. -/
  pointOrigin : scheme.PointOrigin algebra realization A (Set.range selection.selected.sort) realizePoint
  /-- Evaluate on the designated states at the selected positions in the scheme. -/
  evaluateOn (choice : scheme.Choice) (R : CoefficientAlgebra base) (a : scheme.Realization R) :
    selection.selected.Values (scheme.structureOf R a).carrier → R.scalars.Carrier

namespace CoefficientReading

variable {P Q : PrimitivePresentation.{u}} {U : DeclarationContext P} {V : DeclarationContext Q}
  {A : Structure P.signature} {B : Structure Q.signature}
  {Γ : CoefficientProduct P.signature.SortType} {Δ : CoefficientProduct Q.signature.SortType}

/-- The actual coefficient ring of the reading. -/
abbrev ring (reading : CoefficientReading U A Γ) : CoefficientRing.{u} :=
  reading.algebra.scalars

/-- Realize the selected inputs. -/
def selectedPoint (reading : CoefficientReading U A Γ) (i : reading.selection.selected.Index) :
    A.carrier (reading.selection.selected.sort i) →
      (reading.scheme.structureOf reading.algebra reading.realization).carrier
        (reading.selection.selected.sort i) :=
  reading.realizePoint _ ⟨i, rfl⟩

/-- Realize the tuple at the selected inputs. -/
def selectedTuple (reading : CoefficientReading U A Γ) (e : reading.selection.used.Values A.carrier) :
    reading.selection.selected.Values (reading.scheme.structureOf reading.algebra reading.realization).carrier :=
  fun i => reading.selectedPoint i (reading.selection.tuple e i)

/-- Use the actual reading's state at the specified positions of the chosen realization. -/
def inputTuple (reading : CoefficientReading U A Γ) (e : Γ.product.Values A.carrier) :
    reading.selection.selected.Values (reading.scheme.structureOf reading.algebra reading.realization).carrier :=
  reading.selectedTuple (fun i => e i.val)

/-- Evaluate from values at the used positions. -/
def evaluateSelected (reading : CoefficientReading U A Γ) (e : reading.selection.used.Values A.carrier) :
    reading.ring.Carrier :=
  reading.evaluateOn reading.choice reading.algebra reading.realization (reading.selectedTuple e)

/-- Evaluate the chosen realization at the supplied state of the reading. -/
def evaluate (reading : CoefficientReading U A Γ) (e : Γ.product.Values A.carrier) :
    reading.ring.Carrier :=
  reading.evaluateSelected (fun i => e i.val)

/-- Changing a state outside the chosen input positions leaves the coefficient value fixed. -/
theorem evaluate_eq_of_inputs (reading : CoefficientReading U A Γ) {e e' : Γ.product.Values A.carrier}
    (same : ∀ i : reading.selection.used.Index, e i.val = e' i.val) :
    reading.evaluate e = reading.evaluate e' :=
  congrArg reading.evaluateSelected (funext same)

/-- A realized input consists of a realization and the values at its selected state positions. -/
abbrev RealizedInput (reading : CoefficientReading U A Γ) (R : CoefficientAlgebra reading.base) :=
  Σ a : reading.scheme.Realization R,
    reading.selection.selected.Values (reading.scheme.structureOf R a).carrier

/-- Compare only retained primitive data and chosen states at the same coefficient algebra. -/
def AgreeOn (reading : CoefficientReading U A Γ) {W : DeclarationContext P}
    (inside : W.declarations ⊆ U.declarations)
    (supported : ∀ i, Declaration.sort (reading.selection.selected.sort i) ∈ W.declarations)
    {R : CoefficientAlgebra reading.base} (left right : reading.RealizedInput R) : Prop :=
  ∃ same : ((reading.scheme.structureOf R left.1).restrictWithin inside).Agrees
      ((reading.scheme.structureOf R right.1).restrictWithin inside),
    right.2 = fun i => same.carrier_eq _ (supported i) ▸ left.2 i

/-- Restrict the actual point correspondence and evaluation at the chosen coefficient algebra. -/
structure RespectsRestriction (reading : CoefficientReading U A Γ) (W : DeclarationContext P)
    (inside : W.declarations ⊆ U.declarations) : Prop where
  /-- Every coordinate used in the evaluation belongs to the smaller context. -/
  supported (i : reading.selection.selected.Index) :
    Declaration.sort (reading.selection.selected.sort i) ∈ W.declarations
  /-- The scheme's local point rule recovers the actual selected points on the retained source data. -/
  points (i : reading.selection.selected.Index) (X Y : RestrictedStructure W)
    (sourceAgree : ((RestrictedStructure.restrict U A).restrictWithin inside).Agrees X)
    (targetAgree : ((reading.scheme.structureOf reading.algebra reading.realization).restrictWithin inside).Agrees Y) :
    reading.scheme.pointsWithin reading.algebra reading.choice
        W X Y (reading.selection.selected.sort i) (supported i) =
      some (fun x => cast (targetAgree.carrier_eq _ (supported i))
        (reading.selectedPoint i (cast (sourceAgree.carrier_eq _ (supported i)).symm x)))
  /-- Retained primitive data, coefficient data and points determine the value at the chosen algebra. -/
  agrees (left right : reading.RealizedInput reading.algebra) :
    reading.AgreeOn inside supported left right →
      reading.evaluateOn reading.choice reading.algebra left.1 left.2 =
        reading.evaluateOn reading.choice reading.algebra right.1 right.2

/-- A restricted input is the class of a realized input with the same retained data. -/
abbrev RetainedInput (reading : CoefficientReading U A Γ) {W : DeclarationContext P}
    (inside : W.declarations ⊆ U.declarations) (locality : reading.RespectsRestriction W inside) :=
  Quot (reading.AgreeOn inside locality.supported (R := reading.algebra))

/-- Evaluate on the retained data alone. -/
def evaluateRetained (reading : CoefficientReading U A Γ) {W : DeclarationContext P}
    {inside : W.declarations ⊆ U.declarations} (locality : reading.RespectsRestriction W inside)
    : reading.RetainedInput inside locality → reading.ring.Carrier :=
  Quot.lift (fun input : reading.RealizedInput reading.algebra =>
    reading.evaluateOn reading.choice reading.algebra input.1 input.2) locality.agrees

/-- Recover the selected point map from the scheme's local rule on the actual restrictions. -/
private def localPointRule (reading : CoefficientReading U A Γ) {W : DeclarationContext P}
    {inside : W.declarations ⊆ U.declarations} (locality : reading.RespectsRestriction W inside)
    (i : reading.selection.selected.Index) :
    Option (A.carrier (reading.selection.selected.sort i) →
      (reading.scheme.structureOf reading.algebra reading.realization).carrier
        (reading.selection.selected.sort i)) :=
  reading.scheme.pointsWithin reading.algebra reading.choice
    W ((RestrictedStructure.restrict U A).restrictWithin inside)
    ((reading.scheme.structureOf reading.algebra reading.realization).restrictWithin inside)
    _ (locality.supported i)

/-- The chosen local point rule is defined and agrees with the original correspondence. -/
private theorem localPointRule_eq (reading : CoefficientReading U A Γ) {W : DeclarationContext P}
    {inside : W.declarations ⊆ U.declarations} (locality : reading.RespectsRestriction W inside)
    (i : reading.selection.selected.Index) :
    reading.localPointRule locality i = some (reading.selectedPoint i) :=
  locality.points i _ _ (RestrictedStructure.Agrees.refl _) (RestrictedStructure.Agrees.refl _)

/-- Realize the retained state tuple using the actual local point rule and restrict its data. -/
def restrictSelected (reading : CoefficientReading U A Γ) {W : DeclarationContext P}
    {inside : W.declarations ⊆ U.declarations} (locality : reading.RespectsRestriction W inside)
    (e : reading.selection.used.Values A.carrier) : reading.RetainedInput inside locality :=
  Quot.mk _ ⟨reading.realization, fun i =>
    (reading.localPointRule locality i).get
      (congrArg Option.isSome (reading.localPointRule_eq locality i))
      (reading.selection.tuple e i)⟩

/-- Restricting the actual input and evaluating gives the reading's original value. -/
theorem evaluateRetained_mk (reading : CoefficientReading U A Γ) {W : DeclarationContext P}
    {inside : W.declarations ⊆ U.declarations} (locality : reading.RespectsRestriction W inside)
    (e : reading.selection.used.Values A.carrier) :
    reading.evaluateRetained locality (reading.restrictSelected locality e) =
      reading.evaluateSelected e := by
  change reading.evaluateOn reading.choice reading.algebra reading.realization _ =
    reading.evaluateOn reading.choice reading.algebra reading.realization (reading.selectedTuple e)
  apply congrArg (reading.evaluateOn reading.choice reading.algebra reading.realization)
  funext i
  exact congrFun (Option.get_of_eq_some _ (reading.localPointRule_eq locality i)) _

/-- The retained context either keeps the entire realization or supports its restricted evaluator. -/
def RestrictionAllowed (reading : CoefficientReading U A Γ) (W : DeclarationContext P)
    (inside : W.declarations ⊆ U.declarations) : Prop :=
  W.declarations = U.declarations ∨ reading.RespectsRestriction W inside

open Classical in
/-- Evaluate the chosen input through the full or restricted realization, as applicable. -/
noncomputable def evaluateWithin (reading : CoefficientReading U A Γ) {W : DeclarationContext P}
    {inside : W.declarations ⊆ U.declarations} (allowed : reading.RestrictionAllowed W inside)
    (e : reading.selection.used.Values A.carrier) : reading.ring.Carrier :=
  if same : W.declarations = U.declarations then
    reading.evaluateSelected e
  else
    let locality := allowed.resolve_left same
    reading.evaluateRetained locality (reading.restrictSelected locality e)

/-- Evaluation through either localization route gives the same selected value. -/
theorem evaluateWithin_eq (reading : CoefficientReading U A Γ) {W : DeclarationContext P}
    {inside : W.declarations ⊆ U.declarations} (allowed : reading.RestrictionAllowed W inside)
    (e : reading.selection.used.Values A.carrier) :
    reading.evaluateWithin allowed e = reading.evaluateSelected e := by
  unfold evaluateWithin
  split
  · rfl
  · exact evaluateRetained_mk _ _ _

/-- The changed structure comes from the selected realization by the scheme's rule. -/
def changedStructure (reading : CoefficientReading U A Γ) {target : CoefficientRing.{u}}
    (f : reading.ring.Hom target) : RestrictedStructure U :=
  reading.scheme.structureOf (reading.algebra.extend f) (reading.scheme.change f reading.realization)

/-- Transport the selected state's coordinates by the scheme's coefficient change. -/
def changedState (reading : CoefficientReading U A Γ) {target : CoefficientRing.{u}}
    (f : reading.ring.Hom target) (e : Γ.product.Values A.carrier) :
    reading.selection.selected.Values (reading.changedStructure f).carrier :=
  fun i => reading.scheme.changePoints f reading.realization _ (reading.supported i) (reading.inputTuple e i)

/-- Evaluate on the actual realization and state produced by the coefficient-change rule. -/
def changedEvaluation (reading : CoefficientReading U A Γ) {target : CoefficientRing.{u}}
    (f : reading.ring.Hom target) (e : Γ.product.Values A.carrier) : target.Carrier :=
  reading.evaluateOn reading.choice (reading.algebra.extend f) (reading.scheme.change f reading.realization)
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
    (states : Γ.product.Values A.carrier → Δ.product.Values B.carrier) :=
  EvaluationComparison source target source.evaluate (target.evaluate ∘ states)

/-- Obtain the comparison by transporting first along the source scheme's scalar rule. -/
def Change.alongScheme {source : CoefficientReading U A Γ} {target : CoefficientReading V B Δ}
    {states : Γ.product.Values A.carrier → Δ.product.Values B.carrier}
    (baseMap : source.base.Hom target.base)
    (f : source.ring.Hom target.ring)
    (algebra_commutes : f.comp source.algebra.fromBase = target.algebra.fromBase.comp baseMap)
    (toTarget : source.selection.selected.Values (source.changedStructure f).carrier → Δ.product.Values B.carrier)
    (state_commutes : ∀ e, toTarget (source.changedState f e) = states e)
    (change_commutes : ∀ e, source.changedEvaluation f e = f (source.evaluate e))
    (target_commutes : ∀ e, target.evaluate (toTarget (source.changedState f e)) =
      source.changedEvaluation f e) : Change source target states where
  baseMap := baseMap
  coefficients := f
  algebra_commutes := algebra_commutes
  evaluate_commutes e := (congrArg target.evaluate (state_commutes e)).symm.trans
    ((target_commutes e).trans (change_commutes e))

/-- Two ambient models have the same source data for a fixed retained coefficient scheme. -/
inductive SameRetainedSource : {P Q : PrimitivePresentation.{u}} →
    (U : DeclarationContext P) → (V : DeclarationContext Q) →
    Structure P.signature → Structure Q.signature → Prop
  | ofAgreement {P : PrimitivePresentation.{u}} {U : DeclarationContext P}
      {A B : Structure P.signature}
      (same : (RestrictedStructure.restrict U A).Agrees (RestrictedStructure.restrict U B)) :
      SameRetainedSource U U A B

/-- An unchanged choice of coefficient algebra, scheme, and evaluation rule. -/
structure SameParameters (source : CoefficientReading.{u, v} U A Γ)
    (target : CoefficientReading.{u, v} V B Δ) : Prop where
  /-- The chosen base ring is unchanged. -/
  base : source.base = target.base
  /-- The chosen algebra, including its structure map, is unchanged. -/
  algebra : (base ▸ source.algebra) = target.algebra
  /-- The same scheme is used at both endpoints. -/
  scheme : HEq source.scheme target.scheme
  /-- The evaluation uses the same sorts and order. -/
  context : HEq source.selection.selected target.selection.selected
  /-- The selected inputs refer to the same named original positions. -/
  names : HEq source.selection.selectedSlots target.selection.selectedSlots
  /-- The raw coordinate namespace is unchanged. -/
  nameScope : Γ.product.nameScope = Δ.product.nameScope
  /-- In a common original product, both inputs select the same coordinates. -/
  positions : HEq Γ Δ → HEq source.selection.inputs target.selection.inputs
  /-- Keep the same application on a retained source, or apply the common native rule to changed
  retained source data. -/
  application : (source.pointOrigin.isNative ∧ target.pointOrigin.isNative ∧
      (SameRetainedSource U V A B →
        HEq source.realization target.realization ∧ HEq source.selectedPoint target.selectedPoint)) ∨
    (HEq source.realization target.realization ∧ HEq source.selectedPoint target.selectedPoint)
  /-- The rule over the selected scheme is unchanged. -/
  rule : HEq source.evaluateOn target.evaluateOn
  /-- The selected coefficient data is unchanged. -/
  choice : HEq source.choice target.choice

end CoefficientReading

end SHIGURE
