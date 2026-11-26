import Formal.SHIGURE.Part2.QuantityTransport.DeclarationStates
import Formal.SHIGURE.Part2.QuantityTransport.Coefficients
import Mathlib.RingTheory.Localization.Away.Basic

/-! # Restriction of written coefficient equations

A coefficient Law is given by its written scalar expressions and its
designated inputs. Restricting the declarations retains exactly the
specified names and references in the reduct. Each retained state
argument is evaluated in that reduct, and the scalar literals remain
in the base ring.

## Implementation notes

One family of written equations and occurrence types supplies both
contexts. The selection carries closure under those occurrences, the
condition for retaining a whole equation. Definition 5.1 supplies
coefficient literals and arithmetic directly. The interpretation of a
registered native state equation uses the separate evaluation proof
in `DeclarationRestriction`.
-/

namespace SHIGURE.Quantities

open DeclarationContext

noncomputable section

universe u

namespace Expression

variable {k J K N : Type u}

/-- The variable occurrences that the expression actually uses. -/
def occurrences : Expression k J → Set J
  | .scalar _ => ∅
  | .quantity a => {a}
  | .add p q | .mul p q => p.occurrences ∪ q.occurrences
  | .neg p => p.occurrences

/-- Compile only the variables used by the expression. -/
def compile : (p : Expression k J) → (∀ a ∈ p.occurrences, K) → Expression k K
  | .scalar r, _ => .scalar r
  | .quantity a, f => .quantity (f a (Set.mem_singleton _))
  | .add p q, f => .add (p.compile fun a h => f a (Or.inl h)) (q.compile fun a h => f a (Or.inr h))
  | .mul p q, f => .mul (p.compile fun a h => f a (Or.inl h)) (q.compile fun a h => f a (Or.inr h))
  | .neg p, f => .neg (p.compile f)

/-- All coefficient literals and operations are unchanged by compiling and then renaming. -/
theorem rename_compile (p : Expression k J) (f : ∀ a ∈ p.occurrences, K) (g : K → N) :
    (p.compile f).rename g = p.compile (fun a h => g (f a h)) := by
  induction p <;> simp [compile, rename, *]
  rfl

/-- Compiling along a function defined on every occurrence is ordinary renaming. -/
theorem compile_eq_rename (p : Expression k J) (f : J → K) :
    p.compile (fun a _ => f a) = p.rename f := by
  induction p <;> simp [compile, rename, *]
  assumption

end Expression

namespace WrittenLaws

variable {P : PrimitivePresentation.{u}} {k : Type u}
variable (L : WrittenLaws k P.signature)

/-- The occurrences used in either of the two original sides. -/
abbrev UsedOccurrence (l : L.Law) :=
  {a : L.Occurrence l // a ∈ (L.left l).occurrences ∪ (L.right l).occurrences}

/-- A declaration context for the state, together with the retained scalar quantities and Law names.
Every retained Law keeps its entire written expression and all of its typed state arguments. -/
structure DeclarationSelection where
  /-- The dependency-closed declarations of the fixed state. -/
  context : DeclarationContext P
  /-- The names of the retained quantities. -/
  quantities : Set L.Quantity
  /-- The names of the retained written coefficient Laws. -/
  laws : Set L.Law
  /-- The retained domains use retained state sorts. -/
  domainSorts {j : L.Quantity} : j ∈ quantities →
    Declaration.sorts (L.domainContext j) ⊆ context.declarations
  /-- The retained inputs use retained state sorts. -/
  inputSorts {l : L.Law} : l ∈ laws →
    Declaration.sorts (L.inputContext l) ⊆ context.declarations
  /-- Every occurrence refers to a retained quantity. -/
  applicationKept {l : L.Law} : l ∈ laws → ∀ a : L.UsedOccurrence l,
    (L.application l a.val).1 ∈ quantities
  /-- The complete term of each occurrence is supported by the retained state declarations. -/
  termKept {l : L.Law} : l ∈ laws → ∀ (a : L.UsedOccurrence l) {s : P.signature.SortType}
    (i : Var (L.domainContext (L.application l a.val).1) s), Declaration.termContext ((L.application l a.val).2 i) ≤ context

namespace DeclarationSelection

variable {L} {U V : DeclarationSelection L}

/-- An inclusion forgets state declarations, quantity names and entire written Laws. -/
structure Inclusion (V U : DeclarationSelection L) where
  /-- The inclusion inducing the actual state reduct. -/
  context : V.context ≤ U.context
  /-- The retained quantity names are among the original names. -/
  quantities : V.quantities ⊆ U.quantities
  /-- The retained coefficient equations are among the original ones. -/
  laws : V.laws ⊆ U.laws

/-- A retained occurrence designates its original quantity. -/
def applicationQuantity (l : U.laws) (a : L.UsedOccurrence l.val) : U.quantities :=
  ⟨(L.application l.val a.val).1, U.applicationKept l.property a⟩

/-- Each argument of a retained occurrence is an actual supported state term. -/
def applicationTerm (l : U.laws) (a : L.UsedOccurrence l.val) {s : P.signature.SortType}
    (i : Var (L.domainContext (L.application l.val a.val).1) s) : U.context.TermIn (L.inputContext l.val) s :=
  ⟨(L.application l.val a.val).2 i, U.termKept l.property a i⟩

/-- The designated sets and the actual evaluation of every written state argument. -/
structure Interpretation (U : DeclarationSelection L) (A : ContextStructure U.context) where
  /-- The fixed argument domain of each retained quantity. -/
  domain (j : U.quantities) : Set (Assignment A.carrier (L.domainContext j.val))
  /-- The given input set for each retained coefficient Law. -/
  input (l : U.laws) : Set (Assignment A.carrier (L.inputContext l.val))
  /-- The arguments of the written application at the specified input. -/
  value (l : U.laws) (e : input l) (a : L.UsedOccurrence l.val) : domain (applicationQuantity l a)
  /-- Every argument is the evaluation of its actual fixed state term. -/
  argument (l : U.laws) (e : input l) (a : L.UsedOccurrence l.val)
    {s : P.signature.SortType} (i : Var (L.domainContext (L.application l.val a.val).1) s) :
    A.evaluates (applicationTerm l a i) e.val ((value l e a).val i)

namespace Interpretation

variable {A : ContextStructure U.context} (I : U.Interpretation A)

/-- Compile the given scalar expressions using the actual evaluated arguments. -/
def presentation : Presentation k (Selected.readStructure A) where
  Quantity := U.quantities
  Domain := fun j => I.domain j
  Law := U.laws
  Input := fun l => I.input l
  left l e := (L.left l.val).compile fun a h => ⟨applicationQuantity l ⟨a, Or.inl h⟩, I.value l e ⟨a, Or.inl h⟩⟩
  right l e := (L.right l.val).compile fun a h => ⟨applicationQuantity l ⟨a, Or.inr h⟩, I.value l e ⟨a, Or.inr h⟩⟩

variable [CommRing k]

/-- The model tests the two original written expressions at exactly the prescribed inputs. -/
theorem holds_iff_written {R : Type u} [CommRing R] [Algebra k R]
    (q : I.presentation.Candidate R) :
    I.presentation.Holds q ↔
      ∀ l (e : I.input l),
        ((L.left l.val).compile fun a h => (⟨a, Or.inl h⟩ : L.UsedOccurrence l.val)).eval
          (fun a => q (applicationQuantity l a) (I.value l e a)) =
        ((L.right l.val).compile fun a h => (⟨a, Or.inr h⟩ : L.UsedOccurrence l.val)).eval
          (fun a => q (applicationQuantity l a) (I.value l e a)) := by
  have side (l : U.laws) (e : I.input l) (p : Expression k (L.Occurrence l.val))
      (used : p.occurrences ⊆ (L.left l.val).occurrences ∪ (L.right l.val).occurrences) :
      (p.compile fun a h => (⟨applicationQuantity l ⟨a, used h⟩,
        I.value l e ⟨a, used h⟩⟩ : I.presentation.Coordinate)).eval (fun x => q x.1 x.2) =
      (p.compile fun a h => (⟨a, used h⟩ : L.UsedOccurrence l.val)).eval
        (fun a => q (applicationQuantity l a) (I.value l e a)) := by
    let coordinate (a : L.UsedOccurrence l.val) : I.presentation.Coordinate :=
      ⟨applicationQuantity l a, I.value l e a⟩
    rw [← p.rename_compile (fun a h => (⟨a, used h⟩ : L.UsedOccurrence l.val)) coordinate, Expression.eval_rename]
    rfl
  unfold Presentation.Holds
  constructor
  · intro h l e
    exact (side l e _ Set.subset_union_left).symm.trans ((h l e).trans (side l e _ Set.subset_union_right))
  · intro h l e
    exact (side l e _ Set.subset_union_left).trans ((h l e).trans (side l e _ Set.subset_union_right).symm)
variable (inside : Inclusion V U)

private def restrictDomain (j : V.quantities) :
    Set (Assignment (A.restrict inside.context).carrier (L.domainContext j.val)) :=
  (A.restrictAssignmentEquiv inside.context (V.domainSorts j.property)) ⁻¹' I.domain (Set.inclusion inside.quantities j)

private def restrictInput (l : V.laws) :
    Set (Assignment (A.restrict inside.context).carrier (L.inputContext l.val)) :=
  (A.restrictAssignmentEquiv inside.context (V.inputSorts l.property)) ⁻¹' I.input (Set.inclusion inside.laws l)

private def includeInput (l : V.laws) (e : I.restrictInput inside l) :
    I.input (Set.inclusion inside.laws l) :=
  ⟨A.restrictAssignmentEquiv inside.context (V.inputSorts l.property) e.val, e.property⟩

private def restrictValue (l : V.laws) (e : I.restrictInput inside l) (a : L.UsedOccurrence l.val) :
    I.restrictDomain inside (applicationQuantity l a) := by
  let reading := A.restrictAssignmentEquiv inside.context (V.domainSorts (applicationQuantity l a).property)
  let original := I.value (Set.inclusion inside.laws l) (I.includeInput inside l e) a
  refine ⟨reading.symm original.val, ?_⟩
  change reading (reading.symm original.val) ∈ I.domain (applicationQuantity (Set.inclusion inside.laws l) a)
  rw [reading.apply_symm_apply]
  exact original.property

/-- The retained interpretations use the actual reduct of the state structure. -/
def restrict : V.Interpretation (A.restrict inside.context) where
  domain := I.restrictDomain inside
  input := I.restrictInput inside
  value := I.restrictValue inside
  argument l e a := by
    intro s i
    let t := applicationTerm l a i
    let v := (I.restrictValue inside l e a).val
    let x := I.value (Set.inclusion inside.laws l) (I.includeInput inside l e) a
    let reading := A.restrictAssignmentEquiv inside.context (V.domainSorts (applicationQuantity l a).property)
    have mapped := congrArg (fun e : Assignment A.carrier _ => e i) (reading.apply_symm_apply x.val)
    apply (A.restrict_evaluates_iff inside.context t e.val (v i)).2
    change A.evaluates (applicationTerm (Set.inclusion inside.laws l) a i)
      (I.includeInput inside l e).val (reading v i)
    change reading v i = x.val i at mapped
    rw [mapped]
    exact I.argument (Set.inclusion inside.laws l) (I.includeInput inside l e) a i

private def quantityMap : QuantityMap (I.restrict inside).presentation I.presentation where
  name := Set.inclusion inside.quantities
  argument j x := ⟨A.restrictAssignmentEquiv inside.context (V.domainSorts j.property) x.val, x.property⟩

omit [CommRing k] in
private theorem coordinate (l : V.laws) (e : I.restrictInput inside l) (a : L.UsedOccurrence l.val) :
    (I.quantityMap inside).coordinate ⟨applicationQuantity l a, I.restrictValue inside l e a⟩ =
      ⟨applicationQuantity (Set.inclusion inside.laws l) a, I.value (Set.inclusion inside.laws l) (I.includeInput inside l e) a⟩ := by
  refine Sigma.ext rfl (heq_of_eq (Subtype.ext ?_))
  exact (A.restrictAssignmentEquiv inside.context (V.domainSorts (applicationQuantity l a).property)).apply_symm_apply _

/-- The actual declaration restriction preserves each original coefficient equation. -/
def lawMap : LawMap (I.restrict inside).presentation I.presentation where
  toQuantityMap := I.quantityMap inside
  law := Set.inclusion inside.laws
  input := I.includeInput inside
  left l e := by
    change ((L.left l.val).compile _).rename (I.quantityMap inside).coordinate =
      (L.left l.val).compile _
    rw [Expression.rename_compile]
    congr 1
    funext a h
    exact I.coordinate inside l e ⟨a, Or.inl h⟩
  right l e := by
    change ((L.right l.val).compile _).rename (I.quantityMap inside).coordinate =
      (L.right l.val).compile _
    rw [Expression.rename_compile]
    congr 1
    funext a h
    exact I.coordinate inside l e ⟨a, Or.inr h⟩

omit [CommRing k] in
/-- A retained quantity domain is read by pulling back its original domain along the carrier comparison. -/
theorem restrict_domain (j : V.quantities) :
    (I.restrict inside).domain j =
      (A.restrictAssignmentEquiv inside.context (V.domainSorts j.property)) ⁻¹'
        I.domain (Set.inclusion inside.quantities j) := rfl

omit [CommRing k] in
/-- A retained Law input set is the corresponding inverse image of its original input set. -/
theorem restrict_input (l : V.laws) :
    (I.restrict inside).input l =
      (A.restrictAssignmentEquiv inside.context (V.inputSorts l.property)) ⁻¹'
        I.input (Set.inclusion inside.laws l) := rfl

omit [CommRing k] in
/-- A quantity keeps its original name. -/
theorem lawMap_name (j : V.quantities) :
    (I.lawMap inside).name j = Set.inclusion inside.quantities j := rfl

omit [CommRing k] in
/-- The comparison sends the arguments of a retained quantity through the carrier equivalence. -/
theorem lawMap_argument (j : V.quantities) (x : (I.restrict inside).domain j) :
    ((I.lawMap inside).argument j x).val =
      A.restrictAssignmentEquiv inside.context (V.domainSorts j.property) x.val := rfl

omit [CommRing k] in
/-- The comparison sends the input of a retained Law through the same carrier equivalence. -/
theorem lawMap_input (l : V.laws) (e : (I.restrict inside).input l) :
    ((I.lawMap inside).input l e).val =
      A.restrictAssignmentEquiv inside.context (V.inputSorts l.property) e.val := rfl

/-- Declaration restriction and arbitrary coefficient change induce the same map on the Law quotient. -/
theorem lawMap_baseChange (R : Type u) [CommRing R] [Algebra k R] :
    let F := (I.restrict inside).presentation
    let ι := I.lawMap inside
    (baseChangeQuotient (R := k) R I.presentation.residualIdeal).symm.toAlgHom.comp (ι.extendedEquationMap R) =
      (ι.extendedLawMap R).comp (baseChangeQuotient (R := k) R F.residualIdeal).symm.toAlgHom :=
  (I.lawMap inside).extendedEquationMap_natural R

/-- Principal-open localization is a special case of the coefficient-change square. -/
theorem lawMap_localization (r : k) :
    let R := Localization.Away r
    let F := (I.restrict inside).presentation
    let ι := I.lawMap inside
    (baseChangeQuotient (R := k) R I.presentation.residualIdeal).symm.toAlgHom.comp (ι.extendedEquationMap R) =
      (ι.extendedLawMap R).comp (baseChangeQuotient (R := k) R F.residualIdeal).symm.toAlgHom :=
  I.lawMap_baseChange inside (Localization.Away r)

end Interpretation

end DeclarationSelection

end WrittenLaws

end

end SHIGURE.Quantities
