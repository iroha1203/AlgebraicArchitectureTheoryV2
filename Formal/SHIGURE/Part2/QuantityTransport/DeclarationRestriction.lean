import Formal.SHIGURE.Part1.ContextSelectedStructures
import Formal.SHIGURE.Part1.MarkedLawSupport
import Formal.SHIGURE.Part2.QuantityTransport.Coefficients
import Mathlib.RingTheory.Localization.Away.Basic

/-!
# Restriction of written quantity Laws along declaration contexts

Chapter 3 supplies the contexts, retained assignments, and preservation
of each supported term's evaluation. The Law expressions in §5.4 are
compiled from those terms in both contexts.

## Implementation notes

The original names index the retained Law and quantity declarations.
The interpretation reads the original antecedent and transports the
quantity domains along the retained carrier maps. It transports the actual argument
values by the retained assignment equivalences, using the term graph to
certify their evaluation. Selecting only the compiled coordinate
expressions would discard the original state declarations.
-/

open scoped TensorProduct

universe u

noncomputable section

namespace SHIGURE.Quantities

open DeclarationContext

namespace Expression

variable {C k X Y Z : Type u}

/-- The labels of the quantity applications actually occurring in a finite expression. -/
def applications : Expression C X → Set X
  | .scalar _ => ∅
  | .quantity x => {x}
  | .add l r | .mul l r => l.applications ∪ r.applications
  | .neg x => x.applications

/-- Compile the scalar literals and only the quantity applications appearing in the expression. -/
def compile (scalar : C → k) :
    (e : Expression C X) → (∀ x ∈ e.applications, Y) → Expression k Y
  | .scalar a, _ => .scalar (scalar a)
  | .quantity x, f => .quantity (f x (Set.mem_singleton x))
  | .add l r, f => .add (compile scalar l (fun x h => f x (Or.inl h)))
      (compile scalar r (fun x h => f x (Or.inr h)))
  | .neg x, f => .neg (compile scalar x f)
  | .mul l r, f => .mul (compile scalar l (fun x h => f x (Or.inl h)))
      (compile scalar r (fun x h => f x (Or.inr h)))

/-- An application mapping after compilation is the same mapping on the actual leaves. -/
theorem rename_compile (scalar : C → k) (e : Expression C X)
    (f : ∀ x ∈ e.applications, Y) (g : Y → Z) :
    (e.compile scalar f).rename g = e.compile scalar (fun x h => g (f x h)) := by
  induction e <;> simp [compile, rename, *]
  rfl

end Expression

/-- A coefficient vocabulary renders literals and arithmetic as named terms of the signature.
Only the scalar literals supplied by the vocabulary need declared symbols. -/
structure CoefficientSyntax (k : Type u) (sig : Signature.{u}) where
  /-- The result sort of the coefficient expressions. -/
  sort : sig.SortType
  /-- The written literal names and their coefficients. -/
  Literal : Type u
  value : Literal → k
  /-- Each literal denotes a distinct declared nullary operation. -/
  literal : Literal ↪ sig.Total
  literalArity : ∀ a, sig.totalArity (literal a) = ⟨[], sort⟩
  /-- The declared ring operations used in the equality. -/
  add : TypedTotal sig ⟨[sort, sort], sort⟩
  neg : TypedTotal sig ⟨[sort], sort⟩
  mul : TypedTotal sig ⟨[sort, sort], sort⟩

namespace CoefficientSyntax

variable {k : Type u} {sig : Signature.{u}} (C : CoefficientSyntax k sig)
variable {Γ : List sig.SortType}

/-- A named quantity of the coefficient sort applied to a tuple of original state terms. -/
abbrev Application (Γ : List sig.SortType) :=
  Σ j : {j : sig.Quantity // (sig.quantityArity j).output = C.sort},
    Substitution sig (sig.quantityArity j.val).inputs Γ

/-- The typed term denoted by a quantity application. -/
def applicationTerm (a : C.Application Γ) : Term sig Γ C.sort :=
  cast (congrArg (Term sig Γ) a.1.property) (.app (.quantity a.1.val) (fun i => a.2 i))

/-- The literal equality can be read as an ordinary typed term equality of the presentation. -/
def term (C : CoefficientSyntax k sig) : Expression C.Literal (C.Application Γ) → Term sig Γ C.sort
  | .scalar a => (TypedTotal.mk (.ordinary (C.literal a)) (C.literalArity a)).term Term.argsNil
  | .quantity a => C.applicationTerm a
  | .add x y => C.add.term ((term C x).argsCons ((term C y).argsCons Term.argsNil))
  | .neg x => C.neg.term ((term C x).argsCons Term.argsNil)
  | .mul x y => C.mul.term ((term C x).argsCons ((term C y).argsCons Term.argsNil))

end CoefficientSyntax

/-- The fixed family of required quantity equations in the original presentation.
The same presentation may also contain state Laws. -/
structure DeclaredQuantityLaws (k : Type u) (P : PrimitivePresentation.{u}) where
  coefficients : CoefficientSyntax k P.signature
  /-- The required Law declarations that serve as the quantity equations of §5.1. -/
  quantityLaw : Set P.theory.LawName
  /-- The two sides of each designated equation, with the applications as actual leaves. -/
  left (l : quantityLaw) :
    Expression coefficients.Literal (coefficients.Application (P.theory.law l.val).context)
  right (l : quantityLaw) :
    Expression coefficients.Literal (coefficients.Application (P.theory.law l.val).context)
  /-- The expressions present the conclusion of that very Law declaration. -/
  conclusion (l : quantityLaw) :
    (P.theory.law l.val).conclusion =
      Formula.termEq (coefficients.term (left l)) (coefficients.term (right l))

namespace DeclaredQuantityLaws

variable {k : Type u} {P : PrimitivePresentation.{u}} (L : DeclaredQuantityLaws k P)
variable {U V : DeclarationContext P}

/-- A quantity of the original signature retained in this declaration context. -/
abbrev KeptQuantity (U : DeclarationContext P) :=
  {j : P.signature.Quantity // Declaration.quantity j ∈ U.declarations}

/-- The Chapter 3 selection of required Laws, within the fixed quantity Law family. -/
abbrev KeptLaw (U : DeclarationContext P) :=
  {l : L.quantityLaw // Declaration.law l.val.val ∈ U.declarations}

/-- The full declaration context retains every required quantity Law. -/
def keptLaw_full (l : L.quantityLaw) : L.KeptLaw (DeclarationContext.full P) :=
  ⟨l, Set.mem_univ _⟩

/-- The selected quantity Law is a selected rule in the contextual theory. -/
def KeptLaw.scoped (l : L.KeptLaw U) : U.scopedTheory.LawName :=
  ⟨l.val.val, l.property⟩

/-- The actual quantity applications of the original two sides. -/
abbrev UsedApplication (l : L.quantityLaw) :=
  {a : L.coefficients.Application (P.theory.law l.val).context //
    a ∈ (L.left l).applications ∪ (L.right l).applications}

/-- The input sorts of a retained Law survive by dependency closure. -/
theorem keptLaw_sorts (l : L.KeptLaw U) :
    Declaration.sorts (P.theory.law l.val.val).context ⊆ U.declarations :=
  lawSortSupport (Declaration.lawBody_subset_of_mem l.property)

/-- The references of an argument are present in the corresponding operation term. -/
private theorem refs_typedArg {profile : Arity P.signature.SortType}
    {Γ : List P.signature.SortType} (op : TypedTotal P.signature profile)
    (args : ∀ {s}, Var profile.inputs s → Term P.signature Γ s)
    {s : P.signature.SortType} (i : Var profile.inputs s) :
    Selected.termReferences (args i) ⊆ Selected.termReferences (op.term args) := by
  rcases op with ⟨symbol, same⟩
  subst profile
  intro d used
  change d ∈ Selected.termReferences (.app symbol.operation args)
  exact Or.inr ⟨_, i, used⟩

private theorem refs_castResult {Γ : List P.signature.SortType} {s t : P.signature.SortType}
    (h : s = t) (x : Term P.signature Γ s) :
    Selected.termReferences (cast (congrArg (Term P.signature Γ) h) x) =
      Selected.termReferences x := by
  cases h
  rfl

/-- An actual application contributes its quantity name and all its argument references. -/
private theorem application_refs {Γ : List P.signature.SortType}
    (C : CoefficientSyntax k P.signature) (e : Expression C.Literal (C.Application Γ))
    {a : C.Application Γ} (used : a ∈ e.applications) :
    Selected.termReferences (C.applicationTerm a) ⊆ Selected.termReferences (C.term e) := by
  induction e with
  | scalar c => exact False.elim used
  | quantity x =>
    obtain rfl := Set.mem_singleton_iff.mp used
    exact Set.Subset.rfl
  | add x y hx hy =>
    rcases used with h | h
    · exact (hx h).trans (refs_typedArg C.add (fun i => (C.term x).argsCons ((C.term y).argsCons Term.argsNil) i) .here)
    · exact (hy h).trans (refs_typedArg C.add (fun i => (C.term x).argsCons ((C.term y).argsCons Term.argsNil) i) (.there .here))
  | neg x hx => exact (hx used).trans (refs_typedArg C.neg (fun i => (C.term x).argsCons Term.argsNil i) .here)
  | mul x y hx hy =>
    rcases used with h | h
    · exact (hx h).trans (refs_typedArg C.mul (fun i => (C.term x).argsCons ((C.term y).argsCons Term.argsNil) i) .here)
    · exact (hy h).trans (refs_typedArg C.mul (fun i => (C.term x).argsCons ((C.term y).argsCons Term.argsNil) i) (.there .here))

private theorem keptApplication_refs (l : L.KeptLaw U) (a : L.UsedApplication l.val) :
    Selected.termReferences (Term.app (.quantity a.val.1.val) (fun i => a.val.2 i)) ⊆ U.declarations := by
  have written := lawConclusionSupport (Declaration.lawBody_subset_of_mem l.property)
  change Declaration.formulaSupport (P.theory.law l.val.val).conclusion ⊆ U.declarations at written
  rw [L.conclusion] at written
  have refs := Selected.termEq_support _ _ written
  have kept : Selected.termReferences (L.coefficients.applicationTerm a.val) ⊆ U.declarations :=
    a.property.elim (fun h => (application_refs _ _ h).trans refs.2.1)
      (fun h => (application_refs _ _ h).trans refs.2.2)
  unfold CoefficientSyntax.applicationTerm at kept
  rw [refs_castResult (P := P) a.val.1.property
    (Term.app (.quantity a.val.1.val) (fun i => a.val.2 i))] at kept
  exact kept

/-- The written Law's dependency closure contains the quantity of each actual application. -/
def keptApplication (l : L.KeptLaw U) (a : L.UsedApplication l.val) : KeptQuantity U :=
  ⟨a.val.1.val, L.keptApplication_refs l a (Or.inl (Set.mem_singleton _))⟩

/-- References and retained input and result sorts suffice for the support of a term graph. -/
private theorem termContext_le {Γ : List P.signature.SortType} {s : P.signature.SortType}
    (t : Term P.signature Γ s) (context : Declaration.sorts Γ ⊆ U.declarations)
    (result : Declaration.sort s ∈ U.declarations)
    (refs : Selected.termReferences t ⊆ U.declarations) : Declaration.termContext t ≤ U := by
  have equality := lawConclusionSupport (Marked.equality_law_support t t operationInputs context result refs refs)
  change Declaration.formulaSupport (Formula.termEq t t) ⊆ U.declarations at equality
  rw [Formula.termEq_eq_ex] at equality
  apply (Declaration.termContext_le_iff t).2
  exact (Declaration.binarySupport_left (Declaration.formula_conj t.graph t.graph)).trans
    ((Declaration.formulaSupport_ex_body _).trans equality)

/-- Each argument of an actual application is retained by the written Law's dependency closure. -/
def keptTerm (l : L.KeptLaw U) (a : L.UsedApplication l.val) {s : P.signature.SortType}
    (i : Var (P.signature.quantityArity (L.keptApplication l a).val).inputs s) :
    U.TermIn (P.theory.law l.val.val).context s :=
  ⟨a.val.2 i, termContext_le _ (L.keptLaw_sorts l)
    (varKept (operationInputs (.quantity a.val.1.val) (L.keptApplication l a).property) i)
    (fun _ used => L.keptApplication_refs l a (Or.inr ⟨_, i, used⟩))⟩

/-- The required argument sorts of a retained quantity survive by dependency closure. -/
theorem keptQuantity_sorts (j : KeptQuantity U) :
    Declaration.sorts (P.signature.quantityArity j.val).inputs ⊆ U.declarations :=
  operationInputs (.quantity j.val) (by simpa only [Declaration.ofOperation_quantity] using j.property)

/-- Inclusion keeps precisely the same original required Law and its written equation. -/
def includeLaw (inside : V ≤ U) (l : L.KeptLaw V) : L.KeptLaw U :=
  ⟨l.val, inside l.property⟩

/-- The original required Law's input set, read on the fixed state structure. -/
def lawInput (A : ContextStructure U) (l : L.KeptLaw U) :
    Set (Assignment A.carrier (P.theory.law l.val.val).context) :=
  {e | A.evaluation.holds (P.theory.law l.val.val).input
    (lawInputSupport (Declaration.lawBody_subset_of_mem l.property)) e}

/-- The quantity domains and evaluated arguments on the original required input sets. -/
structure Interpretation (A : ContextStructure U) where
  /-- The fixed domain on each retained quantity's actual carrier product. -/
  domain (j : KeptQuantity U) :
    Set (Assignment A.carrier (P.signature.quantityArity j.val).inputs)
  /-- At each prescribed input the evaluated tuple of each actual application is in its domain. -/
  value (l : L.KeptLaw U) (e : L.lawInput A l) (a : L.UsedApplication l.val) :
    domain (L.keptApplication l a)
  /-- Each coordinate is the actual evaluation of its supported state term. -/
  evaluates (l : L.KeptLaw U) (e : L.lawInput A l) (a : L.UsedApplication l.val) {s : P.signature.SortType}
    (i : Var (P.signature.quantityArity (L.keptApplication l a).val).inputs s) :
    A.evaluates (L.keptTerm l a i) e.val ((value l e a).val i)

/-- Obtain the argument tuples from definedness on the original Law inputs. -/
def Interpretation.ofDefined (A : ContextStructure U)
    (domain : ∀ j : KeptQuantity U, Set (Assignment A.carrier (P.signature.quantityArity j.val).inputs))
    (w : ∀ (l : L.KeptLaw U) (e : L.lawInput A l) (a : L.UsedApplication l.val),
      ∃ x : domain (L.keptApplication l a), ∀ {s} (i : Var (P.signature.quantityArity (L.keptApplication l a).val).inputs s),
        A.evaluates (L.keptTerm l a i) e.val (x.val i)) :
    L.Interpretation A where
  domain := domain
  value l e a := (w l e a).choose
  evaluates l e a := by
    intro s i
    exact (w l e a).choose_spec i

namespace Interpretation

variable {L} {A : ContextStructure U} (I : L.Interpretation A)

/-- Read the finite expressions using their actual state arguments. -/
def presentation : Presentation k (Selected.readStructure A) where
  Quantity := KeptQuantity U
  Domain := fun j => I.domain j
  Law := L.KeptLaw U
  Input := fun l => L.lawInput A l
  left l e := (L.left l.val).compile L.coefficients.value fun a h =>
    ⟨L.keptApplication l ⟨a, Or.inl h⟩, I.value l e ⟨a, Or.inl h⟩⟩
  right l e := (L.right l.val).compile L.coefficients.value fun a h =>
    ⟨L.keptApplication l ⟨a, Or.inr h⟩, I.value l e ⟨a, Or.inr h⟩⟩

variable (inside : V ≤ U)

/-- A supported tuple in the actual reduct has the same assigned values in the ambient structure. -/
private def assignmentEquiv {Γ : List P.signature.SortType}
    (support : Declaration.sorts Γ ⊆ V.declarations) :
    Assignment (A.restrict inside).carrier Γ ≃ Assignment A.carrier Γ :=
  Equiv.ofBijective (mapAssignment (selectedMap V A.carrier) support) (by
    refine ⟨?_, mapAssignment_surjective _ (fun s hs => (selectedMap_bijective A.carrier s hs).2) _⟩
    intro a b same
    apply Assignment.ext
    intro s i
    exact (selectedMap_bijective A.carrier s (varKept support i)).1
      (congrArg (fun e : Assignment A.carrier Γ => e i) same))

/-- The domain of a retained quantity is transported along the retained carrier identification. -/
private def restrictDomain (j : KeptQuantity V) :
    Set (Assignment (A.restrict inside).carrier (P.signature.quantityArity j.val).inputs) :=
  (assignmentEquiv (A := A) inside (keptQuantity_sorts j)) ⁻¹' I.domain ⟨j.val, inside j.property⟩

/-- The original antecedent has the same truth on the corresponding ambient assignment. -/
theorem restrict_lawInput_iff (l : L.KeptLaw V)
    (e : Assignment (A.restrict inside).carrier (P.theory.law l.val.val).context) :
    e ∈ L.lawInput (A.restrict inside) l ↔
      mapAssignment (selectedMap V A.carrier) (L.keptLaw_sorts l) e ∈ L.lawInput A (L.includeLaw inside l) :=
  A.restrict_holds_iff inside _ _ e

/-- The image of a retained input in the original antecedent's input set. -/
private def includeInput (l : L.KeptLaw V) (e : L.lawInput (A.restrict inside) l) :
    L.lawInput A (L.includeLaw inside l) :=
  ⟨assignmentEquiv (A := A) inside (L.keptLaw_sorts l) e.val,
    (restrict_lawInput_iff inside l e.val).1 e.property⟩

/-- The original value tuple transported to the carriers of the actual reduct. -/
private def restrictValue (l : L.KeptLaw V) (e : L.lawInput (A.restrict inside) l) (a : L.UsedApplication l.val) :
    I.restrictDomain inside (L.keptApplication l a) := by
  let value := I.value (L.includeLaw inside l) (includeInput inside l e) a
  let reads := assignmentEquiv (A := A) inside (keptQuantity_sorts (L.keptApplication l a))
  exact ⟨reads.symm value.val, by
    change reads (reads.symm value.val) ∈ I.domain (L.keptApplication (L.includeLaw inside l) a)
    rw [reads.apply_symm_apply]
    exact value.property⟩

/-- The restricted interpretation evaluates the same supported terms in the actual reduct. -/
def restrict : L.Interpretation (A.restrict inside) where
  domain := I.restrictDomain inside
  value := I.restrictValue inside
  evaluates l e a := by
    intro s i
    apply (A.restrict_evaluates_iff inside (L.keptTerm l a i) _ _).2
    have same := (assignmentEquiv (A := A) inside (keptQuantity_sorts (L.keptApplication l a))).apply_symm_apply
      (I.value (L.includeLaw inside l) (includeInput inside l e) a).val
    have atIndex := congrArg (fun x : Assignment A.carrier _ => x i) same
    change selectedMap V A.carrier s (varKept (keptQuantity_sorts (L.keptApplication l a)) i)
      ((I.restrictValue inside l e a).val i) =
        (I.value (L.includeLaw inside l) (includeInput inside l e) a).val i at atIndex
    rw [atIndex]
    exact I.evaluates (L.includeLaw inside l) (includeInput inside l e) a i

/-- The map on retained quantity arguments reads their values in the ambient carriers. -/
private def declarationQuantityMap : QuantityMap (I.restrict inside).presentation I.presentation where
  name j := ⟨j.val, inside j.property⟩
  argument j x := ⟨assignmentEquiv (A := A) inside (keptQuantity_sorts j) x.val, x.property⟩

/-- The declaration comparison sends each evaluated retained argument to the original one. -/
private theorem declarationCoordinate (l : L.KeptLaw V) (e : L.lawInput (A.restrict inside) l) (a : L.UsedApplication l.val) :
    (I.declarationQuantityMap inside).coordinate ⟨L.keptApplication l a, I.restrictValue inside l e a⟩ =
      ⟨L.keptApplication (L.includeLaw inside l) a, I.value (L.includeLaw inside l) (includeInput inside l e) a⟩ := by
  refine Sigma.ext ?_ ?_
  · rfl
  apply heq_of_eq
  apply Subtype.ext
  exact (assignmentEquiv (A := A) inside (keptQuantity_sorts (L.keptApplication l a))).apply_symm_apply _

/-- The actual declaration restriction induces the comparison of quantity Law models in §5.4. -/
def declarationLawMap : LawMap (I.restrict inside).presentation I.presentation where
  toQuantityMap := I.declarationQuantityMap inside
  law := L.includeLaw inside
  input := fun l e => includeInput (A := A) inside l e
  left l e := by
    change ((L.left l.val).compile L.coefficients.value (fun a h =>
      ⟨L.keptApplication l ⟨a, Or.inl h⟩, I.restrictValue inside l e ⟨a, Or.inl h⟩⟩)).rename
      (I.declarationQuantityMap inside).coordinate = _
    rw [Expression.rename_compile]
    congr 1
    funext a h
    exact I.declarationCoordinate inside l e ⟨a, Or.inl h⟩
  right l e := by
    change ((L.right l.val).compile L.coefficients.value (fun a h =>
      ⟨L.keptApplication l ⟨a, Or.inr h⟩, I.restrictValue inside l e ⟨a, Or.inr h⟩⟩)).rename
      (I.declarationQuantityMap inside).coordinate = _
    rw [Expression.rename_compile]
    congr 1
    funext a h
    exact I.declarationCoordinate inside l e ⟨a, Or.inr h⟩

variable [CommRing k]

/-- Declaration restriction along the Chapter 3 context inclusion commutes with changing coefficients. -/
theorem declarationLawMap_baseChange (R : Type u) [CommRing R] [Algebra k R] :
    let F := (I.restrict inside).presentation
    let ι := I.declarationLawMap inside
    (baseChangeQuotient (R := k) R I.presentation.residualIdeal).symm.toAlgHom.comp (ι.extendedEquationMap R) =
      (ι.extendedLawMap R).comp (baseChangeQuotient (R := k) R F.residualIdeal).symm.toAlgHom :=
  (I.declarationLawMap inside).extendedEquationMap_natural R

/-- The same square for the coefficient restriction to the principal open of `r`. -/
theorem declarationLawMap_localization (r : k) :
    let R := Localization.Away r
    let F := (I.restrict inside).presentation
    let ι := I.declarationLawMap inside
    (baseChangeQuotient (R := k) R I.presentation.residualIdeal).symm.toAlgHom.comp (ι.extendedEquationMap R) =
      (ι.extendedLawMap R).comp (baseChangeQuotient (R := k) R F.residualIdeal).symm.toAlgHom :=
  I.declarationLawMap_baseChange inside (Localization.Away r)

end Interpretation
end DeclaredQuantityLaws
end SHIGURE.Quantities
