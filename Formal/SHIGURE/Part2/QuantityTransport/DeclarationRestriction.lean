import Formal.SHIGURE.Part1.ContextSelectedStructures
import Formal.SHIGURE.Part2.QuantityTransport.Coefficients
import Mathlib.RingTheory.Localization.Away.Basic

/-!
# Restriction of written quantity Laws along declaration contexts

Chapter 3 supplies the contexts, retained assignments, and preservation
of each supported term's evaluation. The Law expressions in §5.4 are
compiled from those terms in both contexts.

## Implementation notes

The original names index the retained Law and quantity declarations.
The interpretation takes the inverse images of the original input sets
under the retained carrier maps. It transports the actual argument
values by the retained assignment equivalences, using the term graph to
certify their evaluation. Selecting only the compiled coordinate
expressions would discard the original state declarations.
-/

open scoped TensorProduct

universe u

noncomputable section

namespace SHIGURE.Quantities

open DeclarationContext

/-- Fixed quantity equations using the original quantity and Law declarations. -/
structure DeclaredQuantityLaws (k : Type u) (P : PrimitivePresentation.{u}) where
  /-- Names of the quantity applications in each written equality. -/
  Occurrence : P.laws.LawName → Type u
  /-- A named quantity and the typed state terms for its arguments. -/
  application (l : P.laws.LawName) : Occurrence l →
    Σ j : P.signature.Quantity,
      Substitution P.signature (P.signature.quantityArity j).inputs (P.laws.statement l).context
  /-- The written left side over the named applications. -/
  left (l : P.laws.LawName) : Expression k (Occurrence l)
  /-- The written right side over the named applications. -/
  right (l : P.laws.LawName) : Expression k (Occurrence l)

namespace DeclaredQuantityLaws

variable {k : Type u} {P : PrimitivePresentation.{u}} (L : DeclaredQuantityLaws k P)
variable {U V : DeclarationContext P}

/-- A quantity of the original signature retained in this declaration context. -/
abbrev KeptQuantity (U : DeclarationContext P) :=
  {j : P.signature.Quantity // Declaration.quantity j ∈ U.declarations}

/-- A retained Law keeps the quantities and state terms of both written expressions. -/
abbrev KeptLaw (U : DeclarationContext P) :=
  {l : P.laws.LawName //
    Declaration.law l ∈ U.declarations ∧
      ∀ a : L.Occurrence l,
        Declaration.quantity (L.application l a).1 ∈ U.declarations ∧
          ∀ {s} (i : Var (P.signature.quantityArity (L.application l a).1).inputs s),
            Declaration.termContext ((L.application l a).2 i) ≤ U}

/-- The full declaration context retains every written quantitative Law. -/
def keptLaw_full (l : P.laws.LawName) : L.KeptLaw (DeclarationContext.full P) :=
  ⟨l, Set.mem_univ _, fun _ => ⟨Set.mem_univ _, by
    intro s i d _
    exact Set.mem_univ d⟩⟩

/-- A Law cannot survive a context that forgets a state term in one of its written applications. -/
theorem not_keptLaw_of_missingTerm (l : P.laws.LawName) (a : L.Occurrence l)
    {s : P.signature.SortType} (i : Var (P.signature.quantityArity (L.application l a).1).inputs s)
    (lost : ¬ Declaration.termContext ((L.application l a).2 i) ≤ U) :
    ¬ ∃ kept : L.KeptLaw U, kept.val = l := by
  rintro ⟨⟨_, support⟩, rfl⟩
  exact lost ((support.2 a).2 i)

/-- The same requirement applies to the quantity's name, independently of the Law's input set. -/
theorem not_keptLaw_of_missingQuantity (l : P.laws.LawName) (a : L.Occurrence l)
    (lost : Declaration.quantity (L.application l a).1 ∉ U.declarations) :
    ¬ ∃ kept : L.KeptLaw U, kept.val = l := by
  rintro ⟨⟨_, support⟩, rfl⟩
  exact lost (support.2 a).1

/-- The quantity name of a retained application is retained in the same context. -/
def keptApplication (l : L.KeptLaw U) (a : L.Occurrence l.val) : KeptQuantity U :=
  ⟨(L.application l.val a).1, (l.property.2 a).1⟩

/-- Each argument term of a retained application is a term of the declaration context. -/
def keptTerm (l : L.KeptLaw U) (a : L.Occurrence l.val) {s : P.signature.SortType}
    (i : Var (P.signature.quantityArity (L.keptApplication l a).val).inputs s) :
    U.TermIn (P.laws.statement l.val).context s :=
  ⟨(L.application l.val a).2 i, (l.property.2 a).2 i⟩

/-- The input sorts of a retained Law survive by dependency closure. -/
theorem keptLaw_sorts (l : L.KeptLaw U) :
    Declaration.sorts (P.laws.statement l.val).context ⊆ U.declarations :=
  lawSortSupport (Declaration.lawBody_subset_of_mem l.property.1)

/-- The required argument sorts of a retained quantity survive by dependency closure. -/
theorem keptQuantity_sorts (j : KeptQuantity U) :
    Declaration.sorts (P.signature.quantityArity j.val).inputs ⊆ U.declarations :=
  operationInputs (.quantity j.val) (by simpa only [Declaration.ofOperation_quantity] using j.property)

/-- Inclusion of declaration contexts retains every dependency of the written equation. -/
def includeLaw (inside : V ≤ U) (l : L.KeptLaw V) : L.KeptLaw U :=
  ⟨l.val, inside l.property.1, fun a =>
    ⟨inside (l.property.2 a).1, fun i => ((l.property.2 a).2 i).trans inside⟩⟩

/-- Fixed input sets and the evaluated arguments of each application in a contextual structure. -/
structure Interpretation (A : ContextStructure U) where
  /-- The fixed domain on each retained quantity's actual carrier product. -/
  domain (j : KeptQuantity U) :
    Set (Assignment A.carrier (P.signature.quantityArity j.val).inputs)
  /-- The prescribed input set of each retained written Law. -/
  input (l : L.KeptLaw U) : Set (Assignment A.carrier (P.laws.statement l.val).context)
  /-- At each prescribed input the evaluated argument tuple belongs to the quantity domain. -/
  value (l : L.KeptLaw U) (e : input l) (a : L.Occurrence l.val) :
    domain (L.keptApplication l a)
  /-- Each coordinate is the actual evaluation of its supported state term. -/
  evaluates (l : L.KeptLaw U) (e : input l) (a : L.Occurrence l.val) {s : P.signature.SortType}
    (i : Var (P.signature.quantityArity (L.keptApplication l a).val).inputs s) :
    A.evaluates (L.keptTerm l a i) e.val ((value l e a).val i)

/-- Obtain the argument tuples from definedness at the prescribed inputs in the contextual structure. -/
def Interpretation.ofDefined (A : ContextStructure U)
    (domain : ∀ j : KeptQuantity U, Set (Assignment A.carrier (P.signature.quantityArity j.val).inputs))
    (input : ∀ l : L.KeptLaw U, Set (Assignment A.carrier (P.laws.statement l.val).context))
    (w : ∀ (l : L.KeptLaw U) (e : input l) (a : L.Occurrence l.val),
      ∃ x : domain (L.keptApplication l a), ∀ {s} (i : Var (P.signature.quantityArity (L.keptApplication l a).val).inputs s),
        A.evaluates (L.keptTerm l a i) e.val (x.val i)) :
    L.Interpretation A where
  domain := domain
  input := input
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
  Input := fun l => I.input l
  left l e := (L.left l.val).rename (fun a => ⟨L.keptApplication l a, I.value l e a⟩)
  right l e := (L.right l.val).rename (fun a => ⟨L.keptApplication l a, I.value l e a⟩)

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

/-- The retained Law input set comes from the same written Law in the ambient structure. -/
private def restrictInput (l : L.KeptLaw V) :
    Set (Assignment (A.restrict inside).carrier (P.laws.statement l.val).context) :=
  (assignmentEquiv (A := A) inside (L.keptLaw_sorts l)) ⁻¹' I.input (L.includeLaw inside l)

/-- The image of a retained Law input in the original input set. -/
private def includeInput (l : L.KeptLaw V) (e : I.restrictInput inside l) :
    I.input (L.includeLaw inside l) :=
  ⟨assignmentEquiv (A := A) inside (L.keptLaw_sorts l) e.val, e.property⟩

/-- The original value tuple transported to the carriers of the actual reduct. -/
private def restrictValue (l : L.KeptLaw V) (e : I.restrictInput inside l) (a : L.Occurrence l.val) :
    I.restrictDomain inside (L.keptApplication l a) := by
  let value := I.value (L.includeLaw inside l) (I.includeInput inside l e) a
  let reads := assignmentEquiv (A := A) inside (keptQuantity_sorts (L.keptApplication l a))
  exact ⟨reads.symm value.val, by
    change reads (reads.symm value.val) ∈ I.domain (L.keptApplication (L.includeLaw inside l) a)
    rw [reads.apply_symm_apply]
    exact value.property⟩

/-- The restricted interpretation evaluates the same supported terms in the actual reduct. -/
def restrict : L.Interpretation (A.restrict inside) where
  domain := I.restrictDomain inside
  input := I.restrictInput inside
  value := I.restrictValue inside
  evaluates l e a := by
    intro s i
    apply (A.restrict_evaluates_iff inside (L.keptTerm l a i) _ _).2
    have same := (assignmentEquiv (A := A) inside (keptQuantity_sorts (L.keptApplication l a))).apply_symm_apply
      (I.value (L.includeLaw inside l) (I.includeInput inside l e) a).val
    have atIndex := congrArg (fun x : Assignment A.carrier _ => x i) same
    change selectedMap V A.carrier s (varKept (keptQuantity_sorts (L.keptApplication l a)) i)
      ((I.restrictValue inside l e a).val i) =
        (I.value (L.includeLaw inside l) (I.includeInput inside l e) a).val i at atIndex
    rw [atIndex]
    exact I.evaluates (L.includeLaw inside l) (I.includeInput inside l e) a i

/-- The map on retained quantity arguments reads their values in the ambient carriers. -/
private def declarationQuantityMap : QuantityMap (I.restrict inside).presentation I.presentation where
  name j := ⟨j.val, inside j.property⟩
  argument j x := ⟨assignmentEquiv (A := A) inside (keptQuantity_sorts j) x.val, x.property⟩

/-- The declaration comparison sends each evaluated retained argument to the original one. -/
private theorem declarationCoordinate (l : L.KeptLaw V) (e : I.restrictInput inside l) (a : L.Occurrence l.val) :
    (I.declarationQuantityMap inside).coordinate ⟨L.keptApplication l a, I.restrictValue inside l e a⟩ =
      ⟨L.keptApplication (L.includeLaw inside l) a, I.value (L.includeLaw inside l) (I.includeInput inside l e) a⟩ := by
  refine Sigma.ext ?_ ?_
  · rfl
  apply heq_of_eq
  apply Subtype.ext
  exact (assignmentEquiv (A := A) inside (keptQuantity_sorts (L.keptApplication l a))).apply_symm_apply _

/-- The actual declaration restriction induces the comparison of quantity Law models in §5.4. -/
def declarationLawMap : LawMap (I.restrict inside).presentation I.presentation where
  toQuantityMap := I.declarationQuantityMap inside
  law := L.includeLaw inside
  input := I.includeInput inside
  left l e := by
    change ((L.left l.val).rename (fun a => ⟨L.keptApplication l a, I.restrictValue inside l e a⟩)).rename
      (I.declarationQuantityMap inside).coordinate = _
    rw [Expression.rename_comp]
    exact congrArg (fun f => (L.left l.val).rename f) (funext (I.declarationCoordinate inside l e))
  right l e := by
    change ((L.right l.val).rename (fun a => ⟨L.keptApplication l a, I.restrictValue inside l e a⟩)).rename
      (I.declarationQuantityMap inside).coordinate = _
    rw [Expression.rename_comp]
    exact congrArg (fun f => (L.right l.val).rename f) (funext (I.declarationCoordinate inside l e))

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
