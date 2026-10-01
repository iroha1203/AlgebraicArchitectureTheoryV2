import ResearchLean.AG.RelativeRepairComposition.SubdivisionGeometry

/-!
# Actual categorical objects and arrows at retained names and the two factors

The construction retains every arbitrary original arrow separately from its
reference. The same construction applies to total arrows and projected arrows.

## Implementation notes

Dependent incidence proofs transport each named arrow to its indexed endpoints.
The old branch uses the full original Sigma name and the factor branches use
only their actual endpoint arrows. Treating all remaining arrows as references
was rejected: original core choices may differ, and their inverse reconstruction
must keep the same original input arrow.
-/
namespace AAT.AG.RelativeRepairComposition.Subdivision
open CategoryTheory TransportCoherence
universe uG uE vE
variable (K : FiniteTransportPresentation.{uG}) (chosen : EdgeName (K := K))
variable {E : Type uE} [Category.{vE} E]

/-- Every old object is retained and the fresh vertex carries the specified actual middle object. -/
def objectAssignment (X : K.Vertex → E) (middle : E) : Vertex K → E :=
  Sum.elim X (fun _ => middle)

/-- All retained original arrows and both actual factor arrows, at their complete indexed endpoints. -/
def edgeAssignment (X : K.Vertex → E) (middle : E)
    (old : ∀ {i j : K.Vertex}, K.Edge i j → (X i ⟶ X j))
    (first : X chosen.1 ⟶ middle) (second : middle ⟶ X chosen.2.1)
    {i j : Vertex K} (e : Edge K chosen i j) :
    objectAssignment K X middle i ⟶ objectAssignment K X middle j := by
  let a : objectAssignment K X middle (source K chosen e.1) ⟶
      objectAssignment K X middle (target K chosen e.1) := match e.1 with
    | .inl n => old n.1.2.2
    | .inr false => first
    | .inr true => second
  exact eqToHom (congrArg (objectAssignment K X middle) e.2.1).symm ≫ a ≫
    eqToHom (congrArg (objectAssignment K X middle) e.2.2)

omit [Category.{vE} E] in
/-- The actual object at every old named vertex is unchanged. -/
theorem objectAssignment_old (X : K.Vertex → E) (middle : E) (v : K.Vertex) :
    objectAssignment K X middle (.inl v) = X v := rfl

omit [Category.{vE} E] in
/-- The fresh vertex has exactly the supplied actual intermediate object. -/
theorem objectAssignment_middle (X : K.Vertex → E) (middle : E) :
    objectAssignment K X middle (.inr ()) = middle := rfl

/-- Each retained original indexed edge is the same arbitrary actual original arrow. -/
theorem edgeAssignment_old (X : K.Vertex → E) (middle : E)
    (old : ∀ {i j : K.Vertex}, K.Edge i j → (X i ⟶ X j))
    (first : X chosen.1 ⟶ middle) (second : middle ⟶ X chosen.2.1)
    (e : EdgeName (K := K)) (he : e ≠ chosen) :
    edgeAssignment K chosen X middle old first second (oldEdge K chosen e he) = old e.2.2 := by
  simp [edgeAssignment,oldEdge,source,target,objectAssignment]

/-- The first named factor evaluates to the supplied actual first arrow. -/
theorem edgeAssignment_first (X : K.Vertex → E) (middle : E)
    (old : ∀ {i j : K.Vertex}, K.Edge i j → (X i ⟶ X j))
    (first : X chosen.1 ⟶ middle) (second : middle ⟶ X chosen.2.1) :
    edgeAssignment K chosen X middle old first second (firstEdge K chosen) = first := by
  simp [edgeAssignment,firstEdge,source,target,objectAssignment]

/-- The second named factor evaluates to the supplied actual second arrow. -/
theorem edgeAssignment_second (X : K.Vertex → E) (middle : E)
    (old : ∀ {i j : K.Vertex}, K.Edge i j → (X i ⟶ X j))
    (first : X chosen.1 ⟶ middle) (second : middle ⟶ X chosen.2.1) :
    edgeAssignment K chosen X middle old first second (secondEdge K chosen) = second := by
  simp [edgeAssignment,secondEdge,source,target,objectAssignment]

end AAT.AG.RelativeRepairComposition.Subdivision
#assert_standard_axioms_only AAT.AG.RelativeRepairComposition.Subdivision
