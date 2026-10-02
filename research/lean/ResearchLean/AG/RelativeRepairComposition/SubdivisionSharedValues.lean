import ResearchLean.AG.RelativeRepairComposition.SubdivisionPermissions
import ResearchLean.AG.RelativeRepairComposition.SubdivisionRetainedChoices
import ResearchLean.AG.RelativeRepairComposition.ContextRelations

/-!
# Literal full shared actual choices and all external strict joins

The shared values consist of every original full fiber-automorphism choice on
the independently specified closed shared region. Its objects, original
arrows, core, reference, face names and both full three-cell routes are retained
by `oldRegion`; the first-factor restoration changes none of these choices.
The external objects below are independent and their entire shared-value map
is arbitrary. Existence therefore commutes with every strict external join,
without quotienting the shared values or imposing a selected environment.

## Implementation notes

Shared values are read directly from independently given actual old and new repair choices on every original shared edge. Defining the new shared value by collapse would encode the desired equality instead of proving literal strict agreement.
-/
namespace AAT.AG.RelativeRepairComposition.Subdivision
open CategoryTheory TransportCoherence TransportCoherence.Arbitrary AbelianLiftingObstruction
universe uG uE uB uD vE vB vD uX
variable {K : FiniteTransportPresentation.{uG}}
variable {E : Type uE} {B : Type uB} {D : Type uD}
variable [Category.{vE} E] [Category.{vB} B] [Category.{vD} D]
variable {p : E ⥤ B} {q : B ⥤ D}
variable (T : OriginalTowerPresentation K p q) (chosen : EdgeName (K := K))
variable (F : Factorization T chosen) (W : ClosedRegion K) (hw : chosen ∉ W.edges)

/-- All full actual original choices on the shared named edges, before any coordinates or quotient. -/
def SharedValues := ∀ e : W.edges, FiberAut (p ⋙ q) (T.original.object e.1.2.1)

omit chosen F hw in
/-- The old shared value is the entire independent actual choice family on the shared region. -/
def sharedOld (R : Solution T) : SharedValues T W := fun e => R.choice e.1.2.2

/-- The new shared value reads every actual retained edge directly from the new independent repair. -/
def sharedNew (R : Solution (originalTower T chosen F)) : SharedValues T W :=
  fun e => R.choice (oldEdge K chosen e.1 (fun h => hw (h ▸ e.2)))

/-- Actual collapse gives literal equality on the entire shared actual choice family. -/
theorem shared_collapse (R : Solution (originalTower T chosen F)) :
    sharedOld T W (collapseSolution T chosen F R) = sharedNew T chosen F W hw R := by
  funext e
  exact collapseSolution_choice_old T chosen F R e.1 (fun h => hw (h ▸ e.2))

/-- Every full first-factor restoration preserves all original actual shared choices literally. -/
theorem shared_expand (R : Solution T) (r : Additive (Kernel p q F.middle)) :
    sharedNew T chosen F W hw (expandSolution T chosen F R r) = sharedOld T W R := by
  funext e
  exact expandSolution_choice_old T chosen F R r e.1 (fun h => hw (h ▸ e.2))

variable (vertices : Set K.Vertex) (fixed : Set (EdgeName (K := K)))
variable (hchosen : chosen ∉ fixed)

include hchosen in
/-- The full relation of realized shared actual choices is identical for the independent old and new supported repairs. -/
theorem shared_relation :
    Set.range (fun R : SupportedRepair (originalTower T chosen F) (oldEdgeSet K chosen fixed) =>
      sharedNew T chosen F W hw R.1) =
    Set.range (fun R : SupportedRepair T fixed => sharedOld T W R.1) := by
  ext t
  constructor
  · rintro ⟨R,rfl⟩
    exact ⟨collapseSupported T chosen F fixed hchosen R,shared_collapse T chosen F W hw R.1⟩
  · rintro ⟨R,rfl⟩
    exact ⟨expandSupported T chosen F fixed R 0,shared_expand T chosen F W hw R.1 0⟩

include hchosen in
/-- Every independent external object family has the same existence outcome under literal full shared agreement. -/
theorem external_strict_join {X : Type uX} (boundary : X → SharedValues T W) :
    Nonempty (ContextRelations.StrictJoin
      (fun R : SupportedRepair (originalTower T chosen F) (oldEdgeSet K chosen fixed) =>
        sharedNew T chosen F W hw R.1) boundary) ↔
    Nonempty (ContextRelations.StrictJoin
      (fun R : SupportedRepair T fixed => sharedOld T W R.1) boundary) := by
  rw [ContextRelations.strict_join_nonempty,ContextRelations.strict_join_nonempty,
    shared_relation T chosen F W hw fixed hchosen]

/-- Every collapsed actual morphism keeps every shared vertex's complete original label. -/
theorem shared_inverse_label
    {R Q : RepairGroupoid (originalTower T chosen F) (Sum.inl '' vertices) (oldEdgeSet K chosen fixed)}
    (f : R ⟶ Q) (v : W.vertices) :
    (Multiplicative.toAdd ((equivalence T chosen F vertices fixed hchosen).inverse.map f).1).1 v.1 =
      (Multiplicative.toAdd f.1).1 (.inl v.1) :=
  equivalence_inverse_label_old T chosen F vertices fixed hchosen f v.1

/-- Every restored actual morphism keeps every shared vertex's complete original label. -/
theorem shared_functor_label {R Q : RepairGroupoid T vertices fixed}
    (f : R ⟶ Q) (v : W.vertices) :
    (Multiplicative.toAdd ((equivalence T chosen F vertices fixed hchosen).functor.map f).1).1 (.inl v.1) =
      (Multiplicative.toAdd f.1).1 v.1 :=
  equivalence_functor_label_old T chosen F vertices fixed hchosen f v.1

/-- The full natural comparison is literally zero on every shared vertex. -/
theorem shared_counit_label
    (R : RepairGroupoid (originalTower T chosen F) (Sum.inl '' vertices) (oldEdgeSet K chosen fixed))
    (v : W.vertices) :
    (Multiplicative.toAdd ((equivalence T chosen F vertices fixed hchosen).counitIso.hom.app R).1).1
      (.inl v.1) = 0 :=
  equivalence_counit_old T chosen F vertices fixed hchosen R v.1

end AAT.AG.RelativeRepairComposition.Subdivision
#assert_standard_axioms_only AAT.AG.RelativeRepairComposition.Subdivision
