import Formal.SHIGURE.Part1.ContextOrdinaryDescent
import Mathlib.Data.Set.Finite.Lattice

/-! # Finite declaration fragments

A finite declaration fragment has finitely many names and uses the usual
selected presentation of its dependency-closed context. Its ordinary reduct
keeps the full carriers and interpretations of all retained declarations.

## Implementation notes

The fragment stores a DeclarationContext so the same dependency closure
and selected presentation govern all model and arrow restrictions in
Definition 3.8. A finset of names would require a separate conversion to
the closed context used by the assembly theorems. Set finiteness keeps
that interface and supports finite indexed unions directly.
-/

universe u v

namespace SHIGURE.DeclarationContext

open CategoryTheory

variable {P : PrimitivePresentation.{u}}

/-- A finite dependency-closed subcontext of the given declarations. -/
structure FiniteFragment (U : DeclarationContext P) where
  /-- The retained context and its dependency closure. -/
  context : DeclarationContext P
  /-- The fragment uses only declarations of the original context. -/
  inside : context ≤ U
  /-- There are only finitely many retained declaration names. -/
  finite : context.declarations.Finite

namespace FiniteFragment

variable {U : DeclarationContext P}

/-- The actual restricted presentation on a finite declaration fragment. -/
noncomputable def presentation (F : FiniteFragment U) : PrimitivePresentation.{u} :=
  Selected.presentation F.context

/-- The ordinary restriction functor along the selected inclusion of declarations. -/
noncomputable def restriction (F : FiniteFragment U) :
    Model (Selected.presentation U).theory ⥤ Model F.presentation.theory :=
  Selected.modelRestriction F.inside

/-- Restricting an ordinary model reads the same primitive reduct on this fragment. -/
theorem restriction_write (F : FiniteFragment U) (A : Model (Selected.presentation U).theory) :
    Selected.writeModel (F.restriction.obj A) = (Selected.writeModel A).restrict F.inside :=
  (Functor.congr_obj (Selected.write_res F.inside) A).symm

/-- Each retained sort keeps the entire carrier of the global model after writing its named data. -/
theorem restriction_carrier (F : FiniteFragment U) (A : Model (Selected.presentation U).theory)
    {s : P.signature.SortType} (keep : Declaration.sort s ∈ F.context.declarations) :
    (Selected.writeModel (F.restriction.obj A)).obj.carrier s =
      (Selected.writeModel A).obj.carrier s := by
  rw [F.restriction_write A]
  exact (Selected.writeModel A).obj.restrict_carrier F.inside keep

/-- The primitive interpretation of the ordinary reduct agrees on the full retained carriers.
This equality covers the graphs of total and partial operations and quantities, the partial
domains, and relations, for every input of each retained declaration. -/
theorem restriction_evaluation (F : FiniteFragment U) (A : Model (Selected.presentation U).theory) :
    ((Selected.writeModel (F.restriction.obj A)).obj.evaluation).pullback (le_refl F.context)
        (fun s keep x => cast (F.restriction_carrier A (s := s) keep).symm x) =
      (Selected.writeModel A).obj.evaluation.pullback F.inside (fun _ _ x => x) := by
  let G := (Selected.writeModel A).obj
  have same : (Selected.writeModel (F.restriction.obj A)).obj = G.restrict F.inside :=
    congrArg (fun M : Models F.context => M.obj) (F.restriction_write A)
  calc
    _ = (G.restrict F.inside).evaluation.pullback (le_refl F.context)
        (fun s keep x => cast (G.restrict_carrier F.inside (s := s) keep).symm x) := by
      apply ContextStructure.pullback_along_eq same
      intro s keep x
      rw [cast_cast]
    _ = _ := G.restrict_evaluation_view F.inside (fun _ _ x => x)

/-- The empty set of names gives a finite fragment of any context. -/
def empty (U : DeclarationContext P) : FiniteFragment U where
  context := DeclarationContext.empty P
  inside := Set.empty_subset _
  finite := Set.finite_empty

/-- The union of any finite family of fragments is a finite fragment. -/
def union {I : Type v} [Finite I] (F : I → FiniteFragment U) : FiniteFragment U where
  context := DeclarationContext.union fun i => (F i).context
  inside := union_le fun i => (F i).inside
  finite := by
    have same : (DeclarationContext.union fun i => (F i).context).declarations =
        ⋃ i, (F i).context.declarations :=
      Set.ext fun _ => Set.mem_iUnion.symm
    rw [same]
    exact Set.finite_iUnion fun i => (F i).finite

/-- Each fragment of a finite family lies in its union. -/
theorem le_union {I : Type v} [Finite I] (F : I → FiniteFragment U) (i : I) :
    (F i).context ≤ (union F).context :=
  DeclarationContext.le_union (fun j => (F j).context) i

/-- The union of two fragments is another finite fragment. -/
def merge (F G : FiniteFragment U) : FiniteFragment U :=
  union (fun b : Bool => if b then F else G)

/-- Finite fragments are directed by inclusion of their declarations. -/
theorem directed (U : DeclarationContext P) :
    Directed (· ≤ ·) (context : FiniteFragment U → DeclarationContext P) := by
  intro F G
  refine ⟨merge F G, ?_, ?_⟩
  · simpa [merge] using le_union (fun b : Bool => if b then F else G) true
  · simpa [merge] using le_union (fun b : Bool => if b then F else G) false

/-- Each retained name lies in some finite dependency-closed subcontext. -/
def HasFiniteClosure (U : DeclarationContext P) : Prop :=
  ∀ d ∈ U.declarations, ∃ F : FiniteFragment U, d ∈ F.context.declarations

/-- Under finite dependency closure, the family of all finite fragments covers the context. -/
def cover (U : DeclarationContext P) (closed : HasFiniteClosure U) : DeclarationCover U where
  Index := FiniteFragment U
  piece := context
  subset F := F.inside
  covers := closed _

/-- Apply Theorem 3.4 to ordinary models on all finite dependency-closed fragments. -/
theorem existsUnique_model (closed : HasFiniteClosure U)
    (A : OrdinaryMatch (cover U closed).piece) :
    ∃! X : Model (Selected.presentation U).theory, ∀ F : FiniteFragment U,
      F.restriction.obj X = A.pieceModel F :=
  (cover U closed).existsUnique_ordinary_glue A

/-- Apply Theorem 3.5 to compatible arrows on all finite dependency-closed fragments. -/
theorem existsUnique_map_heq (closed : HasFiniteClosure U)
    {A B : Model (Selected.presentation U).theory}
    (f : OrdinaryMatch.Hom ((cover U closed).ordinaryRead.obj A)
      ((cover U closed).ordinaryRead.obj B)) :
    ∃! h : A ⟶ B, ∀ F : FiniteFragment U, HEq (F.restriction.map h) (f.pieceMap F) :=
  (cover U closed).existsUnique_ordinary_assemble_heq f

/-- The finite-fragment form also has the homogeneous comparison for compatible arrows. -/
theorem existsUnique_map (closed : HasFiniteClosure U)
    {A B : Model (Selected.presentation U).theory}
    (f : OrdinaryMatch.Hom ((cover U closed).ordinaryRead.obj A)
      ((cover U closed).ordinaryRead.obj B)) :
    ∃! h : A ⟶ B, ∀ F : FiniteFragment U, F.restriction.map h = f.pieceMap F := by
  obtain ⟨h, components, unique⟩ := existsUnique_map_heq closed f
  exact ⟨h, fun F => eq_of_heq (components F), fun g same => unique g (fun F => heq_of_eq (same F))⟩

end FiniteFragment

end SHIGURE.DeclarationContext
