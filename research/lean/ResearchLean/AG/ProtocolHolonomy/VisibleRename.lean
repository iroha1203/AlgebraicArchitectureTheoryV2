import ResearchLean.AG.ProtocolHolonomy.ProtocolConnection
import Formal.Util.AssertStandardAxioms

/-!
# Visible operation-name changes on quotient executions

The original congruence-preservation condition in the A input is used to
descend visible edge renaming to the independent execution category.
-/

namespace AAT.AG.ProtocolHolonomy

open AAT.AG.RealizationReconstruction CategoryTheory

universe u v w

/-- The original path embedding respects concatenation. -/
theorem upPath_comp (Q : FixedFDirectedMultigraph.{u, v})
    {s t z : Q.Vertex} (p : PositivePath Q s t)
    (q : PositivePath Q t z) :
    upPath Q (positiveComp Q p q) =
      (upPath Q p).comp (upPath Q q) := by
  letI : Quiver Q.Vertex := typedQuiver Q
  exact Prefunctor.mapPath_comp (upPrefunctor Q) p q

/-- Every consequence of the original finite path equations is equal in
the independent quotient execution category. -/
theorem FiniteProtocolInput.congruent_sound
    {Q : FixedFDirectedMultigraph.{u, v}}
    (P : FiniteProtocolInput.{u, v, w} Q)
    {s t : Q.Vertex} {p q : PositivePath Q s t}
    (h : P.equations.Congruent p q) :
    P.schema.pathMorphism (upPath Q p) =
      P.schema.pathMorphism (upPath Q q) := by
  induction h with
  | equation r =>
      exact P.schema.relation_sound (ULift.up r)
  | refl p => rfl
  | symm _ ih => exact ih.symm
  | trans _ _ ih₁ ih₂ => exact ih₁.trans ih₂
  | comp h₁ h₂ ih₁ ih₂ =>
      rw [upPath_comp, upPath_comp]
      change (Quotient.functor P.schema.pathRelation).map
          (_ ≫ _) =
        (Quotient.functor P.schema.pathRelation).map
          (_ ≫ _)
      rw [CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_comp]
      exact congrArg₂ (fun x y => x ≫ y) ih₁ ih₂

/-- Rename lifted original vertices and edges using the given actual graph
automorphism. Every edge keeps its original name before renaming. -/
def FiniteProtocolInput.renamePrefunctor
    {Q : FixedFDirectedMultigraph.{u, v}}
    (P : FiniteProtocolInput.{u, v, w} Q)
    (g : FixedFGraphAutomorphism Q) :
    P.schema.Vertex ⥤q P.schema.Vertex where
  obj x := ULift.up (g.vertex x.down)
  map e := ULift.up (renameTypedEdge g e.down)

/-- Rename all original named edges in a lifted execution. -/
def FiniteProtocolInput.renamePath
    {Q : FixedFDirectedMultigraph.{u, v}}
    (P : FiniteProtocolInput.{u, v, w} Q)
    (g : FixedFGraphAutomorphism Q)
    {a b : P.schema.Vertex} (p : Quiver.Path a b) :
    Quiver.Path ((P.renamePrefunctor g).obj a)
      ((P.renamePrefunctor g).obj b) :=
  (P.renamePrefunctor g).mapPath p

/-- Renaming a lifted original path is the lift of renaming the original
named path. -/
theorem FiniteProtocolInput.renamePath_up
    {Q : FixedFDirectedMultigraph.{u, v}}
    (P : FiniteProtocolInput.{u, v, w} Q)
    (g : FixedFGraphAutomorphism Q)
    {s t : Q.Vertex} (p : PositivePath Q s t) :
    P.renamePath g (upPath Q p) =
      upPath Q (renamePositive g p) := by
  letI : Quiver Q.Vertex := typedQuiver Q
  induction p with
  | nil => rfl
  | cons p e ih =>
      change (P.renamePath g (upPath Q p)).cons
          (ULift.up (renameTypedEdge g e)) =
        (upPath Q (renamePositive g p)).cons
          (ULift.up (renameTypedEdge g e))
      rw [ih]

/-- Original graph automorphisms rename all free-path executions. -/
def FiniteProtocolInput.renamePathFunctor
    {Q : FixedFDirectedMultigraph.{u, v}}
    (P : FiniteProtocolInput.{u, v, w} Q)
    (g : FixedFGraphAutomorphism Q) :
    Paths P.schema.Vertex ⥤ Paths P.schema.Vertex where
  obj := (P.renamePrefunctor g).obj
  map := P.renamePath g
  map_id := fun _ => rfl
  map_comp := fun p q => Prefunctor.mapPath_comp (P.renamePrefunctor g) p q

/-- The A-input's congruence-preservation condition is exactly what
allows visible renaming to descend to the execution quotient. -/
theorem FiniteProtocolInput.renamePathFunctor_relation
    {Q : FixedFDirectedMultigraph.{u, v}}
    (P : FiniteProtocolInput.{u, v, w} Q)
    (g : FixedFGraphAutomorphism Q) (hg : g ∈ P.H)
    {a b : Paths P.schema.Vertex} (p q : a ⟶ b)
    (h : P.schema.pathRelation p q) :
    (P.renamePathFunctor g ⋙ Quotient.functor P.schema.pathRelation).map p =
      (P.renamePathFunctor g ⋙ Quotient.functor P.schema.pathRelation).map q := by
  obtain ⟨r, hs, ht, hp, hq⟩ := h
  cases hs
  cases ht
  subst p
  subst q
  have hcong := P.renaming_preserves g hg r.down
  have hsound := P.congruent_sound hcong
  rw [← P.renamePath_up g (P.equations.left r.down),
    ← P.renamePath_up g (P.equations.right r.down)] at hsound
  exact hsound

/-- The genuine operation-name rename on every quotient execution. -/
def FiniteProtocolInput.renameExecutionFunctor
    {Q : FixedFDirectedMultigraph.{u, v}}
    (P : FiniteProtocolInput.{u, v, w} Q)
    (g : FixedFGraphAutomorphism Q) (hg : g ∈ P.H) :
    P.schema.ExecutionCategory ⥤ P.schema.ExecutionCategory :=
  CategoryTheory.Quotient.lift P.schema.pathRelation
    (P.renamePathFunctor g ⋙ Quotient.functor P.schema.pathRelation)
    (fun _ _ p q h => P.renamePathFunctor_relation g hg p q h)

/-- On an original execution, the quotient rename is precisely the
original vertex/edge-name rename of the same path. -/
theorem FiniteProtocolInput.renameExecutionFunctor_map_up
    {Q : FixedFDirectedMultigraph.{u, v}}
    (P : FiniteProtocolInput.{u, v, w} Q)
    (g : FixedFGraphAutomorphism Q) (hg : g ∈ P.H)
    {s t : Q.Vertex} (p : PositivePath Q s t) :
    (P.renameExecutionFunctor g hg).map
      (P.schema.pathMorphism (upPath Q p)) =
        P.schema.pathMorphism (upPath Q (renamePositive g p)) := by
  rw [← P.renamePath_up g p]
  rfl

end AAT.AG.ProtocolHolonomy

#print axioms AAT.AG.ProtocolHolonomy.upPath_comp
#print axioms AAT.AG.ProtocolHolonomy.FiniteProtocolInput.congruent_sound
#print axioms AAT.AG.ProtocolHolonomy.FiniteProtocolInput.renamePath_up
#print axioms AAT.AG.ProtocolHolonomy.FiniteProtocolInput.renamePathFunctor_relation
#print axioms AAT.AG.ProtocolHolonomy.FiniteProtocolInput.renameExecutionFunctor
#print axioms AAT.AG.ProtocolHolonomy.FiniteProtocolInput.renameExecutionFunctor_map_up
#assert_standard_axioms_only AAT.AG.ProtocolHolonomy
