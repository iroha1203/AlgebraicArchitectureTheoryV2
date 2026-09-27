import ResearchLean.AG.ProtocolHolonomy.NaturalIsomorphism
import Formal.Util.AssertStandardAxioms

/-!
# Composition of original visible renamings on independent executions

The original graph automorphism product renames original named edges in the
same order as the composition of their two quotient execution functors.
-/

namespace AAT.AG.ProtocolHolonomy

open AAT.AG.RealizationReconstruction CategoryTheory

universe u v w

theorem renameTypedEdge_mul {Q : FixedFDirectedMultigraph.{u, v}}
    (g h : FixedFGraphAutomorphism Q) {s t : Q.Vertex}
    (e : TypedEdge Q s t) :
    renameTypedEdge (g * h) e =
      renameTypedEdge g (renameTypedEdge h e) := by
  apply Subtype.ext
  rfl

theorem renamePositive_mul {Q : FixedFDirectedMultigraph.{u, v}}
    (g h : FixedFGraphAutomorphism Q) {s t : Q.Vertex}
    (p : PositivePath Q s t) :
    renamePositive (g * h) p =
      renamePositive g (renamePositive h p) := by
  letI : Quiver Q.Vertex := typedQuiver Q
  induction p with
  | nil => rfl
  | cons p e ih =>
      change (renamePositive (g * h) p).cons
          (renameTypedEdge (g * h) e) =
        (renamePositive g (renamePositive h p)).cons
          (renameTypedEdge g (renameTypedEdge h e))
      rw [ih, renameTypedEdge_mul]

theorem FiniteProtocolInput.renamePath_mul
    {Q : FixedFDirectedMultigraph.{u, v}}
    (P : FiniteProtocolInput.{u, v, w} Q)
    (g h : FixedFGraphAutomorphism Q)
    {a b : P.schema.Vertex} (p : Quiver.Path a b) :
    P.renamePath (g * h) p =
      P.renamePath g (P.renamePath h p) := by
  induction p with
  | nil => rfl
  | cons p e ih =>
      cases e with
      | up f =>
          change (P.renamePath (g * h) p).cons
              (ULift.up (renameTypedEdge (g * h) f)) =
            (P.renamePath g (P.renamePath h p)).cons
              (ULift.up (renameTypedEdge g (renameTypedEdge h f)))
          rw [ih, renameTypedEdge_mul]

theorem FiniteProtocolInput.renamePath_one
    {Q : FixedFDirectedMultigraph.{u, v}}
    (P : FiniteProtocolInput.{u, v, w} Q)
    {a b : P.schema.Vertex} (p : Quiver.Path a b) :
    P.renamePath 1 p = p := by
  induction p with
  | nil => rfl
  | cons p e ih =>
      cases e with
      | up f =>
          change (P.renamePath 1 p).cons
              (ULift.up (renameTypedEdge 1 f)) = p.cons (ULift.up f)
          rw [ih]
          rfl

theorem FiniteProtocolInput.renameExecutionFunctor_map_up_mul
    {Q : FixedFDirectedMultigraph.{u, v}}
    (P : FiniteProtocolInput.{u, v, w} Q)
    (g h : FixedFGraphAutomorphism Q)
    (hg : g ∈ P.H) (hh : h ∈ P.H)
    {s t : Q.Vertex} (p : PositivePath Q s t) :
    (P.renameExecutionFunctor (g * h) (P.H.mul_mem hg hh)).map
        (P.schema.pathMorphism (upPath Q p)) =
      (P.renameExecutionFunctor h hh ⋙ P.renameExecutionFunctor g hg).map
        (P.schema.pathMorphism (upPath Q p)) := by
  rw [P.renameExecutionFunctor_map_up,
    show (P.renameExecutionFunctor h hh ⋙
      P.renameExecutionFunctor g hg).map
        (P.schema.pathMorphism (upPath Q p)) =
      (P.renameExecutionFunctor g hg).map
        ((P.renameExecutionFunctor h hh).map
          (P.schema.pathMorphism (upPath Q p))) from rfl]
  rw [P.renameExecutionFunctor_map_up,
    P.renameExecutionFunctor_map_up]
  rw [renamePositive_mul]

/-- The full quotient-execution rename preserves multiplication of the
original visible group, on every quotient morphism. -/
theorem FiniteProtocolInput.renameExecutionFunctor_mul
    {Q : FixedFDirectedMultigraph.{u, v}}
    (P : FiniteProtocolInput.{u, v, w} Q)
    (g h : FixedFGraphAutomorphism Q)
    (hg : g ∈ P.H) (hh : h ∈ P.H) :
    P.renameExecutionFunctor (g * h) (P.H.mul_mem hg hh) =
      P.renameExecutionFunctor h hh ⋙ P.renameExecutionFunctor g hg := by
  refine CategoryTheory.Functor.ext (fun x => ?_) ?_
  · rfl
  · intro x y f
    have hmap : ∀ {a b : P.schema.ExecutionCategory} (f : a ⟶ b),
        (P.renameExecutionFunctor (g * h) (P.H.mul_mem hg hh)).map f =
          (P.renameExecutionFunctor h hh ⋙
            P.renameExecutionFunctor g hg).map f := by
      refine CategoryTheory.Quotient.induction (r := P.schema.pathRelation)
        (P := fun {a b} f =>
          (P.renameExecutionFunctor (g * h) (P.H.mul_mem hg hh)).map f =
            (P.renameExecutionFunctor h hh ⋙
              P.renameExecutionFunctor g hg).map f) ?_
      intro a b p
      change P.schema.pathMorphism (P.renamePath (g * h) p) =
        P.schema.pathMorphism (P.renamePath g (P.renamePath h p))
      rw [P.renamePath_mul]
    simpa using hmap f

/-- The identity visible change fixes every quotient execution. -/
theorem FiniteProtocolInput.renameExecutionFunctor_one
    {Q : FixedFDirectedMultigraph.{u, v}}
    (P : FiniteProtocolInput.{u, v, w} Q) :
    P.renameExecutionFunctor 1 P.H.one_mem = 𝟭 _ := by
  refine CategoryTheory.Functor.ext (fun x => ?_) ?_
  · rfl
  · intro x y f
    have hmap : ∀ {a b : P.schema.ExecutionCategory} (f : a ⟶ b),
        (P.renameExecutionFunctor 1 P.H.one_mem).map f = f := by
      refine CategoryTheory.Quotient.induction (r := P.schema.pathRelation)
        (P := fun {a b} f =>
          (P.renameExecutionFunctor 1 P.H.one_mem).map f = f) ?_
      intro a b p
      change P.schema.pathMorphism (P.renamePath 1 p) =
        P.schema.pathMorphism p
      rw [P.renamePath_one]
    simpa using hmap f

/-- Renaming by a visible change followed by its inverse is the identity on
the complete quotient execution category. -/
theorem FiniteProtocolInput.renameExecutionFunctor_inv_right
    {Q : FixedFDirectedMultigraph.{u, v}}
    (P : FiniteProtocolInput.{u, v, w} Q)
    (g : FixedFGraphAutomorphism Q) (hg : g ∈ P.H) :
    P.renameExecutionFunctor g hg ⋙
      P.renameExecutionFunctor g⁻¹ (P.H.inv_mem hg) = 𝟭 _ := by
  rw [← P.renameExecutionFunctor_mul g⁻¹ g (P.H.inv_mem hg) hg]
  simpa using P.renameExecutionFunctor_one

theorem FiniteProtocolInput.renameExecutionFunctor_inv_left
    {Q : FixedFDirectedMultigraph.{u, v}}
    (P : FiniteProtocolInput.{u, v, w} Q)
    (g : FixedFGraphAutomorphism Q) (hg : g ∈ P.H) :
    P.renameExecutionFunctor g⁻¹ (P.H.inv_mem hg) ⋙
      P.renameExecutionFunctor g hg = 𝟭 _ := by
  rw [← P.renameExecutionFunctor_mul g g⁻¹ hg (P.H.inv_mem hg)]
  simpa using P.renameExecutionFunctor_one

end AAT.AG.ProtocolHolonomy

#print axioms AAT.AG.ProtocolHolonomy.renameTypedEdge_mul
#print axioms AAT.AG.ProtocolHolonomy.renamePositive_mul
#print axioms AAT.AG.ProtocolHolonomy.FiniteProtocolInput.renamePath_mul
#print axioms AAT.AG.ProtocolHolonomy.FiniteProtocolInput.renamePath_one
#print axioms AAT.AG.ProtocolHolonomy.FiniteProtocolInput.renameExecutionFunctor_map_up_mul
#print axioms AAT.AG.ProtocolHolonomy.FiniteProtocolInput.renameExecutionFunctor_mul
#print axioms AAT.AG.ProtocolHolonomy.FiniteProtocolInput.renameExecutionFunctor_one
#print axioms AAT.AG.ProtocolHolonomy.FiniteProtocolInput.renameExecutionFunctor_inv_right
#print axioms AAT.AG.ProtocolHolonomy.FiniteProtocolInput.renameExecutionFunctor_inv_left
#assert_standard_axioms_only AAT.AG.ProtocolHolonomy
