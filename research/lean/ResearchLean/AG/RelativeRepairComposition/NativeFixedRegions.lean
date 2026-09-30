import ResearchLean.AG.RelativeRepairComposition.RestrictedPresentation
import ResearchLean.AG.RelativeRepairComposition.RelativeComplex

/-!
Native fixed regions in a complete restricted presentation.

The selected native cells are precisely the inverse images of the original P
cells. Closure follows from the original P closure and preservation of every
path occurrence, face occurrence and contextual edge occurrence by forgetting.

## Implementation notes

The dependent recursor fixes all typed indices explicitly. Bookend transport
changes only indices, so face and context incidence can be recovered from the
full original routes. Relative kernels use the same original fixed cells.
-/

namespace AAT.AG.RelativeRepairComposition
open TransportCoherence AbelianLiftingObstruction
universe uG uA
variable {K : FiniteTransportPresentation.{uG}}
namespace ClosedRegion
variable (U P : ClosedRegion K)

/-- Every selected path occurrence forgets to the same original named edge. -/
theorem path_edge_mem_forget {i j : Vertex U} (w : Path U i j)
    (e : EdgeName (K := presentation U))
    (he : e ∈ pathEdges (K := presentation U) w) :
    (edgeNameEquiv U e).1 ∈ pathEdges (forgetPath U w) := by
  induction w with
  | nil i => exact he.elim
  | cons a tail ih =>
    rcases he with he | he
    · cases he
      exact Or.inl rfl
    · exact Or.inr (ih he)

/-- Every face occurrence in a native route keeps its original face name. -/
theorem pasting_face_mem_forget {i j : Vertex U} {w z : Path U i j}
    (pasting : RewritePasting (presentation U).toFiniteTransportTwoPresentation w z)
    (f : (presentation U).TwoCell)
    (hf : f ∈ pastingFaces (K := presentation U) pasting) :
    f.1 ∈ pastingFaces (forgetPasting U pasting) := by
  exact @RewritePasting.rec (twoPresentation U) i j
    (fun _ _ pasting => ∀ f : U.faces,
      f ∈ pastingFaces (K := presentation U) pasting →
        f.1 ∈ pastingFaces (forgetPasting U pasting))
    (fun _ _ hf => hf.elim)
    (fun {_ _ _} step _ ih f hf => by
      simp only [forgetPasting, pastingFaces, forgetStep, forgetWhiskeredFace]
      rcases hf with hf | hf
      · cases hf
        exact Or.inl rfl
      · exact Or.inr (ih f hf)) w z pasting f hf

/-- Every prefix and suffix edge occurrence keeps its original named edge. -/
theorem pasting_context_edge_mem_forget {i j : Vertex U} {w z : Path U i j}
    (pasting : RewritePasting (presentation U).toFiniteTransportTwoPresentation w z)
    (e : EdgeName (K := presentation U))
    (he : e ∈ pastingContextEdges (K := presentation U) pasting) :
    (edgeNameEquiv U e).1 ∈ pastingContextEdges (forgetPasting U pasting) := by
  exact @RewritePasting.rec (twoPresentation U) i j
    (fun _ _ pasting => ∀ e : EdgeName (K := presentation U),
      e ∈ pastingContextEdges (K := presentation U) pasting →
        (edgeNameEquiv U e).1 ∈ pastingContextEdges (forgetPasting U pasting))
    (fun _ _ he => he.elim)
    (fun {_ _ _} step _ ih e he => by
      simp only [forgetPasting, pastingContextEdges, forgetStep, forgetWhiskeredFace]
      rcases he with (he | he) | he
      · exact Or.inl (Or.inl (path_edge_mem_forget U step.face.incoming e he))
      · exact Or.inl (Or.inr (path_edge_mem_forget U step.face.outgoing e he))
      · exact Or.inr (ih e he)) w z pasting e he

/-- Transporting the bookend path indices preserves every route face occurrence. -/
theorem cast_pasting_faces {i j : K.Vertex} {w w' z z' : K.Path i j}
    (hw : w = w') (hz : z = z')
    (pasting : RewritePasting K.toFiniteTransportTwoPresentation w z) :
    pastingFaces (castPasting hw hz pasting) = pastingFaces pasting := by
  cases hw
  cases hz
  rfl

/-- Transporting the bookend path indices preserves all prefix and suffix edges. -/
theorem cast_pasting_context_edges {i j : K.Vertex} {w w' z z' : K.Path i j}
    (hw : w = w') (hz : z = z')
    (pasting : RewritePasting K.toFiniteTransportTwoPresentation w z) :
    pastingContextEdges (castPasting hw hz pasting) = pastingContextEdges pasting := by
  cases hw
  cases hz
  rfl

/-- Native P intersection U retains exactly the original P cells selected by U. -/
noncomputable def nativeIntersection : ClosedRegion (presentation U) where
  vertices := {v | v.1 ∈ P.vertices}
  edges := {e | (edgeNameEquiv U e).1 ∈ P.edges}
  faces := {f | f.1 ∈ P.faces}
  triples := {t | t.1 ∈ P.triples}
  edge_closed := by
    intro e he
    exact P.edge_closed (edgeNameEquiv U e).1 he
  face_closed := by
    intro f hf
    have hp := P.face_closed f.1 hf
    refine ⟨hp.1, hp.2.1, ?_, ?_⟩
    · intro e he
      apply hp.2.2.1
      rw [← forget_two_left U f]
      exact path_edge_mem_forget U _ e he
    · intro e he
      apply hp.2.2.2
      rw [← forget_two_right U f]
      exact path_edge_mem_forget U _ e he
  triple_closed := by
    intro t ht
    have hp := P.triple_closed t.1 ht
    refine ⟨hp.1, hp.2.1, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro e he
      apply hp.2.2.1
      rw [← forget_three_start U t]
      exact path_edge_mem_forget U _ e he
    · intro e he
      apply hp.2.2.2.1
      rw [← forget_three_finish U t]
      exact path_edge_mem_forget U _ e he
    · intro f hf
      apply hp.2.2.2.2.1
      rw [← forget_three_left U t, cast_pasting_faces]
      exact pasting_face_mem_forget U _ f hf
    · intro f hf
      apply hp.2.2.2.2.2.1
      rw [← forget_three_right U t, cast_pasting_faces]
      exact pasting_face_mem_forget U _ f hf
    · intro e he
      apply hp.2.2.2.2.2.2.1
      rw [← forget_three_left U t, cast_pasting_context_edges]
      exact pasting_context_edge_mem_forget U _ e he
    · intro e he
      apply hp.2.2.2.2.2.2.2
      rw [← forget_three_right U t, cast_pasting_context_edges]
      exact pasting_context_edge_mem_forget U _ e he

/-- The native fixed vertex condition is the original P vertex condition. -/
theorem mem_native_intersection_vertices (v : (presentation U).Vertex) :
    v ∈ (nativeIntersection U P).vertices ↔ v.1 ∈ P.vertices := Iff.rfl

/-- The native fixed edge condition is the original P condition on the same name. -/
theorem mem_native_intersection_edges (e : EdgeName (K := presentation U)) :
    e ∈ (nativeIntersection U P).edges ↔ (edgeNameEquiv U e).1 ∈ P.edges := Iff.rfl

/-- The native fixed face condition is the original P face condition. -/
theorem mem_native_intersection_faces (f : (presentation U).TwoCell) :
    f ∈ (nativeIntersection U P).faces ↔ f.1 ∈ P.faces := Iff.rfl

/-- The native fixed triple condition is the original P triple condition. -/
theorem mem_native_intersection_triples (t : (presentation U).ThreeCell) :
    t ∈ (nativeIntersection U P).triples ↔ t.1 ∈ P.triples := Iff.rfl

variable (M : LocalCoefficients.{uG,uA} K)

/-- Native relative degree zero is exactly zero on the original P vertices of U. -/
theorem native_relative_zero_iff
    (b : AbelianLiftingObstruction.C0 (restrictCoefficients U M)) :
    r0 (restrictCoefficients U M) (nativeIntersection U P) b = 0 ↔
      ∀ v : U.vertices, v.1 ∈ P.vertices → b v = 0 :=
  RelativeComplex.family_restrict_eq_zero _ _ _

/-- Native relative degree one is exactly zero on the original P edge names of U. -/
theorem native_relative_one_iff
    (h : AbelianLiftingObstruction.C1 (restrictCoefficients U M)) :
    r1 (restrictCoefficients U M) (nativeIntersection U P) h = 0 ↔
      ∀ e : U.edges, e.1 ∈ P.edges → nativeC1Equiv U M h e = 0 := by
  change Family.restrict _ _ h = 0 ↔ _
  rw [RelativeComplex.family_restrict_eq_zero]
  constructor
  · intro hh e he
    have hm : (edgeNameEquiv U ((edgeNameEquiv U).symm e)).1 ∈ P.edges := by
      rw [Equiv.apply_symm_apply]
      exact he
    exact hh ((edgeNameEquiv U).symm e) hm
  · intro hh e he
    have hz := hh (edgeNameEquiv U e) he
    change h ((edgeNameEquiv U).symm (edgeNameEquiv U e)) = 0 at hz
    rw [Equiv.symm_apply_apply] at hz
    exact hz

/-- Native relative degree two is exactly zero on the original P face names of U. -/
theorem native_relative_two_iff
    (c : AbelianLiftingObstruction.C2 (restrictCoefficients U M)) :
    r2 (restrictCoefficients U M) (nativeIntersection U P) c = 0 ↔
      ∀ f : U.faces, f.1 ∈ P.faces → c f = 0 :=
  RelativeComplex.family_restrict_eq_zero _ _ _

/-- Native relative degree three is exactly zero on the original P triple names of U. -/
theorem native_relative_three_iff
    (c : AbelianLiftingObstruction.C3 (restrictCoefficients U M)) :
    r3 (restrictCoefficients U M) (nativeIntersection U P) c = 0 ↔
      ∀ t : U.triples, t.1 ∈ P.triples → c t = 0 :=
  RelativeComplex.family_restrict_eq_zero _ _ _

end ClosedRegion
end AAT.AG.RelativeRepairComposition

#assert_standard_axioms_only AAT.AG.RelativeRepairComposition
