import ResearchLean.AG.RelativeRepairComposition.SubdivisionArrowAssignment
import ResearchLean.AG.RelativeRepairComposition.SubdivisionFactors

/-!
# Strong original and reference arrows on the full subdivided presentation

Every indexed edge is a retained original edge or one of the two actual factors.
Its base is the image of that actual arrow. Strongness at retained edges follows
from their original base equation; it is supplied at the two primitive factors.

## Implementation notes

Original edge bases are the actual projections of the primitive new arrows; retained edges still use the arbitrary original L. Setting every original arrow equal to its reference would erase the original correction coordinates. Selected and original LiftData therefore remain separate.
-/
namespace AAT.AG.RelativeRepairComposition.Subdivision
open CategoryTheory TransportCoherence TransportCoherence.Arbitrary AbelianLiftingObstruction
universe uG uE uB uD vE vB vD
variable {K : FiniteTransportPresentation.{uG}}
variable (chosen : EdgeName (K := K))

/-- Exhaust the entire indexed edge family by retained complete names and both factors. -/
theorem edge_induction (P : ∀ {i j : Vertex K}, Edge K chosen i j → Prop)
    (hold : ∀ (e : EdgeName (K := K)) (he : e ≠ chosen), P (oldEdge K chosen e he))
    (hfirst : P (firstEdge K chosen)) (hsecond : P (secondEdge K chosen))
    {i j : Vertex K} (e : Edge K chosen i j) : P e := by
  rcases e with ⟨n,hs,ht⟩
  cases hs; cases ht
  cases n with
  | inl n => exact hold n.1 n.2
  | inr b => cases b <;> assumption

variable {E : Type uE} {B : Type uB} {D : Type uD}
variable [Category.{vE} E] [Category.{vB} B] [Category.{vD} D]
variable {p : E ⥤ B} {q : B ⥤ D}
variable (L : LiftData K.toFiniteTransportTwoPresentation (p ⋙ q))
variable (middle : E) (first : L.object chosen.1 ⟶ middle)
variable (second : middle ⟶ L.object chosen.2.1)

/-- The mapped original actual arrow is its specified original base arrow. -/
theorem original_edge_base {i j : K.Vertex} (e : K.Edge i j) :
    (p ⋙ q).map (L.edgeLift e) = L.edgeBase e := by
  letI := L.edgeStrong e
  exact (IsHomLift.eq_of_isHomLift (p ⋙ q) (L.edgeBase e) (L.edgeLift e)).symm

/-- Build all actual subdivided arrows from the original arrows and the two supplied strong factors. -/
def liftData
    (hfirst : (p ⋙ q).IsStronglyCocartesian ((p ⋙ q).map first) first)
    (hsecond : (p ⋙ q).IsStronglyCocartesian ((p ⋙ q).map second) second) :
    LiftData (presentation K chosen).toFiniteTransportTwoPresentation (p ⋙ q) where
  object := objectAssignment K L.object middle
  edgeLift := edgeAssignment K chosen L.object middle L.edgeLift first second
  edgeBase e := (p ⋙ q).map (edgeAssignment K chosen L.object middle L.edgeLift first second e)
  edgeStrong := by
    apply edge_induction chosen
    · intro e he
      rw [edgeAssignment_old, original_edge_base]
      exact L.edgeStrong e.2.2
    · rw [edgeAssignment_first]
      exact hfirst
    · rw [edgeAssignment_second]
      exact hsecond

/-- Both lower strong factors and all original lower strong arrows supply the full lower strong family. -/
theorem liftData_lowerStrong
    (hfirst : (p ⋙ q).IsStronglyCocartesian ((p ⋙ q).map first) first)
    (hsecond : (p ⋙ q).IsStronglyCocartesian ((p ⋙ q).map second) second)
    (hLower : ∀ {i j : K.Vertex} (e : K.Edge i j),
      q.IsStronglyCocartesian (L.edgeBase e) (p.map (L.edgeLift e)))
    (hf : q.IsStronglyCocartesian ((p ⋙ q).map first) (p.map first))
    (hs : q.IsStronglyCocartesian ((p ⋙ q).map second) (p.map second))
    {i j : (presentation K chosen).Vertex} (e : (presentation K chosen).Edge i j) :
    q.IsStronglyCocartesian
      ((liftData chosen L middle first second hfirst hsecond).edgeBase e)
      (p.map ((liftData chosen L middle first second hfirst hsecond).edgeLift e)) := by
  change q.IsStronglyCocartesian
    ((p ⋙ q).map (edgeAssignment K chosen L.object middle L.edgeLift first second e))
    (p.map (edgeAssignment K chosen L.object middle L.edgeLift first second e))
  apply edge_induction chosen _ _ _ _ e
  · intro e he
    rw [edgeAssignment_old,original_edge_base]
    exact hLower e.2.2
  · rw [edgeAssignment_first]
    exact hf
  · rw [edgeAssignment_second]
    exact hs

variable (T : OriginalTowerPresentation K p q) (F : Factorization T chosen)

/-- The new original input retains arbitrary original arrows and uses the two specified actual factors. -/
def originalLiftData : LiftData (presentation K chosen).toFiniteTransportTwoPresentation (p ⋙ q) :=
  liftData chosen T.original F.middle F.first F.second F.firstStrong F.secondStrong

/-- The new reference retains the original selected references and the same two specified actual factors. -/
def referenceLiftData : LiftData (presentation K chosen).toFiniteTransportTwoPresentation (p ⋙ q) :=
  liftData chosen T.toTower.upper F.middle F.first F.second F.firstStrong F.secondStrong

end AAT.AG.RelativeRepairComposition.Subdivision
#assert_standard_axioms_only AAT.AG.RelativeRepairComposition.Subdivision
