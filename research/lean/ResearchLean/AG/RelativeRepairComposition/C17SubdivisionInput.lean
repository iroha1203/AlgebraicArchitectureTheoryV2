import ResearchLean.AG.RelativeRepairComposition.SubdivisionSharedValues
import ResearchLean.AG.RelativeRepairComposition.SubdivisionThreeLaws
import ResearchLean.AG.RelativeRepairComposition.NativeAffineRepairs
import ResearchLean.AG.RelativeRepairComposition.NativeAffineCoefficients
import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.Field.ZMod

/-! # W4's original full affine tower and specified actual factorization
## Implementation notes

This is the specified W4 full affine tower, with the original flip, translation comparator and the two specified actual factors. It instantiates the general Factorization rather than supplying a specialized repair equivalence. The separately fixed fresh vertex is modeled by a second closed part.
-/
namespace AAT.AG.RelativeRepairComposition.C17SubdivisionInput
open CategoryTheory TransportCoherence TransportCoherence.Arbitrary AbelianLiftingObstruction
open NativeAffine
attribute [local instance] Classical.propDecidable

/-- The same prime field F3 is generated from the arithmetic prime-three theorem. -/
instance primeThree : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩

/-- W4 has two actual named loops a,b and the authored temporal word baa compared with the empty word. -/
def geometry : FiniteTransportPresentation where
  Vertex := Unit
  vertexFintype := inferInstance
  Edge := fun _ _ => Bool
  edgeFintype := fun _ _ => inferInstance
  TwoCell := Unit
  twoCellFintype := inferInstance
  twoSource := fun _ => ()
  twoTarget := fun _ => ()
  twoLeft := fun _ => .cons (i := ()) (j := ()) true (.cons (i := ()) (j := ()) false (.cons (i := ()) (j := ()) false (.nil ())))
  twoRight := fun _ => .nil ()
  ThreeCell := Empty
  threeCellFintype := inferInstance
  threeSource := fun t => nomatch t
  threeTarget := fun t => nomatch t
  threeStart := fun t => nomatch t
  threeFinish := fun t => nomatch t
  threeLeft := fun t => nomatch t
  threeRight := fun t => nomatch t

/-- The entire affine operation group acts on F3. -/
abbrev Op := Operations (ZMod 3) (ZMod 3)
/-- The original a operation is the actual negation affine equivalence. -/
noncomputable def flip : Op := (LinearEquiv.neg (ZMod 3) : ZMod 3 ≃ₗ[ZMod 3] ZMod 3).toAffineEquiv
/-- Negation evaluates on every vector, not only on an observed sample. -/
theorem flip_apply (x : ZMod 3) : flip x = -x := rfl
/-- The two original reference operations are a=-id and b=id. -/
noncomputable def reference : ∀ {i j : geometry.Vertex}, geometry.Edge i j → Op :=
  fun e => if (e : Bool) = true then 1 else flip
/-- The designated real comparison is translation by minus one. -/
def comparison : geometry.TwoCell → ZMod 3 := fun _ => -1
/-- The original full reference word has identity linear part. -/
theorem linear_faces (f : geometry.TwoCell) :
    (GroupExtension.pathValue geometry reference (geometry.twoLeft f)).linear =
      (GroupExtension.pathValue geometry reference (geometry.twoRight f)).linear := by
  have hh : flip * flip = (1 : Op) := by
    ext x
    change -(-x) = x
    exact neg_neg x
  simp only [geometry,GroupExtension.pathValue,reference,if_pos,if_neg,
    Bool.false_eq_true,not_false_eq_true,one_mul,mul_one,hh]

/-- The original tower retains these actual original arrows and the same selected references. -/
noncomputable abbrev originalTower := NativeAffine.tower geometry reference reference comparison linear_faces
/-- The chosen internal always-available name is a, never the candidate b. -/
def chosen : EdgeName (K := geometry) := ⟨(),(),false⟩
/-- The sole candidate is the complete original b name. -/
def candidate : EdgeName (K := geometry) := ⟨(),(),true⟩
/-- W4 fixes its original vertex and no original edge, face or triple. -/
def fixedRegion : ClosedRegion geometry where
  vertices := Set.univ
  edges := ∅
  faces := ∅
  triples := ∅
  edge_closed := by intro e he; exact he.elim
  face_closed := by intro f hf; exact hf.elim
  triple_closed := by intro t ht; exact ht.elim
/-- The actual first factor sends x to x+1. -/
noncomputable def first : Op := translation (k := ZMod 3) 1
/-- The actual second factor sends x to -x+1. -/
noncomputable def second : Op := translation (k := ZMod 3) 1 * flip
/-- Both specified operations compose to the same actual original selected a operation. -/
theorem factor_product : second * first = flip := by
  ext x
  simp only [second,first,AffineEquiv.coe_mul,Function.comp_apply,translation_apply,flip_apply]
  abel

/-- The whole-factor strongness and bijective full-kernel transports come from the same native affine tower. -/
noncomputable def factors : Subdivision.Factorization originalTower chosen where
  middle := SingleObj.star Op
  first := first
  second := second
  composite := by
    rw [NativeAffine.tower_reference_edge]
    simpa [SingleObj.comp_as_mul,reference,chosen] using factor_product
  firstStrong := by
    simpa using GroupExtension.selectedStrong (projection (k := ZMod 3) (A := ZMod 3)) first
  secondStrong := by
    simpa using GroupExtension.selectedStrong (projection (k := ZMod 3) (A := ZMod 3)) second
  firstLowerStrong := by
    simpa using GroupExtension.selectedLowerStrong (projection (k := ZMod 3) (A := ZMod 3)) first
  secondLowerStrong := by
    simpa using GroupExtension.selectedLowerStrong (projection (k := ZMod 3) (A := ZMod 3)) second
  firstBijective := GroupExtension.transport_bijective (projection (k := ZMod 3) (A := ZMod 3)) first
  secondBijective := GroupExtension.transport_bijective (projection (k := ZMod 3) (A := ZMod 3)) second

/-- W4's subdivided tower is exactly the general original-tower construction above. -/
noncomputable abbrev splitTower := Subdivision.originalTower originalTower chosen factors
/-- The first factor has precisely its designated real value on the entire field. -/
theorem first_apply (x : ZMod 3) : first x = x + 1 := by
  simp only [first,translation_apply,add_comm]
/-- The second factor has precisely its designated real value on the entire field. -/
theorem second_apply (x : ZMod 3) : second x = -x + 1 := by
  simp only [second,AffineEquiv.coe_mul,Function.comp_apply,translation_apply,flip_apply,add_comm]
/-- The actual new vertex belongs to neither fixed P nor shared W (here W=P). -/
theorem fresh_free :
    (Sum.inr () : (Subdivision.presentation geometry chosen).Vertex) ∉
      (Subdivision.oldRegion geometry chosen fixedRegion (by exact not_false)).vertices :=
  Subdivision.new_vertex_not_old_region geometry chosen fixedRegion (by exact not_false)

end AAT.AG.RelativeRepairComposition.C17SubdivisionInput
#assert_standard_axioms_only AAT.AG.RelativeRepairComposition.C17SubdivisionInput
