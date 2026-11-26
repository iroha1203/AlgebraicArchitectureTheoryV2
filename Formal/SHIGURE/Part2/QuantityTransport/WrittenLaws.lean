import Formal.SHIGURE.Part2.QuantityTransport.Maps
import Formal.SHIGURE.Part1.StructureMaps

/-!
# Transport of written quantity Laws along structure maps

Chapter 5, Theorem 5.8. A quantity application is a tuple of typed state
terms. The same written equation is interpreted at each structure.
Domain and Law input preservation are the input conditions on the map.
The comparison of the equations follows from Theorem 1.8 for the actual
state terms.
-/

universe u

noncomputable section

namespace SHIGURE.Quantities.WrittenLaws.Interpretation

variable {k : Type u} {sig : Signature.{u}} {L : WrittenLaws k sig}
variable {A B : Structure sig}
variable (I : L.Interpretation A) (J : L.Interpretation B)

variable (f : StructureMap A B)
variable (onDomain : ∀ (j : L.Quantity) (x : I.domain j), x.val.map f.onSort ∈ J.domain j)
variable (onInput : ∀ (l : L.Law) (e : I.input l), e.val.map f.onSort ∈ J.input l)

/-- The structure map acts on the actual tuples in each fixed quantity domain. -/
def quantityMap : QuantityMap I.presentation J.presentation where
  name := id
  argument j x := ⟨x.val.map f.onSort, onDomain j x⟩

/-- The coordinates of the same written application commute with the structure map.
Each component is the image of the value of the corresponding defined state term. -/
theorem applicationCoordinate_map (l : L.Law) (e : I.input l) (a : L.Occurrence l) :
    (I.quantityMap J f onDomain).coordinate (I.applicationCoordinate l e a) =
      J.applicationCoordinate l ⟨e.val.map f.onSort, onInput l e⟩ a := by
  refine Sigma.ext ?_ ?_
  · rfl
  apply heq_of_eq
  apply Subtype.ext
  apply Assignment.ext
  intro s i
  exact f.eval_get_map ((L.application l a).2 i) e.val (I.defined l e a i)

/-- Theorem 5.8 for a structure map preserving the specified domain and input sets.
Comparisons of the two written sides are derived from typed evaluation. -/
def lawMap : LawMap I.presentation J.presentation where
  toQuantityMap := I.quantityMap J f onDomain
  law := id
  input l e := ⟨e.val.map f.onSort, onInput l e⟩
  left l e := by
    change ((L.left l).rename (I.applicationCoordinate l e)).rename
      (I.quantityMap J f onDomain).coordinate = _
    rw [Expression.rename_comp]
    exact congrArg (fun a => (L.left l).rename a)
      (funext (I.applicationCoordinate_map J f onDomain onInput l e))
  right l e := by
    change ((L.right l).rename (I.applicationCoordinate l e)).rename
      (I.quantityMap J f onDomain).coordinate = _
    rw [Expression.rename_comp]
    exact congrArg (fun a => (L.right l).rename a)
      (funext (I.applicationCoordinate_map J f onDomain onInput l e))

end SHIGURE.Quantities.WrittenLaws.Interpretation
