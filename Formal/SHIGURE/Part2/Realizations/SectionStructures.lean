import Formal.SHIGURE.Part1.StructureMaps
import Formal.SHIGURE.Part2.Realizations.SheafStructureMaps

/-!
# Primitive structures on sections

Reading a particular test object's sections gives a Part I structure
and a map on those sections. The full sheaf morphism is the input to this
reading.
-/

open CategoryTheory Opposite

universe u v w

namespace SHIGURE.SheafStructure

variable {C : Type v} [Category.{w} C] {J : GrothendieckTopology C}
variable {sig : Signature.{u}}

/-- Read every primitive structure on the sections over a fixed test object. -/
def sections (A : SheafStructure sig J) (U : Cᵒᵖ) : Structure sig where
  carrier s := (A.carrier s).val.obj U
  total f := (A.total f).val.app U
  relation r := (A.relation r).carrier.obj U
  partialDomain p := (A.partialDomain p).carrier.obj U
  partialValue p := (A.partialValue p).val.app U
  quantity q := (A.quantity q).val.app U

/-- A sheaf morphism induces the Part I structure map on the selected sections. -/
def Hom.sections {A B : SheafStructure sig J} (h : Hom A B) (U : Cᵒᵖ) :
    StructureMap (A.sections U) (B.sections U) where
  onSort s := (h.onSort s).val.app U
  total_comm f xs := congrArg (fun k => k.val.app U xs) (h.preservesTotal f)
  relation_mem r _ hx := h.preservesRelation r U hx
  partial_mem p _ hx := h.preservesDomain p U hx
  partial_comm p xs := congrArg (fun k => k.val.app U xs) (h.preservesPartial p)
  quantity_comm q xs := congrArg (fun k => k.val.app U xs) (h.preservesQuantity q)

end SHIGURE.SheafStructure
