import Formal.SHIGURE.Part2.Recovery.StructureMaps
import Formal.SHIGURE.Part2.Realizations.ZariskiModels
import Formal.SHIGURE.Part1.SelectedPresentation

/-!
# Restriction of the declarations of a copying structure

A reduct retypes the tuples of sections using the Part I position map.
Relations and partial domains are the preimages of the original
predicates, and the partial value uses the induced map on those domains.
-/

open AlgebraicGeometry CategoryTheory Opposite

universe u

noncomputable section

namespace SHIGURE.Copying

variable {B B' : Scheme.{u}} {S T : Signature.{u}}

/-- Retype every section of a finite tuple to its corresponding named position. -/
private def renameTuple {K L : Type u} (g : K → L) (A : L → ZariskiSheaf B)
    (Γ : List K) : sheafTuple (A ∘ g) Γ ⟶ sheafTuple A (Γ.map g) :=
  ⟨{ app := fun U => ↾fun a => Assignment.mapSorts (X := fun i => (A i).val.obj U) g a
     naturality := by
       intro U V f
       ext a
       apply Assignment.ext_mapSorts g
       intro s i
       let aU : Assignment (fun k => (A (g k)).val.obj U) Γ := a
       let aV : Assignment (fun k => (A (g k)).val.obj V) Γ := (sheafTuple (A ∘ g) Γ).val.map f a
       change (aV.mapSorts (X := fun l => (A l).val.obj V) g).get (i.mapSorts g) =
         (A (g s)).val.map f ((aU.mapSorts (X := fun l => (A l).val.obj U) g).get (i.mapSorts g))
       rw [Assignment.mapSorts_apply, Assignment.mapSorts_apply]
       rfl }⟩

/-- Retyping arguments along the specified equality of contexts keeps their actual sections. -/
private def renameTupleAt {K L : Type u} (g : K → L) (A : L → ZariskiSheaf B)
    {Γ : List K} {Δ : List L} (h : Γ.map g = Δ) :
    sheafTuple (A ∘ g) Γ ⟶ sheafTuple A Δ :=
  ⟨{ app := fun U => ↾fun a =>
       cast (congrArg (Assignment (fun i => (A i).val.obj U)) h)
         (Assignment.mapSorts (X := fun i => (A i).val.obj U) g a)
     naturality := by
       subst Δ
       exact (renameTuple g A Γ).val.naturality }⟩

/-- A total operation on the reduct is the original operation on the retyped arguments. -/
private def renameTotal {K L : Type u} (g : K → L) (A : L → ZariskiSheaf B)
    {a : Arity K} {b : Arity L} (h : ⟨a.inputs.map g, g a.output⟩ = b)
    (op : sheafTuple A b.inputs ⟶ A b.output) :
    sheafTuple (A ∘ g) a.inputs ⟶ A (g a.output) :=
  ⟨{ app := fun U => ↾fun x =>
       cast (congrArg (fun arity : Arity L => (A arity.output).val.obj U) h.symm)
         (op.val.app U ((renameTupleAt g A (congrArg Arity.inputs h)).val.app U x))
     naturality := by
       subst b
       exact (renameTuple g A a.inputs ≫ op).val.naturality }⟩

/-- The partial operation on the reduct uses the original operation on the retyped domain. -/
private def renamePartial {K L : Type u} (g : K → L) (A : L → ZariskiSheaf B)
    {a : Arity K} {b : Arity L} (h : ⟨a.inputs.map g, g a.output⟩ = b)
    (P : SheafPredicate (sheafTuple A b.inputs)) (op : P.toSheaf ⟶ A b.output) :
    (P.preimage (renameTupleAt g A (congrArg Arity.inputs h))).toSheaf ⟶ A (g a.output) :=
  let r := renameTupleAt g A (congrArg Arity.inputs h)
  ⟨{ app := fun U => ↾fun x =>
       cast (congrArg (fun arity : Arity L => (A arity.output).val.obj U) h.symm)
         (op.val.app U ⟨r.val.app U x.val, x.property⟩)
     naturality := by
       subst b
       exact (SheafPredicate.mapAlong (renameTuple g A _) (P := P.preimage (renameTuple g A _))
         (Q := P) le_rfl ≫ op).val.naturality }⟩

/-- Restrict a sheaf structure to the selected Part I names and arities. -/
def restrictDeclarations (names : SignatureNames S T)
    (A : SheafStructure T (Scheme.zariskiTopology.over B)) :
    SheafStructure S (Scheme.zariskiTopology.over B) where
  carrier := A.carrier ∘ names.onSort
  total p := renameTotal names.onSort A.carrier (names.totalArity p) (A.total (names.onTotal p))
  relation r := (A.relation (names.onRel r)).preimage (renameTupleAt names.onSort A.carrier (names.relInputs r))
  partialDomain p := (A.partialDomain (names.onPartial p)).preimage
    (renameTupleAt names.onSort A.carrier (congrArg Arity.inputs (names.partialArity p)))
  partialValue p := renamePartial names.onSort A.carrier (names.partialArity p)
    (A.partialDomain (names.onPartial p)) (A.partialValue (names.onPartial p))
  quantity q := renameTotal names.onSort A.carrier (names.quantityArity q) (A.quantity (names.onQuantity q))

/-- Changing coefficients on a native map keeps each original carrier function. -/
theorem restrictConstantStructureMap_onSort (f : B' ⟶ B) {A C : Structure T}
    (h : StructureMap A C) (s : T.SortType) :
    (restrictStructureMap f (constantStructureMap B h)).onSort s =
      (constantStructureMap B' h).onSort s := by
  ext U a
  rfl

/-- Changing coefficients on a native arrow gives its constant realization over the new base. -/
theorem restrictConstantStructureMap_eq (f : B' ⟶ B) {A C : Structure T}
    (h : StructureMap A C) :
    restrictStructureMap f (constantStructureMap B h) = constantStructureMap B' h :=
  SheafStructure.Hom.ext (funext (restrictConstantStructureMap_onSort f h))

/-- Pulling coefficients back commutes with the named reduct of a copying structure. -/
theorem restrictStructure_restrictDeclarations (f : B' ⟶ B) (names : SignatureNames S T)
    (A : SheafStructure T (Scheme.zariskiTopology.over B)) :
    restrictStructure f (restrictDeclarations names A) =
      restrictDeclarations names (restrictStructure f A) := by
  rfl

end SHIGURE.Copying
