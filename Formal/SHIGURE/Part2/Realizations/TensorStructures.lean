import Formal.SHIGURE.Part1.Signature
import Mathlib.Algebra.Category.ModuleCat.Basic
import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
import Mathlib.LinearAlgebra.Multilinear.Basic

/-!
# Tensor realization structures

Definition 4.1 allows arbitrary modules as carriers. Each total operation
and quantity acts multilinearly on its finite tuple of inputs. A nullary
operation is evaluated at the empty tuple, giving a designated element.

## Implementation notes

The typed variable positions index mathlib multilinear maps. Using a
homogeneous product would lose the different module in each argument
position. Multilinear maps are used here as the maps represented by the
corresponding tensor products.
-/

open CategoryTheory

universe u

namespace SHIGURE

variable (R : Type u) [CommRing R]

/-- A multilinear tensor operation with the input and output sorts of its arity. -/
abbrev TensorOperation {S : Type u} (M : S → ModuleCat.{u} R) (a : Arity S) :=
  MultilinearMap R (fun i : (s : S) × Var a.inputs s => M i.1) (M a.output)

/-- The module-valued part of the tensor realization scheme of Definition 4.1. -/
structure TensorStructure (sig : Signature.{u}) where
  /-- Any module over the chosen coefficients is an allowed carrier. -/
  carrier : sig.SortType → ModuleCat.{u} R
  /-- Each total operation is multilinear in its typed inputs. -/
  total (f : sig.Total) : TensorOperation R carrier (sig.totalArity f)
  /-- Each quantity is a multilinear operation in its typed inputs. -/
  quantity (q : sig.Quantity) : TensorOperation R carrier (sig.quantityArity q)

namespace TensorStructure

variable {R} {sig : Signature.{u}}

/-- A nullary total operation picks a designated element of its output sort. -/
def designated (A : TensorStructure R sig) (f : sig.Total)
    (h : (sig.totalArity f).inputs = []) : A.carrier (sig.totalArity f).output :=
  A.total f fun i => nomatch (h ▸ i.2 : Var [] i.1)

/-- A tensor Law equates two multilinear expressions of the same input and output types. -/
def tensorEquality (A : TensorStructure R sig) (a : Arity sig.SortType)
    (left right : TensorOperation R A.carrier a) : Prop :=
  left = right

/-- A map of tensor structures is a family of linear maps preserving the operations and quantities. -/
structure Hom (A B : TensorStructure R sig) where
  /-- The linear map between the modules at a carrier sort. -/
  onSort (s : sig.SortType) : A.carrier s →ₗ[R] B.carrier s
  /-- Total operations commute with the carrier maps. -/
  preservesTotal (f : sig.Total) (xs : ∀ i : (s : sig.SortType) × Var (sig.totalArity f).inputs s,
      A.carrier i.1) :
    onSort _ (A.total f xs) = B.total f (fun i => onSort i.1 (xs i))
  /-- Quantities commute with the carrier maps. -/
  preservesQuantity (q : sig.Quantity) (xs : ∀ i : (s : sig.SortType) × Var (sig.quantityArity q).inputs s,
      A.carrier i.1) :
    onSort _ (A.quantity q xs) = B.quantity q (fun i => onSort i.1 (xs i))

namespace Hom

variable {A B D : TensorStructure R sig}

/-- A structure-preserving linear map sends each designated element to its corresponding element. -/
theorem preserves_designated (f : Hom A B) (n : sig.Total) (h : (sig.totalArity n).inputs = []) :
    f.onSort _ (A.designated n h) = B.designated n h := by
  unfold designated
  rw [f.preservesTotal]
  congr 1
  funext i
  exact nomatch (h ▸ i.2 : Var [] i.1)

/-- The carrier maps determine a tensor structure morphism. -/
@[ext]
theorem ext {f g : Hom A B} (h : f.onSort = g.onSort) : f = g := by
  cases f
  cases g
  cases h
  rfl

/-- The identity linear maps preserve every tensor operation. -/
def id (A : TensorStructure R sig) : Hom A A where
  onSort _ := LinearMap.id
  preservesTotal _ _ := rfl
  preservesQuantity _ _ := rfl

/-- Linear maps preserving the tensor operations compose sort by sort. -/
def comp (f : Hom A B) (g : Hom B D) : Hom A D where
  onSort s := (g.onSort s).comp (f.onSort s)
  preservesTotal op xs := by
    simp only [LinearMap.comp_apply]
    rw [f.preservesTotal, g.preservesTotal]
  preservesQuantity q xs := by
    simp only [LinearMap.comp_apply]
    rw [f.preservesQuantity, g.preservesQuantity]

end Hom

/-- Tensor structures and their structure-preserving linear maps form a category. -/
instance : Category (TensorStructure R sig) where
  Hom := Hom
  id := Hom.id
  comp := Hom.comp
  id_comp f := Hom.ext (funext fun s => LinearMap.comp_id (f.onSort s))
  comp_id f := Hom.ext (funext fun s => LinearMap.id_comp (f.onSort s))
  assoc f g h := Hom.ext (funext fun s => (LinearMap.comp_assoc (f.onSort s) (g.onSort s) (h.onSort s)).symm)

end TensorStructure

/-- Two tensor expressions with the same typed input and output are a Law of the tensor scheme. -/
structure TensorLaw (sig : Signature.{u}) where
  /-- The common input and output types of the two expressions. -/
  arity : Arity sig.SortType
  /-- Evaluate the left typed expression in a given tensor realization. -/
  left (A : TensorStructure R sig) : TensorOperation R A.carrier arity
  /-- Evaluate the right typed expression in a given tensor realization. -/
  right (A : TensorStructure R sig) : TensorOperation R A.carrier arity

variable {R} {sig : Signature.{u}}

/-- A tensor realization satisfies a Law as equality of the interpreted tensor maps. -/
def TensorLaw.holds (law : TensorLaw R sig) (A : TensorStructure R sig) : Prop :=
  A.tensorEquality law.arity (law.left A) (law.right A)

/-- Required tensor Laws restrict the objects, with every structure-preserving linear map retained. -/
def tensorModelProperty {L : Type u} (law : L → TensorLaw R sig) :
    ObjectProperty (TensorStructure R sig) :=
  fun A => ∀ l : L, (law l).holds A

/-- The tensor-mode semantic category for a family of required typed expressions. -/
abbrev TensorModels {L : Type u} (law : L → TensorLaw R sig) :=
  (tensorModelProperty law).FullSubcategory

end SHIGURE
