import Formal.SHIGURE.Part1.Signature
import Formal.SHIGURE.Part2.Schemes.ModuleTensor
import Mathlib.CategoryTheory.Pi.Basic

/-! # Tensor structures on a scheme

Definition 6.1 and equation (6.1): carriers are actual sheaves of modules
over an arbitrary scheme, and primitive operations are morphisms from the
ordered tensor product of their input carriers. Structure-preserving maps
are the morphisms used in Lemma 6.2, including noninvertible maps.

## Implementation notes

The data use `Scheme.Modules` and the sheafified tensor product constructed
in `SchemeDescent`. Global sections would lose the local sheaf data, and
an affine chart is therefore not part of a structure. Finite local
freeness, prescribed rank, and Law satisfaction are separate properties;
they are not assumptions of this data category. The coefficient base
scheme is also independent of a chosen map to a coefficient ring.

Morphisms impose the usual commuting diagrams. Their identity and
composition use the functoriality of the tensor product, rather than
adding functoriality certificates to the objects. The carrier functor
connects the category to mathlib's product category of module sheaves.
-/

namespace SHIGURE.SchemeDescent

open AlgebraicGeometry CategoryTheory

universe u

variable {X : Scheme.{u}} {S : Type u}

/-- API for the ordered sheaf tensor: identity carrier maps induce an identity. -/
theorem tensorModulesMap_id (E : S → X.Modules) (ss : List S) :
    tensorModulesMap (fun s => 𝟙 (E s)) ss = 𝟙 (tensorModules E ss) := by
  induction ss with
  | nil => rfl
  | cons s ss ih =>
    change tensorModuleMap (𝟙 (E s)) (tensorModulesMap (fun t => 𝟙 (E t)) ss) = _
    rw [ih, tensorModuleMap_id]
    rfl

/-- API for the ordered sheaf tensor: induced maps preserve composition. -/
theorem tensorModulesMap_comp {E F G : S → X.Modules}
    (f : ∀ s, E s ⟶ F s) (g : ∀ s, F s ⟶ G s) (ss : List S) :
    tensorModulesMap (fun s => f s ≫ g s) ss =
      tensorModulesMap f ss ≫ tensorModulesMap g ss := by
  induction ss with
  | nil => exact (Category.id_comp _).symm
  | cons s ss ih =>
    change tensorModuleMap (f s ≫ g s) (tensorModulesMap (fun t => f t ≫ g t) ss) = _
    rw [ih, tensorModuleMap_comp]
    rfl

end SHIGURE.SchemeDescent

namespace SHIGURE.RealizationFamilies

open AlgebraicGeometry CategoryTheory SchemeDescent

noncomputable section

universe u

/-- The module and multilinear-operation data of Definition 6.1 on a scheme.
The empty tensor input is `𝒪_X`, so nullary operations are included. -/
structure SchemeTensorStructure (X : Scheme.{u}) (sig : Signature.{u}) where
  /-- The sheaf of modules at each carrier sort. -/
  carrier : sig.SortType → X.Modules
  /-- The module-sheaf morphism interpreting a total primitive operation. -/
  total (op : sig.Total) :
    tensorModules carrier (sig.totalArity op).inputs ⟶ carrier (sig.totalArity op).output
  /-- The module-sheaf morphism interpreting a primitive quantity. -/
  quantity (q : sig.Quantity) :
    tensorModules carrier (sig.quantityArity q).inputs ⟶ carrier (sig.quantityArity q).output

namespace SchemeTensorStructure

variable {X : Scheme.{u}} {sig : Signature.{u}}

/-- API for the data of Definition 6.1: carrier and primitive-map data
determine a structure. Heterogeneous equality transports the maps when
the carrier family changes. -/
@[ext]
theorem ext {A B : SchemeTensorStructure X sig}
    (carrier : A.carrier = B.carrier)
    (total : HEq A.total B.total) (quantity : HEq A.quantity B.quantity) : A = B := by
  cases A
  cases B
  cases carrier
  cases total
  cases quantity
  rfl

/-- A structure-preserving family of module-sheaf maps, as in Lemma 6.2.
Its equations express preservation of the primitive operation data. -/
structure Hom (A B : SchemeTensorStructure X sig) where
  /-- The carrier map at a sort. -/
  onSort (s : sig.SortType) : A.carrier s ⟶ B.carrier s
  /-- The diagram for a total primitive operation commutes. -/
  preservesTotal (op : sig.Total) :
    A.total op ≫ onSort _ = tensorModulesMap onSort _ ≫ B.total op
  /-- The diagram for a primitive quantity commutes. -/
  preservesQuantity (q : sig.Quantity) :
    A.quantity q ≫ onSort _ = tensorModulesMap onSort _ ≫ B.quantity q

namespace Hom

variable {A B C : SchemeTensorStructure X sig}

/-- API for structure-preserving maps: the carrier maps determine a morphism. -/
@[ext]
theorem ext {f g : Hom A B} (h : ∀ s, f.onSort s = g.onSort s) : f = g := by
  have same : f.onSort = g.onSort := funext h
  cases f
  cases g
  cases same
  rfl

/-- Identity carrier morphisms preserve the primitive maps.
Implementation notes: this lifts the identity of module sheaves using
finite tensor functoriality, with no assumptions on the carriers. -/
@[simps]
def id (A : SchemeTensorStructure X sig) : Hom A A where
  onSort _ := 𝟙 _
  preservesTotal op := by
    rw [tensorModulesMap_id]
    simp
  preservesQuantity q := by
    rw [tensorModulesMap_id]
    simp

/-- Composition lifts composition of module sheaves.
Implementation notes: the preservation proof pastes the two commuting
diagrams and uses tensor functoriality; no inverse is required. -/
@[simps]
def comp (f : Hom A B) (g : Hom B C) : Hom A C where
  onSort s := f.onSort s ≫ g.onSort s
  preservesTotal op := by
    rw [← Category.assoc, f.preservesTotal, Category.assoc, g.preservesTotal,
      tensorModulesMap_comp, Category.assoc]
  preservesQuantity q := by
    rw [← Category.assoc, f.preservesQuantity, Category.assoc, g.preservesQuantity,
      tensorModulesMap_comp, Category.assoc]

end Hom

/-- The data of Definition 6.1 and all structure-preserving maps form a category. -/
instance : Category (SchemeTensorStructure X sig) where
  Hom := Hom
  id := Hom.id
  comp := Hom.comp
  id_comp f := Hom.ext fun s => Category.id_comp (f.onSort s)
  comp_id f := Hom.ext fun s => Category.comp_id (f.onSort s)
  assoc f g h := Hom.ext fun s => Category.assoc (f.onSort s) (g.onSort s) (h.onSort s)

/-- API for the categorical identity: its carrier map is the identity.
The simplifier eliminates the carrier projection of an identity. -/
@[simp]
theorem id_onSort (A : SchemeTensorStructure X sig) (s : sig.SortType) :
    (𝟙 A : A ⟶ A).onSort s = 𝟙 (A.carrier s) := rfl

/-- API for categorical composition: compute the carrier map by composition.
The simplifier eliminates the carrier projection of a composite. -/
@[simp]
theorem comp_onSort {A B C : SchemeTensorStructure X sig}
    (f : A ⟶ B) (g : B ⟶ C) (s : sig.SortType) :
    (f ≫ g).onSort s = f.onSort s ≫ g.onSort s := rfl

/-- Forget primitive operations to obtain the family of carrier module sheaves.
Implementation notes: the target is mathlib's product category, retaining
the module-sheaf maps and their composition at every sort. -/
@[simps]
def carrierFunctor : SchemeTensorStructure X sig ⥤ (sig.SortType → X.Modules) where
  obj A := A.carrier
  map f := f.onSort

/-- The carrier functor is faithful because preservation has no extra map data. -/
instance : (carrierFunctor (X := X) (sig := sig)).Faithful where
  map_injective h := Hom.ext fun s => congrFun h s

end SchemeTensorStructure

end

end SHIGURE.RealizationFamilies
