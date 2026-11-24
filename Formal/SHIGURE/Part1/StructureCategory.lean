import Formal.SHIGURE.Part1.StructureMaps
import Mathlib.CategoryTheory.Category.Basic
import Mathlib.CategoryTheory.Iso

/-! # The category of structures and its isomorphisms

## Implementation notes

The category uses the existing `StructureMap` of Definition 2.1 as its Hom type.
Reflection is tested on the forward image of each original tuple so that it is a
predicate on any map, without choosing an inverse until bijectivity is available.
-/

universe u

namespace SHIGURE.StructureMap

variable {sig : Signature.{u}} {A B C D : Structure sig}

/-- Identity consists of the identity map on each sort. -/
def id (A : Structure sig) : StructureMap A A where
  onSort s := _root_.id
  total_comm _ _ := by rw [Assignment.map_id]; rfl
  relation_mem _ _ := by rw [Assignment.map_id]; exact _root_.id
  partial_mem _ _ := by rw [Assignment.map_id]; exact _root_.id
  partial_comm p xs := by
    have kept : xs.val.map (fun _ => _root_.id) ∈ A.partialDomain p := by
      rw [Assignment.map_id]
      exact xs.property
    have same : (⟨xs.val.map (fun _ => _root_.id), kept⟩ : A.partialDomain p) = xs :=
      Subtype.ext (Assignment.map_id xs.val)
    rw [same]
    rfl
  quantity_comm _ _ := by rw [Assignment.map_id]; rfl

/-- Composition maps each sort by the corresponding composite of functions. -/
def comp (g : StructureMap B C) (f : StructureMap A B) : StructureMap A C where
  onSort s := g.onSort s ∘ f.onSort s
  total_comm op xs := by
    change g.onSort _ (f.onSort _ (A.total op xs)) = _
    rw [f.total_comm, g.total_comm, Assignment.map_map]
  relation_mem r xs h := g.relation_mem r _ (f.relation_mem r xs h)
  partial_mem p xs h := g.partial_mem p _ (f.partial_mem p xs h)
  partial_comm p xs := by
    change g.onSort _ (f.onSort _ (A.partialValue p xs)) = _
    rw [f.partial_comm]
    exact g.partial_comm p ⟨xs.val.map f.onSort, f.partial_mem p xs.val xs.property⟩
  quantity_comm q xs := by
    change g.onSort _ (f.onSort _ (A.quantity q xs)) = _
    rw [f.quantity_comm, g.quantity_comm, Assignment.map_map]

/-- A structure's identity law is the identity at every component. -/
@[simp] theorem id_comp (f : StructureMap A B) : (id B).comp f = f :=
  ext (fun _ _ => rfl)

/-- Identity on the source leaves a structure map unchanged. -/
@[simp] theorem comp_id (f : StructureMap A B) : f.comp (id A) = f :=
  ext (fun _ _ => rfl)

/-- The two orders of composing three structure maps agree. -/
theorem comp_assoc (h : StructureMap C D) (g : StructureMap B C) (f : StructureMap A B) :
    h.comp (g.comp f) = (h.comp g).comp f :=
  ext (fun _ _ => rfl)

end SHIGURE.StructureMap

namespace SHIGURE.Structure

open CategoryTheory

variable {sig : Signature.{u}}

/-- The category of structures and structure-preserving maps of a fixed signature. -/
instance category : CategoryTheory.Category.{u} (Structure sig) where
  Hom := StructureMap
  id := StructureMap.id
  comp f g := g.comp f
  id_comp := StructureMap.comp_id
  comp_id := StructureMap.id_comp
  assoc f g h := h.comp_assoc g f

/-- The identity arrow acts as the identity on every carrier. -/
@[simp] theorem id_apply (A : Structure sig) (s : sig.SortType) (x : A.carrier s) :
    (show StructureMap A A from 𝟙 A).onSort s x = x := rfl

/-- A composite arrow acts by applying the source and target carrier maps in order. -/
theorem comp_apply {A B C : Structure sig} (f : A ⟶ B) (g : B ⟶ C)
    (s : sig.SortType) (x : A.carrier s) :
    (show StructureMap A C from f ≫ g).onSort s x =
      (show StructureMap B C from g).onSort s ((show StructureMap A B from f).onSort s x) := rfl

end SHIGURE.Structure

namespace SHIGURE.StructureMap

variable {sig : Signature.{u}} {A B : Structure sig}

/-- Reflection of the primitive relations along the family of carrier maps. -/
def ReflectsRelations (f : StructureMap A B) : Prop :=
  ∀ r (xs : Assignment A.carrier (sig.relInputs r)),
    xs.map f.onSort ∈ B.relation r → xs ∈ A.relation r

/-- Reflection of the partial domains along the family of carrier maps. -/
def ReflectsDomains (f : StructureMap A B) : Prop :=
  ∀ p (xs : Assignment A.carrier (sig.partialArity p).inputs),
    xs.map f.onSort ∈ B.partialDomain p → xs ∈ A.partialDomain p

/-- The inverse family of a componentwise bijective structure map. -/
noncomputable def inverseFamily (f : StructureMap A B) (bijective : ∀ s, Function.Bijective (f.onSort s)) :
    ∀ s, B.carrier s → A.carrier s :=
  fun s => (Equiv.ofBijective _ (bijective s)).symm

/-- A forward coordinate map sends an inverse value back to its original value. -/
theorem forward_inverseFamily (f : StructureMap A B) (bijective : ∀ s, Function.Bijective (f.onSort s))
    (s : sig.SortType) (x : B.carrier s) : f.onSort s (f.inverseFamily bijective s x) = x :=
  (Equiv.ofBijective _ (bijective s)).apply_symm_apply x

/-- An inverse coordinate map sends a forward value back to its original value. -/
theorem inverseFamily_forward (f : StructureMap A B) (bijective : ∀ s, Function.Bijective (f.onSort s))
    (s : sig.SortType) (x : A.carrier s) : f.inverseFamily bijective s (f.onSort s x) = x :=
  (Equiv.ofBijective _ (bijective s)).symm_apply_apply x

/-- An inverse assignment maps back to the starting tuple. -/
theorem map_inverseFamily_forward (f : StructureMap A B) (bijective : ∀ s, Function.Bijective (f.onSort s))
    {Γ : List sig.SortType} (xs : Assignment B.carrier Γ) :
    (xs.map (f.inverseFamily bijective)).map f.onSort = xs := by
  apply Assignment.ext
  intro s i
  exact f.forward_inverseFamily bijective s (xs i)

/-- A componentwise bijective structure map has an inverse when the predicates are reflected. -/
noncomputable def inverse (f : StructureMap A B) (bijective : ∀ s, Function.Bijective (f.onSort s))
    (relation : f.ReflectsRelations) (domain : f.ReflectsDomains) :
    StructureMap B A where
  onSort := f.inverseFamily bijective
  total_comm op xs := by
    apply (bijective _).injective
    rw [f.forward_inverseFamily, f.total_comm, f.map_inverseFamily_forward]
  relation_mem r xs h :=
    relation r (xs.map (f.inverseFamily bijective)) ((f.map_inverseFamily_forward bijective xs).symm ▸ h)
  partial_mem p xs h :=
    domain p (xs.map (f.inverseFamily bijective)) ((f.map_inverseFamily_forward bijective xs).symm ▸ h)
  partial_comm p xs := by
    let inverseInput : A.partialDomain p :=
      ⟨xs.val.map (f.inverseFamily bijective),
        domain p _ ((f.map_inverseFamily_forward bijective xs.val).symm ▸ xs.property)⟩
    change f.inverseFamily bijective _ (B.partialValue p xs) = A.partialValue p inverseInput
    apply (bijective _).injective
    rw [f.forward_inverseFamily, f.partial_comm]
    have same : (⟨inverseInput.val.map f.onSort, f.partial_mem p _ inverseInput.property⟩ : B.partialDomain p) =
        xs := Subtype.ext (f.map_inverseFamily_forward bijective xs.val)
    rw [same]
  quantity_comm q xs := by
    apply (bijective _).injective
    rw [f.forward_inverseFamily, f.quantity_comm, f.map_inverseFamily_forward]

/-- Bijectivity with reflection gives a categorical isomorphism with the original forward map. -/
noncomputable def iso_of_bijective_reflects (f : StructureMap A B)
    (bijective : ∀ s, Function.Bijective (f.onSort s))
    (relation : f.ReflectsRelations) (domain : f.ReflectsDomains) :
    CategoryTheory.Iso A B where
  hom := f
  inv := f.inverse bijective relation domain
  hom_inv_id := ext (fun s x => f.inverseFamily_forward bijective s x)
  inv_hom_id := ext (fun s x => f.forward_inverseFamily bijective s x)

end SHIGURE.StructureMap

namespace SHIGURE.Structure

open CategoryTheory
variable {sig : Signature.{u}} {A B : Structure sig}

/-- Each component of a structure isomorphism is a type equivalence. -/
def isoComponent (e : A ≅ B) (s : sig.SortType) : A.carrier s ≃ B.carrier s where
  toFun := (show StructureMap A B from e.hom).onSort s
  invFun := (show StructureMap B A from e.inv).onSort s
  left_inv x := congrArg (fun f : StructureMap A A => f.onSort s x) e.hom_inv_id
  right_inv x := congrArg (fun f : StructureMap B B => f.onSort s x) e.inv_hom_id

/-- Mapping a tuple along an isomorphism and its inverse recovers the tuple. -/
theorem assignment_hom_inv (e : A ≅ B) {Γ : List sig.SortType} (xs : Assignment A.carrier Γ) :
    (xs.map (show StructureMap A B from e.hom).onSort).map
      (show StructureMap B A from e.inv).onSort = xs := by
  apply Assignment.ext
  intro s i
  exact (isoComponent e s).symm_apply_apply (xs i)

/-- The inverse of a structure isomorphism witnesses reflection of relations. -/
theorem reflects_relations (e : A ≅ B) : (show StructureMap A B from e.hom).ReflectsRelations := by
  intro r xs held
  have back := (show StructureMap B A from e.inv).relation_mem r _ held
  simpa only [assignment_hom_inv e] using back

/-- The inverse of a structure isomorphism witnesses reflection of partial domains. -/
theorem reflects_domains (e : A ≅ B) : (show StructureMap A B from e.hom).ReflectsDomains := by
  intro p xs held
  have back := (show StructureMap B A from e.inv).partial_mem p _ held
  simpa only [assignment_hom_inv e] using back

/-- A structure-preserving map is an isomorphism exactly when its components are bijections
and its inverse preserves the relation and domain predicates. -/
theorem isIso_iff_bijective_reflects (f : A ⟶ B) :
    IsIso f ↔ (∀ s, Function.Bijective ((show StructureMap A B from f).onSort s)) ∧
      (show StructureMap A B from f).ReflectsRelations ∧
      (show StructureMap A B from f).ReflectsDomains := by
  constructor
  · intro h
    let e := asIso f
    exact ⟨fun s => (isoComponent e s).bijective, reflects_relations e, reflects_domains e⟩
  · rintro ⟨bijective, relation, domain⟩
    let e := (show StructureMap A B from f).iso_of_bijective_reflects bijective relation domain
    change IsIso e.hom
    infer_instance

/-- Isomorphic structures satisfy the same Law sequents. -/
theorem law_holds_of_iso (e : A ≅ B) {law : Law sig} (satisfied : law.Holds A) : law.Holds B := by
  intro xs input
  let back : StructureMap B A := e.inv
  let forward : StructureMap A B := e.hom
  have old := back.holds_map law.input xs input
  have conclusion := forward.holds_map law.conclusion _ (satisfied _ old)
  have returned : (xs.map back.onSort).map forward.onSort = xs := assignment_hom_inv e.symm xs
  rwa [returned] at conclusion

end SHIGURE.Structure
