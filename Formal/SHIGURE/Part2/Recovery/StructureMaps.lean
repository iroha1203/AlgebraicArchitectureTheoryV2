import Formal.SHIGURE.Part2.Recovery.ConstantFormulas
import Formal.SHIGURE.Part2.Recovery.ConstantMaps
import Formal.SHIGURE.Part2.Realizations.SectionStructures
import Formal.SHIGURE.Part1.StructureCategory

/-!
# Recovering maps of globally split structures

A native map acts on locally constant sections by postcomposition.
Conversely the structure on the sections of the identity test detects
all its native operations and relations at a point of the base.
-/

open AlgebraicGeometry CategoryTheory Opposite

universe u

noncomputable section

namespace SHIGURE.Copying

variable {S : Scheme.{u}} {sig : Signature.{u}} {Γ : List sig.SortType} {A B : Structure sig}

/-- The tuple predicate holds precisely when every point has a value in the native subset. -/
private theorem mem_constantTuplePredicate (A : Structure sig) (T : Over S)
    (p : Set (Assignment A.carrier Γ))
    (a : (sheafTuple (constantStructure S A).carrier Γ).val.obj (op T)) :
    a ∈ ((constantPredicate S p).preimage (constantTupleMap S A.carrier Γ)).carrier.obj (op T) ↔
      ∀ x : T.left, nativeAssignmentAt A a x ∈ p :=
  mem_constantPredicate S p (op T) ((constantTupleMap S A.carrier Γ).val.app (op T) a)

/-- Evaluating sections at a point preserves all native primitive interpretations. -/
def evaluateConstantSections (A : Structure sig) (T : Over S) (x : T.left) :
    StructureMap ((constantStructure S A).sections (op T)) A where
  onSort s a :=
    let b : LocallyConstant T.left (A.carrier s) := a
    b x
  total_comm _ _ := rfl
  relation_mem r a ha := (mem_constantTuplePredicate A T (A.relation r) a).mp ha x
  partial_mem p a ha := (mem_constantTuplePredicate A T (A.partialDomain p) a).mp ha x
  partial_comm _ _ := rfl
  quantity_comm _ _ := rfl

/-- Native constant sections preserve the operations, relations, and domains of the original structure. -/
def constantSections (A : Structure sig) (T : Over S) :
    StructureMap A ((constantStructure S A).sections (op T)) where
  onSort _ := nativeState S T
  total_comm _ _ := LocallyConstant.ext fun _ => rfl
  relation_mem r a ha :=
    (mem_constantTuplePredicate A T (A.relation r) (a.map (fun _ => nativeState S T))).mpr fun _ => ha
  partial_mem p a ha :=
    (mem_constantTuplePredicate A T (A.partialDomain p) (a.map (fun _ => nativeState S T))).mpr fun _ => ha
  partial_comm _ _ := LocallyConstant.ext fun _ => rfl
  quantity_comm _ _ := LocallyConstant.ext fun _ => rfl

/-- A native structure map acts on all the sheaf carriers and preserves all the primitives. -/
def constantStructureMap (S : Scheme.{u}) (h : StructureMap A B) :
    SheafStructure.Hom (constantStructure S A) (constantStructure S B) where
  onSort s := constantCarrierMap S (h.onSort s)
  preservesTotal f := by
    ext U a
    apply LocallyConstant.ext
    intro x
    exact h.total_comm f (nativeAssignmentAt A a x)
  preservesRelation r := by
    intro U a ha
    apply (mem_constantTuplePredicate B U.unop (B.relation r) _).mpr
    intro x
    exact h.relation_mem r (nativeAssignmentAt A a x)
      ((mem_constantTuplePredicate A U.unop (A.relation r) a).mp ha x)
  preservesDomain p := by
    intro U a ha
    apply (mem_constantTuplePredicate B U.unop (B.partialDomain p) _).mpr
    intro x
    exact h.partial_mem p (nativeAssignmentAt A a x)
      ((mem_constantTuplePredicate A U.unop (A.partialDomain p) a).mp ha x)
  preservesPartial p := by
    ext U a
    apply LocallyConstant.ext
    intro x
    exact h.partial_comm p ⟨nativeAssignmentAt A a.val x,
      (mem_constantTuplePredicate A U.unop (A.partialDomain p) a.val).mp a.property x⟩
  preservesQuantity q := by
    ext U a
    apply LocallyConstant.ext
    intro x
    exact h.quantity_comm q (nativeAssignmentAt A a x)

/-- Read the maps on native sections of the identity test at a point of the base. -/
def readConstantStructureMap [Nonempty S]
    (f : SheafStructure.Hom (constantStructure S A) (constantStructure S B)) : StructureMap A B :=
  let T : Over S := Over.mk (𝟙 S)
  let x : S := Classical.choice inferInstance
  (evaluateConstantSections B T x).comp ((f.sections (op T)).comp (constantSections A T))

/-- The carrier maps of the recovered structure map are the recovered maps of carrier sheaves. -/
theorem readConstantStructureMap_onSort [Nonempty S]
    (f : SheafStructure.Hom (constantStructure S A) (constantStructure S B)) (s : sig.SortType) :
    (readConstantStructureMap f).onSort s = readConstantCarrierMap (f.onSort s) :=
  rfl

/-- All structure-preserving arrows between constant realizations correspond to native arrows. -/
def constantStructureMapsEquiv [PreconnectedSpace S] [Nonempty S] :
    StructureMap A B ≃ SheafStructure.Hom (constantStructure S A) (constantStructure S B) where
  toFun := constantStructureMap S
  invFun := readConstantStructureMap
  left_inv _ := StructureMap.ext fun _ _ => rfl
  right_inv f := SheafStructure.Hom.ext (funext fun s => constantCarrierMap_readConstantCarrierMap (f.onSort s))

/-- Taking the constant realization preserves identities and composites of native arrows. -/
def constantStructureFunctor (sig : Signature.{u}) (S : Scheme.{u}) :
    Structure sig ⥤ SheafStructure sig (Scheme.zariskiTopology.over S) where
  obj := constantStructure S
  map := constantStructureMap S
  map_id A := by
    apply SheafStructure.Hom.ext
    funext s
    ext U a
    apply LocallyConstant.ext
    intro x
    rfl
  map_comp f g := by
    apply SheafStructure.Hom.ext
    funext s
    ext U a
    apply LocallyConstant.ext
    intro x
    rfl

end SHIGURE.Copying
