import ResearchLean.AG.LocalSemanticReconstruction.PrimitiveFunctionGraphCategory
import ResearchLean.AG.LocalSemanticReconstruction.CompleteGeometryFunctionGraphSeparation
import Mathlib.CategoryTheory.Equivalence
import Formal.Util.AssertStandardAxioms

/-!
# Separation and assembly characterize categorical reconstruction

A reading functor is reconstructed from three independently stated pieces:
injectivity on every Hom set, an assembly map onto every local Hom, and an
assembly object whose reading is isomorphic to every local object.  Hom
assembly and separation give both inverse laws; object assembly gives essential
surjectivity.  Together they produce a categorical equivalence and uniqueness
of every assembled Hom.  Conversely, every categorical equivalence supplies
the same reconstruction data.

The theorem is realized by primitive total-functional Bool graphs: graph
reading and graph assembly give the Hom inverse, while wrapping a type supplies
the object inverse.  The complete-geometry graph reading from Cycle 64 realizes
the underlying indexed Hom-family separation contract for every package pair.
Its local category and assembly remain unconstructed here.

## Implementation notes

Separation, Hom assembly, and object assembly are separate structures so that
an application cannot conceal a missing assembly theorem inside injectivity.
The categorical equivalence is derived only after all three structures are
present.  Defining coherent local values as the image of a global morphism was
rejected because that would make assembly true by construction rather than by
independent local equations.
-/

namespace AAT.AG.LocalSemanticReconstruction

open CategoryTheory AtomFoundation GeometryTransport

noncomputable section

namespace LocalReconstructionEquivalence

universe v₁ v₂ u₁ u₂ u v

variable {C : Type u₁} [Category.{v₁} C]
variable {D : Type u₂} [Category.{v₂} D]

/-- A reading is separating when equal local values force equal global values. -/
structure ReadingSeparation {Global Local : Sort*} (read : Global → Local) : Prop where
  /-- The reading map is injective. -/
  injective : Function.Injective read

/-- Pointwise separation for an object-indexed family of global and local Hom
types.  No category or composition is required at this layer. -/
structure HomFamilySeparation (Object : Sort*)
    (GlobalHom LocalHom : Object → Object → Sort*)
    (read : ∀ {X Y}, GlobalHom X Y → LocalHom X Y) : Prop where
  /-- Every indexed Hom reading is separating. -/
  hom : ∀ X Y, ReadingSeparation (@read X Y)

/-- Hom separation for a functor is the indexed-family contract specialized to
the source and target Hom types of that functor. -/
abbrev HomSeparation (F : C ⥤ D) :=
  HomFamilySeparation C
    (fun X Y => X ⟶ Y)
    (fun X Y => F.obj X ⟶ F.obj Y)
    (fun morphism => F.map morphism)

/-- Assembly of every local Hom, with only the read-after-assembly law. -/
structure HomAssembly (F : C ⥤ D) where
  /-- Assemble one local Hom into a global Hom. -/
  assemble {X Y : C} : (F.obj X ⟶ F.obj Y) → (X ⟶ Y)
  /-- Reading an assembled local Hom recovers it. -/
  map_assemble {X Y : C} (localMorphism : F.obj X ⟶ F.obj Y) :
    F.map (assemble localMorphism) = localMorphism

/-- Assembly of local objects up to the isomorphism required by categorical
reconstruction. -/
structure ObjectAssembly (F : C ⥤ D) where
  /-- Assemble one local object. -/
  assembleObject : D → C
  /-- Reading the assembled object recovers the local object up to isomorphism. -/
  readAssembledIso (localObject : D) :
    F.obj (assembleObject localObject) ≅ localObject

/-- The complete separation-and-assembly contract for a reading functor. -/
structure ReconstructionData (F : C ⥤ D) where
  /-- Separation is logically independent of assembly. -/
  separation : HomSeparation F
  /-- Every local Hom assembles. -/
  homAssembly : HomAssembly F
  /-- Every local object assembles up to isomorphism. -/
  objectAssembly : ObjectAssembly F

namespace ReconstructionData

variable {F : C ⥤ D} (data : ReconstructionData F)

/-- Assembly after reading follows from the independent separation and
read-after-assembly hypotheses. -/
@[simp]
theorem assemble_map {X Y : C} (global : X ⟶ Y) :
    data.homAssembly.assemble (F.map global) = global := by
  apply (data.separation.hom X Y).injective
  exact data.homAssembly.map_assemble (F.map global)

/-- Reading and assembly give an explicit equivalence on every Hom set. -/
def homEquiv (X Y : C) : (X ⟶ Y) ≃ (F.obj X ⟶ F.obj Y) where
  toFun := F.map
  invFun := data.homAssembly.assemble
  left_inv := data.assemble_map
  right_inv := data.homAssembly.map_assemble

/-- The reconstruction contract supplies Mathlib's fully faithful structure. -/
def fullyFaithful : F.FullyFaithful where
  preimage := data.homAssembly.assemble
  map_preimage := data.homAssembly.map_assemble
  preimage_map := data.assemble_map

/-- The reconstruction contract supplies essential surjectivity without
choosing an unspecified global preimage. -/
def essSurj : F.EssSurj where
  mem_essImage localObject :=
    ⟨data.objectAssembly.assembleObject localObject,
      ⟨data.objectAssembly.readAssembledIso localObject⟩⟩

/-- Separation and both assembly clauses produce a categorical equivalence. -/
noncomputable def equivalence : C ≌ D := by
  let fullyFaithful := data.fullyFaithful
  letI : F.Faithful := fullyFaithful.faithful
  letI : F.Full := fullyFaithful.full
  letI : F.EssSurj := data.essSurj
  letI : F.IsEquivalence :=
    { faithful := inferInstance
      full := inferInstance
      essSurj := inferInstance }
  exact F.asEquivalence

/-- Every local Hom has exactly one global preimage under reading. -/
theorem existsUnique_preimage (data : ReconstructionData F) {X Y : C}
    (localMorphism : F.obj X ⟶ F.obj Y) :
    ∃! global : X ⟶ Y, F.map global = localMorphism := by
  refine ⟨(ReconstructionData.homEquiv (F := F) data X Y).symm localMorphism,
    (ReconstructionData.homEquiv (F := F) data X Y).apply_symm_apply
      localMorphism, ?_⟩
  intro global equality
  exact (ReconstructionData.homEquiv (F := F) data X Y).injective
    (equality.trans
      ((ReconstructionData.homEquiv (F := F) data X Y).apply_symm_apply
        localMorphism).symm)

end ReconstructionData

/-- Every categorical equivalence provides explicit separation, Hom assembly,
and object assembly data for its forward functor. -/
def ofEquivalence (equivalence : C ≌ D) :
    ReconstructionData equivalence.functor where
  separation :=
    ⟨fun _ _ =>
      ⟨fun _ _ equality =>
        equivalence.fullyFaithfulFunctor.map_injective equality⟩⟩
  homAssembly :=
    { assemble := equivalence.fullyFaithfulFunctor.preimage
      map_assemble := equivalence.fullyFaithfulFunctor.map_preimage }
  objectAssembly :=
    { assembleObject := equivalence.inverse.obj
      readAssembledIso := fun localObject =>
        equivalence.counitIso.app localObject }

/-- Being an equivalence is equivalent to carrying explicit separation and
assembly data. -/
theorem nonempty_reconstructionData_iff_isEquivalence (F : C ⥤ D) :
    Nonempty (ReconstructionData F) ↔ F.IsEquivalence := by
  constructor
  · rintro ⟨data⟩
    let fullyFaithful := data.fullyFaithful
    exact
      { faithful := fullyFaithful.faithful
        full := fullyFaithful.full
        essSurj := data.essSurj }
  · intro isEquivalence
    letI : F.IsEquivalence := isEquivalence
    exact ⟨ofEquivalence F.asEquivalence⟩

/-! ## Primitive Bool graphs realize the general reconstruction theorem -/

open PrimitiveFunctionGraph

/-- Primitive graph assembly is the independent Hom-assembly half. -/
def primitiveGraphHomAssembly :
    HomAssembly PrimitiveFunctionGraph.Object.toType where
  assemble := GraphCode.read
  map_assemble := GraphCode.assemble_read

/-- Primitive graph reading separates all graph morphisms. -/
def primitiveGraphHomSeparation :
    HomSeparation PrimitiveFunctionGraph.Object.toType where
  hom _ _ := ⟨GraphCode.assemble_injective⟩

/-- A local type assembles as the graph object carrying that type. -/
def primitiveGraphObjectAssembly :
    ObjectAssembly PrimitiveFunctionGraph.Object.toType where
  assembleObject localObject := ⟨localObject⟩
  readAssembledIso _ := Iso.refl _

/-- Primitive Bool graphs satisfy the complete reconstruction contract. -/
def primitiveGraphReconstructionData :
    ReconstructionData PrimitiveFunctionGraph.Object.toType where
  separation := primitiveGraphHomSeparation
  homAssembly := primitiveGraphHomAssembly
  objectAssembly := primitiveGraphObjectAssembly

/-- The category of primitive total-functional Bool graphs is equivalent to
the category of types and arbitrary functions. -/
noncomputable def primitiveGraphEquivalenceType :
    PrimitiveFunctionGraph.Object.{u} ≌ Type u :=
  primitiveGraphReconstructionData.equivalence

/-- The general theorem's Hom inverse is the original graph reading. -/
theorem primitiveGraph_homEquiv_symm_apply
    (source target : PrimitiveFunctionGraph.Object.{u})
    (function : source.Carrier → target.Carrier) :
    (primitiveGraphReconstructionData.homEquiv source target).symm function =
      GraphCode.read function :=
  rfl

/-! ## Cycle 64 supplies exactly the complete-geometry separation half -/

open CompleteGeometryFunctionGraphSeparation

/-- Complete graph reading realizes the indexed Hom-family separation contract
for every pair of geometry packages, without asserting a local category or
assembly for an arbitrary graph bundle. -/
def completeGeometryGraphSeparation {U : AtomCarrier.{u}} :
    HomFamilySeparation (GeometryPackage.{u, v} U)
      (fun G H => GeometryTotalHom G H)
      (fun G H => CompleteMapGraphs G H)
      (fun morphism => readCompleteMapGraphs morphism) where
  hom _ _ := ⟨readCompleteMapGraphs_injective⟩

end LocalReconstructionEquivalence

#assert_standard_axioms_only AAT.AG.LocalSemanticReconstruction.LocalReconstructionEquivalence

end

end AAT.AG.LocalSemanticReconstruction
