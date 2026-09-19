import ResearchLean.AG.LocalSemanticReconstruction.CompleteGeometryDirectCategory
import Formal.Util.AssertStandardAxioms

/-!
# Independent complete-geometry objects and their direct graph-code category

The package-indexed category of Cycle 72 stores a completed `GeometryPackage`
inside every local object.  This module replaces that wrapper by independently
supplied object data: generated core, selected geometry, coefficient carrier
and ring, and raw restriction system.  Assembly constructs the geometry
package, while reading projects those five fields.  Both inverse laws are
proved before any categorical reconstruction is invoked.

Lawful complete graph codes between the assembled endpoints are then equipped
with the direct identity and composition of Cycle 75.  Object assembly and Hom
assembly combine with separation to give essential surjectivity, exact Hom
inverses, and a categorical equivalence.  The same construction is connected
to the accepted raw complete-map graph surface in this module.

This is the complete-geometry object/Hom reconstruction layer.  It does not
identify the heterogeneous tagged, G-122, lens, and protocol branches with one
final local-model category.
-/

namespace AAT.AG.LocalSemanticReconstruction

open CategoryTheory AtomFoundation GeometryTransport
open LocalReconstructionEquivalence
open CompleteGeometryGraphAssembly

noncomputable section

namespace CompleteGeometryObjectCategory

universe u v

/-- Independently supplied constituents of a complete geometry object.

No completed `GeometryPackage`, global morphism, decoder, or extension witness
is retained.  The dependent types enforce that the selected geometry and raw
restriction system have the stated core and coefficient provenance. -/
structure ObjectCode (U : AtomCarrier.{u}) where
  core : AATCorePackage U
  geometry : Site.SelectedGeometryReading core
  Coefficient : Type v
  coefficientCommRing : CommRing Coefficient
  raw :
    let _ := coefficientCommRing
    LawAlgebra.RawAmbientRestrictionSystem geometry.toAATSite Coefficient

attribute [instance] ObjectCode.coefficientCommRing

namespace ObjectCode

/-- Assemble independently supplied object constituents into a complete
geometry package. -/
def assemble {U : AtomCarrier.{u}} (code : ObjectCode.{u, v} U) :
    GeometryPackage.{u, v} U where
  core := code.core
  geometry := code.geometry
  Coefficient := code.Coefficient
  coefficientCommRing := code.coefficientCommRing
  raw := code.raw

/-- Read a complete geometry package into independent object constituents. -/
def read {U : AtomCarrier.{u}} (package : GeometryPackage.{u, v} U) :
    ObjectCode.{u, v} U where
  core := package.core
  geometry := package.geometry
  Coefficient := package.Coefficient
  coefficientCommRing := package.coefficientCommRing
  raw := package.raw

/-- Assembling a read object recovers the original complete geometry package. -/
@[simp]
theorem assemble_read {U : AtomCarrier.{u}}
    (package : GeometryPackage.{u, v} U) :
    assemble (read package) = package := by
  cases package
  rfl

/-- Reading an assembled independent object recovers every supplied field. -/
@[simp]
theorem read_assemble {U : AtomCarrier.{u}} (code : ObjectCode.{u, v} U) :
    read code.assemble = code := by
  cases code
  rfl

/-- Complete geometry packages and independent object codes are exactly
equivalent, with assembly as the inverse direction. -/
def equivalence {U : AtomCarrier.{u}} :
    GeometryPackage.{u, v} U ≃ ObjectCode.{u, v} U where
  toFun := read
  invFun := assemble
  left_inv := assemble_read
  right_inv := read_assemble

end ObjectCode

/-- Category of independent complete-geometry objects and direct lawful graph
codes between their assembled endpoints. -/
noncomputable instance {U : AtomCarrier.{u}} :
    Category (ObjectCode.{u, v} U) where
  Hom source target := CompleteGeometryGraphCode source.assemble target.assemble
  id object :=
    CompleteGeometryDirectCategory.CompleteGeometryGraphCode.id object.assemble
  comp first second :=
    CompleteGeometryDirectCategory.CompleteGeometryGraphCode.comp first second
  id_comp :=
    CompleteGeometryDirectCategory.CompleteGeometryGraphCode.id_comp
  comp_id :=
    CompleteGeometryDirectCategory.CompleteGeometryGraphCode.comp_id
  assoc :=
    CompleteGeometryDirectCategory.CompleteGeometryGraphCode.comp_assoc

/-! ## Exact object and Hom reconstruction -/

/-- Read every complete geometry object and morphism into the independent
object/direct-code category. -/
noncomputable def readingFunctor (U : AtomCarrier.{u}) :
    GeomReadCategory.{u, v} U ⥤ ObjectCode.{u, v} U where
  obj package := ObjectCode.read package
  map morphism := by
    change CompleteGeometryGraphCode
      (ObjectCode.read _).assemble (ObjectCode.read _).assemble
    simpa using CompleteGeometryGraphCode.read morphism
  map_id package := by
    change CompleteGeometryGraphCode.read (GeometryTotalHom.id package) =
      CompleteGeometryDirectCategory.CompleteGeometryGraphCode.id package
    exact
      (CompleteGeometryDirectCategory.CompleteGeometryGraphCode.id_eq_lawfulCode_id
        package).symm
  map_comp first second := by
    change CompleteGeometryGraphCode.read
        (GeometryTotalHom.comp first second) =
      CompleteGeometryDirectCategory.CompleteGeometryGraphCode.comp
        (CompleteGeometryGraphCode.read first)
        (CompleteGeometryGraphCode.read second)
    rw [CompleteGeometryDirectCategory.CompleteGeometryGraphCode.comp_eq_lawfulCode_comp]
    exact (CompleteGeometryGraphCategoryEquivalence.readingFunctor U).map_comp
      first second

/-- Assemble a local Hom whose endpoints are independent readings back to the
corresponding global endpoints. -/
noncomputable def assembleHom {U : AtomCarrier.{u}}
    {G H : GeomReadCategory.{u, v} U}
    (code : (readingFunctor U).obj G ⟶ (readingFunctor U).obj H) : G ⟶ H := by
  change CompleteGeometryGraphCode _ _ at code
  simpa using code.assemble

/-- Reading an explicitly assembled local Hom is the original local Hom. -/
@[simp]
theorem read_assembleHom {U : AtomCarrier.{u}}
    {G H : GeomReadCategory.{u, v} U}
    (code : (readingFunctor U).obj G ⟶ (readingFunctor U).obj H) :
    (readingFunctor U).map (assembleHom code) = code := by
  change CompleteGeometryGraphCode _ _ at code
  change CompleteGeometryGraphCode.read code.assemble = code
  exact CompleteGeometryGraphCode.read_assemble code

/-- Assembling the local reading of a global Hom recovers that Hom. -/
@[simp]
theorem assembleHom_read {U : AtomCarrier.{u}}
    {G H : GeomReadCategory.{u, v} U} (morphism : G ⟶ H) :
    assembleHom ((readingFunctor U).map morphism) = morphism := by
  change (CompleteGeometryGraphCode.read morphism).assemble = morphism
  exact CompleteGeometryGraphCode.assemble_read morphism

/-- Assemble every independent object and direct lawful graph code. -/
noncomputable def assemblyFunctor (U : AtomCarrier.{u}) :
    ObjectCode.{u, v} U ⥤ GeomReadCategory.{u, v} U where
  obj code := code.assemble
  map code := by
    change CompleteGeometryGraphCode _ _ at code
    exact code.assemble
  map_id code :=
    CompleteGeometryDirectCategory.CompleteGeometryGraphCode.assemble_id
      code.assemble
  map_comp first second :=
    CompleteGeometryDirectCategory.CompleteGeometryGraphCode.assemble_comp
      first second

/-- Complete graph reading separates all global Homs between independently
read endpoints. -/
def homSeparation (U : AtomCarrier.{u}) :
    HomSeparation (readingFunctor.{u, v} U) where
  hom _ _ := ⟨fun first second equality => by
    change CompleteGeometryGraphCode.read first =
      CompleteGeometryGraphCode.read second at equality
    calc
      first = (CompleteGeometryGraphCode.read first).assemble :=
        (CompleteGeometryGraphCode.assemble_read first).symm
      _ = (CompleteGeometryGraphCode.read second).assemble :=
        congrArg CompleteGeometryGraphCode.assemble equality
      _ = second := CompleteGeometryGraphCode.assemble_read second⟩

/-- Every direct lawful local Hom assembles to a global geometry Hom and reads
back exactly. -/
def homAssembly (U : AtomCarrier.{u}) :
    HomAssembly (readingFunctor.{u, v} U) where
  assemble := assembleHom
  map_assemble := read_assembleHom

/-- Every independently supplied local object assembles to a geometry package
whose reading is exactly that object, hence isomorphic by identity transport. -/
def objectAssembly (U : AtomCarrier.{u}) :
    ObjectAssembly (readingFunctor.{u, v} U) where
  assembleObject code := code.assemble
  readAssembledIso code := eqToIso (ObjectCode.read_assemble code)

/-- The independently supplied object and Hom assemblers form the complete
reconstruction datum. -/
def reconstructionData (U : AtomCarrier.{u}) :
    ReconstructionData (readingFunctor.{u, v} U) where
  separation := homSeparation U
  homAssembly := homAssembly U
  objectAssembly := objectAssembly U

/-- Independent object assembly is essentially surjective. -/
def readingEssSurj (U : AtomCarrier.{u}) :
    (readingFunctor.{u, v} U).EssSurj :=
  (reconstructionData U).essSurj

/-- Complete geometry is categorically equivalent to the independent object
and direct lawful-code category. -/
noncomputable def equivalence (U : AtomCarrier.{u}) :
    GeomReadCategory.{u, v} U ≌ ObjectCode.{u, v} U :=
  (reconstructionData U).equivalence

/-- The reconstructed equivalence uses the primitive reader as its forward
functor. -/
@[simp]
theorem equivalence_functor (U : AtomCarrier.{u}) :
    (equivalence.{u, v} U).functor = readingFunctor U :=
  rfl

/-- The Hom equivalence reads the supplied global morphism componentwise. -/
theorem homEquiv_apply {U : AtomCarrier.{u}}
    (G H : GeomReadCategory.{u, v} U) (morphism : G ⟶ H) :
    (reconstructionData U).homEquiv G H morphism =
      CompleteGeometryGraphCode.read morphism :=
  rfl

/-- The inverse Hom equivalence is direct complete-code assembly. -/
theorem homEquiv_symm_apply {U : AtomCarrier.{u}}
    (G H : GeomReadCategory.{u, v} U)
    (code : (readingFunctor U).obj G ⟶ (readingFunctor U).obj H) :
    ((reconstructionData U).homEquiv G H).symm code = assembleHom code :=
  rfl

/-- Every independent local Hom has one and only one global preimage. -/
theorem existsUnique_preimage {U : AtomCarrier.{u}}
    (G H : GeomReadCategory.{u, v} U)
    (code : (readingFunctor U).obj G ⟶ (readingFunctor U).obj H) :
    ∃! morphism : G ⟶ H,
      (readingFunctor U).map morphism = code :=
  (reconstructionData U).existsUnique_preimage code

/-! ## Connection to the accepted raw common graph surface -/

/-- Forget object coherence and lawful certificates while retaining every raw
complete-map graph. -/
noncomputable def commonSurfaceFunctor (U : AtomCarrier.{u}) :
    ObjectCode.{u, v} U ⥤ CompleteGeometryGraphCategory.Object.{u, v} U where
  obj code := ⟨code.assemble⟩
  map code := by
    change CompleteGeometryGraphCode _ _ at code
    exact code.completeMapGraphs
  map_id code := by
    change
      (CompleteGeometryDirectCategory.CompleteGeometryGraphCode.id
        code.assemble).completeMapGraphs = _
    rw [CompleteGeometryDirectCategory.CompleteGeometryGraphCode.id_eq_lawfulCode_id]
    exact
      (CompleteGeometryDirectCategory.CompleteGeometryGraphCode.id_cycle72_and_commonSurface
        code.assemble).2
  map_comp first second := by
    change
      (CompleteGeometryDirectCategory.CompleteGeometryGraphCode.comp
        first second).completeMapGraphs = _
    rw [CompleteGeometryDirectCategory.CompleteGeometryGraphCode.comp_eq_lawfulCode_comp]
    exact
      (CompleteGeometryDirectCategory.CompleteGeometryGraphCode.comp_cycle72_and_commonSurface
        first second).2

/-- Reading through the independent category reaches exactly the accepted raw
complete-map graph reading. -/
theorem commonSurface_map_read {U : AtomCarrier.{u}}
    {G H : GeomReadCategory.{u, v} U} (morphism : G ⟶ H) :
    (commonSurfaceFunctor U).map ((readingFunctor U).map morphism) =
      CompleteGeometryFunctionGraphSeparation.readCompleteMapGraphs morphism :=
  by
    change (CompleteGeometryGraphCode.read morphism).completeMapGraphs = _
    exact CompleteGeometryGraphCode.completeMapGraphs_read morphism

/-- The common raw graph surface still separates lawful local Homs. -/
instance commonSurfaceFunctorFaithful (U : AtomCarrier.{u}) :
    (commonSurfaceFunctor.{u, v} U).Faithful where
  map_injective := fun {X Y} first second equality =>
    by
      change CompleteGeometryGraphCode _ _ at first second
      change first.completeMapGraphs = second.completeMapGraphs at equality
      exact CompleteGeometryGraphCode.completeMapGraphs_injective equality

/-- The assembled object underlying the common surface is exactly the object
assembled by the categorical inverse. -/
@[simp]
theorem commonSurface_object (U : AtomCarrier.{u})
    (code : ObjectCode.{u, v} U) :
    (commonSurfaceFunctor U).obj code =
      ⟨(assemblyFunctor U).obj code⟩ :=
  rfl

end CompleteGeometryObjectCategory

#assert_standard_axioms_only
  AAT.AG.LocalSemanticReconstruction.CompleteGeometryObjectCategory

end

end AAT.AG.LocalSemanticReconstruction
