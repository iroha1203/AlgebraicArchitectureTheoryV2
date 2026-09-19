import ResearchLean.AG.LocalSemanticReconstruction.CompleteGeometryGraphAssembly
import ResearchLean.AG.LocalSemanticReconstruction.CompleteGeometryGraphCategory
import Formal.Util.AssertStandardAxioms

/-!
# The category of lawful complete geometry graph codes

Cycle 72 promotes the Cycle 71 read/assemble equivalence from each Hom type to
an equivalence of categories.  The local Hom type is the lawful independent
`CompleteGeometryGraphCode`, not the raw common graph bundle and not an image
subtype.  Identity and composition are operations on these codes, their
assembly formulas determine them uniquely, and the category laws follow from
the separation theorem proved in Cycle 71.

The resulting reading functor has explicit Hom separation, Hom assembly, and
object assembly.  The general reconstruction theorem therefore gives an
equivalence with the actual complete-geometry category.  In the same cycle a
functor to the accepted raw `CompleteMapGraphs` category records that the new
lawful category still exposes the existing common graph surface.

## Premise boundary

No new mathematical premise is introduced here.  A lawful code carries the
predecessor and cross-component Prop certificates made explicit in Cycle 71.
This file uses the reviewed two-sided read/assemble theorems to transport
identity and composition and proves their universal assembly formulas; it does
not add a completed geometry morphism or reader-image membership to a code.

## Implementation notes

The category operations are transported along the already reviewed Cycle 71
Hom equivalence and then characterized by unique assembly formulas.  Expanding
them into a second component-by-component implementation would duplicate the
dependent reindexing already proved by the package and realization assemblers.
Using raw `CompleteMapGraphs` as the Hom type was also rejected: that category
forgets the local laws and its reading functor is not full.  The separate
`commonSurfaceFunctor` below retains that accepted diagnostic surface without
weakening the lawful local Hom type.
-/

namespace AAT.AG.LocalSemanticReconstruction

open CategoryTheory AtomFoundation GeometryTransport
open LocalReconstructionEquivalence
open CompleteGeometryFunctionGraphSeparation

noncomputable section

namespace CompleteGeometryGraphCategoryEquivalence

universe u v

namespace LawfulCode

open CompleteGeometryGraphAssembly

/-- Identity in the lawful complete-code Hom family.  Its computational graph
data and every local law are recovered by the Cycle 71 reader. -/
noncomputable def id {U : AtomCarrier.{u}}
    (G : GeometryPackage.{u, v} U) :
    CompleteGeometryGraphCode G G :=
  CompleteGeometryGraphCode.read (GeometryTotalHom.id G)

/-- Composition in the lawful complete-code Hom family.  Assembly first
composes the independently reconstructed morphisms; reading then returns the
unique lawful code for that composite. -/
noncomputable def comp {U : AtomCarrier.{u}}
    {G H K : GeometryPackage.{u, v} U}
    (first : CompleteGeometryGraphCode G H)
    (second : CompleteGeometryGraphCode H K) :
    CompleteGeometryGraphCode G K :=
  CompleteGeometryGraphCode.read
    (GeometryTotalHom.comp first.assemble second.assemble)

/-- Assembly sends lawful-code identity to actual geometry identity. -/
@[simp]
theorem assemble_id {U : AtomCarrier.{u}}
    (G : GeometryPackage.{u, v} U) :
    (id G).assemble = GeometryTotalHom.id G :=
  CompleteGeometryGraphCode.assemble_read _

/-- The identity assembly formula characterizes the lawful identity code
uniquely. -/
theorem eq_id_iff_assemble_eq {U : AtomCarrier.{u}}
    (G : GeometryPackage.{u, v} U)
    (candidate : CompleteGeometryGraphCode G G) :
    candidate = id G ↔ candidate.assemble = GeometryTotalHom.id G := by
  constructor
  · rintro rfl
    exact assemble_id G
  · intro equality
    apply CompleteGeometryGraphCode.assemble_injective
    rw [assemble_id]
    exact equality

/-- Assembly sends lawful-code composition to actual geometry composition. -/
@[simp]
theorem assemble_comp {U : AtomCarrier.{u}}
    {G H K : GeometryPackage.{u, v} U}
    (first : CompleteGeometryGraphCode G H)
    (second : CompleteGeometryGraphCode H K) :
    (comp first second).assemble =
      GeometryTotalHom.comp first.assemble second.assemble :=
  CompleteGeometryGraphCode.assemble_read _

/-- The assembly formula is a universal property for lawful composition: it
characterizes the composite code uniquely. -/
theorem eq_comp_iff_assemble_eq {U : AtomCarrier.{u}}
    {G H K : GeometryPackage.{u, v} U}
    (first : CompleteGeometryGraphCode G H)
    (second : CompleteGeometryGraphCode H K)
    (candidate : CompleteGeometryGraphCode G K) :
    candidate = comp first second ↔
      candidate.assemble =
        GeometryTotalHom.comp first.assemble second.assemble := by
  constructor
  · rintro rfl
    exact assemble_comp first second
  · intro equality
    apply CompleteGeometryGraphCode.assemble_injective
    rw [assemble_comp]
    exact equality

/-- Left identity for lawful complete graph codes. -/
@[simp]
theorem id_comp {U : AtomCarrier.{u}}
    {G H : GeometryPackage.{u, v} U}
    (code : CompleteGeometryGraphCode G H) :
    comp (id G) code = code := by
  apply CompleteGeometryGraphCode.assemble_injective
  rw [assemble_comp, assemble_id]
  change (𝟙 G : G ⟶ G) ≫ (code.assemble : G ⟶ H) = code.assemble
  exact @Category.id_comp (GeomReadCategory.{u, v} U)
    (geometryTotalCategory U) G H code.assemble

/-- Right identity for lawful complete graph codes. -/
@[simp]
theorem comp_id {U : AtomCarrier.{u}}
    {G H : GeometryPackage.{u, v} U}
    (code : CompleteGeometryGraphCode G H) :
    comp code (id H) = code := by
  apply CompleteGeometryGraphCode.assemble_injective
  rw [assemble_comp, assemble_id]
  change (code.assemble : G ⟶ H) ≫ (𝟙 H : H ⟶ H) = code.assemble
  exact @Category.comp_id (GeomReadCategory.{u, v} U)
    (geometryTotalCategory U) G H code.assemble

/-- Associativity for lawful complete graph codes. -/
@[simp]
theorem assoc {U : AtomCarrier.{u}}
    {G H K L : GeometryPackage.{u, v} U}
    (first : CompleteGeometryGraphCode G H)
    (second : CompleteGeometryGraphCode H K)
    (third : CompleteGeometryGraphCode K L) :
    comp (comp first second) third = comp first (comp second third) := by
  apply CompleteGeometryGraphCode.assemble_injective
  rw [assemble_comp, assemble_comp, assemble_comp, assemble_comp]
  exact @Category.assoc (GeomReadCategory.{u, v} U)
    (geometryTotalCategory U) G H K L
    first.assemble second.assemble third.assemble

end LawfulCode

/-- A geometry package regarded as an object whose morphisms are lawful
complete geometry graph codes. -/
structure Object (U : AtomCarrier.{u}) where
  /-- Package indexing the source and target types of every local graph. -/
  package : GeometryPackage.{u, v} U

namespace Object

/-- Lawful complete geometry graph codes form a category. -/
noncomputable instance {U : AtomCarrier.{u}} : Category (Object.{u, v} U) where
  Hom source target :=
    CompleteGeometryGraphAssembly.CompleteGeometryGraphCode
      source.package target.package
  id object := LawfulCode.id object.package
  comp first second := LawfulCode.comp first second
  id_comp := LawfulCode.id_comp
  comp_id := LawfulCode.comp_id
  assoc := LawfulCode.assoc

end Object

/-! ## Exact reading and reconstruction -/

open CompleteGeometryGraphAssembly

/-- Read actual complete geometry morphisms into the lawful local category. -/
noncomputable def readingFunctor (U : AtomCarrier.{u}) :
    GeomReadCategory.{u, v} U ⥤ Object.{u, v} U where
  obj package := ⟨package⟩
  map morphism := CompleteGeometryGraphCode.read morphism
  map_id _ := rfl
  map_comp first second := by
    apply CompleteGeometryGraphCode.assemble_injective
    rw [CompleteGeometryGraphCode.assemble_read]
    change first ≫ second =
      (LawfulCode.comp (CompleteGeometryGraphCode.read first)
        (CompleteGeometryGraphCode.read second)).assemble
    rw [LawfulCode.assemble_comp,
      CompleteGeometryGraphCode.assemble_read,
      CompleteGeometryGraphCode.assemble_read]
    rfl

/-- Assemble lawful local morphisms back into actual geometry morphisms. -/
noncomputable def assemblyFunctor (U : AtomCarrier.{u}) :
    Object.{u, v} U ⥤ GeomReadCategory.{u, v} U where
  obj object := object.package
  map code := code.assemble
  map_id object := LawfulCode.assemble_id object.package
  map_comp first second := LawfulCode.assemble_comp first second

/-- Reading separates actual geometry morphisms on every Hom type. -/
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

/-- Every lawful local Hom assembles, and reading recovers it exactly. -/
def homAssembly (U : AtomCarrier.{u}) :
    HomAssembly (readingFunctor.{u, v} U) where
  assemble {X Y} code := by
    change CompleteGeometryGraphCode X Y at code
    exact code.assemble
  map_assemble {X Y} code := by
    change CompleteGeometryGraphCode.read
      (CompleteGeometryGraphCode.assemble code) = code
    exact CompleteGeometryGraphCode.read_assemble code

/-- Every lawful local object is read from its underlying geometry package,
with no choice and no essential-image predicate. -/
def objectAssembly (U : AtomCarrier.{u}) :
    ObjectAssembly (readingFunctor.{u, v} U) where
  assembleObject object := object.package
  readAssembledIso object := by
    rcases object with ⟨package⟩
    exact Iso.refl (⟨package⟩ : Object U)

/-- The fixed-target B reconstruction contract for lawful complete graph
codes: Hom separation, Hom assembly, and object assembly are all explicit. -/
def reconstructionData (U : AtomCarrier.{u}) :
    ReconstructionData (readingFunctor.{u, v} U) where
  separation := homSeparation U
  homAssembly := homAssembly U
  objectAssembly := objectAssembly U

/-- Actual complete geometry and lawful complete graph codes are equivalent as
categories. -/
noncomputable def equivalence (U : AtomCarrier.{u}) :
    GeomReadCategory.{u, v} U ≌ Object.{u, v} U :=
  (reconstructionData U).equivalence

/-- The Hom equivalence induced by categorical reconstruction is exactly the
Cycle 71 read/assemble equivalence. -/
theorem homEquiv_apply {U : AtomCarrier.{u}}
    (G H : GeomReadCategory.{u, v} U)
    (morphism : GeometryTotalHom G H) :
    (reconstructionData U).homEquiv G H morphism =
      CompleteGeometryGraphCode.read morphism :=
  rfl

/-- The inverse Hom equivalence is exactly complete-code assembly. -/
theorem homEquiv_symm_apply {U : AtomCarrier.{u}}
    (G H : GeomReadCategory.{u, v} U)
    (code : CompleteGeometryGraphCode G H) :
    ((reconstructionData U).homEquiv G H).symm code = code.assemble :=
  rfl

/-! ## Same-cycle connection to the accepted common graph surface -/

/-- Forget only the local laws, exposing each lawful morphism through the
accepted raw complete-map graph category. -/
noncomputable def commonSurfaceFunctor (U : AtomCarrier.{u}) :
    Object.{u, v} U ⥤ CompleteGeometryGraphCategory.Object.{u, v} U where
  obj object := ⟨object.package⟩
  map code := code.completeMapGraphs
  map_id object := by
    change readCompleteMapGraphs (LawfulCode.id object.package).assemble =
      CompleteGeometryGraphCategory.CompleteMapGraphs.id object.package
    rw [LawfulCode.assemble_id,
      CompleteGeometryGraphCategory.readCompleteMapGraphs_id]
  map_comp first second := by
    change readCompleteMapGraphs (LawfulCode.comp first second).assemble =
      CompleteGeometryGraphCategory.CompleteMapGraphs.comp
        (readCompleteMapGraphs first.assemble)
        (readCompleteMapGraphs second.assemble)
    rw [LawfulCode.assemble_comp,
      CompleteGeometryGraphCategory.readCompleteMapGraphs_comp]

/-- The new lawful reading reaches exactly the pre-existing raw common graph
reading, so the categorical equivalence and the accepted separation surface
do not diverge. -/
theorem commonSurface_map_read {U : AtomCarrier.{u}}
    {G H : GeomReadCategory.{u, v} U}
    (morphism : GeometryTotalHom G H) :
    (commonSurfaceFunctor U).map ((readingFunctor U).map morphism) =
      readCompleteMapGraphs morphism :=
  CompleteGeometryGraphCode.completeMapGraphs_read morphism

/-- Forgetting local laws is faithful because the common graph surface
separates lawful codes. -/
instance commonSurfaceFunctorFaithful (U : AtomCarrier.{u}) :
    (commonSurfaceFunctor.{u, v} U).Faithful where
  map_injective := fun {X Y} first second equality => by
    change first.completeMapGraphs = second.completeMapGraphs at equality
    exact CompleteGeometryGraphCode.completeMapGraphs_injective equality

end CompleteGeometryGraphCategoryEquivalence

#assert_standard_axioms_only
  AAT.AG.LocalSemanticReconstruction.CompleteGeometryGraphCategoryEquivalence

end

end AAT.AG.LocalSemanticReconstruction
