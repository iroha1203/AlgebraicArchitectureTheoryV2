import ResearchLean.AG.AtomFoundation.Categories

/-!
# The refinement category

This module constructs the G-114 category `Refin_U`.  Its objects wrap existing
extraction doctrines so that the refinement category and the reviewed exact
category `Doct_U` have distinct category instances.  Morphisms are exactly the
existing `RefinementDoctrineHom`; no reflection or upper lift is added.

## Implementation notes

The object wrapper is necessary because Lean assigns a category structure to an
object type, while `ExtractionDoctrine U` already carries the exact category.
An alternative second instance on that same type would make the meaning of
`D ⟶ E` depend on instance search.  The comparison functor is identity on the
underlying doctrines and forgets only the reverse half of extraction exactness.
-/

namespace AAT.AG.DoctrineFiberProduct

universe u

open CategoryTheory
open AtomFoundation

/-- An extraction doctrine regarded as an object of the refinement category. -/
structure RefinementDoctrineObject (U : AtomCarrier.{u}) where
  /-- The underlying reviewed extraction doctrine. -/
  doctrine : ExtractionDoctrine U

/-- The refinement category `Refin_U`. -/
abbrev RefinementDoctrineCategory (U : AtomCarrier.{u}) :=
  RefinementDoctrineObject U

/-- Identity refinement morphism. -/
def refinementHomId (D : ExtractionDoctrine U) :
    RefinementDoctrineHom D D where
  sourceMap := _root_.id
  atomMap := _root_.id
  atomMap_bijective := Function.bijective_id
  normalize_eq _ := rfl
  extraction_forward _ _ := _root_.id

/-- Composition of refinement morphisms. -/
def refinementHomComp
    {D E F : ExtractionDoctrine U}
    (f : RefinementDoctrineHom D E) (g : RefinementDoctrineHom E F) :
    RefinementDoctrineHom D F where
  sourceMap := g.sourceMap ∘ f.sourceMap
  atomMap := g.atomMap ∘ f.atomMap
  atomMap_bijective := g.atomMap_bijective.comp f.atomMap_bijective
  normalize_eq source := by
    change F.normalize (g.sourceMap (f.sourceMap source)) =
      g.sourceMap (f.sourceMap (D.normalize source))
    rw [g.normalize_eq, f.normalize_eq]
  extraction_forward source atom extracted :=
    g.extraction_forward (f.sourceMap source) (f.atomMap atom)
      (f.extraction_forward source atom extracted)

/-- Refinement doctrines form the category `Refin_U`. -/
instance refinementDoctrineCategory (U : AtomCarrier.{u}) :
    Category.{u} (RefinementDoctrineCategory U) where
  Hom D E := RefinementDoctrineHom D.doctrine E.doctrine
  id D := refinementHomId D.doctrine
  comp f g := refinementHomComp f g
  id_comp := by
    intro D E f
    apply RefinementDoctrineHom.ext
    · rfl
    · rfl
  comp_id := by
    intro D E f
    apply RefinementDoctrineHom.ext
    · rfl
    · rfl
  assoc := by
    intro A B C D f g h
    apply RefinementDoctrineHom.ext
    · rfl
    · rfl

/-- An exact doctrine morphism, read in the forward refinement direction. -/
def exactToRefinement
    {D E : ExtractionDoctrine U} (f : ExactDoctrineHom D E) :
    RefinementDoctrineHom D E where
  sourceMap := f.sourceMap
  atomMap := f.atomEquiv
  atomMap_bijective := f.atomEquiv.bijective
  normalize_eq := f.normalize_eq
  extraction_forward source atom := (f.extraction_iff source atom).mp

/-- The comparison functor from exact doctrines to refinement doctrines. -/
def doctrineToRefinement (U : AtomCarrier.{u}) :
    DoctrineCategory U ⥤ RefinementDoctrineCategory U where
  obj D := ⟨D⟩
  map f := exactToRefinement f
  map_id _ := rfl
  map_comp f g := by
    apply RefinementDoctrineHom.ext
    · rfl
    · rfl

/-- A refinement morphism preserving selected sources. -/
structure PointedRefinementHom (X Y : ExtractionInstance U) where
  /-- The underlying one-way refinement morphism. -/
  doctrineHom : RefinementDoctrineHom X.doctrine Y.doctrine
  /-- The selected target source is generated from the selected source. -/
  source_eq : doctrineHom.sourceMap X.source = Y.source

namespace PointedRefinementHom

/-- Pointed refinement morphisms are determined by their doctrine morphism. -/
@[ext]
theorem ext {X Y : ExtractionInstance U} {f g : PointedRefinementHom X Y}
    (h : f.doctrineHom = g.doctrineHom) : f = g := by
  cases f
  cases g
  cases h
  rfl

/-- Identity pointed refinement. -/
def id (X : ExtractionInstance U) : PointedRefinementHom X X where
  doctrineHom := refinementHomId X.doctrine
  source_eq := rfl

/-- Composition of pointed refinements. -/
def comp {X Y Z : ExtractionInstance U}
    (f : PointedRefinementHom X Y) (g : PointedRefinementHom Y Z) :
    PointedRefinementHom X Z where
  doctrineHom := refinementHomComp f.doctrineHom g.doctrineHom
  source_eq := by
    change g.doctrineHom.sourceMap (f.doctrineHom.sourceMap X.source) = Z.source
    rw [f.source_eq, g.source_eq]

/-- Read an exact pointed morphism as a pointed refinement. -/
def ofExact {X Y : ExtractionInstance U} (f : X ⟶ Y) :
    PointedRefinementHom X Y where
  doctrineHom := exactToRefinement f.doctrineHom
  source_eq := f.source_eq

end PointedRefinementHom

/--
An isomorphism at pointed refinement level.  It is kept separate from
`ExtInst_U` because its two directions need not be exact morphisms.
-/
structure PointedRefinementIso (X Y : ExtractionInstance U) where
  /-- Forward pointed refinement. -/
  hom : PointedRefinementHom X Y
  /-- Backward pointed refinement. -/
  inv : PointedRefinementHom Y X
  /-- Forward followed by backward is the identity refinement. -/
  hom_inv_id : hom.comp inv = PointedRefinementHom.id X
  /-- Backward followed by forward is the identity refinement. -/
  inv_hom_id : inv.comp hom = PointedRefinementHom.id Y

end AAT.AG.DoctrineFiberProduct

#assert_standard_axioms_only AAT.AG.DoctrineFiberProduct
