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

/-! ## Public wrapper categories required by G-114 revision 3 -/

/-- Public G-114 name for the unpointed refinement wrapper. -/
abbrev RefinementObject (U : AtomCarrier.{u}) := RefinementDoctrineObject U

/-- Public G-114 name for the unpointed refinement category. -/
abbrev RefinementCategory (U : AtomCarrier.{u}) :=
  RefinementDoctrineCategory U

/-- A pointed extraction instance read in the refinement category. -/
structure PointedRefinementObject (U : AtomCarrier.{u}) where
  /-- The underlying pointed extraction doctrine. -/
  pointed : ExtractionInstance U

/-- The category of pointed refinements. -/
abbrev PointedRefinementCategory (U : AtomCarrier.{u}) :=
  PointedRefinementObject U

instance pointedRefinementCategory (U : AtomCarrier.{u}) :
    Category.{u} (PointedRefinementCategory U) where
  Hom X Y := PointedRefinementHom X.pointed Y.pointed
  id X := PointedRefinementHom.id X.pointed
  comp f g := f.comp g
  id_comp := by
    intro X Y f
    apply PointedRefinementHom.ext
    apply RefinementDoctrineHom.ext <;> rfl
  comp_id := by
    intro X Y f
    apply PointedRefinementHom.ext
    apply RefinementDoctrineHom.ext <;> rfl
  assoc := by
    intro W X Y Z f g h
    apply PointedRefinementHom.ext
    apply RefinementDoctrineHom.ext <;> rfl

/-- Exact pointed maps embed functorially into pointed refinements. -/
def exactPointedToRefinement (U : AtomCarrier.{u}) :
    ExtractionInstance U ⥤ PointedRefinementCategory U where
  obj X := ⟨X⟩
  map f := PointedRefinementHom.ofExact f
  map_id _ := rfl
  map_comp f g := by
    apply PointedRefinementHom.ext
    apply RefinementDoctrineHom.ext <;> rfl

/-- A core package read as an object of the refinement package total category. -/
structure RefinementPackageObject (U : AtomCarrier.{u}) where
  /-- The underlying complete core package. -/
  package : AATCorePackage U

/-- The total category whose lower arrows are pointed refinements. -/
abbrev RefinementPackageTotalCategory (U : AtomCarrier.{u}) :=
  RefinementPackageObject U

/--
A complete package morphism over a pointed refinement.  No cartesian witness,
cleavage, mate, or reflection certificate is stored here.
-/
structure RefinementPackageHom {U : AtomCarrier.{u}}
    (P Q : RefinementPackageObject U) where
  /-- The lower pointed refinement. -/
  base : PointedRefinementHom (packagePoint P.package) (packagePoint Q.package)
  /-- The complete upper reading morphism. -/
  upper : SignedExactCoreReadingHom P.package Q.package
  /-- Upper and lower maps use the same primitive Atom equivalence. -/
  atomEquiv_eq : upper.atomEquiv = base.doctrineHom.atomEquiv

namespace RefinementPackageHom

@[ext]
theorem ext {U : AtomCarrier.{u}} {P Q : RefinementPackageObject U}
    {f g : RefinementPackageHom P Q}
    (hbase : f.base = g.base) (hupper : f.upper = g.upper) : f = g := by
  cases f
  cases g
  cases hbase
  cases hupper
  rfl

/-- Identity complete package morphism over the identity refinement. -/
def id {U : AtomCarrier.{u}} (P : RefinementPackageObject U) :
    RefinementPackageHom P P where
  base := PointedRefinementHom.id (packagePoint P.package)
  upper := SignedExactCoreReadingHom.refl P.package
  atomEquiv_eq := by
    apply Equiv.ext
    intro atom
    rfl

/-- Composition of complete package morphisms over pointed refinements. -/
def comp {U : AtomCarrier.{u}} {P Q R : RefinementPackageObject U}
    (f : RefinementPackageHom P Q) (g : RefinementPackageHom Q R) :
    RefinementPackageHom P R where
  base := f.base.comp g.base
  upper := f.upper.comp g.upper
  atomEquiv_eq := by
    apply Equiv.ext
    intro atom
    change g.upper.atomEquiv (f.upper.atomEquiv atom) =
      g.base.doctrineHom.atomEquiv (f.base.doctrineHom.atomEquiv atom)
    rw [f.atomEquiv_eq, g.atomEquiv_eq]

end RefinementPackageHom

instance refinementPackageTotalCategory (U : AtomCarrier.{u}) :
    Category.{u + 1} (RefinementPackageTotalCategory U) where
  Hom P Q := RefinementPackageHom P Q
  id P := RefinementPackageHom.id P
  comp f g := f.comp g
  id_comp := by
    intro P Q f
    apply RefinementPackageHom.ext
    · apply PointedRefinementHom.ext
      apply RefinementDoctrineHom.ext <;> rfl
    · change (SignedExactCoreReadingHom.refl P.package).comp f.upper = f.upper
      exact PackageTotalHom.upper_id_comp f.upper
  comp_id := by
    intro P Q f
    apply RefinementPackageHom.ext
    · apply PointedRefinementHom.ext
      apply RefinementDoctrineHom.ext <;> rfl
    · change f.upper.comp (SignedExactCoreReadingHom.refl Q.package) = f.upper
      exact PackageTotalHom.upper_comp_id f.upper
  assoc := by
    intro P Q R S f g h
    apply RefinementPackageHom.ext
    · rfl
    · exact PackageTotalHom.upper_comp_assoc f.upper g.upper h.upper

/-- The explicit G-114 refinement package projection. -/
def refinementPackageProjection (U : AtomCarrier.{u}) :
    RefinementPackageTotalCategory U ⥤ PointedRefinementCategory U where
  obj P := ⟨packagePoint P.package⟩
  map f := f.base
  map_id X := by
    apply PointedRefinementHom.ext
    apply RefinementDoctrineHom.ext <;> rfl
  map_comp f g := by
    apply PointedRefinementHom.ext
    apply RefinementDoctrineHom.ext <;> rfl

/-- Exact package morphisms embed into the refinement total category. -/
def exactPackageToRefinement (U : AtomCarrier.{u}) :
    PackageTotalCategory U ⥤ RefinementPackageTotalCategory U where
  obj P := ⟨P⟩
  map f := {
    base := PointedRefinementHom.ofExact f.base
    upper := f.upper
    atomEquiv_eq := by
      apply Equiv.ext
      intro atom
      exact congrFun (congrArg Equiv.toFun f.atomEquiv_eq) atom
  }
  map_id X := by
    apply RefinementPackageHom.ext
    · apply PointedRefinementHom.ext
      apply RefinementDoctrineHom.ext <;> rfl
    · rfl
  map_comp f g := by
    apply RefinementPackageHom.ext
    · apply PointedRefinementHom.ext
      apply RefinementDoctrineHom.ext <;> rfl
    · rfl

/-- The exact and refinement projections form a strictly commuting square. -/
theorem exact_refinement_projection_square (U : AtomCarrier.{u}) :
    exactPackageToRefinement U ⋙ refinementPackageProjection U =
      packageProjection U ⋙ exactPointedToRefinement U := by
  apply CategoryTheory.Functor.ext
  · intro X Y f
    apply PointedRefinementHom.ext
    apply RefinementDoctrineHom.ext <;> rfl
  · intro X
    rfl

end AAT.AG.DoctrineFiberProduct

#assert_standard_axioms_only AAT.AG.DoctrineFiberProduct
