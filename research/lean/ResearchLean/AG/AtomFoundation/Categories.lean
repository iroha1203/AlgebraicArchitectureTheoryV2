import ResearchLean.AG.AtomFoundation.Doctrine

/-!
# Pointed doctrines and the core-package total category

This module constructs the categorical spine used by the G-101 opcartesian
transport statement: pointed extraction doctrines, the total category of core
packages, and the projection from a package to its actual doctrine and source.

## Implementation notes

The total hom keeps both its lower exact pointed morphism and its complete
`SignedExactCoreReadingHom`.  Equality is ordinary structure equality.  A
quotient or a forgetful equality through `ObjectAlgebraHom` was rejected because
either would weaken the lift uniqueness required by G-101.
-/

namespace AAT.AG.AtomFoundation

universe u

open CategoryTheory

/-- A pointed extraction doctrine, the object type of `ExtInst_U`. -/
structure ExtractionInstance (U : AtomCarrier.{u}) where
  /-- The selected extraction doctrine. -/
  doctrine : ExtractionDoctrine U
  /-- The selected source in that doctrine. -/
  source : doctrine.Source

/-- The pointed extraction-doctrine category `ExtInst_U`. -/
abbrev ExtInstCategory (U : AtomCarrier.{u}) := ExtractionInstance U

/-- An exact doctrine morphism carrying the selected source to the selected source. -/
structure ExtInstHom {U : AtomCarrier.{u}}
    (X Y : ExtractionInstance U) where
  /-- The underlying exact doctrine morphism. -/
  doctrineHom : ExactDoctrineHom X.doctrine Y.doctrine
  /-- The source selected by `Y` is the image of the source selected by `X`. -/
  source_eq : doctrineHom.sourceMap X.source = Y.source

namespace ExtInstHom

/-- Pointed exact morphisms are determined by their underlying doctrine morphism. -/
@[ext]
theorem ext {U : AtomCarrier.{u}} {X Y : ExtractionInstance U}
    {f g : ExtInstHom X Y} (hdoctrineHom : f.doctrineHom = g.doctrineHom) :
    f = g := by
  cases f
  cases g
  cases hdoctrineHom
  rfl

/-- The identity pointed exact morphism. -/
def id {U : AtomCarrier.{u}} (X : ExtractionInstance U) : ExtInstHom X X where
  doctrineHom := ExactDoctrineHom.id X.doctrine
  source_eq := rfl

/-- Composition of pointed exact morphisms. -/
def comp {U : AtomCarrier.{u}} {X Y Z : ExtractionInstance U}
    (f : ExtInstHom X Y) (g : ExtInstHom Y Z) : ExtInstHom X Z where
  doctrineHom := f.doctrineHom.comp g.doctrineHom
  source_eq := by
    change g.doctrineHom.sourceMap (f.doctrineHom.sourceMap X.source) = Z.source
    rw [f.source_eq, g.source_eq]

/-- Pointed extraction doctrines and exact source-preserving maps form `ExtInst_U`. -/
instance extractionInstanceCategory (U : AtomCarrier.{u}) :
    Category.{u} (ExtractionInstance U) where
  Hom := ExtInstHom
  id := id
  comp f g := f.comp g
  id_comp := by
    intro X Y f
    apply ExtInstHom.ext
    apply ExactDoctrineHom.ext
    · rfl
    · apply Equiv.ext
      intro atom
      rfl
  comp_id := by
    intro X Y f
    apply ExtInstHom.ext
    apply ExactDoctrineHom.ext
    · rfl
    · apply Equiv.ext
      intro atom
      rfl
  assoc := by
    intro W X Y Z f g h
    apply ExtInstHom.ext
    apply ExactDoctrineHom.ext
    · rfl
    · apply Equiv.ext
      intro atom
      rfl

end ExtInstHom

/-- The actual pointed doctrine carried by a core package. -/
def packagePoint {U : AtomCarrier.{u}} (P : AATCorePackage U) :
    ExtractionInstance U where
  doctrine := P.reading.doctrine
  source := P.reading.source

/-- The object type of the G-101 package total category. -/
abbrev PackageTotalCategory (U : AtomCarrier.{u}) := AATCorePackage U

/--
A morphism in the core-package total category.

The compatibility equality states that the complete upper transport lies over
the same Atom equivalence as the pointed doctrine morphism.  No lift or
factorization conclusion is stored here.
-/
structure PackageTotalHom {U : AtomCarrier.{u}}
    (P Q : AATCorePackage U) where
  /-- The exact pointed doctrine morphism under the package change. -/
  base : ExtInstHom (packagePoint P) (packagePoint Q)
  /-- The complete signed exact change between the two packages. -/
  upper : SignedExactCoreReadingHom P Q
  /-- The upper and lower morphisms use the same primitive Atom equivalence. -/
  atomEquiv_eq : upper.atomEquiv = base.doctrineHom.atomEquiv

namespace PackageTotalHom

/-- Total-package morphisms are determined by their lower and upper morphisms. -/
@[ext]
theorem ext {U : AtomCarrier.{u}} {P Q : AATCorePackage U}
    {f g : PackageTotalHom P Q}
    (hbase : f.base = g.base) (hupper : f.upper = g.upper) :
    f = g := by
  cases f
  cases g
  cases hbase
  cases hupper
  rfl

/-- The identity total-package morphism. -/
def id {U : AtomCarrier.{u}} (P : AATCorePackage U) : PackageTotalHom P P where
  base := ExtInstHom.id (packagePoint P)
  upper := SignedExactCoreReadingHom.refl P
  atomEquiv_eq := rfl

/-- Composition in the total-package category. -/
def comp {U : AtomCarrier.{u}} {P Q R : AATCorePackage U}
    (f : PackageTotalHom P Q) (g : PackageTotalHom Q R) :
    PackageTotalHom P R where
  base := f.base.comp g.base
  upper := f.upper.comp g.upper
  atomEquiv_eq := by
    apply Equiv.ext
    intro atom
    change g.upper.atomEquiv (f.upper.atomEquiv atom) =
      g.base.doctrineHom.atomEquiv (f.base.doctrineHom.atomEquiv atom)
    rw [f.atomEquiv_eq, g.atomEquiv_eq]

/-- `SignedExactCoreReadingHom.refl` is a strict left unit for arbitrary upper homs. -/
theorem upper_id_comp {U : AtomCarrier.{u}} {P Q : AATCorePackage U}
    (f : SignedExactCoreReadingHom P Q) :
    (SignedExactCoreReadingHom.refl P).comp f = f := by
  apply SignedExactCoreReadingHom.ext
  · apply Equiv.ext
    intro atom
    rfl
  · rfl
  · cases f
    rfl
  · cases f
    rfl
  · cases f
    rfl
  · cases f
    rfl
  · cases f
    rfl

/-- `SignedExactCoreReadingHom.refl` is a strict right unit for arbitrary upper homs. -/
theorem upper_comp_id {U : AtomCarrier.{u}} {P Q : AATCorePackage U}
    (f : SignedExactCoreReadingHom P Q) :
    f.comp (SignedExactCoreReadingHom.refl Q) = f := by
  apply SignedExactCoreReadingHom.ext
  · apply Equiv.ext
    intro atom
    rfl
  · rfl
  · cases f
    rfl
  · cases f
    rfl
  · cases f
    rfl
  · cases f
    rfl
  · cases f
    rfl

/-- Composition of arbitrary upper homs is strictly associative. -/
theorem upper_comp_assoc {U : AtomCarrier.{u}}
    {P Q R S : AATCorePackage U}
    (f : SignedExactCoreReadingHom P Q)
    (g : SignedExactCoreReadingHom Q R)
    (h : SignedExactCoreReadingHom R S) :
    (f.comp g).comp h = f.comp (g.comp h) := by
  apply SignedExactCoreReadingHom.ext
  · apply Equiv.ext
    intro atom
    rfl
  · rfl
  · cases f
    cases g
    cases h
    rfl
  · cases f
    cases g
    cases h
    rfl
  · cases f
    cases g
    cases h
    rfl
  · cases f
    cases g
    cases h
    rfl
  · cases f
    cases g
    cases h
    rfl

/-- Core packages and compatible lower/upper morphisms form the package total category. -/
instance packageTotalCategory (U : AtomCarrier.{u}) :
    Category.{u + 1} (AATCorePackage U) where
  Hom P Q := PackageTotalHom P Q
  id P := PackageTotalHom.id P
  comp f g := PackageTotalHom.comp f g
  id_comp := by
    intro P Q f
    apply PackageTotalHom.ext
    · apply ExtInstHom.ext
      apply ExactDoctrineHom.ext
      · rfl
      · apply Equiv.ext
        intro atom
        rfl
    · exact upper_id_comp f.upper
  comp_id := by
    intro P Q f
    apply PackageTotalHom.ext
    · apply ExtInstHom.ext
      apply ExactDoctrineHom.ext
      · rfl
      · apply Equiv.ext
        intro atom
        rfl
    · exact upper_comp_id f.upper
  assoc := by
    intro P Q R S f g h
    apply PackageTotalHom.ext
    · apply ExtInstHom.ext
      apply ExactDoctrineHom.ext
      · rfl
      · apply Equiv.ext
        intro atom
        rfl
    · exact upper_comp_assoc f.upper g.upper h.upper

end PackageTotalHom

/-- The projection from the package total category to pointed extraction doctrines. -/
def packageProjection (U : AtomCarrier.{u}) :
    AATCorePackage U ⥤ ExtractionInstance U where
  obj := packagePoint
  map f := PackageTotalHom.base f
  map_id _ := rfl
  map_comp _ _ := rfl

/-- The projection reads the doctrine selected by the package itself. -/
@[simp]
theorem packageProjection_obj_doctrine {U : AtomCarrier.{u}}
    (P : AATCorePackage U) :
    ((packageProjection U).obj P).doctrine = P.reading.doctrine :=
  rfl

/-- The projection reads the source selected by the package itself. -/
@[simp]
theorem packageProjection_obj_source {U : AtomCarrier.{u}}
    (P : AATCorePackage U) :
    ((packageProjection U).obj P).source = P.reading.source :=
  rfl

/-- The projection maps a total hom to its actual lower pointed morphism. -/
@[simp]
theorem packageProjection_map {U : AtomCarrier.{u}}
    {P Q : AATCorePackage U} (f : P ⟶ Q) :
    (packageProjection U).map f = PackageTotalHom.base f :=
  rfl

end AAT.AG.AtomFoundation

#assert_standard_axioms_only AAT.AG.AtomFoundation
