import Formal.AG.RepresentationAnalysis.Bootstrap

noncomputable section

namespace AAT.AG
namespace RepresentationAnalysis

universe u v w x y z

/--
VII.定義2.1: reading parameter for decorated architecture schemes.

The underlying scheme object comes from PRD-3.  The morphism interface is kept
as selected data because PRD-7 only needs a functor-like representation surface;
it does not construct a general category of all decorated AAT schemes.
-/
structure AATSchReadingParameter {U : AtomCarrier.{u}} {A : ArchitectureObject U}
    (S : Site.AATSite A) (k : Type v) [CommRing k] where
  SchemeMorphism :
    UsesArchitectureScheme.{u, v, w, x, y} S k ->
      UsesArchitectureScheme.{u, v, w, x, y} S k -> Type y
  id :
    ∀ X : UsesArchitectureScheme.{u, v, w, x, y} S k, SchemeMorphism X X
  comp :
    ∀ {X Y Z : UsesArchitectureScheme.{u, v, w, x, y} S k},
      SchemeMorphism X Y -> SchemeMorphism Y Z -> SchemeMorphism X Z
  AtomLabelReading : Type u
  LawReading : Type u
  ObstructionIdealReading : Type w
  SignatureReading : Type u
  InterpretationMapReading : Type x

/--
VII.定義2.1: decorated architecture scheme `AATSch p`.

The scheme is the PRD-3 architecture scheme together with the selected
decoration readings that later representation families are allowed to read.
-/
structure AATSch {U : AtomCarrier.{u}} {A : ArchitectureObject U}
    {S : Site.AATSite A} {k : Type v} [CommRing k]
    (p : AATSchReadingParameter.{u, v, w, x, y} S k) where
  scheme : UsesArchitectureScheme.{u, v, w, x, y} S k
  atomLabels : p.AtomLabelReading
  lawReading : p.LawReading
  obstructionIdealReading : p.ObstructionIdealReading
  signatureReading : p.SignatureReading
  interpretationMapReading : p.InterpretationMapReading

namespace AATSch

variable {U : AtomCarrier.{u}} {A : ArchitectureObject U}
variable {S : Site.AATSite A} {k : Type v} [CommRing k]
variable {p : AATSchReadingParameter.{u, v, w, x, y} S k}

/-- VII.定義2.1: forget the decoration to the PRD-3 architecture scheme. -/
def underlyingScheme (X : AATSch p) :
    UsesArchitectureScheme.{u, v, w, x, y} S k :=
  X.scheme

/-- VII.定義2.1: the forgetful scheme reading is the stored scheme. -/
theorem underlyingScheme_eq (X : AATSch p) :
    X.underlyingScheme = X.scheme :=
  rfl

end AATSch

/--
VII.定義2.1: morphism of decorated architecture schemes.

Compatibility with labels, law readings, obstruction ideals, signature
readings, and interpretation maps is recorded as explicit selected predicates.
-/
structure AATSchMorphism {U : AtomCarrier.{u}} {A : ArchitectureObject U}
    {S : Site.AATSite A} {k : Type v} [CommRing k]
    {p : AATSchReadingParameter.{u, v, w, x, y} S k}
    (X Y : AATSch p) where
  underlying : p.SchemeMorphism X.scheme Y.scheme
  atomLabelsCompatible : Prop
  atomLabelsCompatible_cert : atomLabelsCompatible
  lawReadingCompatible : Prop
  lawReadingCompatible_cert : lawReadingCompatible
  obstructionIdealCompatible : Prop
  obstructionIdealCompatible_cert : obstructionIdealCompatible
  signatureReadingCompatible : Prop
  signatureReadingCompatible_cert : signatureReadingCompatible
  interpretationMapCompatible : Prop
  interpretationMapCompatible_cert : interpretationMapCompatible

namespace AATSchMorphism

variable {U : AtomCarrier.{u}} {A : ArchitectureObject U}
variable {S : Site.AATSite A} {k : Type v} [CommRing k]
variable {p : AATSchReadingParameter.{u, v, w, x, y} S k}
variable {X Y : AATSch p}

/-- VII.定義2.1: expose selected atom-label compatibility. -/
theorem atomLabelsCompatible_holds (f : AATSchMorphism X Y) :
    f.atomLabelsCompatible :=
  f.atomLabelsCompatible_cert

/-- VII.定義2.1: expose selected law-reading compatibility. -/
theorem lawReadingCompatible_holds (f : AATSchMorphism X Y) :
    f.lawReadingCompatible :=
  f.lawReadingCompatible_cert

/-- VII.定義2.1: expose selected obstruction-ideal compatibility. -/
theorem obstructionIdealCompatible_holds (f : AATSchMorphism X Y) :
    f.obstructionIdealCompatible :=
  f.obstructionIdealCompatible_cert

/-- VII.定義2.1: expose selected signature-reading compatibility. -/
theorem signatureReadingCompatible_holds (f : AATSchMorphism X Y) :
    f.signatureReadingCompatible :=
  f.signatureReadingCompatible_cert

/-- VII.定義2.1: expose selected interpretation-map compatibility. -/
theorem interpretationMapCompatible_holds (f : AATSchMorphism X Y) :
    f.interpretationMapCompatible :=
  f.interpretationMapCompatible_cert

end AATSchMorphism

/-- VII.定義2.1: selected identity morphism data for `AATSch p`. -/
structure AATSchIdentityData {U : AtomCarrier.{u}} {A : ArchitectureObject U}
    {S : Site.AATSite A} {k : Type v} [CommRing k]
    {p : AATSchReadingParameter.{u, v, w, x, y} S k}
    (X : AATSch p) where
  morphism : AATSchMorphism X X
  underlying_eq : morphism.underlying = p.id X.scheme

/-- VII.定義2.1: selected composition data for `AATSch p`. -/
structure AATSchCompositionData {U : AtomCarrier.{u}} {A : ArchitectureObject U}
    {S : Site.AATSite A} {k : Type v} [CommRing k]
    {p : AATSchReadingParameter.{u, v, w, x, y} S k}
    {X Y Z : AATSch p}
    (f : AATSchMorphism X Y) (g : AATSchMorphism Y Z) where
  morphism : AATSchMorphism X Z
  underlying_eq : morphism.underlying = p.comp f.underlying g.underlying

/--
VII.定義2.1: optional fiber-product surface.

This data only exists when an underlying pullback and compatible decoration
pullback have been selected.  No general pullback existence theorem is claimed.
-/
structure AATSchFiberProductData {U : AtomCarrier.{u}} {A : ArchitectureObject U}
    {S : Site.AATSite A} {k : Type v} [CommRing k]
    {p : AATSchReadingParameter.{u, v, w, x, y} S k}
    {X Y Z : AATSch p}
    (f : AATSchMorphism X Z) (g : AATSchMorphism Y Z) where
  object : AATSch p
  fst : AATSchMorphism object X
  snd : AATSchMorphism object Y
  underlyingPullback : Prop
  underlyingPullback_cert : underlyingPullback
  decorationPullbackCompatible : Prop
  decorationPullbackCompatible_cert : decorationPullbackCompatible

namespace AATSchFiberProductData

variable {U : AtomCarrier.{u}} {A : ArchitectureObject U}
variable {S : Site.AATSite A} {k : Type v} [CommRing k]
variable {p : AATSchReadingParameter.{u, v, w, x, y} S k}
variable {X Y Z : AATSch p}
variable {f : AATSchMorphism X Z} {g : AATSchMorphism Y Z}

/-- VII.定義2.1: the selected underlying pullback condition holds. -/
theorem underlyingPullback_holds (P : AATSchFiberProductData f g) :
    P.underlyingPullback :=
  P.underlyingPullback_cert

/-- VII.定義2.1: the selected decoration pullback compatibility holds. -/
theorem decorationPullbackCompatible_holds (P : AATSchFiberProductData f g) :
    P.decorationPullbackCompatible :=
  P.decorationPullbackCompatible_cert

end AATSchFiberProductData

/-- VII.定義2.1: minimal target category interface for analytic readings. -/
structure AnalyticTargetCategory (Target : Type z) where
  Hom : Target -> Target -> Type z
  id : ∀ X : Target, Hom X X
  comp : ∀ {X Y Z : Target}, Hom X Y -> Hom Y Z -> Hom X Z

/--
VII.定義2.1: analytic representation of decorated architecture schemes.

This is a functor-like structure: it maps objects and selected morphisms and
stores identity / composition laws as fields.  A later bridge may connect this
to Mathlib functors when a concrete category instance is selected.
-/
structure AnalyticRepresentation {U : AtomCarrier.{u}} {A : ArchitectureObject U}
    {S : Site.AATSite A} {k : Type v} [CommRing k]
    (p : AATSchReadingParameter.{u, v, w, x, y} S k) (Target : Type z) where
  targetCategory : AnalyticTargetCategory.{z} Target
  obj : AATSch p -> Target
  map :
    ∀ {X Y : AATSch p}, AATSchMorphism X Y ->
      targetCategory.Hom (obj X) (obj Y)
  map_id :
    ∀ {X : AATSch p} (I : AATSchIdentityData X),
      map I.morphism = targetCategory.id (obj X)
  map_comp :
    ∀ {X Y Z : AATSch p} {f : AATSchMorphism X Y} {g : AATSchMorphism Y Z}
      (C : AATSchCompositionData f g),
      map C.morphism = targetCategory.comp (map f) (map g)

namespace AnalyticRepresentation

variable {U : AtomCarrier.{u}} {A : ArchitectureObject U}
variable {S : Site.AATSite A} {k : Type v} [CommRing k]
variable {p : AATSchReadingParameter.{u, v, w, x, y} S k}
variable {Target : Type z}

/-- VII.定義2.1: analytic representations preserve selected identities. -/
theorem map_identity (R : AnalyticRepresentation p Target)
    {X : AATSch p} (I : AATSchIdentityData X) :
    R.map I.morphism = R.targetCategory.id (R.obj X) :=
  R.map_id I

/-- VII.定義2.1: analytic representations preserve selected compositions. -/
theorem map_composition (R : AnalyticRepresentation p Target)
    {X Y Z : AATSch p} {f : AATSchMorphism X Y} {g : AATSchMorphism Y Z}
    (C : AATSchCompositionData f g) :
    R.map C.morphism = R.targetCategory.comp (R.map f) (R.map g) :=
  R.map_comp C

end AnalyticRepresentation

end RepresentationAnalysis
end AAT.AG
