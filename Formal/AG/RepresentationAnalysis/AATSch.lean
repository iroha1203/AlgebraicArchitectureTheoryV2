import Formal.AG.RepresentationAnalysis.Bootstrap
import Mathlib.CategoryTheory.Category.Basic

noncomputable section

namespace AAT.AG
namespace RepresentationAnalysis

open CategoryTheory

universe u v w x y z

/--
VII.定義2.1: reading parameter for decorated architecture schemes.

The underlying scheme object comes from Part III.  The morphism interface is kept
as selected data over a fixed reading contract.  The identity / composition laws
and decoration-compatibility closure data are part of the parameter, so
decorated schemes form a Mathlib category relative to this selected contract.
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
  id_comp :
    ∀ {X Y : UsesArchitectureScheme.{u, v, w, x, y} S k}
      (f : SchemeMorphism X Y), comp (id X) f = f
  comp_id :
    ∀ {X Y : UsesArchitectureScheme.{u, v, w, x, y} S k}
      (f : SchemeMorphism X Y), comp f (id Y) = f
  assoc :
    ∀ {W X Y Z : UsesArchitectureScheme.{u, v, w, x, y} S k}
      (f : SchemeMorphism W X) (g : SchemeMorphism X Y) (h : SchemeMorphism Y Z),
      comp (comp f g) h = comp f (comp g h)
  AtomLabelReading : Type u
  LawReading : Type u
  ObstructionIdealReading : Type w
  SignatureReading : Type u
  InterpretationMapReading : Type x
  atomLabelsCompatible :
    ∀ {X Y : UsesArchitectureScheme.{u, v, w, x, y} S k},
      SchemeMorphism X Y -> AtomLabelReading -> AtomLabelReading -> Prop
  lawReadingCompatible :
    ∀ {X Y : UsesArchitectureScheme.{u, v, w, x, y} S k},
      SchemeMorphism X Y -> LawReading -> LawReading -> Prop
  obstructionIdealCompatible :
    ∀ {X Y : UsesArchitectureScheme.{u, v, w, x, y} S k},
      SchemeMorphism X Y -> ObstructionIdealReading -> ObstructionIdealReading -> Prop
  signatureReadingCompatible :
    ∀ {X Y : UsesArchitectureScheme.{u, v, w, x, y} S k},
      SchemeMorphism X Y -> SignatureReading -> SignatureReading -> Prop
  interpretationMapCompatible :
    ∀ {X Y : UsesArchitectureScheme.{u, v, w, x, y} S k},
      SchemeMorphism X Y -> InterpretationMapReading -> InterpretationMapReading -> Prop
  id_atomLabelsCompatible :
    ∀ (X : UsesArchitectureScheme.{u, v, w, x, y} S k) (a : AtomLabelReading),
      atomLabelsCompatible (id X) a a
  id_lawReadingCompatible :
    ∀ (X : UsesArchitectureScheme.{u, v, w, x, y} S k) (a : LawReading),
      lawReadingCompatible (id X) a a
  id_obstructionIdealCompatible :
    ∀ (X : UsesArchitectureScheme.{u, v, w, x, y} S k)
      (a : ObstructionIdealReading),
      obstructionIdealCompatible (id X) a a
  id_signatureReadingCompatible :
    ∀ (X : UsesArchitectureScheme.{u, v, w, x, y} S k) (a : SignatureReading),
      signatureReadingCompatible (id X) a a
  id_interpretationMapCompatible :
    ∀ (X : UsesArchitectureScheme.{u, v, w, x, y} S k)
      (a : InterpretationMapReading),
      interpretationMapCompatible (id X) a a
  comp_atomLabelsCompatible :
    ∀ {X Y Z : UsesArchitectureScheme.{u, v, w, x, y} S k}
      {f : SchemeMorphism X Y} {g : SchemeMorphism Y Z}
      {aX aY aZ : AtomLabelReading},
      atomLabelsCompatible f aX aY ->
        atomLabelsCompatible g aY aZ ->
        atomLabelsCompatible (comp f g) aX aZ
  comp_lawReadingCompatible :
    ∀ {X Y Z : UsesArchitectureScheme.{u, v, w, x, y} S k}
      {f : SchemeMorphism X Y} {g : SchemeMorphism Y Z}
      {aX aY aZ : LawReading},
      lawReadingCompatible f aX aY ->
        lawReadingCompatible g aY aZ ->
        lawReadingCompatible (comp f g) aX aZ
  comp_obstructionIdealCompatible :
    ∀ {X Y Z : UsesArchitectureScheme.{u, v, w, x, y} S k}
      {f : SchemeMorphism X Y} {g : SchemeMorphism Y Z}
      {aX aY aZ : ObstructionIdealReading},
      obstructionIdealCompatible f aX aY ->
        obstructionIdealCompatible g aY aZ ->
        obstructionIdealCompatible (comp f g) aX aZ
  comp_signatureReadingCompatible :
    ∀ {X Y Z : UsesArchitectureScheme.{u, v, w, x, y} S k}
      {f : SchemeMorphism X Y} {g : SchemeMorphism Y Z}
      {aX aY aZ : SignatureReading},
      signatureReadingCompatible f aX aY ->
        signatureReadingCompatible g aY aZ ->
        signatureReadingCompatible (comp f g) aX aZ
  comp_interpretationMapCompatible :
    ∀ {X Y Z : UsesArchitectureScheme.{u, v, w, x, y} S k}
      {f : SchemeMorphism X Y} {g : SchemeMorphism Y Z}
      {aX aY aZ : InterpretationMapReading},
      interpretationMapCompatible f aX aY ->
        interpretationMapCompatible g aY aZ ->
        interpretationMapCompatible (comp f g) aX aZ

/--
VII.定義2.1: decorated architecture scheme `AATSch p`.

The scheme is the Part III architecture scheme together with the selected
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

/-- VII.定義2.1: forget the decoration to the Part III architecture scheme. -/
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
readings, and interpretation maps is checked against the fixed predicates in
the reading parameter.  A morphism can no longer choose arbitrary local
compatibility propositions.
-/
structure AATSchMorphism {U : AtomCarrier.{u}} {A : ArchitectureObject U}
    {S : Site.AATSite A} {k : Type v} [CommRing k]
    {p : AATSchReadingParameter.{u, v, w, x, y} S k}
    (X Y : AATSch p) where
  underlying : p.SchemeMorphism X.scheme Y.scheme
  atomLabelsCompatible :
    p.atomLabelsCompatible underlying X.atomLabels Y.atomLabels
  lawReadingCompatible :
    p.lawReadingCompatible underlying X.lawReading Y.lawReading
  obstructionIdealCompatible :
    p.obstructionIdealCompatible underlying
      X.obstructionIdealReading Y.obstructionIdealReading
  signatureReadingCompatible :
    p.signatureReadingCompatible underlying X.signatureReading Y.signatureReading
  interpretationMapCompatible :
    p.interpretationMapCompatible underlying
      X.interpretationMapReading Y.interpretationMapReading

namespace AATSchMorphism

variable {U : AtomCarrier.{u}} {A : ArchitectureObject U}
variable {S : Site.AATSite A} {k : Type v} [CommRing k]
variable {p : AATSchReadingParameter.{u, v, w, x, y} S k}
variable {X Y : AATSch p}

/-- VII.定義2.1: expose selected atom-label compatibility. -/
theorem atomLabelsCompatible_holds (f : AATSchMorphism X Y) :
    p.atomLabelsCompatible f.underlying X.atomLabels Y.atomLabels :=
  f.atomLabelsCompatible

/-- VII.定義2.1: expose selected law-reading compatibility. -/
theorem lawReadingCompatible_holds (f : AATSchMorphism X Y) :
    p.lawReadingCompatible f.underlying X.lawReading Y.lawReading :=
  f.lawReadingCompatible

/-- VII.定義2.1: expose selected obstruction-ideal compatibility. -/
theorem obstructionIdealCompatible_holds (f : AATSchMorphism X Y) :
    p.obstructionIdealCompatible f.underlying
      X.obstructionIdealReading Y.obstructionIdealReading :=
  f.obstructionIdealCompatible

/-- VII.定義2.1: expose selected signature-reading compatibility. -/
theorem signatureReadingCompatible_holds (f : AATSchMorphism X Y) :
    p.signatureReadingCompatible f.underlying X.signatureReading Y.signatureReading :=
  f.signatureReadingCompatible

/-- VII.定義2.1: expose selected interpretation-map compatibility. -/
theorem interpretationMapCompatible_holds (f : AATSchMorphism X Y) :
    p.interpretationMapCompatible f.underlying
      X.interpretationMapReading Y.interpretationMapReading :=
  f.interpretationMapCompatible

/-- VII.定義2.1: equality of decorated morphisms is determined by the selected
underlying scheme morphism; compatibility proofs are propositions. -/
@[ext]
theorem ext {f g : AATSchMorphism X Y}
    (h : f.underlying = g.underlying) : f = g := by
  cases f
  cases g
  cases h
  simp

/-- VII.定義2.1: canonical identity decorated morphism. -/
def id (X : AATSch p) : AATSchMorphism X X where
  underlying := p.id X.scheme
  atomLabelsCompatible := p.id_atomLabelsCompatible X.scheme X.atomLabels
  lawReadingCompatible := p.id_lawReadingCompatible X.scheme X.lawReading
  obstructionIdealCompatible :=
    p.id_obstructionIdealCompatible X.scheme X.obstructionIdealReading
  signatureReadingCompatible :=
    p.id_signatureReadingCompatible X.scheme X.signatureReading
  interpretationMapCompatible :=
    p.id_interpretationMapCompatible X.scheme X.interpretationMapReading

/-- VII.定義2.1: canonical composition of decorated morphisms. -/
def comp {X Y Z : AATSch p}
    (f : AATSchMorphism X Y) (g : AATSchMorphism Y Z) :
    AATSchMorphism X Z where
  underlying := p.comp f.underlying g.underlying
  atomLabelsCompatible :=
    p.comp_atomLabelsCompatible f.atomLabelsCompatible g.atomLabelsCompatible
  lawReadingCompatible :=
    p.comp_lawReadingCompatible f.lawReadingCompatible g.lawReadingCompatible
  obstructionIdealCompatible :=
    p.comp_obstructionIdealCompatible
      f.obstructionIdealCompatible g.obstructionIdealCompatible
  signatureReadingCompatible :=
    p.comp_signatureReadingCompatible
      f.signatureReadingCompatible g.signatureReadingCompatible
  interpretationMapCompatible :=
    p.comp_interpretationMapCompatible
      f.interpretationMapCompatible g.interpretationMapCompatible

end AATSchMorphism

namespace AATSch

variable {U : AtomCarrier.{u}} {A : ArchitectureObject U}
variable {S : Site.AATSite A} {k : Type v} [CommRing k]
variable {p : AATSchReadingParameter.{u, v, w, x, y} S k}

/-- VII.定義2.1 / AC14: selected decorated schemes form a Mathlib category. -/
instance category : Category (AATSch p) where
  Hom X Y := AATSchMorphism X Y
  id X := AATSchMorphism.id X
  comp f g := AATSchMorphism.comp f g
  id_comp f := by
    apply AATSchMorphism.ext
    exact p.id_comp f.underlying
  comp_id f := by
    apply AATSchMorphism.ext
    exact p.comp_id f.underlying
  assoc f g h := by
    apply AATSchMorphism.ext
    exact p.assoc f.underlying g.underlying h.underlying

end AATSch

/-- VII.定義2.1: selected identity morphism data for `AATSch p`. -/
structure AATSchIdentityData {U : AtomCarrier.{u}} {A : ArchitectureObject U}
    {S : Site.AATSite A} {k : Type v} [CommRing k]
    {p : AATSchReadingParameter.{u, v, w, x, y} S k}
    (X : AATSch p) where
  morphism : AATSchMorphism X X
  underlying_eq : morphism.underlying = p.id X.scheme

namespace AATSchIdentityData

variable {U : AtomCarrier.{u}} {A : ArchitectureObject U}
variable {S : Site.AATSite A} {k : Type v} [CommRing k]
variable {p : AATSchReadingParameter.{u, v, w, x, y} S k}

/-- VII.定義2.1: category identity as selected identity data. -/
def ofCategory (X : AATSch p) : AATSchIdentityData X where
  morphism := 𝟙 X
  underlying_eq := rfl

end AATSchIdentityData

/-- VII.定義2.1: selected composition data for `AATSch p`. -/
structure AATSchCompositionData {U : AtomCarrier.{u}} {A : ArchitectureObject U}
    {S : Site.AATSite A} {k : Type v} [CommRing k]
    {p : AATSchReadingParameter.{u, v, w, x, y} S k}
    {X Y Z : AATSch p}
    (f : AATSchMorphism X Y) (g : AATSchMorphism Y Z) where
  morphism : AATSchMorphism X Z
  underlying_eq : morphism.underlying = p.comp f.underlying g.underlying

namespace AATSchCompositionData

variable {U : AtomCarrier.{u}} {A : ArchitectureObject U}
variable {S : Site.AATSite A} {k : Type v} [CommRing k]
variable {p : AATSchReadingParameter.{u, v, w, x, y} S k}
variable {X Y Z : AATSch p}

/-- VII.定義2.1: category composition as selected composition data. -/
def ofCategory (f : AATSchMorphism X Y) (g : AATSchMorphism Y Z) :
    AATSchCompositionData f g where
  morphism := AATSchMorphism.comp f g
  underlying_eq := rfl

end AATSchCompositionData

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
  id_comp : ∀ {X Y : Target} (f : Hom X Y), comp (id X) f = f
  comp_id : ∀ {X Y : Target} (f : Hom X Y), comp f (id Y) = f
  assoc :
    ∀ {W X Y Z : Target} (f : Hom W X) (g : Hom X Y) (h : Hom Y Z),
      comp (comp f g) h = comp f (comp g h)

namespace AnalyticTargetCategory

variable {Target : Type z}

/-- VII.定義2.1 / AC14: wrapper type carrying the selected target category. -/
def AsCategory (_C : AnalyticTargetCategory.{z} Target) : Type z :=
  Target

/-- VII.定義2.1 / AC14: selected analytic targets form a Mathlib category. -/
instance category (C : AnalyticTargetCategory.{z} Target) :
    Category C.AsCategory where
  Hom X Y := C.Hom X Y
  id X := C.id X
  comp f g := C.comp f g
  id_comp f := C.id_comp f
  comp_id f := C.comp_id f
  assoc f g h := C.assoc f g h

end AnalyticTargetCategory

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

/-- VII.定義2.1 / AC14: bridge an analytic representation to a Mathlib functor. -/
def toFunctor (R : AnalyticRepresentation p Target) :
    AATSch p ⥤ R.targetCategory.AsCategory where
  obj X := R.obj X
  map f := R.map f
  map_id X := R.map_id (AATSchIdentityData.ofCategory X)
  map_comp f g := by
    change R.map (AATSchCompositionData.ofCategory f g).morphism =
      R.targetCategory.comp (R.map f) (R.map g)
    exact R.map_comp (AATSchCompositionData.ofCategory f g)

/-- VII.定義2.1 / AC14: the functor bridge keeps the selected object map. -/
theorem toFunctor_obj (R : AnalyticRepresentation p Target) (X : AATSch p) :
    R.toFunctor.obj X = R.obj X :=
  rfl

/-- VII.定義2.1 / AC14: the functor bridge keeps the selected morphism map. -/
theorem toFunctor_map (R : AnalyticRepresentation p Target)
    {X Y : AATSch p} (f : AATSchMorphism X Y) :
    R.toFunctor.map f = R.map f :=
  rfl

end AnalyticRepresentation

end RepresentationAnalysis
end AAT.AG
