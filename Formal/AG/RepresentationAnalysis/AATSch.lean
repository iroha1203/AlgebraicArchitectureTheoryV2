import Formal.AG.ReadingFunctoriality.Core
import Formal.AG.LawAlgebra.StandardScheme
import Mathlib.CategoryTheory.Category.Basic

noncomputable section

namespace AAT.AG
namespace RepresentationAnalysis

open CategoryTheory

universe u v w x z

variable {U : AtomCarrier.{u}} {A : ArchitectureObject U}
variable {S : Site.AATSite A} {k : Type v} [CommRing k]

/-- VII.定義2.1: selected decoration readings and their compatibility laws. -/
structure AATSchReadingParameter
    (raw : LawAlgebra.RawAmbientRestrictionSystem S k)
    [HasSheafify S.topology (LawAlgebra.AATCommAlgCat k)] where
  AtomLabelReading : Type u
  LawReading : Type u
  ObstructionIdealReading : Type w
  SignatureReading : Type u
  InterpretationMapReading : Type x
  atomLabelsCompatible :
    ∀ {X Y : LawAlgebra.StandardArchitectureScheme raw},
      (X ⟶ Y) → AtomLabelReading → AtomLabelReading → Prop
  lawReadingCompatible :
    ∀ {X Y : LawAlgebra.StandardArchitectureScheme raw},
      (X ⟶ Y) → LawReading → LawReading → Prop
  obstructionIdealCompatible :
    ∀ {X Y : LawAlgebra.StandardArchitectureScheme raw},
      (X ⟶ Y) → ObstructionIdealReading → ObstructionIdealReading → Prop
  signatureReadingCompatible :
    ∀ {X Y : LawAlgebra.StandardArchitectureScheme raw},
      (X ⟶ Y) → SignatureReading → SignatureReading → Prop
  interpretationMapCompatible :
    ∀ {X Y : LawAlgebra.StandardArchitectureScheme raw},
      (X ⟶ Y) → InterpretationMapReading → InterpretationMapReading → Prop
  id_atomLabelsCompatible : ∀ X a, atomLabelsCompatible (𝟙 X) a a
  id_lawReadingCompatible : ∀ X a, lawReadingCompatible (𝟙 X) a a
  id_obstructionIdealCompatible : ∀ X a, obstructionIdealCompatible (𝟙 X) a a
  id_signatureReadingCompatible : ∀ X a, signatureReadingCompatible (𝟙 X) a a
  id_interpretationMapCompatible : ∀ X a, interpretationMapCompatible (𝟙 X) a a
  comp_atomLabelsCompatible : ∀ {X Y Z} {f : X ⟶ Y} {g : Y ⟶ Z} {aX aY aZ},
    atomLabelsCompatible f aX aY → atomLabelsCompatible g aY aZ →
      atomLabelsCompatible (f ≫ g) aX aZ
  comp_lawReadingCompatible : ∀ {X Y Z} {f : X ⟶ Y} {g : Y ⟶ Z} {aX aY aZ},
    lawReadingCompatible f aX aY → lawReadingCompatible g aY aZ →
      lawReadingCompatible (f ≫ g) aX aZ
  comp_obstructionIdealCompatible :
    ∀ {X Y Z} {f : X ⟶ Y} {g : Y ⟶ Z} {aX aY aZ},
      obstructionIdealCompatible f aX aY → obstructionIdealCompatible g aY aZ →
        obstructionIdealCompatible (f ≫ g) aX aZ
  comp_signatureReadingCompatible :
    ∀ {X Y Z} {f : X ⟶ Y} {g : Y ⟶ Z} {aX aY aZ},
      signatureReadingCompatible f aX aY → signatureReadingCompatible g aY aZ →
        signatureReadingCompatible (f ≫ g) aX aZ
  comp_interpretationMapCompatible :
    ∀ {X Y Z} {f : X ⟶ Y} {g : Y ⟶ Z} {aX aY aZ},
      interpretationMapCompatible f aX aY → interpretationMapCompatible g aY aZ →
        interpretationMapCompatible (f ≫ g) aX aZ

/-- VII.定義2.1: standard architecture scheme with selected readings. -/
structure AATSch
    {raw : LawAlgebra.RawAmbientRestrictionSystem S k}
    [HasSheafify S.topology (LawAlgebra.AATCommAlgCat k)]
    (p : AATSchReadingParameter raw) where
  scheme : LawAlgebra.StandardArchitectureScheme raw
  atomLabels : p.AtomLabelReading
  lawReading : p.LawReading
  obstructionIdealReading : p.ObstructionIdealReading
  signatureReading : p.SignatureReading
  interpretationMapReading : p.InterpretationMapReading

/-- VII.定義2.1: morphism of decorated standard architecture schemes. -/
structure AATSchMorphism
    {raw : LawAlgebra.RawAmbientRestrictionSystem S k}
    [HasSheafify S.topology (LawAlgebra.AATCommAlgCat k)]
    {p : AATSchReadingParameter raw} (X Y : AATSch p) where
  toSchemeHom : X.scheme ⟶ Y.scheme
  atomLabelsCompatible : p.atomLabelsCompatible toSchemeHom X.atomLabels Y.atomLabels
  lawReadingCompatible : p.lawReadingCompatible toSchemeHom X.lawReading Y.lawReading
  obstructionIdealCompatible : p.obstructionIdealCompatible toSchemeHom
    X.obstructionIdealReading Y.obstructionIdealReading
  signatureReadingCompatible : p.signatureReadingCompatible toSchemeHom
    X.signatureReading Y.signatureReading
  interpretationMapCompatible : p.interpretationMapCompatible toSchemeHom
    X.interpretationMapReading Y.interpretationMapReading

namespace AATSchMorphism

/-- Underlying Mathlib Scheme morphism. -/
def toSchemeMap
    {raw : LawAlgebra.RawAmbientRestrictionSystem S k}
    [HasSheafify S.topology (LawAlgebra.AATCommAlgCat k)]
    {p : AATSchReadingParameter raw} {X Y : AATSch p}
    (f : AATSchMorphism X Y) : X.scheme.underlying ⟶ Y.scheme.underlying :=
  f.toSchemeHom.base

@[ext] theorem ext
    {raw : LawAlgebra.RawAmbientRestrictionSystem S k}
    [HasSheafify S.topology (LawAlgebra.AATCommAlgCat k)]
    {p : AATSchReadingParameter raw} {X Y : AATSch p}
    {f g : AATSchMorphism X Y} (h : f.toSchemeHom = g.toSchemeHom) : f = g := by
  cases f
  cases g
  cases h
  rfl

def id
    {raw : LawAlgebra.RawAmbientRestrictionSystem S k}
    [HasSheafify S.topology (LawAlgebra.AATCommAlgCat k)]
    {p : AATSchReadingParameter raw} (X : AATSch p) : AATSchMorphism X X where
  toSchemeHom := 𝟙 X.scheme
  atomLabelsCompatible := p.id_atomLabelsCompatible X.scheme X.atomLabels
  lawReadingCompatible := p.id_lawReadingCompatible X.scheme X.lawReading
  obstructionIdealCompatible := p.id_obstructionIdealCompatible X.scheme X.obstructionIdealReading
  signatureReadingCompatible := p.id_signatureReadingCompatible X.scheme X.signatureReading
  interpretationMapCompatible :=
    p.id_interpretationMapCompatible X.scheme X.interpretationMapReading

def comp
    {raw : LawAlgebra.RawAmbientRestrictionSystem S k}
    [HasSheafify S.topology (LawAlgebra.AATCommAlgCat k)]
    {p : AATSchReadingParameter raw} {X Y Z : AATSch p}
    (f : AATSchMorphism X Y) (g : AATSchMorphism Y Z) : AATSchMorphism X Z where
  toSchemeHom := f.toSchemeHom ≫ g.toSchemeHom
  atomLabelsCompatible := p.comp_atomLabelsCompatible
    f.atomLabelsCompatible g.atomLabelsCompatible
  lawReadingCompatible := p.comp_lawReadingCompatible
    f.lawReadingCompatible g.lawReadingCompatible
  obstructionIdealCompatible := p.comp_obstructionIdealCompatible
    f.obstructionIdealCompatible g.obstructionIdealCompatible
  signatureReadingCompatible := p.comp_signatureReadingCompatible
    f.signatureReadingCompatible g.signatureReadingCompatible
  interpretationMapCompatible := p.comp_interpretationMapCompatible
    f.interpretationMapCompatible g.interpretationMapCompatible

@[simp] theorem id_toSchemeHom
    {raw : LawAlgebra.RawAmbientRestrictionSystem S k}
    [HasSheafify S.topology (LawAlgebra.AATCommAlgCat k)]
    {p : AATSchReadingParameter raw} (X : AATSch p) :
    (id X).toSchemeHom = 𝟙 X.scheme := rfl

@[simp] theorem comp_toSchemeHom
    {raw : LawAlgebra.RawAmbientRestrictionSystem S k}
    [HasSheafify S.topology (LawAlgebra.AATCommAlgCat k)]
    {p : AATSchReadingParameter raw} {X Y Z : AATSch p}
    (f : AATSchMorphism X Y) (g : AATSchMorphism Y Z) :
    (comp f g).toSchemeHom = f.toSchemeHom ≫ g.toSchemeHom := rfl

@[simp] theorem id_toSchemeMap
    {raw : LawAlgebra.RawAmbientRestrictionSystem S k}
    [HasSheafify S.topology (LawAlgebra.AATCommAlgCat k)]
    {p : AATSchReadingParameter raw} (X : AATSch p) :
    (id X).toSchemeMap = 𝟙 X.scheme.underlying := rfl

@[simp] theorem comp_toSchemeMap
    {raw : LawAlgebra.RawAmbientRestrictionSystem S k}
    [HasSheafify S.topology (LawAlgebra.AATCommAlgCat k)]
    {p : AATSchReadingParameter raw} {X Y Z : AATSch p}
    (f : AATSchMorphism X Y) (g : AATSchMorphism Y Z) :
    (comp f g).toSchemeMap = f.toSchemeMap ≫ g.toSchemeMap := rfl

end AATSchMorphism

namespace AATSch

instance category
    {raw : LawAlgebra.RawAmbientRestrictionSystem S k}
    [HasSheafify S.topology (LawAlgebra.AATCommAlgCat k)]
    (p : AATSchReadingParameter raw) : Category (AATSch p) where
  Hom := AATSchMorphism
  id := AATSchMorphism.id
  comp := AATSchMorphism.comp
  id_comp f := by apply AATSchMorphism.ext; simp [AATSchMorphism.comp, AATSchMorphism.id]
  comp_id f := by apply AATSchMorphism.ext; simp [AATSchMorphism.comp, AATSchMorphism.id]
  assoc f g h := by apply AATSchMorphism.ext; simp [AATSchMorphism.comp]

/-- VII.定義2.1: forget decorations to the canonical standard architecture scheme. -/
def forget
    {raw : LawAlgebra.RawAmbientRestrictionSystem S k}
    [HasSheafify S.topology (LawAlgebra.AATCommAlgCat k)]
    (p : AATSchReadingParameter raw) :
    AATSch p ⥤ LawAlgebra.StandardArchitectureScheme raw where
  obj X := X.scheme
  map f := f.toSchemeHom
  map_id _ := rfl
  map_comp _ _ := rfl

instance forget_faithful
    {raw : LawAlgebra.RawAmbientRestrictionSystem S k}
    [HasSheafify S.topology (LawAlgebra.AATCommAlgCat k)]
    (p : AATSchReadingParameter raw) : (forget p).Faithful where
  map_injective h := AATSchMorphism.ext h

@[simp] theorem forget_obj
    {raw : LawAlgebra.RawAmbientRestrictionSystem S k}
    [HasSheafify S.topology (LawAlgebra.AATCommAlgCat k)]
    (p : AATSchReadingParameter raw) (X : AATSch p) :
    (forget p).obj X = X.scheme := rfl

@[simp] theorem forget_map
    {raw : LawAlgebra.RawAmbientRestrictionSystem S k}
    [HasSheafify S.topology (LawAlgebra.AATCommAlgCat k)]
    (p : AATSchReadingParameter raw) {X Y : AATSch p} (f : X ⟶ Y) :
    (forget p).map f = f.toSchemeHom := rfl

end AATSch

/-- VII.定義2.1: analytic representations are Mathlib functors. -/
abbrev AnalyticRepresentation
    {raw : LawAlgebra.RawAmbientRestrictionSystem S k}
    [HasSheafify S.topology (LawAlgebra.AATCommAlgCat k)]
    (p : AATSchReadingParameter raw) (Target : Type z) [Category Target] :=
  AATSch p ⥤ Target

end RepresentationAnalysis
end AAT.AG
