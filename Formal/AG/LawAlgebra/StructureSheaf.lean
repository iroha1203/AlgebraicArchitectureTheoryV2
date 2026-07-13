import Formal.AG.LawAlgebra.StructuralRelation
import Formal.AG.Site.Descent
import Mathlib.Algebra.Category.Ring.Under.Basic
import Mathlib.CategoryTheory.Sites.Sheafification
import Mathlib.CategoryTheory.Sites.Whiskering

namespace AAT.AG
namespace LawAlgebra

universe u v

noncomputable section

open CategoryTheory
open Opposite

/--
III.R3: the category of commutative `k`-algebras used for the law algebra
sheaf.

This is the Mathlib-facing target category for algebra-valued presheaves:
objects are commutative rings equipped with the selected structure map from the
universe-lifted coefficient ring `ULift k`.
-/
abbrev AATCommAlgCat (k : Type v) [CommRing k] :=
  Under (CommRingCat.of (ULift.{max u v, v} k))

/--
III.R3: a commutative `k`-algebra-valued presheaf on an AAT site.

This extends the Part II Type-valued presheaf surface by changing the codomain to
the bundled category of commutative `k`-algebras.
-/
abbrev AlgebraValuedAATPresheaf {U : AtomCarrier.{u}} {A : ArchitectureObject U}
    (S : Site.AATSite A) (k : Type v) [CommRing k] :=
  S.categoryᵒᵖ ⥤ AATCommAlgCat k

/-! ### Typed raw ambient restriction systems -/

/--
III.R3: typed polynomial restriction data on every morphism of the selected
AAT site, with identity and composition coherence before quotienting.
-/
structure RawAmbientRestrictionSystem {U : AtomCarrier.{u}}
    {A : ArchitectureObject U} (S : Site.AATSite A)
    (k : Type v) [CommRing k] where
  /-- The typed coordinate family assigned to each selected site object. -/
  coordFamily : (W : S.category) -> CoordinateFamily W.ctx
  /-- The structural equations imposed on the coordinates of each object. -/
  relationFamily : (W : S.category) ->
    StructuralRelationFamily (coordFamily W) k
  /-- Restriction data together with preservation of the structural ideal. -/
  restrictionStable : ∀ {X Y : S.category} (f : X ⟶ Y),
    RestrictionStableStructuralRelations
      (relationFamily X) (relationFamily Y)
      (S.contextPreorder.morphism (CategoryTheory.leOfHom f))
  identity_polynomialMap : ∀ X : S.category,
    (restrictionStable (𝟙 X)).restriction.polynomialMap =
      RingHom.id (FreeTypedCommAlg (coordFamily X) k)
  composition_polynomialMap :
    ∀ {X Y Z : S.category} (f : X ⟶ Y) (g : Y ⟶ Z),
      (restrictionStable (f ≫ g)).restriction.polynomialMap =
        ((restrictionStable f).restriction.polynomialMap).comp
          ((restrictionStable g).restriction.polynomialMap)

namespace RawAmbientRestrictionSystem

/-- Two restriction systems agree when their three data-bearing fields agree. -/
@[ext]
theorem ext {U : AtomCarrier.{u}} {A : ArchitectureObject U}
    {S : Site.AATSite A} {k : Type v} [CommRing k]
    (B C : RawAmbientRestrictionSystem S k)
    (hcoord : B.coordFamily = C.coordFamily)
    (hrelation : HEq B.relationFamily C.relationFamily)
    (hrestriction : HEq
      (@RawAmbientRestrictionSystem.restrictionStable U A S k _ B)
      (@RawAmbientRestrictionSystem.restrictionStable U A S k _ C)) :
    B = C := by
  cases B with
  | mk Bcoord Brelation Brestriction Bid Bcomp =>
      cases C with
      | mk Ccoord Crelation Crestriction Cid Ccomp =>
          cases hcoord
          cases hrelation
          cases hrestriction
          rfl

/-- III.R3: the structural quotient assigned to a site object. -/
abbrev rawAlgebra {U : AtomCarrier.{u}} {A : ArchitectureObject U}
    {S : Site.AATSite A} {k : Type v} [CommRing k]
    (B : RawAmbientRestrictionSystem S k) (W : S.category) :
    Type (max u v) :=
  (B.relationFamily W).RawAmbientLawAlgebra

end RawAmbientRestrictionSystem

/-- Typed polynomial restrictions fix coefficients. -/
theorem TypedCoordinateRestriction.polynomialMap_C
    {U : AtomCarrier.{u}} {A : ArchitectureObject U}
    {source target : Site.ArchitectureContext A}
    {sourceFamily : CoordinateFamily source}
    {targetFamily : CoordinateFamily target}
    {k : Type v} [CommRing k]
    {f : Site.ContextMorphism source target}
    (rho : TypedCoordinateRestriction sourceFamily targetFamily k f)
    (x : k) :
    rho.polynomialMap (MvPolynomial.C x) = MvPolynomial.C x := by
  simp [TypedCoordinateRestriction.polynomialMap]

/-- Descended structural restrictions fix coefficient classes. -/
theorem RestrictionStableStructuralRelations.quotientDesc_C
    {U : AtomCarrier.{u}} {A : ArchitectureObject U}
    {source target : Site.ArchitectureContext A}
    {sourceFamily : CoordinateFamily source}
    {targetFamily : CoordinateFamily target}
    {k : Type v} [CommRing k]
    {sourceRelations : StructuralRelationFamily sourceFamily k}
    {targetRelations : StructuralRelationFamily targetFamily k}
    {f : Site.ContextMorphism source target}
    (h : RestrictionStableStructuralRelations sourceRelations targetRelations f)
    (x : k) :
    h.quotientDesc (targetRelations.quotientMap (MvPolynomial.C x)) =
      sourceRelations.quotientMap (MvPolynomial.C x) := by
  rw [h.quotientDesc_mk, h.restriction.polynomialMap_C]

namespace RawAmbientRestrictionSystem

/-- Quotient descent inherits identity from polynomial restriction. -/
theorem quotientDesc_id {U : AtomCarrier.{u}} {A : ArchitectureObject U}
    {S : Site.AATSite A} {k : Type v} [CommRing k]
    (B : RawAmbientRestrictionSystem S k) (X : S.category) :
    (B.restrictionStable (𝟙 X)).quotientDesc =
      RingHom.id (B.rawAlgebra X) := by
  apply Ideal.Quotient.ringHom_ext
  apply RingHom.ext
  intro p
  change (B.restrictionStable (𝟙 X)).quotientDesc
      ((B.relationFamily X).quotientMap p) =
    (B.relationFamily X).quotientMap p
  rw [
    RestrictionStableStructuralRelations.quotientDesc_mk,
    B.identity_polynomialMap]
  rfl

/-- Quotient descent inherits composition from polynomial restriction. -/
theorem quotientDesc_comp {U : AtomCarrier.{u}} {A : ArchitectureObject U}
    {S : Site.AATSite A} {k : Type v} [CommRing k]
    (B : RawAmbientRestrictionSystem S k)
    {X Y Z : S.category} (f : X ⟶ Y) (g : Y ⟶ Z) :
    (B.restrictionStable (f ≫ g)).quotientDesc =
      ((B.restrictionStable f).quotientDesc).comp
        ((B.restrictionStable g).quotientDesc) := by
  apply Ideal.Quotient.ringHom_ext
  apply RingHom.ext
  intro p
  change (B.restrictionStable (f ≫ g)).quotientDesc
      ((B.relationFamily Z).quotientMap p) =
    (B.restrictionStable f).quotientDesc
      ((B.restrictionStable g).quotientDesc
        ((B.relationFamily Z).quotientMap p))
  rw [
    RestrictionStableStructuralRelations.quotientDesc_mk,
    RestrictionStableStructuralRelations.quotientDesc_mk,
    RestrictionStableStructuralRelations.quotientDesc_mk,
    B.composition_polynomialMap]
  rfl

/-- The coefficient structure map for a raw structural quotient. -/
private noncomputable def algebraObject {U : AtomCarrier.{u}}
    {A : ArchitectureObject U} {S : Site.AATSite A}
    {k : Type v} [CommRing k] (B : RawAmbientRestrictionSystem S k)
    (W : S.category) : AATCommAlgCat k :=
  Under.mk (CommRingCat.ofHom
    (((B.relationFamily W).quotientMap.comp MvPolynomial.C).comp
      ULift.ringEquiv.toRingHom))

/-- III.R3: the actual algebra-valued presheaf induced by typed restrictions. -/
noncomputable def toPresheaf {U : AtomCarrier.{u}} {A : ArchitectureObject U}
    {S : Site.AATSite A} {k : Type v} [CommRing k]
    (B : RawAmbientRestrictionSystem S k) :
    AlgebraValuedAATPresheaf S k where
  obj W := B.algebraObject W.unop
  map {X Y} f := Under.homMk
    (CommRingCat.ofHom (B.restrictionStable f.unop).quotientDesc)
    (by
      ext x
      change (B.restrictionStable f.unop).quotientDesc
          ((B.relationFamily X.unop).quotientMap (MvPolynomial.C x.down)) =
        (B.relationFamily Y.unop).quotientMap (MvPolynomial.C x.down)
      rw [RestrictionStableStructuralRelations.quotientDesc_C])
  map_id X := by
    apply Under.UnderMorphism.ext
    exact congrArg CommRingCat.ofHom (B.quotientDesc_id X.unop)
  map_comp f g := by
    apply Under.UnderMorphism.ext
    exact congrArg CommRingCat.ofHom (B.quotientDesc_comp g.unop f.unop)

/-- The presheaf object is definitionally the corresponding raw quotient. -/
noncomputable def toPresheafObjectIso {U : AtomCarrier.{u}}
    {A : ArchitectureObject U} {S : Site.AATSite A}
    {k : Type v} [CommRing k] (B : RawAmbientRestrictionSystem S k)
    (W : S.category) :
    B.rawAlgebra W ≃+* (B.toPresheaf.obj (Opposite.op W)).right :=
  RingEquiv.refl _

/-- The objectwise identification intertwines descended restriction and map. -/
theorem toPresheaf_map {U : AtomCarrier.{u}} {A : ArchitectureObject U}
    {S : Site.AATSite A} {k : Type v} [CommRing k]
    (B : RawAmbientRestrictionSystem S k)
    {X Y : S.category} (f : X ⟶ Y) (x : B.rawAlgebra Y) :
    B.toPresheafObjectIso X ((B.restrictionStable f).quotientDesc x) =
      (B.toPresheaf.map f.op).right (B.toPresheafObjectIso Y x) :=
  rfl

end RawAmbientRestrictionSystem

/-- III.定義2.1: a law algebra sheaf is a `k`-algebra-valued sheaf on `J_U`. -/
abbrev LawAlgebraSheaf {U : AtomCarrier.{u}} {A : ArchitectureObject U}
    (S : Site.AATSite A) (k : Type v) [CommRing k] :=
  Sheaf S.topology (AATCommAlgCat k)

/--
III.R3: bridge from the R2 raw ambient algebra package to an algebra-valued
presheaf on the selected AAT site.

The raw algebra package is indexed by native contexts. The presheaf is indexed
by the wrapped site category. `identifiesObject` records the objectwise reading
of the site presheaf as `O_raw^U(W)`.
-/
structure RawAmbientAlgebraPresheafBridge {U : AtomCarrier.{u}}
    {A : ArchitectureObject U} (S : Site.AATSite A)
    (k : Type v) [CommRing k] where
  rawAmbient : RawAmbientPresheafBridge (A := A) k
  rawPresheaf : AlgebraValuedAATPresheaf S k
  identifiesObject :
    ∀ W : S.category,
      rawAmbient.rawAlgebra W.ctx ≃+* (rawPresheaf.obj (op W)).right
  restriction_naturality :
    ∀ {source target : S.category} (h : S.contextPreorder.Hom source.ctx target.ctx)
      (x : rawAmbient.rawAlgebra target.ctx),
        identifiesObject source
            (rawAmbient.res (S.contextPreorder.morphism h) x) =
          (rawPresheaf.map (CategoryTheory.homOfLE h).op).right
            (identifiesObject target x)

namespace RawAmbientAlgebraPresheafBridge

/-- III.R3: the site-indexed raw algebra presheaf. -/
def toPresheaf {U : AtomCarrier.{u}} {A : ArchitectureObject U}
    {S : Site.AATSite A} {k : Type v} [CommRing k]
    (B : RawAmbientAlgebraPresheafBridge S k) :
    AlgebraValuedAATPresheaf S k :=
  B.rawPresheaf

/-- III.R3: the objectwise identification with the raw ambient quotient. -/
def objectIso {U : AtomCarrier.{u}} {A : ArchitectureObject U}
    {S : Site.AATSite A} {k : Type v} [CommRing k]
    (B : RawAmbientAlgebraPresheafBridge S k) (W : S.category) :
    B.rawAmbient.rawAlgebra W.ctx ≃+* (B.rawPresheaf.obj (op W)).right :=
  B.identifiesObject W

/-- III.R3: objectwise identifications commute with raw restriction maps. -/
theorem restriction_naturality_apply {U : AtomCarrier.{u}} {A : ArchitectureObject U}
    {S : Site.AATSite A} {k : Type v} [CommRing k]
    (B : RawAmbientAlgebraPresheafBridge S k)
    {source target : S.category} (h : S.contextPreorder.Hom source.ctx target.ctx)
    (x : B.rawAmbient.rawAlgebra target.ctx) :
    B.objectIso source
        (B.rawAmbient.res (S.contextPreorder.morphism h) x) =
      (B.rawPresheaf.map (CategoryTheory.homOfLE h).op).right (B.objectIso target x) :=
  B.restriction_naturality h x

end RawAmbientAlgebraPresheafBridge

/--
III.定義2.1: `O_X^U = (O_raw^U)^+` as a selected sheafification bridge.

This records the AAT-facing data supplied by Mathlib's sheafification surface:
the raw algebra-valued presheaf, the sheafified object, and the canonical map
from raw sections to sheafified sections. It does not construct a new
sheafification theory.
-/
structure LawAlgebraSheafificationBridge {U : AtomCarrier.{u}}
    {A : ArchitectureObject U} (S : Site.AATSite A)
    (k : Type v) [CommRing k] where
  raw : AlgebraValuedAATPresheaf S k
  plus : LawAlgebraSheaf S k
  canonical : raw ⟶ plus.val
  isSheafification :
    ∀ (F : LawAlgebraSheaf S k) (η : raw ⟶ F.val),
      ∃! lift : plus.val ⟶ F.val, canonical ≫ lift = η

namespace LawAlgebraSheafificationBridge

/-- III.定義2.1: the sheafified law algebra `O_X^U`. -/
abbrev OX {U : AtomCarrier.{u}} {A : ArchitectureObject U}
    {S : Site.AATSite A} {k : Type v} [CommRing k]
    (B : LawAlgebraSheafificationBridge S k) : LawAlgebraSheaf S k :=
  B.plus

/-- III.定義2.1: the underlying presheaf of `O_X^U`. -/
abbrev OXPresheaf {U : AtomCarrier.{u}} {A : ArchitectureObject U}
    {S : Site.AATSite A} {k : Type v} [CommRing k]
    (B : LawAlgebraSheafificationBridge S k) :
    AlgebraValuedAATPresheaf S k :=
  B.plus.val

/-- III.定義2.1: the canonical component `O_raw^U(W) -> O_X^U(W)`. -/
def canonicalAt {U : AtomCarrier.{u}} {A : ArchitectureObject U}
    {S : Site.AATSite A} {k : Type v} [CommRing k]
    (B : LawAlgebraSheafificationBridge S k) (W : S.category) :
    B.raw.obj (op W) ⟶ B.OXPresheaf.obj (op W) :=
  B.canonical.app (op W)

/-- III.定義2.1: the codomain of the bridge is a sheaf on `J_U`. -/
theorem plus_isSheaf {U : AtomCarrier.{u}} {A : ArchitectureObject U}
    {S : Site.AATSite A} {k : Type v} [CommRing k]
    (B : LawAlgebraSheafificationBridge S k) :
    Presheaf.IsSheaf S.topology B.OXPresheaf :=
  B.plus.cond

/-- III.定義2.1: the notation `O_X^U` is definitionally the selected plus object. -/
theorem OX_eq_plus {U : AtomCarrier.{u}} {A : ArchitectureObject U}
    {S : Site.AATSite A} {k : Type v} [CommRing k]
    (B : LawAlgebraSheafificationBridge S k) :
    B.OX = B.plus :=
  rfl

/--
III.定義2.1: the selected plus object satisfies the sheafification universal
property against every algebra-valued sheaf.
-/
theorem sheafification_lift_unique {U : AtomCarrier.{u}}
    {A : ArchitectureObject U} {S : Site.AATSite A}
    {k : Type v} [CommRing k] (B : LawAlgebraSheafificationBridge S k)
    (F : LawAlgebraSheaf S k) (η : B.raw ⟶ F.val) :
    ∃! lift : B.OXPresheaf ⟶ F.val, B.canonical ≫ lift = η :=
  B.isSheafification F η

/--
III.R4: Mathlib sheafification gives the universal property for the
`k`-algebra-valued raw presheaf whenever the selected codomain has a
`HasSheafify` instance.

This is the Mathlib-facing bridge theorem: it uses `CategoryTheory.toSheafify`,
`CategoryTheory.sheafifyLift`, and `CategoryTheory.sheafifyLift_unique`
directly, rather than consuming a selected `LawAlgebraSheafificationBridge`
field as the conclusion.
-/
theorem mathlib_sheafification_lift_unique {U : AtomCarrier.{u}}
    {A : ArchitectureObject U} {S : Site.AATSite A}
    {k : Type v} [CommRing k]
    [CategoryTheory.HasSheafify S.topology (AATCommAlgCat k)]
    (raw : AlgebraValuedAATPresheaf S k)
    (F : LawAlgebraSheaf S k) (η : raw ⟶ F.val) :
    ∃! lift : CategoryTheory.sheafify S.topology raw ⟶ F.val,
      CategoryTheory.toSheafify S.topology raw ≫ lift = η := by
  refine ⟨CategoryTheory.sheafifyLift S.topology η F.cond, ?_, ?_⟩
  · exact CategoryTheory.toSheafify_sheafifyLift S.topology η F.cond
  · intro lift hlift
    exact CategoryTheory.sheafifyLift_unique S.topology η F.cond lift hlift

/--
III.R4: construct the selected AAT sheafification bridge from Mathlib's
`HasSheafify` surface.

The hypothesis is explicit: this does not assert that every
`AATCommAlgCat`-valued presheaf has an available sheafification instance in the
current imports. When such an instance is supplied, the selected bridge is the
Mathlib sheafification object with its canonical unit map and universal
property.
-/
noncomputable def ofMathlibSheafification {U : AtomCarrier.{u}}
    {A : ArchitectureObject U} {S : Site.AATSite A}
    {k : Type v} [CommRing k]
    [CategoryTheory.HasSheafify S.topology (AATCommAlgCat k)]
    (raw : AlgebraValuedAATPresheaf S k) :
    LawAlgebraSheafificationBridge S k where
  raw := raw
  plus := CategoryTheory.presheafToSheaf S.topology (AATCommAlgCat k) |>.obj raw
  canonical := CategoryTheory.toSheafify S.topology raw
  isSheafification := fun F η =>
    mathlib_sheafification_lift_unique raw F η

@[simp]
theorem ofMathlibSheafification_raw {U : AtomCarrier.{u}}
    {A : ArchitectureObject U} {S : Site.AATSite A}
    {k : Type v} [CommRing k]
    [CategoryTheory.HasSheafify S.topology (AATCommAlgCat k)]
    (raw : AlgebraValuedAATPresheaf S k) :
    (ofMathlibSheafification (S := S) raw).raw = raw :=
  rfl

@[simp]
theorem ofMathlibSheafification_OXPresheaf {U : AtomCarrier.{u}}
    {A : ArchitectureObject U} {S : Site.AATSite A}
    {k : Type v} [CommRing k]
    [CategoryTheory.HasSheafify S.topology (AATCommAlgCat k)]
    (raw : AlgebraValuedAATPresheaf S k) :
    (ofMathlibSheafification (S := S) raw).OXPresheaf =
      CategoryTheory.sheafify S.topology raw :=
  rfl

@[simp]
theorem ofMathlibSheafification_canonical {U : AtomCarrier.{u}}
    {A : ArchitectureObject U} {S : Site.AATSite A}
    {k : Type v} [CommRing k]
    [CategoryTheory.HasSheafify S.topology (AATCommAlgCat k)]
    (raw : AlgebraValuedAATPresheaf S k) :
    (ofMathlibSheafification (S := S) raw).canonical =
      CategoryTheory.toSheafify S.topology raw :=
  rfl

end LawAlgebraSheafificationBridge

/-! ### Ringed AAT site presentation -/

/--
SD4: an AAT site together with the raw algebra-valued presheaf whose Mathlib
sheafification supplies the structure sheaf.
-/
structure RingedAATSite {U : AtomCarrier.{u}} {A : ArchitectureObject U}
    (S : Site.AATSite A) (k : Type v) [CommRing k] where
  /-- The typed raw algebra presheaf on the selected site. -/
  raw : AlgebraValuedAATPresheaf S k

namespace RingedAATSite

/-- The selected AAT site underlying a ringed presentation. -/
def site {U : AtomCarrier.{u}} {A : ArchitectureObject U}
    {S : Site.AATSite A} {k : Type v} [CommRing k]
    (_R : RingedAATSite S k) : Site.AATSite A :=
  S

/-- The architecture object carried by the selected site. -/
def architectureObject {U : AtomCarrier.{u}} {A : ArchitectureObject U}
    {S : Site.AATSite A} {k : Type v} [CommRing k]
    (_R : RingedAATSite S k) : ArchitectureObject U :=
  S.architectureObject

/-- Ringed presentations agree when their raw algebra presheaves agree. -/
@[ext]
theorem ext {U : AtomCarrier.{u}} {A : ArchitectureObject U}
    {S : Site.AATSite A} {k : Type v} [CommRing k]
    (R T : RingedAATSite S k) (hraw : R.raw = T.raw) : R = T := by
  cases R
  cases T
  cases hraw
  rfl

/-- Construct the ringed presentation whose structure sheaf is Mathlib sheafification. -/
noncomputable def ofMathlibSheafification
    {U : AtomCarrier.{u}} {A : ArchitectureObject U}
    {S : Site.AATSite A} {k : Type v} [CommRing k]
    [CategoryTheory.HasSheafify S.topology (AATCommAlgCat k)]
    (raw : AlgebraValuedAATPresheaf S k) : RingedAATSite S k where
  raw := raw

/-- The actual commutative-algebra-valued structure sheaf. -/
noncomputable def structureSheaf
    {U : AtomCarrier.{u}} {A : ArchitectureObject U}
    {S : Site.AATSite A} {k : Type v} [CommRing k]
    (R : RingedAATSite S k)
    [CategoryTheory.HasSheafify S.topology (AATCommAlgCat k)] :
    LawAlgebraSheaf S k :=
  (CategoryTheory.presheafToSheaf S.topology (AATCommAlgCat k)).obj R.raw

/-- The canonical unit from raw sections to the structure sheaf. -/
noncomputable def canonical
    {U : AtomCarrier.{u}} {A : ArchitectureObject U}
    {S : Site.AATSite A} {k : Type v} [CommRing k]
    (R : RingedAATSite S k)
    [CategoryTheory.HasSheafify S.topology (AATCommAlgCat k)] :
    R.raw ⟶ R.structureSheaf.val :=
  CategoryTheory.toSheafify S.topology R.raw

/-- The structure sheaf is exactly Mathlib sheafification. -/
@[simp]
theorem structureSheaf_eq_sheafify
    {U : AtomCarrier.{u}} {A : ArchitectureObject U}
    {S : Site.AATSite A} {k : Type v} [CommRing k]
    (R : RingedAATSite S k)
    [CategoryTheory.HasSheafify S.topology (AATCommAlgCat k)] :
    R.structureSheaf =
      (CategoryTheory.presheafToSheaf S.topology (AATCommAlgCat k)).obj R.raw :=
  rfl

/-- The canonical map is exactly Mathlib's sheafification unit. -/
@[simp]
theorem canonical_eq_toSheafify
    {U : AtomCarrier.{u}} {A : ArchitectureObject U}
    {S : Site.AATSite A} {k : Type v} [CommRing k]
    (R : RingedAATSite S k)
    [CategoryTheory.HasSheafify S.topology (AATCommAlgCat k)] :
    R.canonical = CategoryTheory.toSheafify S.topology R.raw :=
  rfl

/-- The Mathlib structure sheaf satisfies the sheafification universal property. -/
theorem lift_unique
    {U : AtomCarrier.{u}} {A : ArchitectureObject U}
    {S : Site.AATSite A} {k : Type v} [CommRing k]
    (R : RingedAATSite S k)
    [CategoryTheory.HasSheafify S.topology (AATCommAlgCat k)]
    (F : LawAlgebraSheaf S k) (η : R.raw ⟶ F.val) :
    ∃! lift : R.structureSheaf.val ⟶ F.val, R.canonical ≫ lift = η :=
  LawAlgebraSheafificationBridge.mathlib_sheafification_lift_unique R.raw F η

end RingedAATSite

/-- Forget a commutative `k`-algebra to its underlying type. -/
def AATCommAlgToType (k : Type v) [CommRing k] :
    AATCommAlgCat.{u, v} k ⥤ Type (max u v) :=
  CategoryTheory.Under.forget
      (CommRingCat.of (ULift.{max u v, v} k)) ⋙
    CategoryTheory.forget CommRingCat

namespace RingedAATSite

/-- The underlying Type-valued sheaf obtained by forgetting algebra structure. -/
noncomputable def underlyingTypeSheaf
    {U : AtomCarrier.{u}} {A : ArchitectureObject U}
    {S : Site.AATSite A} {k : Type v} [CommRing k]
    (R : RingedAATSite S k)
    [CategoryTheory.HasSheafify S.topology (AATCommAlgCat k)]
    [S.topology.HasSheafCompose (AATCommAlgToType k)] :
    CategoryTheory.Sheaf S.topology (Type (max u v)) :=
  (CategoryTheory.sheafCompose S.topology (AATCommAlgToType k)).obj
    R.structureSheaf

/-- The underlying sheaf is the forgetful image of the structure sheaf. -/
@[simp]
theorem underlyingTypeSheaf_val
    {U : AtomCarrier.{u}} {A : ArchitectureObject U}
    {S : Site.AATSite A} {k : Type v} [CommRing k]
    (R : RingedAATSite S k)
    [CategoryTheory.HasSheafify S.topology (AATCommAlgCat k)]
    [S.topology.HasSheafCompose (AATCommAlgToType k)] :
    R.underlyingTypeSheaf.val =
      R.structureSheaf.val ⋙ AATCommAlgToType k :=
  rfl

end RingedAATSite

/--
III.条件4.5: selected presentation data at a context.

The predicates are assumptions about the selected presentation, not new
global theorems about all sheafifications. They are kept explicit so later
affine chart work can state exactly which presentations survive passage from
`O_raw^U` to `O_X^U`.
-/
structure SelectedLawAlgebraPresentation {U : AtomCarrier.{u}}
    {A : ArchitectureObject U} {S : Site.AATSite A}
    {k : Type v} [CommRing k]
    (B : LawAlgebraSheafificationBridge S k) (W : S.category) where
  Generator : Type u
  Relation : Type u
  rawGenerator : Generator -> (B.raw.obj (op W)).right
  sheafifiedGenerator : Generator -> (B.OXPresheaf.obj (op W)).right
  rawRelation : Relation -> (B.raw.obj (op W)).right
  sheafifiedRelation : Relation -> (B.OXPresheaf.obj (op W)).right
  presentsRaw : Prop
  presentsSheafified : Prop
  canonical_preserves_generator :
    ∀ g : Generator, (B.canonicalAt W).right (rawGenerator g) = sheafifiedGenerator g
  canonical_preserves_relation :
    ∀ r : Relation, (B.canonicalAt W).right (rawRelation r) = sheafifiedRelation r

/-- III.条件4.5: presentation-stability at a single context. -/
def PresentationStableAt {U : AtomCarrier.{u}} {A : ArchitectureObject U}
    {S : Site.AATSite A} {k : Type v} [CommRing k]
    {B : LawAlgebraSheafificationBridge S k} {W : S.category}
    (P : SelectedLawAlgebraPresentation B W) : Prop :=
  P.presentsRaw ∧ P.presentsSheafified

/--
III.条件4.5: presentation-stable AAT site for the law algebra sheaf.

This is an explicit assumption package: every selected context carries a
presentation and that presentation is stable across the canonical
`O_raw^U -> O_X^U` bridge.
-/
structure PresentationStableAATSite {U : AtomCarrier.{u}}
    {A : ArchitectureObject U} {S : Site.AATSite A}
    {k : Type v} [CommRing k]
    (B : LawAlgebraSheafificationBridge S k) where
  presentation :
    ∀ W : S.category, SelectedLawAlgebraPresentation B W
  stable :
    ∀ W : S.category, PresentationStableAt (presentation W)

namespace PresentationStableAATSite

/-- III.条件4.5: expose the raw-presentation part of stability. -/
theorem presentsRaw {U : AtomCarrier.{u}} {A : ArchitectureObject U}
    {S : Site.AATSite A} {k : Type v} [CommRing k]
    {B : LawAlgebraSheafificationBridge S k}
    (H : PresentationStableAATSite B) (W : S.category) :
    (H.presentation W).presentsRaw :=
  (H.stable W).1

/-- III.条件4.5: expose preservation of selected generators by the canonical map. -/
theorem canonicalPreservesGenerators {U : AtomCarrier.{u}}
    {A : ArchitectureObject U} {S : Site.AATSite A}
    {k : Type v} [CommRing k]
    {B : LawAlgebraSheafificationBridge S k}
    (H : PresentationStableAATSite B) (W : S.category)
    (g : (H.presentation W).Generator) :
    (B.canonicalAt W).right ((H.presentation W).rawGenerator g) =
      (H.presentation W).sheafifiedGenerator g :=
  (H.presentation W).canonical_preserves_generator g

/-- III.条件4.5: expose preservation of selected relations by the canonical map. -/
theorem canonicalPreservesRelations {U : AtomCarrier.{u}}
    {A : ArchitectureObject U} {S : Site.AATSite A}
    {k : Type v} [CommRing k]
    {B : LawAlgebraSheafificationBridge S k}
    (H : PresentationStableAATSite B) (W : S.category)
    (r : (H.presentation W).Relation) :
    (B.canonicalAt W).right ((H.presentation W).rawRelation r) =
      (H.presentation W).sheafifiedRelation r :=
  (H.presentation W).canonical_preserves_relation r

/-- III.条件4.5: expose the sheafified-presentation part of stability. -/
theorem presentsSheafified {U : AtomCarrier.{u}}
    {A : ArchitectureObject U} {S : Site.AATSite A}
    {k : Type v} [CommRing k]
    {B : LawAlgebraSheafificationBridge S k}
    (H : PresentationStableAATSite B) (W : S.category) :
    (H.presentation W).presentsSheafified :=
  (H.stable W).2

end PresentationStableAATSite

/--
III.R3: the Law Algebra Sheaf package used by later witness-ideal and affine
chart layers.

The package ties the R2 raw ambient algebra bridge to the selected
sheafification bridge and records condition 4.5 as an explicit assumption.
-/
structure LawAlgebraSheafPackage {U : AtomCarrier.{u}} {A : ArchitectureObject U}
    (S : Site.AATSite A) (k : Type v) [CommRing k] where
  rawAmbient : RawAmbientAlgebraPresheafBridge S k
  sheafification : LawAlgebraSheafificationBridge S k
  raw_eq : sheafification.raw = rawAmbient.rawPresheaf
  presentationStable : PresentationStableAATSite sheafification

namespace LawAlgebraSheafPackage

/-- III.定義2.1: the sheafified law algebra carried by the package. -/
abbrev OX {U : AtomCarrier.{u}} {A : ArchitectureObject U}
    {S : Site.AATSite A} {k : Type v} [CommRing k]
    (P : LawAlgebraSheafPackage S k) : LawAlgebraSheaf S k :=
  P.sheafification.OX

/-- III.R3: the package uses the R2 raw ambient algebra presheaf as its raw input. -/
theorem raw_eq_rawAmbient {U : AtomCarrier.{u}} {A : ArchitectureObject U}
    {S : Site.AATSite A} {k : Type v} [CommRing k]
    (P : LawAlgebraSheafPackage S k) :
    P.sheafification.raw = P.rawAmbient.rawPresheaf :=
  P.raw_eq

/-- III.条件4.5: the packaged site is presentation-stable. -/
theorem presentationStableAt {U : AtomCarrier.{u}} {A : ArchitectureObject U}
    {S : Site.AATSite A} {k : Type v} [CommRing k]
    (P : LawAlgebraSheafPackage S k) (W : S.category) :
    PresentationStableAt (P.presentationStable.presentation W) :=
  P.presentationStable.stable W

end LawAlgebraSheafPackage

end

end LawAlgebra
end AAT.AG
