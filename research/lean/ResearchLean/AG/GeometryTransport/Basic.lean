import Formal.AG.ReadingFunctoriality.Coefficient
import ResearchLean.AG.AtomFoundation.Categories

/-!
# Geometry-stage transport primitives

This module fixes the typed carrier used by G-108 and the canonical index and
raw-system reindexing operations induced by a G-101 core-package morphism.

## Implementation notes

`GeometryPackage` is an abbreviation for the reviewed `ReadingCore`: the
geometry stage reuses `SelectedGeometryReading`, its generated `AATSite`, the
single commutative coefficient ring, and `RawAmbientRestrictionSystem` rather
than redefining any component type.  Raw reindexing copies the coordinate and
relation presentations along the inverse context functor and performs
coefficient base change before reindexing.  It does not accept a completed raw
comparison as input.
-/

namespace AAT.AG.GeometryTransport

universe u v

open CategoryTheory
open AtomFoundation

/-- The G-108 geometry-stage package, using the existing Formal component types. -/
abbrev GeometryPackage (U : AtomCarrier.{u}) := ReadingCore.{u, v} U

/-- Forward context functor carried by a morphism of arbitrary core packages. -/
abbrev coreContextFunctor {U : AtomCarrier.{u}}
    {P Q : AATCorePackage U} (f : PackageTotalHom P Q) :=
  f.upper.equationTransport.contextEquivalence.functor

/-- Inverse context functor carried by a morphism of arbitrary core packages. -/
abbrev coreContextInverse {U : AtomCarrier.{u}}
    {P Q : AATCorePackage U} (f : PackageTotalHom P Q) :=
  f.upper.equationTransport.contextEquivalence.inverse

/-- The forward context functor carried by a core-package morphism. -/
abbrev contextFunctor {U : AtomCarrier.{u}}
    {G H : GeometryPackage.{u, v} U}
    (f : PackageTotalHom G.core H.core) :=
  coreContextFunctor f

/-- The inverse context functor carried by a core-package morphism. -/
abbrev contextInverse {U : AtomCarrier.{u}}
    {G H : GeometryPackage.{u, v} U}
    (f : PackageTotalHom G.core H.core) :=
  coreContextInverse f

/-- Forward image of a context object. -/
abbrev contextForward {U : AtomCarrier.{u}}
    {G H : GeometryPackage.{u, v} U}
    (f : PackageTotalHom G.core H.core)
    (W : G.site.category) : H.site.category :=
  (contextFunctor f).obj W

/-- Inverse image of a context object. -/
abbrev contextBackward {U : AtomCarrier.{u}}
    {G H : GeometryPackage.{u, v} U}
    (f : PackageTotalHom G.core H.core)
    (W : H.site.category) : G.site.category :=
  (contextInverse f).obj W

/-- Forward context images respect composition of core-package morphisms. -/
@[simp] theorem contextForward_comp {U : AtomCarrier.{u}}
    {G H K : GeometryPackage.{u, v} U}
    (f : PackageTotalHom G.core H.core)
    (g : PackageTotalHom H.core K.core) (W : G.site.category) :
    contextForward (PackageTotalHom.comp f g) W =
      contextForward g (contextForward f W) :=
  rfl

/-- Inverse context images respect composition of core-package morphisms. -/
@[simp] theorem contextBackward_comp {U : AtomCarrier.{u}}
    {G H K : GeometryPackage.{u, v} U}
    (f : PackageTotalHom G.core H.core)
    (g : PackageTotalHom H.core K.core) (W : K.site.category) :
    contextBackward (PackageTotalHom.comp f g) W =
      contextBackward f (contextBackward g W) :=
  rfl

/-- The required-coordinate map fixed by the G-108 geometry-hom contract. -/
def requiredCoordinateMap {U : AtomCarrier.{u}}
    {G H : GeometryPackage.{u, v} U}
    (f : PackageTotalHom G.core H.core) :
    G.site.equationSystem.RequiredCoordinate →
      H.site.equationSystem.RequiredCoordinate :=
  fun coordinate =>
    (⟨f.upper.equationMap coordinate.1.1,
        (f.upper.required_iff coordinate.1.1).mp coordinate.1.2⟩,
      f.upper.atomEquiv coordinate.2)

/-- The full equation/Atom coordinate map fixed by the hom contract. -/
def equationCoordinateMap {U : AtomCarrier.{u}}
    {G H : GeometryPackage.{u, v} U}
    (f : PackageTotalHom G.core H.core) :
    G.site.equationSystem.Coordinate →
      H.site.equationSystem.Coordinate :=
  fun coordinate =>
    (f.upper.equationEquiv coordinate.1, f.upper.atomEquiv coordinate.2)

/-- Forward image of a raw architecture context. -/
def contextMap {U : AtomCarrier.{u}}
    {G H : GeometryPackage.{u, v} U}
    (f : PackageTotalHom G.core H.core)
    (W : Site.ArchCtx G.core.object) : Site.ArchCtx H.core.object :=
  (contextForward f ⟨W⟩).ctx

/-- Forward image of a raw context for arbitrary core packages. -/
def coreContextMap {U : AtomCarrier.{u}}
    {P Q : AATCorePackage U} (f : PackageTotalHom P Q)
    (W : Site.ArchCtx P.object) : Site.ArchCtx Q.object :=
  ((coreContextFunctor f).obj ⟨W⟩).ctx

/-- Inverse image of a raw architecture context. -/
def contextBackwardMap {U : AtomCarrier.{u}}
    {G H : GeometryPackage.{u, v} U}
    (f : PackageTotalHom G.core H.core)
    (W : Site.ArchCtx H.core.object) : Site.ArchCtx G.core.object :=
  (contextBackward f ⟨W⟩).ctx

/-- Inverse image of a raw context for arbitrary core packages. -/
def coreContextBackwardMap {U : AtomCarrier.{u}}
    {P Q : AATCorePackage U} (f : PackageTotalHom P Q)
    (W : Site.ArchCtx Q.object) : Site.ArchCtx P.object :=
  ((coreContextInverse f).obj ⟨W⟩).ctx

/-- Equality of context objects induces an equivalence of local support carriers. -/
def supportEquivOfContextEq {U : AtomCarrier.{u}} {P : AATCorePackage U}
    {W V : Site.ContextCategoryObject P.contextPreorder} (h : W = V) :
    W.ctx.Support ≃ V.ctx.Support :=
  Equiv.cast (congrArg (fun X => X.ctx.Support) h)

/-- Equality of context objects induces an equivalence of local axis carriers. -/
def axisEquivOfContextEq {U : AtomCarrier.{u}} {P : AATCorePackage U}
    {W V : Site.ContextCategoryObject P.contextPreorder} (h : W = V) :
    W.ctx.Axis ≃ V.ctx.Axis :=
  Equiv.cast (congrArg (fun X => X.ctx.Axis) h)

/-- Equality of context objects induces an equivalence of local observable carriers. -/
def observableEquivOfContextEq {U : AtomCarrier.{u}} {P : AATCorePackage U}
    {W V : Site.ContextCategoryObject P.contextPreorder} (h : W = V) :
    W.ctx.Observable ≃ V.ctx.Observable :=
  Equiv.cast (congrArg (fun X => X.ctx.Observable) h)

/-- A context-indexed support comparison commutes with equality transport. -/
theorem supportEquivOfContextEq_family {U : AtomCarrier.{u}}
    {P Q : AATCorePackage U}
    (F : Site.ContextCategoryObject P.contextPreorder →
      Site.ContextCategoryObject Q.contextPreorder)
    (family : ∀ W, W.ctx.Support → (F W).ctx.Support)
    {W V : Site.ContextCategoryObject P.contextPreorder} (h : W = V)
    (support : W.ctx.Support) :
    supportEquivOfContextEq (congrArg F h) (family W support) =
      family V (supportEquivOfContextEq h support) := by
  cases h
  rfl

/-- A context-indexed axis comparison commutes with equality transport. -/
theorem axisEquivOfContextEq_family {U : AtomCarrier.{u}}
    {P Q : AATCorePackage U}
    (F : Site.ContextCategoryObject P.contextPreorder →
      Site.ContextCategoryObject Q.contextPreorder)
    (family : ∀ W, W.ctx.Axis → (F W).ctx.Axis)
    {W V : Site.ContextCategoryObject P.contextPreorder} (h : W = V)
    (axis : W.ctx.Axis) :
    axisEquivOfContextEq (congrArg F h) (family W axis) =
      family V (axisEquivOfContextEq h axis) := by
  cases h
  rfl

/-- A context-indexed observable comparison commutes with equality transport. -/
theorem observableEquivOfContextEq_family {U : AtomCarrier.{u}}
    {P Q : AATCorePackage U}
    (F : Site.ContextCategoryObject P.contextPreorder →
      Site.ContextCategoryObject Q.contextPreorder)
    (family : ∀ W, W.ctx.Observable → (F W).ctx.Observable)
    {W V : Site.ContextCategoryObject P.contextPreorder} (h : W = V)
    (observable : W.ctx.Observable) :
    observableEquivOfContextEq (congrArg F h) (family W observable) =
      family V (observableEquivOfContextEq h observable) := by
  cases h
  rfl

/-- Support readability is invariant under context equality. -/
theorem supportEquivOfContextEq_reads_iff {U : AtomCarrier.{u}}
    {P : AATCorePackage U}
    {W V : Site.ContextCategoryObject P.contextPreorder} (h : W = V)
    (support : W.ctx.Support) (atom : U.Atom) :
    V.ctx.minimal.supportReads (supportEquivOfContextEq h support) atom ↔
      W.ctx.minimal.supportReads support atom := by
  cases h
  rfl

/-- Axis readability is invariant under context equality. -/
theorem axisEquivOfContextEq_reads_iff {U : AtomCarrier.{u}}
    {P : AATCorePackage U}
    {W V : Site.ContextCategoryObject P.contextPreorder} (h : W = V)
    (axis : W.ctx.Axis) :
    V.ctx.minimal.axisReads (axisEquivOfContextEq h axis) ↔
      W.ctx.minimal.axisReads axis := by
  cases h
  rfl

/-- Observable readability is invariant under context equality. -/
theorem observableEquivOfContextEq_reads_iff {U : AtomCarrier.{u}}
    {P : AATCorePackage U}
    {W V : Site.ContextCategoryObject P.contextPreorder} (h : W = V)
    (observable : W.ctx.Observable) :
    V.ctx.minimal.observableReads (observableEquivOfContextEq h observable) ↔
      W.ctx.minimal.observableReads observable := by
  cases h
  rfl

/-- Support maps are conjugated by equality of their context endpoints. -/
theorem supportEquivOfContextEq_naturality {U : AtomCarrier.{u}}
    {P : AATCorePackage U}
    {W V W' V' : Site.ContextCategoryObject P.contextPreorder}
    (hW : W' = W) (hV : V' = V) (w' : W' ⟶ V') (w : W ⟶ V)
    (support : W'.ctx.Support) :
    (P.contextPreorder.morphism (leOfHom w)).supportMap
        (supportEquivOfContextEq hW support) =
      supportEquivOfContextEq hV
        ((P.contextPreorder.morphism (leOfHom w')).supportMap support) := by
  cases hW
  cases hV
  have hw : w' = w := Subsingleton.elim _ _
  cases hw
  rfl

/-- Axis maps are conjugated by equality of their context endpoints. -/
theorem axisEquivOfContextEq_naturality {U : AtomCarrier.{u}}
    {P : AATCorePackage U}
    {W V W' V' : Site.ContextCategoryObject P.contextPreorder}
    (hW : W' = W) (hV : V' = V) (w' : W' ⟶ V') (w : W ⟶ V)
    (axis : W'.ctx.Axis) :
    (P.contextPreorder.morphism (leOfHom w)).axisMap
        (axisEquivOfContextEq hW axis) =
      axisEquivOfContextEq hV
        ((P.contextPreorder.morphism (leOfHom w')).axisMap axis) := by
  cases hW
  cases hV
  have hw : w' = w := Subsingleton.elim _ _
  cases hw
  rfl

/-- Observable restrictions are conjugated by equality of their endpoints. -/
theorem observableEquivOfContextEq_naturality {U : AtomCarrier.{u}}
    {P : AATCorePackage U}
    {W V W' V' : Site.ContextCategoryObject P.contextPreorder}
    (hW : W' = W) (hV : V' = V) (w' : W' ⟶ V') (w : W ⟶ V)
    (observable : V'.ctx.Observable) :
    (P.contextPreorder.morphism (leOfHom w)).observableRestrict
        (observableEquivOfContextEq hV observable) =
      observableEquivOfContextEq hW
        ((P.contextPreorder.morphism (leOfHom w')).observableRestrict observable) := by
  cases hW
  cases hV
  have hw : w' = w := Subsingleton.elim _ _
  cases hw
  rfl

/-- Copy a coordinate family across a change of its phantom context index. -/
def copyCoordinateFamily {U : AtomCarrier.{u}}
    {A B : ArchitectureObject U}
    {W : Site.ArchitectureContext A} {V : Site.ArchitectureContext B}
    (F : LawAlgebra.CoordinateFamily W) : LawAlgebra.CoordinateFamily V where
  Coord := F.Coord
  label := F.label
  LocalData := F.LocalData

/-- Copy a structural relation family across the copied coordinate family. -/
def copyRelationFamily {U : AtomCarrier.{u}}
    {A B : ArchitectureObject U}
    {W : Site.ArchitectureContext A} {V : Site.ArchitectureContext B}
    {k : Type v} [CommRing k]
    {F : LawAlgebra.CoordinateFamily W}
    (R : LawAlgebra.StructuralRelationFamily F k) :
    LawAlgebra.StructuralRelationFamily (copyCoordinateFamily (V := V) F) k where
  Relation := R.Relation
  polynomial := R.polynomial

/--
Reindex a raw restriction system along the inverse context functor of a core
morphism.  Coefficient change is deliberately separate and is applied before
this operation by `rawTransport`.
-/
noncomputable def rawReindexCore {U : AtomCarrier.{u}}
    {P Q : AATCorePackage U}
    (sourceGeometry : Site.SelectedGeometryReading P)
    (targetGeometry : Site.SelectedGeometryReading Q)
    {k : Type v} [CommRing k]
    (f : PackageTotalHom P Q)
    (raw : LawAlgebra.RawAmbientRestrictionSystem sourceGeometry.toAATSite k) :
    LawAlgebra.RawAmbientRestrictionSystem targetGeometry.toAATSite k where
  coordFamily W :=
    copyCoordinateFamily (V := W.ctx)
      (raw.coordFamily ((coreContextInverse f).obj W))
  relationFamily W :=
    copyRelationFamily (V := W.ctx)
      (raw.relationFamily ((coreContextInverse f).obj W))
  restrictionStable {X Y} h := by
    let source := raw.restrictionStable ((coreContextInverse f).map h)
    exact {
      restriction := {
        variableImage := source.restriction.variableImage
      }
      maps_JStruct := source.maps_JStruct
    }
  identity_polynomialMap X := by
    have hmap : (coreContextInverse f).map (𝟙 X) =
        𝟙 ((coreContextInverse f).obj X) := by
      simp
    cases hmap
    exact raw.identity_polynomialMap ((coreContextInverse f).obj X)
  composition_polynomialMap h k := by
    have hmap : (coreContextInverse f).map (h ≫ k) =
        (coreContextInverse f).map h ≫ (coreContextInverse f).map k := by
      simp
    cases hmap
    exact raw.composition_polynomialMap
      ((coreContextInverse f).map h) ((coreContextInverse f).map k)

/-- Reindex a raw system between two geometry packages. -/
noncomputable def rawReindex {U : AtomCarrier.{u}}
    {G H : GeometryPackage.{u, v} U} {k : Type v} [CommRing k]
    (f : PackageTotalHom G.core H.core)
    (raw : LawAlgebra.RawAmbientRestrictionSystem G.site k) :
    LawAlgebra.RawAmbientRestrictionSystem H.site k :=
  rawReindexCore G.geometry H.geometry f raw

/-- Base-change coefficients and then reindex the raw system along the core map. -/
noncomputable def rawTransport {U : AtomCarrier.{u}}
    {G H : GeometryPackage.{u, v} U}
    (f : PackageTotalHom G.core H.core)
    (coeff : G.Coefficient →+* H.Coefficient) :
    LawAlgebra.RawAmbientRestrictionSystem H.site H.Coefficient :=
  rawReindex f (G.raw.baseChange coeff)

/-- Raw reindexing along the identity core morphism is the identity. -/
@[simp] theorem rawReindex_id {U : AtomCarrier.{u}}
    (G : GeometryPackage.{u, v} U) {k : Type v} [CommRing k]
    (raw : LawAlgebra.RawAmbientRestrictionSystem G.site k) :
    rawReindex (G := G) (H := G) (PackageTotalHom.id G.core) raw = raw := by
  apply LawAlgebra.RawAmbientRestrictionSystem.ext
  · rfl
  · rfl
  · rfl

/-- Raw reindexing respects composition of core-package morphisms. -/
theorem rawReindex_comp {U : AtomCarrier.{u}}
    {G H K : GeometryPackage.{u, v} U} {k : Type v} [CommRing k]
    (f : PackageTotalHom G.core H.core)
    (g : PackageTotalHom H.core K.core)
    (raw : LawAlgebra.RawAmbientRestrictionSystem G.site k) :
    rawReindex (PackageTotalHom.comp f g) raw =
      rawReindex g (rawReindex f raw) := by
  apply LawAlgebra.RawAmbientRestrictionSystem.ext
  · rfl
  · rfl
  · rfl

/-- Coefficient base change commutes with inverse-context reindexing. -/
theorem rawReindex_baseChange {U : AtomCarrier.{u}}
    {G H : GeometryPackage.{u, v} U}
    {k k' : Type v} [CommRing k] [CommRing k']
    (f : PackageTotalHom G.core H.core)
    (raw : LawAlgebra.RawAmbientRestrictionSystem G.site k)
    (coeff : k →+* k') :
    (rawReindex f raw).baseChange coeff =
      rawReindex f (raw.baseChange coeff) := by
  apply LawAlgebra.RawAmbientRestrictionSystem.ext
  · rfl
  · rfl
  · rfl

/-- The raw component of the identity geometry transport is unchanged. -/
@[simp] theorem rawTransport_id {U : AtomCarrier.{u}}
    (G : GeometryPackage.{u, v} U) :
    rawTransport (G := G) (H := G) (PackageTotalHom.id G.core)
      (RingHom.id G.Coefficient) = G.raw := by
  simp [rawTransport]

/-- Raw transport performs coefficient composition and context composition coherently. -/
theorem rawTransport_comp {U : AtomCarrier.{u}}
    {G H K : GeometryPackage.{u, v} U}
    (f : PackageTotalHom G.core H.core)
    (g : PackageTotalHom H.core K.core)
    (coeff₁ : G.Coefficient →+* H.Coefficient)
    (coeff₂ : H.Coefficient →+* K.Coefficient) :
    rawTransport (PackageTotalHom.comp f g) (coeff₂.comp coeff₁) =
      rawReindex g ((rawTransport f coeff₁).baseChange coeff₂) := by
  rw [rawTransport, rawTransport, LawAlgebra.RawAmbientRestrictionSystem.baseChange_comp]
  rw [rawReindex_comp, rawReindex_baseChange]

end AAT.AG.GeometryTransport

#assert_standard_axioms_only AAT.AG.GeometryTransport
