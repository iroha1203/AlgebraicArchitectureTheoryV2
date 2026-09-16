import ResearchLean.AG.RealizationReconstruction.CSAATGenuineIsoExactData
import ResearchLean.AG.RealizationReconstruction.LensFinitePresentation
import ResearchLean.AG.GeometryTransport.Basic
import Formal.Util.AssertStandardAxioms

/-!
# Isomorphism-invariant raw coordinates for CS reading cores

The strict `GeometryTotalHom.raw_eq` contract compares raw systems by equality,
not merely by an equivalence of their coordinate types.  This module begins a
fixed-target-preserving solution: raw coordinates are indexed by canonical
finite-complement normal-form carriers whose complement cardinal is determined
by the original CS input.  The primitive `View`, total carrier, and resulting
Law-coordinate family may all be infinite.  The original complete
Law-index/Atom coordinate family remains
equivalent to the canonical one; it is not replaced by a selected subset.

The generic constant-coordinate raw system below has empty additional
structural relations and identity restriction maps.  Its strict reindex law is
proved for every package hom.  The lens specialization then proves that a
genuine CS isomorphism preserves the finite reference-fiber cardinal, so the
canonical coordinate types agree literally after eliminating that equality.

This is the raw-coordinate layer only.  It does not yet construct a
`SignedExactCoreReadingHom`, `GeometryTotalHom`, or readback.
-/

namespace AAT.AG.RealizationReconstruction

open CategoryTheory
open AtomFoundation
open GeometryTransport

universe u

/-! ## A raw system with one fixed complete coordinate type -/

/-- A fixed coordinate type, retained unchanged at every selected context. -/
def constantRawCoordinateFamily {U : AtomCarrier.{u}}
    {A : ArchitectureObject U} (S : Site.AATSite A) (Coord : Type u)
    (W : S.category) : LawAlgebra.CoordinateFamily W.ctx where
  Coord := Coord
  label _ := .semantic
  LocalData _ := PUnit

/-- No additional structural equation is imposed on the fixed coordinates. -/
noncomputable def constantEmptyStructuralRelations {U : AtomCarrier.{u}}
    {A : ArchitectureObject U} (S : Site.AATSite A) (Coord : Type u)
    (W : S.category) :
    LawAlgebra.StructuralRelationFamily (constantRawCoordinateFamily S Coord W) Int where
  Relation := PEmpty
  polynomial relation := PEmpty.elim relation

/-- Restriction fixes every coordinate variable. -/
noncomputable def constantRawRestriction {U : AtomCarrier.{u}}
    {A : ArchitectureObject U} (S : Site.AATSite A) (Coord : Type u)
    {W V : S.category} (f : W ⟶ V) :
    LawAlgebra.TypedCoordinateRestriction
      (constantRawCoordinateFamily S Coord W)
      (constantRawCoordinateFamily S Coord V) Int
      (S.contextPreorder.morphism (leOfHom f)) where
  variableImage coordinate := MvPolynomial.X coordinate

/-- The fixed-coordinate restriction induces the identity polynomial map. -/
theorem constantRawRestriction_polynomialMap {U : AtomCarrier.{u}}
    {A : ArchitectureObject U} (S : Site.AATSite A) (Coord : Type u)
    {W V : S.category} (f : W ⟶ V) :
    (constantRawRestriction S Coord f).polynomialMap =
      RingHom.id (LawAlgebra.FreeTypedCommAlg
        (constantRawCoordinateFamily S Coord W) Int) := by
  apply MvPolynomial.ringHom_ext
  · intro value
    exact LawAlgebra.TypedCoordinateRestriction.polynomialMap_C _ _
  · intro coordinate
    rw [LawAlgebra.TypedCoordinateRestriction.polynomialMap_X]
    rfl

/-- Empty structural relations are stable under fixed-coordinate restriction. -/
noncomputable def constantRawRestrictionStable {U : AtomCarrier.{u}}
    {A : ArchitectureObject U} (S : Site.AATSite A) (Coord : Type u)
    {W V : S.category} (f : W ⟶ V) :
    LawAlgebra.RestrictionStableStructuralRelations
      (constantEmptyStructuralRelations S Coord W)
      (constantEmptyStructuralRelations S Coord V)
      (S.contextPreorder.morphism (leOfHom f)) where
  restriction := constantRawRestriction S Coord f
  maps_JStruct := by
    intro polynomial hpolynomial
    rw [constantRawRestriction_polynomialMap S Coord f]
    exact hpolynomial

/-- The coherent raw system on a site with one caller-chosen complete
coordinate type, empty extra relations, and identity restrictions. -/
noncomputable def constantRawSystemOn {U : AtomCarrier.{u}}
    {A : ArchitectureObject U} (S : Site.AATSite A) (Coord : Type u) :
    LawAlgebra.RawAmbientRestrictionSystem S Int where
  coordFamily := constantRawCoordinateFamily S Coord
  relationFamily := constantEmptyStructuralRelations S Coord
  restrictionStable := constantRawRestrictionStable S Coord
  identity_polynomialMap W := constantRawRestriction_polynomialMap S Coord (𝟙 W)
  composition_polynomialMap f g := by
    change (constantRawRestriction S Coord (f ≫ g)).polynomialMap =
      (constantRawRestriction S Coord f).polynomialMap.comp
        (constantRawRestriction S Coord g).polynomialMap
    rw [constantRawRestriction_polynomialMap S Coord (f ≫ g),
      constantRawRestriction_polynomialMap S Coord f,
      constantRawRestriction_polynomialMap S Coord g]
    exact (RingHom.id_comp _).symm

/-- A fixed-coordinate raw system satisfies strict raw reindex equality along
every core-package morphism. -/
theorem constantRawSystemOn_reindex {U : AtomCarrier.{u}}
    {G H : GeometryPackage.{u, 0} U}
    (f : PackageTotalHom G.core H.core) (Coord : Type u) :
    constantRawSystemOn H.site Coord =
      rawReindex f (constantRawSystemOn G.site Coord) := by
  apply LawAlgebra.RawAmbientRestrictionSystem.ext
  · rfl
  · rfl
  · rfl

/-! ## Lens canonical parameter-relative coordinates -/

/-- The canonical finite-complement carrier decoded from the cardinality of
the original lens reference fiber.  Its `View` factor may be infinite. -/
abbrev LensCanonicalCarrier (input : LensFamilyInput.{u})
    (X : LensRealization input.View input.reference) : Type u :=
  ((LensRealization.lensDecoder input.View input.reference).obj
    (LensRealization.presentationOf X)).Carrier

/-- Every raw Law index of the canonical finite-complement lens, paired with
every original AAT Atom.  This coordinate type need not be finite. -/
abbrev LensCanonicalRawCoordinate (input : LensFamilyInput.{u})
    (X : LensRealization input.View input.reference) : Type (u + 1) :=
  ULift.{u + 1, u} (LensLawIndex input.View (LensCanonicalCarrier input X)) ×
    LensAATAtom input

/-- The original complete Law-index/Atom family is equivalent to the canonical
parameter-relative finitely presented coordinate family through the already
constructed normal-form isomorphism. -/
noncomputable def lensCanonicalRawCoordinateEquiv (input : LensFamilyInput.{u})
    (X : LensRealization input.View input.reference) :
    (ULift.{u + 1, u} (LensLawIndex input.View X.Carrier) × LensAATAtom input) ≃
      LensCanonicalRawCoordinate input X :=
  lensIsoLawCoordinateIndexEquiv (LensRealization.normalFormIso X).symm

/-- The canonical coordinate image of every original Law-index/Atom pair is
the index transported by the normal-form isomorphism, with the Atom unchanged. -/
@[simp] theorem lensCanonicalRawCoordinateEquiv_apply
    (input : LensFamilyInput.{u})
    (X : LensRealization input.View input.reference)
    (index : LensLawIndex input.View X.Carrier) (atom : LensAATAtom input) :
    lensCanonicalRawCoordinateEquiv input X (ULift.up index, atom) =
      (ULift.up (lensIsoLawIndexEquiv
        (LensRealization.normalFormIso X).symm index), atom) :=
  rfl

/-- A genuine lens isomorphism restricts to an equivalence of the complete
finite reference fibers. -/
def lensIsoFiberEquiv {input : LensFamilyInput.{u}}
    {X Y : LensRealization input.View input.reference} (e : X ≅ Y) :
    X.Fiber ≃ Y.Fiber where
  toFun := LensRealization.res e.hom
  invFun := LensRealization.res e.inv
  left_inv state := by
    apply Subtype.ext
    have h := congrArg (fun f : X ⟶ X => f.toFun state.1) e.hom_inv_id
    exact h
  right_inv state := by
    apply Subtype.ext
    have h := congrArg (fun f : Y ⟶ Y => f.toFun state.1) e.inv_hom_id
    exact h

/-- Isomorphic lenses have exactly the same canonical presentation cardinal. -/
theorem lensIsoPresentationCard_eq {input : LensFamilyInput.{u}}
    {X Y : LensRealization input.View input.reference} (e : X ≅ Y) :
    (LensRealization.presentationOf X).card =
      (LensRealization.presentationOf Y).card := by
  unfold LensRealization.presentationOf
  letI := Fintype.ofFinite X.Fiber
  letI := Fintype.ofFinite Y.Fiber
  exact Fintype.card_congr (lensIsoFiberEquiv e)

/-- After eliminating the cardinal equality supplied by a genuine lens
isomorphism, the canonical raw coordinate types are literally identical. -/
theorem lensIsoCanonicalRawCoordinate_eq {input : LensFamilyInput.{u}}
    {X Y : LensRealization input.View input.reference} (e : X ≅ Y) :
    LensCanonicalRawCoordinate input X = LensCanonicalRawCoordinate input Y := by
  have hp : LensRealization.presentationOf X =
      LensRealization.presentationOf Y := by
    apply LensPresentation.ext
    exact lensIsoPresentationCard_eq e
  unfold LensCanonicalRawCoordinate LensCanonicalCarrier
  rw [hp]

/-- The source-generated lens core and geometry equipped with the canonical
finite-complement raw presentation.  Only the raw presentation changes; core
and geometry remain exactly those constructed from the original CS source. -/
noncomputable def lensAATCanonicalRawReadingCore (input : LensFamilyInput.{u})
    (X : LensRealization input.View input.reference) :
    ReadingCore (lensAATCarrier input) where
  core := lensAATCorePackage input X
  geometry := lensAATSelectedGeometryReading input X
  Coefficient := Int
  coefficientCommRing := inferInstance
  raw := constantRawSystemOn (lensAATSelectedGeometryReading input X).toAATSite
    (LensCanonicalRawCoordinate input X)

/-- A genuine lens isomorphism makes the canonical raw systems satisfy the
literal reindex equality required by `GeomReadHom.raw_eq`, once a core package
hom has been constructed.  No equality of the original carrier types is
assumed. -/
theorem lensAATCanonicalRawReadingCore_reindex
    {input : LensFamilyInput.{u}}
    {X Y : LensRealization input.View input.reference} (e : X ≅ Y)
    (f : PackageTotalHom
      (lensAATCanonicalRawReadingCore input X).core
      (lensAATCanonicalRawReadingCore input Y).core) :
    (lensAATCanonicalRawReadingCore input Y).raw =
      rawReindex f (lensAATCanonicalRawReadingCore input X).raw := by
  have hcoord := lensIsoCanonicalRawCoordinate_eq e
  unfold lensAATCanonicalRawReadingCore
  rw [← hcoord]
  exact constantRawSystemOn_reindex f (LensCanonicalRawCoordinate input X)

#assert_standard_axioms_only AAT.AG.RealizationReconstruction

end AAT.AG.RealizationReconstruction
