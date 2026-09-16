import ResearchLean.AG.RealizationReconstruction.CSAATForwardMorphisms
import Formal.AG.LawAlgebra.StructureSheaf
import Formal.AG.Site.Geometry
import Formal.Util.AssertStandardAxioms

/-!
# Geometry endpoint scaffolds for the two CS semantics

This module constructs a morphism-independent endpoint scaffold toward the
complete geometry required by G-123(E).  Each independently given lens or
protocol realization produces an actual `AATSite` on its actual Law object.
The site marks the fixed Atom vocabulary and Law-coordinate roles as required,
uses the canonical product overlap, and carries a coherent raw restriction
system over `Int` whose pre-quotient variables keep every Law index and Atom.

The raw structural-relation family is empty on purpose: in the Formal AAT
contract, Law witness equations remain outside the raw structural quotient.
Thus the pre-quotient raw presentation is the free polynomial algebra on all
Law/Atom coordinates.  This file does not yet identify the actual quotient
with that presentation.

This file constructs endpoint geometry independently of any morphism.  It does
not use `GeometryTotalHom`: that exact-change API requires an equivalence of
equation indices and would exclude the arbitrary noninjective CS morphisms
fixed by n1015.  Actual admissible covers, componentwise
Support/Axis/Observable readings, ReadingCore provenance, and one-way
morphism transport remain obligations.
-/

namespace AAT.AG.RealizationReconstruction

open CategoryTheory

universe u

/-! ## Generic Law endpoint scaffold -/

/-- Every primitive Atom is retained as a distinct signature axis. -/
def completeLawSignature (U : AtomCarrier.{u}) : ArchitectureSignature U where
  Axis := U.Atom
  Coordinate _ := PUnit
  selected _ := True
  coordinate _ _ := PUnit.unit

/-- Required-role predicates for the complete Atom vocabulary and every Law
coordinate.  These predicates do not by themselves construct an
`AATCoverageFamily` or an admissible cover. -/
def completeLawCoverageRequirements {U : AtomCarrier.{u}}
    {A : ArchitectureObject U} {C : Site.ContextPreorderCategory A}
    (E : ArchitecturalEquationSystem C) :
    Site.CoverageRequirements A E (completeLawSignature U) where
  requiredSupport _ := True
  requiredEquationCoordinate _ := True
  selectedViolationWitness _ := True
  requiredAxis _ := True
  supportVisibleOn W atom := ∃ support, W.minimal.supportReads support atom
  equationCoordinateVisibleOn _ _ := True
  violationWitnessVisibleOn _ _ := True
  axisReadableOn W _ := ∃ axis, W.minimal.axisReads axis
  boundaryVisibleOn _ _ := True

/-- Every Atom is marked as a required support role. -/
@[simp] theorem completeLawCoverageRequirements_requiredSupport
    {U : AtomCarrier.{u}} {A : ArchitectureObject U}
    {C : Site.ContextPreorderCategory A} (E : ArchitecturalEquationSystem C)
    (atom : U.Atom) :
    (completeLawCoverageRequirements E).requiredSupport atom :=
  trivial

/-- Every required Law coordinate is marked as required. -/
@[simp] theorem completeLawCoverageRequirements_requiredCoordinate
    {U : AtomCarrier.{u}} {A : ArchitectureObject U}
    {C : Site.ContextPreorderCategory A} (E : ArchitecturalEquationSystem C)
    (coordinate : E.RequiredCoordinate) :
    (completeLawCoverageRequirements E).requiredEquationCoordinate coordinate :=
  trivial

/-- Every Law/Atom violation coordinate is marked as selected. -/
@[simp] theorem completeLawCoverageRequirements_selectedViolation
    {U : AtomCarrier.{u}} {A : ArchitectureObject U}
    {C : Site.ContextPreorderCategory A} (E : ArchitecturalEquationSystem C)
    (coordinate : E.Coordinate) :
    (completeLawCoverageRequirements E).selectedViolationWitness coordinate :=
  trivial

/-- Every primitive Atom axis is marked as required by the signature. -/
@[simp] theorem completeLawCoverageRequirements_requiredAxis
    {U : AtomCarrier.{u}} {A : ArchitectureObject U}
    {C : Site.ContextPreorderCategory A} (E : ArchitecturalEquationSystem C)
    (axis : U.Atom) :
    (completeLawCoverageRequirements E).requiredAxis axis :=
  trivial

/-- The canonical product overlap on the full restriction-context preorder. -/
noncomputable def completeLawOverlap {U : AtomCarrier.{u}}
    (A : ArchitectureObject U) :
    Site.ContextOverlapPullback (Site.contextMorphismPreorderCategory A) :=
  Site.meetOverlapPullback (Site.contextMorphismPreorderCategory A)
    Site.productContextFiniteMeet

/-- The AAT-site scaffold attached directly to an actual Law object and its
object-dependent equation system.  Its requirements are selectors, not an
existence proof of admissible covers. -/
noncomputable def completeLawSite {U : AtomCarrier.{u}}
    (A : ArchitectureObject U)
    (E : ArchitecturalEquationSystem
      (Site.contextMorphismPreorderCategory A)) : Site.AATSite A where
  contextPreorder := Site.contextMorphismPreorderCategory A
  equationSystem := E
  signature := completeLawSignature U
  requirements := completeLawCoverageRequirements E
  overlap := completeLawOverlap A

/-- Every Law-index/Atom coordinate remains a distinct raw semantic
coordinate at every context. -/
def completeLawRawCoordinateFamily {U : AtomCarrier.{u}}
    {A : ArchitectureObject U}
    (E : ArchitecturalEquationSystem
      (Site.contextMorphismPreorderCategory A))
    (W : (completeLawSite A E).category) :
    LawAlgebra.CoordinateFamily W.ctx where
  Coord := E.Coordinate
  label _ := .semantic
  LocalData _ := PUnit

/-- There are no additional structural equations at the raw stage.  Law
witness equations remain represented by `E`, outside this ambient quotient. -/
noncomputable def completeLawRawRelationFamily {U : AtomCarrier.{u}}
    {A : ArchitectureObject U}
    (E : ArchitecturalEquationSystem
      (Site.contextMorphismPreorderCategory A))
    (W : (completeLawSite A E).category) :
    LawAlgebra.StructuralRelationFamily
      (completeLawRawCoordinateFamily E W) Int where
  Relation := PEmpty
  polynomial relation := PEmpty.elim relation

/-- Raw restriction retains every global Law coordinate unchanged. -/
noncomputable def completeLawRawCoordinateRestriction {U : AtomCarrier.{u}}
    {A : ArchitectureObject U}
    (E : ArchitecturalEquationSystem
      (Site.contextMorphismPreorderCategory A))
    {W V : (completeLawSite A E).category} (f : W ⟶ V) :
    LawAlgebra.TypedCoordinateRestriction
      (completeLawRawCoordinateFamily E W)
      (completeLawRawCoordinateFamily E V) Int
      ((completeLawSite A E).contextPreorder.morphism (leOfHom f)) where
  variableImage coordinate := MvPolynomial.X coordinate

/-- The raw coordinate restriction is the identity polynomial homomorphism. -/
theorem completeLawRawCoordinateRestriction_polynomialMap
    {U : AtomCarrier.{u}} {A : ArchitectureObject U}
    (E : ArchitecturalEquationSystem
      (Site.contextMorphismPreorderCategory A))
    {W V : (completeLawSite A E).category} (f : W ⟶ V) :
    (completeLawRawCoordinateRestriction E f).polynomialMap =
      RingHom.id (LawAlgebra.FreeTypedCommAlg
        (completeLawRawCoordinateFamily E W) Int) := by
  apply MvPolynomial.ringHom_ext
  · intro value
    exact LawAlgebra.TypedCoordinateRestriction.polynomialMap_C _ _
  · intro coordinate
    rw [LawAlgebra.TypedCoordinateRestriction.polynomialMap_X]
    rfl

/-- Empty structural relations are stable under the coordinate-preserving raw
restriction. -/
noncomputable def completeLawRawRestrictionStable {U : AtomCarrier.{u}}
    {A : ArchitectureObject U}
    (E : ArchitecturalEquationSystem
      (Site.contextMorphismPreorderCategory A))
    {W V : (completeLawSite A E).category} (f : W ⟶ V) :
    LawAlgebra.RestrictionStableStructuralRelations
      (completeLawRawRelationFamily E W)
      (completeLawRawRelationFamily E V)
      ((completeLawSite A E).contextPreorder.morphism (leOfHom f)) where
  restriction := completeLawRawCoordinateRestriction E f
  maps_JStruct := by
    intro polynomial hpolynomial
    rw [completeLawRawCoordinateRestriction_polynomialMap E f]
    exact hpolynomial

/-- Coherent raw ambient restriction data retaining all Law/Atom variables. -/
noncomputable def completeLawRawSystem {U : AtomCarrier.{u}}
    {A : ArchitectureObject U}
    (E : ArchitecturalEquationSystem
      (Site.contextMorphismPreorderCategory A)) :
    LawAlgebra.RawAmbientRestrictionSystem (completeLawSite A E) Int where
  coordFamily := completeLawRawCoordinateFamily E
  relationFamily := completeLawRawRelationFamily E
  restrictionStable := completeLawRawRestrictionStable E
  identity_polynomialMap W :=
    completeLawRawCoordinateRestriction_polynomialMap E (𝟙 W)
  composition_polynomialMap f g := by
    change (completeLawRawCoordinateRestriction E (f ≫ g)).polynomialMap =
      (completeLawRawCoordinateRestriction E f).polynomialMap.comp
        (completeLawRawCoordinateRestriction E g).polynomialMap
    rw [completeLawRawCoordinateRestriction_polynomialMap E (f ≫ g),
      completeLawRawCoordinateRestriction_polynomialMap E f,
      completeLawRawCoordinateRestriction_polynomialMap E g]
    exact (RingHom.id_comp _).symm

/-- An endpoint scaffold assembled from actual Formal AAT component types.
The coefficient ring is fixed to `Int`, as in the CS Law coordinates.  The
historical name is retained for downstream compatibility; no `ReadingCore` or
admissible-cover completeness theorem is part of this structure. -/
structure CSAATCompleteGeometryObject (U : AtomCarrier.{u}) where
  /-- The actual object whose operation data the Law residual evaluates. -/
  object : ArchitectureObject U
  /-- Its selected context, equation, coverage, signature, and overlap site. -/
  site : Site.AATSite object
  /-- The coherent `Int`-coefficient raw algebra on every Law coordinate. -/
  raw : LawAlgebra.RawAmbientRestrictionSystem site Int

/-! ## Lens endpoint geometry -/

/-- The actual lens Law object with its site/raw endpoint scaffold. -/
noncomputable def lensAATCompleteGeometry (input : LensFamilyInput.{u})
    (X : LensRealization input.View input.reference) :
    CSAATCompleteGeometryObject (lensAATCarrier input) where
  object := lensLawObject input X.Carrier X.toLensData.toLawStructure
  site := completeLawSite _
    (lensLawEquationSystem input X.Carrier X.toLensData.toLawStructure)
  raw := completeLawRawSystem
    (lensLawEquationSystem input X.Carrier X.toLensData.toLawStructure)

/-- Lens endpoint geometry uses the actual object-dependent Law system. -/
@[simp] theorem lensAATCompleteGeometry_equationSystem
    (input : LensFamilyInput.{u})
    (X : LensRealization input.View input.reference) :
    (lensAATCompleteGeometry input X).site.equationSystem =
      lensLawEquationSystem input X.Carrier X.toLensData.toLawStructure :=
  rfl

/-- Lens raw coordinates are exactly the complete Law-index/Atom pairs. -/
@[simp] theorem lensAATCompleteGeometry_rawCoordinate
    (input : LensFamilyInput.{u})
    (X : LensRealization input.View input.reference)
    (W : (lensAATCompleteGeometry input X).site.category) :
    ((lensAATCompleteGeometry input X).raw.coordFamily W).Coord =
      (lensLawEquationSystem input X.Carrier
        X.toLensData.toLawStructure).Coordinate :=
  rfl

/-- The lens pre-quotient raw presentation is the existing polynomial Law
coordinate ring, not a one-coordinate or empty replacement. -/
theorem lensAATCompleteGeometry_rawFreePresentation
    (input : LensFamilyInput.{u})
    (X : LensRealization input.View input.reference)
    (W : (lensAATCompleteGeometry input X).site.category) :
    LawAlgebra.FreeTypedCommAlg
        ((lensAATCompleteGeometry input X).raw.coordFamily W) Int =
      LensLawCoordinateRing input X.Carrier :=
  rfl

/-! ## Protocol endpoint geometry -/

/-- The actual protocol Law object with its site/raw endpoint scaffold. -/
noncomputable def protocolAATCompleteGeometry (input : ProtocolFamilyInput.{u})
    (X : ProtocolRealization input.schema input.observation) :
    CSAATCompleteGeometryObject (protocolAATCarrier input) where
  object := protocolLawObject input X.State X.toLawStructure
  site := completeLawSite _
    (protocolLawEquationSystem input X.State X.toLawStructure)
  raw := completeLawRawSystem
    (protocolLawEquationSystem input X.State X.toLawStructure)

/-- Protocol endpoint geometry uses the actual object-dependent Law system. -/
@[simp] theorem protocolAATCompleteGeometry_equationSystem
    (input : ProtocolFamilyInput.{u})
    (X : ProtocolRealization input.schema input.observation) :
    (protocolAATCompleteGeometry input X).site.equationSystem =
      protocolLawEquationSystem input X.State X.toLawStructure :=
  rfl

/-- Protocol raw coordinates are exactly the complete Law-index/Atom pairs. -/
@[simp] theorem protocolAATCompleteGeometry_rawCoordinate
    (input : ProtocolFamilyInput.{u})
    (X : ProtocolRealization input.schema input.observation)
    (W : (protocolAATCompleteGeometry input X).site.category) :
    ((protocolAATCompleteGeometry input X).raw.coordFamily W).Coord =
      (protocolLawEquationSystem input X.State X.toLawStructure).Coordinate :=
  rfl

/-- The protocol pre-quotient raw presentation is the existing polynomial Law
coordinate ring on every original named relation, edge, observation, and Atom. -/
theorem protocolAATCompleteGeometry_rawFreePresentation
    (input : ProtocolFamilyInput.{u})
    (X : ProtocolRealization input.schema input.observation)
    (W : (protocolAATCompleteGeometry input X).site.category) :
    LawAlgebra.FreeTypedCommAlg
        ((protocolAATCompleteGeometry input X).raw.coordFamily W) Int =
      ProtocolLawCoordinateRing input X.State :=
  rfl

#assert_standard_axioms_only AAT.AG.RealizationReconstruction

end AAT.AG.RealizationReconstruction
