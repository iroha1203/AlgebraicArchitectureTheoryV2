import ResearchLean.AG.RealizationReconstruction.CSAATGeometryReadings
import Formal.Util.AssertStandardAxioms

/-!
# Raw-algebra integration for the concrete CS geometry readings

Cycle 130 constructed a coherent raw system on a marker site, while Cycle 131
constructed the actual lens and protocol reading sites and covers.  This file
constructs the raw restriction data directly on any selected AAT site, using
that site's own equation-coordinate type.  It then instantiates the
construction on the two concrete reading sites.

The structural-relation family is empty: Law witness equations remain in the
site's `equationSystem` and are not silently added to the ambient structural
quotient.  Consequently the structural ideal is bottom, and the objectwise
raw quotient is proved algebra-equivalent to the full polynomial coordinate
ring.  This is an objectwise endpoint result, not yet a presheaf equivalence,
geometry morphism, readback theorem, or `ReadingCore` construction.
-/

namespace AAT.AG.RealizationReconstruction

open CategoryTheory

universe u

/-! ## A coherent empty-structural-relation raw system on any AAT site -/

/-- Every equation-index/Atom coordinate of the selected site remains a
distinct semantic coordinate at every context. -/
def equationCoordinateRawFamily {U : AtomCarrier.{u}}
    {A : ArchitectureObject U} (S : Site.AATSite A) (W : S.category) :
    LawAlgebra.CoordinateFamily W.ctx where
  Coord := S.equationSystem.Coordinate
  label _ := .semantic
  LocalData _ := PUnit

/-- No additional structural relation is imposed on the selected site's Law
coordinates. -/
noncomputable def emptyStructuralRelationFamilyOn {U : AtomCarrier.{u}}
    {A : ArchitectureObject U} (S : Site.AATSite A) (W : S.category) :
    LawAlgebra.StructuralRelationFamily (equationCoordinateRawFamily S W) Int where
  Relation := PEmpty
  polynomial relation := PEmpty.elim relation

/-- Coordinate restriction on the selected site fixes every Law coordinate. -/
noncomputable def equationCoordinateRawRestriction {U : AtomCarrier.{u}}
    {A : ArchitectureObject U} (S : Site.AATSite A)
    {W V : S.category} (f : W ⟶ V) :
    LawAlgebra.TypedCoordinateRestriction
      (equationCoordinateRawFamily S W)
      (equationCoordinateRawFamily S V) Int
      (S.contextPreorder.morphism (leOfHom f)) where
  variableImage coordinate := MvPolynomial.X coordinate

/-- Raw coordinate restriction is the identity polynomial homomorphism. -/
theorem equationCoordinateRawRestriction_polynomialMap
    {U : AtomCarrier.{u}} {A : ArchitectureObject U}
    (S : Site.AATSite A) {W V : S.category} (f : W ⟶ V) :
    (equationCoordinateRawRestriction S f).polynomialMap =
      RingHom.id (LawAlgebra.FreeTypedCommAlg
        (equationCoordinateRawFamily S W) Int) := by
  apply MvPolynomial.ringHom_ext
  · intro value
    exact LawAlgebra.TypedCoordinateRestriction.polynomialMap_C _ _
  · intro coordinate
    rw [LawAlgebra.TypedCoordinateRestriction.polynomialMap_X]
    rfl

/-- Empty structural relations are stable under coordinate-preserving
restriction on the selected site. -/
noncomputable def emptyStructuralRestrictionStableOn
    {U : AtomCarrier.{u}} {A : ArchitectureObject U}
    (S : Site.AATSite A) {W V : S.category} (f : W ⟶ V) :
    LawAlgebra.RestrictionStableStructuralRelations
      (emptyStructuralRelationFamilyOn S W)
      (emptyStructuralRelationFamilyOn S V)
      (S.contextPreorder.morphism (leOfHom f)) where
  restriction := equationCoordinateRawRestriction S f
  maps_JStruct := by
    intro polynomial hpolynomial
    rw [equationCoordinateRawRestriction_polynomialMap S f]
    exact hpolynomial

/-- Coherent raw ambient restriction data, constructed directly on the
selected site rather than transported from another site by a cast. -/
noncomputable def equationCoordinateRawSystemOn
    {U : AtomCarrier.{u}} {A : ArchitectureObject U}
    (S : Site.AATSite A) :
    LawAlgebra.RawAmbientRestrictionSystem S Int where
  coordFamily := equationCoordinateRawFamily S
  relationFamily := emptyStructuralRelationFamilyOn S
  restrictionStable := emptyStructuralRestrictionStableOn S
  identity_polynomialMap W :=
    equationCoordinateRawRestriction_polynomialMap S (𝟙 W)
  composition_polynomialMap f g := by
    change (equationCoordinateRawRestriction S (f ≫ g)).polynomialMap =
      (equationCoordinateRawRestriction S f).polynomialMap.comp
        (equationCoordinateRawRestriction S g).polynomialMap
    rw [equationCoordinateRawRestriction_polynomialMap S (f ≫ g),
      equationCoordinateRawRestriction_polynomialMap S f,
      equationCoordinateRawRestriction_polynomialMap S g]
    exact (RingHom.id_comp _).symm

/-! ## The empty quotient is the full coordinate ring -/

/-- An empty structural-relation family generates the bottom ideal. -/
@[simp] theorem emptyStructuralRelationFamilyOn_JStruct
    {U : AtomCarrier.{u}} {A : ArchitectureObject U}
    (S : Site.AATSite A) (W : S.category) :
    (emptyStructuralRelationFamilyOn S W).JStruct = ⊥ := by
  apply le_antisymm
  · rw [LawAlgebra.StructuralRelationFamily.JStruct, Ideal.span_le]
    rintro polynomial ⟨relation, rfl⟩
    exact PEmpty.elim relation
  · exact bot_le

/-- Objectwise, the empty structural quotient is algebra-equivalent to the
complete polynomial algebra on all equation-index/Atom coordinates. -/
noncomputable def equationCoordinateRawQuotientEquiv
    {U : AtomCarrier.{u}} {A : ArchitectureObject U}
    (S : Site.AATSite A) (W : S.category) :
    (equationCoordinateRawSystemOn S).rawAlgebra W ≃ₐ[Int]
      LawAlgebra.FreeTypedCommAlg (equationCoordinateRawFamily S W) Int :=
  (Ideal.quotientEquivAlgOfEq Int
      (emptyStructuralRelationFamilyOn_JStruct S W)).trans
    (AlgEquiv.quotientBot Int _)

/-- The quotient equivalence sends the class of every polynomial back to that
same polynomial. -/
@[simp] theorem equationCoordinateRawQuotientEquiv_quotientMap
    {U : AtomCarrier.{u}} {A : ArchitectureObject U}
    (S : Site.AATSite A) (W : S.category)
    (polynomial : LawAlgebra.FreeTypedCommAlg
      (equationCoordinateRawFamily S W) Int) :
    equationCoordinateRawQuotientEquiv S W
        ((emptyStructuralRelationFamilyOn S W).quotientMap polynomial) =
      polynomial := by
  rfl

/-! ## Lens and protocol reading-site instances -/

/-- The coherent raw system is attached directly to the concrete lens reading
site constructed in Cycle 131. -/
noncomputable def lensAATGeometryReadingRawSystem
    (input : LensFamilyInput.{u})
    (X : LensRealization input.View input.reference) :
    LawAlgebra.RawAmbientRestrictionSystem
      (lensAATGeometryReadingSite input X) Int :=
  equationCoordinateRawSystemOn (lensAATGeometryReadingSite input X)

/-- The lens reading-site raw quotient is exactly the previously constructed
Law polynomial coordinate ring, objectwise. -/
noncomputable def lensAATGeometryReadingRawQuotientEquiv
    (input : LensFamilyInput.{u})
    (X : LensRealization input.View input.reference)
    (W : (lensAATGeometryReadingSite input X).category) :
    (lensAATGeometryReadingRawSystem input X).rawAlgebra W ≃ₐ[Int]
      LensLawCoordinateRing input X.Carrier :=
  equationCoordinateRawQuotientEquiv (lensAATGeometryReadingSite input X) W

/-- The coherent raw system is attached directly to the concrete protocol
reading site constructed in Cycle 131. -/
noncomputable def protocolAATGeometryReadingRawSystem
    (input : ProtocolFamilyInput.{u})
    (X : ProtocolRealization input.schema input.observation) :
    LawAlgebra.RawAmbientRestrictionSystem
      (protocolAATGeometryReadingSite input X) Int :=
  equationCoordinateRawSystemOn (protocolAATGeometryReadingSite input X)

/-- The protocol reading-site raw quotient is exactly the previously
constructed Law polynomial coordinate ring, objectwise. -/
noncomputable def protocolAATGeometryReadingRawQuotientEquiv
    (input : ProtocolFamilyInput.{u})
    (X : ProtocolRealization input.schema input.observation)
    (W : (protocolAATGeometryReadingSite input X).category) :
    (protocolAATGeometryReadingRawSystem input X).rawAlgebra W ≃ₐ[Int]
      ProtocolLawCoordinateRing input X.State :=
  equationCoordinateRawQuotientEquiv (protocolAATGeometryReadingSite input X) W

#assert_standard_axioms_only AAT.AG.RealizationReconstruction

end AAT.AG.RealizationReconstruction
