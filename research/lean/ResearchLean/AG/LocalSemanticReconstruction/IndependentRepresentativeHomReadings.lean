import ResearchLean.AG.LocalSemanticReconstruction.IndependentRawLocalValidation
import ResearchLean.AG.LocalSemanticReconstruction.CompleteGeometryDirectCategory
import Formal.Util.AssertStandardAxioms

/-!
# Representative geometry Homs with pointwise raw laws

Implementation notes: package, coefficient, and realization maps are built by
the reviewed primitive graph assemblers. The new raw law compares individual
type references, labels, relation polynomials, and variable images. Its expected
response is computed directly from inverse context action and coefficient action;
neither a whole raw-system equality nor a completed geometry Hom is a local field.

The native strict raw equality is a theorem derived from those responses. This
module retains the representative-selected realization naturality of G-122.
The explicit-context Hom mode has a different contract and remains separate.
-/

namespace AAT.AG.LocalSemanticReconstruction.IndependentRepresentativeHom

noncomputable section

universe u v

open CategoryTheory AtomFoundation GeometryTransport LawAlgebra
open CompleteGeometryGraphAssembly

variable {U : AtomCarrier.{u}} {G H K : GeometryPackage.{u, v} U}

/-- Compute one expected raw response by inverse context action and coefficient point transport. -/
def transportTable (f : PackageTotalHom G.core H.core)
    (h : G.Coefficient →+* H.Coefficient) : IndependentRawLocal.Table H.site H.Coefficient := by
  classical
  intro q
  cases q with
  | coordinate W => exact ⟨(G.raw.coordFamily ((coreContextInverse f).obj W)).Coord⟩
  | relation W => exact ⟨(G.raw.relationFamily ((coreContextInverse f).obj W)).Relation⟩
  | label W C c => exact ⟨if hC : C = (G.raw.coordFamily ((coreContextInverse f).obj W)).Coord then
      some ((G.raw.coordFamily ((coreContextInverse f).obj W)).label (hC ▸ c)) else none⟩
  | localData W C c => exact ⟨if hC : C = (G.raw.coordFamily ((coreContextInverse f).obj W)).Coord then
      some ((G.raw.coordFamily ((coreContextInverse f).obj W)).LocalData (hC ▸ c)) else none⟩
  | polynomial W C R r =>
    exact ⟨if hC : C = (G.raw.coordFamily ((coreContextInverse f).obj W)).Coord then
      if hR : R = (G.raw.relationFamily ((coreContextInverse f).obj W)).Relation then
        some (hC.symm ▸ MvPolynomial.map h
          ((G.raw.relationFamily ((coreContextInverse f).obj W)).polynomial (hR ▸ r)))
      else none else none⟩
  | @image X Y g C D d =>
    exact ⟨if hC : C = (G.raw.coordFamily ((coreContextInverse f).obj X)).Coord then
      if hD : D = (G.raw.coordFamily ((coreContextInverse f).obj Y)).Coord then
        some (hC.symm ▸ MvPolynomial.map h
          ((G.raw.restrictionStable ((coreContextInverse f).map g)).restriction.variableImage
            (cast hD d))) else none else none⟩

/-- Every expected response agrees with the corresponding native transported primitive field. -/
theorem transportTable_eq_read (f : PackageTotalHom G.core H.core)
    (h : G.Coefficient →+* H.Coefficient) :
    transportTable f h = IndependentRawLocal.read (rawTransport f h) := by
  funext q
  cases q <;> rfl

/-- Matching primitive responses derive precisely the original strict raw transport equality. -/
theorem raw_eq_iff_points (f : PackageTotalHom G.core H.core)
    (h : G.Coefficient →+* H.Coefficient) :
    H.raw = rawTransport f h ↔
      ∀ q, IndependentRawLocal.read H.raw q = transportTable f h q := by
  rw [transportTable_eq_read]
  exact IndependentRawLocal.raw_transport_eq_iff_points f h

/-- The coordinate declaration is copied from the inverse context image. -/
theorem transport_coordinate (f : PackageTotalHom G.core H.core)
    (h : G.Coefficient →+* H.Coefficient) (W : H.site.category) :
    (transportTable f h (.coordinate W)).down =
      (G.raw.coordFamily ((coreContextInverse f).obj W)).Coord := rfl

/-- Active relation responses apply coefficient change to that single finite polynomial. -/
theorem transport_polynomial (f : PackageTotalHom G.core H.core)
    (h : G.Coefficient →+* H.Coefficient) (W : H.site.category)
    (r : (G.raw.relationFamily ((coreContextInverse f).obj W)).Relation) :
    (transportTable f h (.polynomial W
      (G.raw.coordFamily ((coreContextInverse f).obj W)).Coord
      (G.raw.relationFamily ((coreContextInverse f).obj W)).Relation r)).down =
        some (MvPolynomial.map h
          ((G.raw.relationFamily ((coreContextInverse f).obj W)).polynomial r)) := by
  simp [transportTable]

/-- Active variable-image responses apply coefficient change after the inverse arrow action. -/
theorem transport_image (f : PackageTotalHom G.core H.core)
    (h : G.Coefficient →+* H.Coefficient) {X Y : H.site.category} (g : X ⟶ Y)
    (d : (G.raw.coordFamily ((coreContextInverse f).obj Y)).Coord) :
    (transportTable f h (.image g
      (G.raw.coordFamily ((coreContextInverse f).obj X)).Coord
      (G.raw.coordFamily ((coreContextInverse f).obj Y)).Coord d)).down =
        some (MvPolynomial.map h
          ((G.raw.restrictionStable ((coreContextInverse f).map g)).restriction.variableImage d)) := by
  simp [transportTable]

/-- Representative Hom laws use the nine original coverage implications, both overlap orders,
and raw primitive comparisons at every query. The base and coefficient maps are assembled. -/
structure IsLawful (d : CompleteGeometryGraphData G H) : Prop where
  /-- Preserve every native coverage predicate at its original point arguments. -/
  coverage : CoverageTransport G H d.package.assemble
  /-- Forward order comparison for the selected overlap. -/
  overlapForward : ∀ base left right,
    overlapSource d.package.assemble base left right ≤ overlapTarget base left right
  /-- Reverse order comparison for the selected overlap. -/
  overlapBackward : ∀ base left right,
    overlapTarget base left right ≤ overlapSource d.package.assemble base left right
  /-- Every target raw response is the explicitly computed transported source response. -/
  raw : ∀ q, IndependentRawLocal.read H.raw q =
    transportTable d.package.assemble d.coefficientGraph.assemble q

/-- Lawful graph data, with a primitive raw law instead of a stored complete raw equality. -/
abbrev Code (G H : GeometryPackage.{u, v} U) :=
  {d : CompleteGeometryGraphData G H // IsLawful d}

/-- Construct the old full certificate after deriving its strict raw equality from local points. -/
def complete (c : Code G H) : CompleteGeometryGraphCode G H :=
  ⟨c.val, c.property.coverage, c.property.overlapForward, c.property.overlapBackward,
    (raw_eq_iff_points c.val.package.assemble c.val.coefficientGraph.assemble).2 c.property.raw⟩

/-- A native full certificate provides each primitive raw comparison separately. -/
def ofComplete (c : CompleteGeometryGraphCode G H) : Code G H :=
  ⟨c.val, c.property.coverage, c.property.overlapForward, c.property.overlapBackward,
    (raw_eq_iff_points c.val.package.assemble c.val.coefficientGraph.assemble).1 c.property.rawCoherent⟩

/-- Recover the old graph code including every computational component. -/
theorem complete_ofComplete (c : CompleteGeometryGraphCode G H) : complete (ofComplete c) = c :=
  Subtype.ext rfl

/-- Replacing and deriving the raw certificate leaves every primitive graph unchanged. -/
theorem ofComplete_complete (c : Code G H) : ofComplete (complete c) = c := Subtype.ext rfl

/-- Raw primitive laws and the original strict certificate have exactly the same solutions. -/
def completeEquiv : Code G H ≃ CompleteGeometryGraphCode G H where
  toFun := complete
  invFun := ofComplete
  left_inv := ofComplete_complete
  right_inv := complete_ofComplete

/-- Every permitted representative geometry Hom is constructed from local graphs and raw points. -/
def homEquiv : Code G H ≃ GeometryTotalHom G H :=
  completeEquiv.trans CompleteGeometryGraphCode.equivGeometryTotalHom

/-- Assemble all native Hom fields after discharging the raw equality. -/
def assemble (c : Code G H) : GeometryTotalHom G H := homEquiv c

/-- Read all native Hom fields, including every realization and coefficient component. -/
def read (f : GeometryTotalHom G H) : Code G H := homEquiv.symm f

/-- All permitted native representative Homs are recovered exactly. -/
theorem assemble_read (f : GeometryTotalHom G H) : assemble (read f) = f := homEquiv.right_inv f

/-- All lawful local graph data and raw responses survive the round trip. -/
theorem read_assemble (c : Code G H) : read (assemble c) = c := homEquiv.left_inv c

/-- Equal object action alone is insufficient: the complete Hom reading is injective. -/
theorem read_injective : Function.Injective (read (G := G) (H := H)) := homEquiv.symm.injective

/-- The raw equality is derived for the actual assembled base and coefficient components. -/
theorem assemble_raw_eq (c : Code G H) :
    H.raw = rawTransport (assemble c).base (assemble c).geometry.coefficientHom :=
  (raw_eq_iff_points c.val.package.assemble c.val.coefficientGraph.assemble).2 c.property.raw

/-- Direct primitive graph identity also satisfies the new raw point law. -/
def id (G : GeometryPackage.{u, v} U) : Code G G :=
  ofComplete (CompleteGeometryDirectCategory.CompleteGeometryGraphCode.id G)

/-- Direct primitive graph composition preserves the point law derived from its input comparisons. -/
def comp (f : Code G H) (g : Code H K) : Code G K :=
  ofComplete (CompleteGeometryDirectCategory.CompleteGeometryGraphCode.comp (complete f) (complete g))

/-- Local identity assembly is the actual native identity. -/
theorem assemble_id (G : GeometryPackage.{u, v} U) : assemble (id G) = GeometryTotalHom.id G := by
  change (complete (ofComplete _)).assemble = _
  rw [complete_ofComplete]
  exact CompleteGeometryDirectCategory.CompleteGeometryGraphCode.assemble_id G

/-- Local composition assembly is the actual native composition. -/
theorem assemble_comp (f : Code G H) (g : Code H K) :
    assemble (comp f g) = GeometryTotalHom.comp (assemble f) (assemble g) := by
  change (complete (ofComplete _)).assemble = _
  rw [complete_ofComplete]
  exact CompleteGeometryDirectCategory.CompleteGeometryGraphCode.assemble_comp (complete f) (complete g)

/-- A mismatching primitive raw response rejects the entire candidate Hom. -/
theorem not_lawful_of_raw_mismatch (d : CompleteGeometryGraphData G H)
    (q : IndependentRawLocal.Query H.site)
    (h : IndependentRawLocal.read H.raw q ≠
      transportTable d.package.assemble d.coefficientGraph.assemble q) : ¬ IsLawful d :=
  fun hd => h (hd.raw q)

/-- The reviewed identity fixture is a concrete positive instance of the new point law. -/
theorem identity_lawful :
    IsLawful (id CompleteGeometryGraphCode.CompleteGraphCertificateFixtures.package).val :=
  (id CompleteGeometryGraphCode.CompleteGraphCertificateFixtures.package).property

/-- The reviewed asymmetric coefficient swap is rejected by the primitive raw comparisons. -/
theorem coefficient_swap_not_lawful : ¬ IsLawful CompleteGeometryGraphCode.CompleteGraphCertificateFixtures.incoherentData := by
  intro h
  exact CompleteGeometryGraphCode.CompleteGraphCertificateFixtures.not_isCompleteGeometryGraphCode_incoherentData
    (complete ⟨_, h⟩).property

end

end AAT.AG.LocalSemanticReconstruction.IndependentRepresentativeHom

#assert_standard_axioms_only AAT.AG.LocalSemanticReconstruction.IndependentRepresentativeHom
