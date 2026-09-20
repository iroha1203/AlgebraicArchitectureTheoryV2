import ResearchLean.AG.LocalSemanticReconstruction.IndependentGeometryHomIntegrationControls
import ResearchLean.AG.LocalSemanticReconstruction.IndependentGeometryHomLocalIdentity
import ResearchLean.AG.GeometryTransport.FiniteWitnesses
import Formal.Util.AssertStandardAxioms

/-!
# Complete-Hom refutations on common local tables

The component counterexamples are lifted here to actual common Hom tables and
the invariant-witness quotient.  A fixture table may change any computational
cell while retaining the direct identity object and invariant-index rows.
Consequently every mutation is an element of the same local Hom type, and its
failure is witnessed by the relevant field of the complete point law.
-/

namespace AAT.AG.LocalSemanticReconstruction.IndependentHomRefutations

noncomputable section

universe u v

open CategoryTheory AtomFoundation GeometryTransport RealizationReconstruction LawAlgebra Site
open IndependentGeometryTableAssembly
open IndependentGeometryHomPrimitive

variable {U : AtomCarrier.{u}}

/-- Change one common Hom cell and leave every other query unchanged. -/
def setCell {mode : Mode} (table : Table.{u, v} U mode)
    (selected : Query.{u, v} U mode) (value : Bool) : Table.{u, v} U mode := by
  classical
  exact fun q => if q = selected then value else table q

@[simp] theorem setCell_selected {mode : Mode} (table : Table.{u, v} U mode)
    (selected : Query.{u, v} U mode) (value : Bool) :
    setCell table selected value selected = value := by
  simp [setCell]

theorem setCell_other {mode : Mode} (table : Table.{u, v} U mode)
    (selected q : Query.{u, v} U mode) (value : Bool) (h : q ≠ selected) :
    setCell table selected value q = table q := by
  simp [setCell, h]

/-- Invariant row laws only inspect the common object cells. -/
theorem rowLaw_of_object_eq {mode : Mode} {I J : Invariant U}
    {first second : Table.{u, v} U mode}
    {w : IndependentInverseGraph.Table.{u, u}}
    (hobjects : ∀ A B, first (.object A B) = second (.object A B))
    (hlaw : InvariantWitness.RowLaw I J first w) :
    InvariantWitness.RowLaw I J second w := by
  cases I with
  | function F =>
      cases J with
      | function G =>
          refine ⟨hlaw.1, ?_⟩
          intro A B hAB
          exact hlaw.2 A B ((hobjects A B).trans hAB)
      | predicate Q => exact False.elim hlaw
  | predicate P =>
      cases J with
      | function G => exact False.elim hlaw
      | predicate Q =>
          intro A B hAB
          exact hlaw A B ((hobjects A B).trans hAB)

/-- A common table with the direct identity object and invariant-index rows
defines retained local data, independently of every other cell. -/
def retainedOfTable (mode : Mode) (G : GeometryPackage.{u, v} U)
    (table : Table.{u, v} U mode)
    (hobject : ∀ A B, table (.object A B) =
      IdentityLocal.tableIdentity mode G (.object A B))
    (hinvariant : ∀ q, table (.invariant q) =
      IdentityLocal.tableIdentity mode G (.invariant q)) :
    InvariantWitness.Retained.{u, v}
      G.core.reading.invariantReading G.core.reading.invariantReading mode where
  family := TagChange.read table
  objectRows := by
    rw [TagChange.assemble_read]
    intro A
    refine ⟨A, ?_, ?_⟩
    · change table (.object A A) = true
      rw [hobject]
      exact (IdentityLocal.tableIdentity_object_iff mode G A A).2 rfl
    · intro B hB
      change table (.object A B) = true at hB
      rw [hobject] at hB
      exact ((IdentityLocal.tableIdentity_object_iff mode G A B).1 hB).symm
  indexRows := by
    rw [TagChange.assemble_read]
    have heq : invariant table =
        invariant (IdentityLocal.tableIdentity mode G) := by
      funext q
      exact hinvariant q
    rw [heq, IdentityLocal.tableIdentity_invariant]
    exact IndependentCarrierGraph.identity_isLawful _

@[simp] theorem retainedOfTable_table (mode : Mode)
    (G : GeometryPackage.{u, v} U) (table : Table.{u, v} U mode)
    (hobject) (hinvariant) :
    (retainedOfTable mode G table hobject hinvariant).table = table :=
  TagChange.assemble_read table

/-- Reuse the diagonal auxiliary invariant rows after checking that the new
common table agrees with the identity exactly where those rows inspect it. -/
def presentationOfTable (mode : Mode) (G : GeometryPackage.{u, v} U)
    (table : Table.{u, v} U mode)
    (hobject : ∀ A B, table (.object A B) =
      IdentityLocal.tableIdentity mode G (.object A B))
    (hinvariant : ∀ q, table (.invariant q) =
      IdentityLocal.tableIdentity mode G (.invariant q)) :
    InvariantWitness.Presentation.{u, v}
      G.core.reading.invariantReading G.core.reading.invariantReading mode where
  retained := retainedOfTable mode G table hobject hinvariant
  auxiliary := TagChange.read
    (IdentityLocal.auxiliaryIdentity G.core.reading.invariantReading)
  auxiliaryTyped := by
    rw [TagChange.assemble_read]
    constructor
    · exact IdentityLocal.auxiliaryIdentity_wrong_indices _
    · intro i j q hn
      apply (IdentityLocal.auxiliaryIdentity_typed mode G).2 i j q
      rcases hn with hn | hn | hn
      · left
        rw [retainedOfTable_table] at hn
        exact (hinvariant _).symm.trans hn
      · exact Or.inr (Or.inl hn)
      · exact Or.inr (Or.inr hn)
  rows := by
    intro i j hij
    rw [retainedOfTable_table] at hij ⊢
    rw [TagChange.assemble_read]
    have hidPoint :
        (IdentityLocal.retainedIdentity mode G).table
          (.invariant (.edge _ _ i j)) = true := by
      rw [IdentityLocal.retainedIdentity_table]
      exact (hinvariant _).symm.trans hij
    have hid := (IdentityLocal.presentationIdentity mode G).rows i j hidPoint
    change InvariantWitness.RowLaw
      (G.core.reading.invariantReading.invariant i)
      (G.core.reading.invariantReading.invariant j)
      (IdentityLocal.retainedIdentity mode G).table
      (InvariantWitness.row
        (TagChange.assemble (TagChange.read
          (IdentityLocal.auxiliaryIdentity G.core.reading.invariantReading)))
        G.core.reading.invariantReading.Index G.core.reading.invariantReading.Index i j) at hid
    rw [IdentityLocal.retainedIdentity_table, TagChange.assemble_read] at hid
    exact rowLaw_of_object_eq (fun A B => (hobject A B).symm) hid

/-- Quotient a compatible common table while erasing the reused auxiliary
diagonal witness rows. -/
def localOfTable (mode : Mode) (G : GeometryPackage.{u, v} U)
    (table : Table.{u, v} U mode)
    (hobject : ∀ A B, table (.object A B) =
      IdentityLocal.tableIdentity mode G (.object A B))
    (hinvariant : ∀ q, table (.invariant q) =
      IdentityLocal.tableIdentity mode G (.invariant q)) :
    InvariantWitness.Local.{u, v}
      G.core.reading.invariantReading G.core.reading.invariantReading mode :=
  Quotient.mk _ (presentationOfTable mode G table hobject hinvariant)

/-- Every original common query survives the auxiliary-witness quotient. -/
theorem localOfTable_point (mode : Mode) (G : GeometryPackage.{u, v} U)
    (table : Table.{u, v} U mode) (hobject) (hinvariant)
    (q : Query.{u, v} U mode) :
    InvariantWitness.point _ _
      (localOfTable mode G table hobject hinvariant) q = table q := by
  change (retainedOfTable mode G table hobject hinvariant).table q = table q
  rw [retainedOfTable_table]

/-- The quotient retains the entire supplied common table extensionally. -/
theorem localOfTable_table (mode : Mode) (G : GeometryPackage.{u, v} U)
    (table : Table.{u, v} U mode) (hobject) (hinvariant) :
    (InvariantWitness.retained _ _
      (localOfTable mode G table hobject hinvariant)).table = table := by
  funext q
  exact localOfTable_point mode G table hobject hinvariant q

/-- Reindex only the target invariant family.  Defining the transport at this
abstract equality keeps the retained common table unchanged. -/
def localOfTableTargetEq (mode : Mode) (G : GeometryPackage.{u, v} U)
    (J : InvariantFamily U)
    (hJ : G.core.reading.invariantReading = J)
    (table : Table.{u, v} U mode)
    (hobject : ∀ A B, table (.object A B) =
      IdentityLocal.tableIdentity mode G (.object A B))
    (hinvariant : ∀ q, table (.invariant q) =
      IdentityLocal.tableIdentity mode G (.invariant q)) :
    InvariantWitness.Local.{u, v}
      G.core.reading.invariantReading J mode := by
  subst J
  exact localOfTable mode G table hobject hinvariant

/-- Target-family reindexing does not alter any retained common query. -/
theorem localOfTableTargetEq_table (mode : Mode)
    (G : GeometryPackage.{u, v} U) (J : InvariantFamily U)
    (hJ : G.core.reading.invariantReading = J)
    (table : Table.{u, v} U mode) (hobject) (hinvariant) :
    (InvariantWitness.retained G.core.reading.invariantReading J
      (localOfTableTargetEq mode G J hJ table hobject hinvariant)).table = table := by
  subst J
  exact localOfTable_table mode G table hobject hinvariant

/-- Transport a completed explicit Hom across endpoint equalities. -/
def castExplicitHom {G H G' H' : GeometryPackage.{u, v} U}
    (hG : G = G') (hH : H = H')
    (F : ExplicitExactGeometryHom G H) : ExplicitExactGeometryHom G' H' := by
  subst G'
  subst H'
  exact F

/-- Endpoint transport leaves the common explicit reader unchanged. -/
theorem readExplicit_castExplicitHom
    {G H G' H' : GeometryPackage.{u, v} U}
    (hG : G = G') (hH : H = H')
    (F : ExplicitExactGeometryHom G H) :
    NativeReader.readExplicit (castExplicitHom hG hH F) =
      NativeReader.readExplicit F := by
  subst G'
  subst H'
  rfl

/-! ## Complete coefficient and actual-action mutations -/

/-- The independently read finite geometry object used by the integrated
mutations. -/
noncomputable abbrev finiteObjectData : ObjectData.{0, 0} FiniteModel.carrier :=
  IndependentGeometryTableAssembly.read GeometryTransport.FiniteGeometryWitness.package

/-- The package assembled from the independently read finite object. -/
noncomputable abbrev finiteAssembledPackage : GeometryPackage.{0, 0} FiniteModel.carrier :=
  IndependentGeometryTableAssembly.assemble finiteObjectData

/-- The first multiplication input differs from its product in the assembled
integer coefficient carrier. -/
theorem finiteAssembled_two_ne_product :
    (2 : finiteAssembledPackage.Coefficient) ≠ 2 * 3 := by
  rw [finiteAssembledPackage, IndependentGeometryTableAssembly.assemble_read]
  intro h
  change (2 : ℤ) = 6 at h
  norm_num at h

/-- The second multiplication input also differs from the product. -/
theorem finiteAssembled_three_ne_product :
    (3 : finiteAssembledPackage.Coefficient) ≠ 2 * 3 := by
  rw [finiteAssembledPackage, IndependentGeometryTableAssembly.assemble_read]
  intro h
  change (3 : ℤ) = 6 at h
  norm_num at h

/-- Change only the identity coefficient cell for `2 * 3` to false. -/
def coefficientMultiplicationMutation :
    Table.{0, 0} FiniteModel.carrier .explicit :=
  setCell
    (IdentityLocal.tableIdentity .explicit finiteAssembledPackage)
    (.coefficient (.edge finiteAssembledPackage.Coefficient
      finiteAssembledPackage.Coefficient (2 * 3) (2 * 3))) false

theorem coefficientMultiplicationMutation_object (A B) :
    coefficientMultiplicationMutation (.object A B) =
      IdentityLocal.tableIdentity .explicit
        finiteAssembledPackage (.object A B) := by
  simp [coefficientMultiplicationMutation, setCell]

theorem coefficientMultiplicationMutation_invariant (q) :
    coefficientMultiplicationMutation (.invariant q) =
      IdentityLocal.tableIdentity .explicit
        finiteAssembledPackage (.invariant q) := by
  simp [coefficientMultiplicationMutation, setCell]

/-- The coefficient mutation as an actual element of the complete local Hom
quotient. -/
def coefficientMultiplicationLocal : InvariantWitness.Local.{0, 0}
    finiteAssembledPackage.core.reading.invariantReading
    finiteAssembledPackage.core.reading.invariantReading
    .explicit :=
  localOfTable .explicit finiteAssembledPackage
    coefficientMultiplicationMutation coefficientMultiplicationMutation_object
    coefficientMultiplicationMutation_invariant

/-- The full explicit law rejects the changed multiplication result even
though both input coefficient points remain true. -/
theorem coefficientMultiplicationMutation_not_full :
    ¬ FullExplicit.PointLaws finiteObjectData finiteObjectData
      coefficientMultiplicationLocal := by
  intro hp
  have htable :
      (PackageAssembly.retained finiteObjectData.1 finiteObjectData.1
        coefficientMultiplicationLocal).table = coefficientMultiplicationMutation :=
    localOfTable_table .explicit finiteAssembledPackage coefficientMultiplicationMutation
      coefficientMultiplicationMutation_object coefficientMultiplicationMutation_invariant
  have htwo :
      (PackageAssembly.retained finiteObjectData.1 finiteObjectData.1
        coefficientMultiplicationLocal).table
        (.coefficient (.edge finiteAssembledPackage.Coefficient
          finiteAssembledPackage.Coefficient 2 2)) = true := by
    rw [htable]
    rw [coefficientMultiplicationMutation, setCell_other]
    · exact (IndependentCarrierGraph.identity_edge
        finiteAssembledPackage.Coefficient 2 2).2 rfl
    · simp [finiteAssembled_two_ne_product]
  have hthree :
      (PackageAssembly.retained finiteObjectData.1 finiteObjectData.1
        coefficientMultiplicationLocal).table
        (.coefficient (.edge finiteAssembledPackage.Coefficient
          finiteAssembledPackage.Coefficient 3 3)) = true := by
    rw [htable]
    rw [coefficientMultiplicationMutation, setCell_other]
    · exact (IndependentCarrierGraph.identity_edge
        finiteAssembledPackage.Coefficient 3 3).2 rfl
    · simp [finiteAssembled_three_ne_product]
  have hsix := hp.coefficient.2.mul
    (2 : finiteAssembledPackage.Coefficient)
    (3 : finiteAssembledPackage.Coefficient)
    (2 : finiteAssembledPackage.Coefficient)
    (3 : finiteAssembledPackage.Coefficient) htwo hthree
  rw [htable] at hsix
  change coefficientMultiplicationMutation
    (.coefficient (.edge finiteAssembledPackage.Coefficient
      finiteAssembledPackage.Coefficient (2 * 3) (2 * 3))) = true at hsix
  rw [coefficientMultiplicationMutation, setCell_selected] at hsix
  exact Bool.noConfusion hsix

/-! ## A concrete actual-axis mutation -/

/-- A one-point axis fixture whose support reading is empty.  It is available
over every architecture object and makes the selected identity-axis action
completely explicit. -/
def axisFixtureContext (A : ArchitectureObject U) : ArchCtx A where
  minimal := {
    Support := PEmpty
    Axis := PUnit
    Observable := PUnit
    supportReads := fun _ _ => False
    supportReads_objectFamily := fun h => False.elim h
    axisReads := fun _ => True
    observableReads := fun _ => True
  }
  Extension := PUnit
  extension := PUnit.unit

/-- The selected actual-axis query for the identity restriction of the
one-point fixture. -/
def axisActionQuery : Query.{0, 0} FiniteModel.carrier .explicit :=
  let W := axisFixtureContext finiteAssembledPackage.core.object
  .atObjects finiteAssembledPackage.core.object finiteAssembledPackage.core.object
    (.realization (.actualAxis W W W W (Site.identityContextMorphism W)
      PUnit.unit PUnit.unit))

/-- Change only the actual-axis answer at the concrete identity restriction. -/
def axisActionMutation : Table.{0, 0} FiniteModel.carrier .explicit :=
  setCell (IdentityLocal.tableIdentity .explicit finiteAssembledPackage)
    axisActionQuery false

theorem axisActionMutation_object (A B) :
    axisActionMutation (.object A B) =
      IdentityLocal.tableIdentity .explicit
        finiteAssembledPackage (.object A B) := by
  simp [axisActionMutation, axisActionQuery, setCell]

theorem axisActionMutation_invariant (q) :
    axisActionMutation (.invariant q) =
      IdentityLocal.tableIdentity .explicit
        finiteAssembledPackage (.invariant q) := by
  simp [axisActionMutation, axisActionQuery, setCell]

/-- The actual-axis mutation as an element of the complete local Hom
quotient. -/
def axisActionMutationLocal : InvariantWitness.Local.{0, 0}
    finiteAssembledPackage.core.reading.invariantReading
    finiteAssembledPackage.core.reading.invariantReading
    .explicit :=
  localOfTable .explicit finiteAssembledPackage axisActionMutation
    axisActionMutation_object axisActionMutation_invariant

/-- The full explicit law rejects a changed actual-axis answer while the two
context rows and the selected input-axis point stay true. -/
theorem axisActionMutation_not_full :
    ¬ FullExplicit.PointLaws finiteObjectData finiteObjectData
      axisActionMutationLocal := by
  intro hp
  let W := axisFixtureContext finiteAssembledPackage.core.object
  let g : ContextMorphism W W := Site.identityContextMorphism W
  have htable :
      (PackageAssembly.retained finiteObjectData.1 finiteObjectData.1
        axisActionMutationLocal).table = axisActionMutation :=
    localOfTable_table .explicit finiteAssembledPackage axisActionMutation
      axisActionMutation_object axisActionMutation_invariant
  have hcontext :
      (PackageAssembly.retained finiteObjectData.1 finiteObjectData.1
        axisActionMutationLocal).table
        (.atObjects finiteAssembledPackage.core.object
          finiteAssembledPackage.core.object (.context .forward W W)) = true := by
    rw [htable]
    rw [axisActionMutation, setCell_other]
    · simp only [IdentityLocal.tableIdentity, Identity.identityWith]
      rw [NativeReader.liftDependent_active]
      simp [Identity.fullDependentIdentity, Context.identity]
    · simp [axisActionQuery]
  have haxis :
      (PackageAssembly.retained finiteObjectData.1 finiteObjectData.1
        axisActionMutationLocal).table
        (.atObjects finiteAssembledPackage.core.object
          finiteAssembledPackage.core.object
          (.realization (.explicitAxis .forward W W PUnit.unit PUnit.unit))) = true := by
    rw [htable]
    rw [axisActionMutation, setCell_other]
    · simp only [IdentityLocal.tableIdentity, Identity.identityWith]
      rw [NativeReader.liftDependent_active]
      simp [Identity.fullDependentIdentity, Identity.explicitRealization]
    · simp [axisActionQuery]
  have haction := hp.realization.axisAction W W W W g
    PUnit.unit PUnit.unit PUnit.unit hcontext hcontext haxis
  rw [htable] at haction
  change axisActionMutation axisActionQuery =
    axisActionMutation
      (.atObjects finiteAssembledPackage.core.object
        finiteAssembledPackage.core.object
        (.realization (.explicitAxis .forward W W (g.axisMap PUnit.unit)
          PUnit.unit))) at haction
  have hleft : axisActionMutation axisActionQuery = false := by
    exact setCell_selected _ _ _
  have hright :
      axisActionMutation
        (.atObjects finiteAssembledPackage.core.object
          finiteAssembledPackage.core.object
          (.realization (.explicitAxis .forward W W (g.axisMap PUnit.unit)
            PUnit.unit))) = true := by
    rw [axisActionMutation, setCell_other]
    · simp only [IdentityLocal.tableIdentity, Identity.identityWith]
      rw [NativeReader.liftDependent_active]
      simp [Identity.fullDependentIdentity, Identity.explicitRealization, g,
        Site.identityContextMorphism]
    · simp [axisActionQuery]
  rw [hleft, hright] at haction
  exact Bool.noConfusion haction

/-! ## A concrete one-sided overlap mutation -/

/-- An inhabited context with deliberately empty support readings. -/
def inhabitedSupportContext (A : ArchitectureObject U) : ArchCtx A where
  minimal := {
    Support := PUnit
    Axis := PUnit
    Observable := PUnit
    supportReads := fun _ _ => False
    supportReads_objectFamily := fun h => False.elim h
    axisReads := fun _ => True
    observableReads := fun _ => True
  }
  Extension := PUnit
  extension := PUnit.unit

/-- A context with no support values. -/
def emptySupportContext (A : ArchitectureObject U) : ArchCtx A where
  minimal := {
    Support := PEmpty
    Axis := PUnit
    Observable := PUnit
    supportReads := fun _ _ => False
    supportReads_objectFamily := fun h => False.elim h
    axisReads := fun _ => True
    observableReads := fun _ => True
  }
  Extension := PUnit
  extension := PUnit.unit

/-- The selected finite overlap on three copies of the inhabited fixture. -/
noncomputable abbrev inhabitedOverlap :
    ArchCtx finiteAssembledPackage.core.object :=
  finiteAssembledPackage.geometry.overlap.overlap
    (inhabitedSupportContext finiteAssembledPackage.core.object)
    (inhabitedSupportContext finiteAssembledPackage.core.object)
    (inhabitedSupportContext finiteAssembledPackage.core.object)

/-- The empty-support fixture refines the product of two inhabited fixtures
in the canonical restriction preorder. -/
theorem emptySupport_le_inhabitedProduct (A : ArchitectureObject U) :
    (Site.contextMorphismPreorderCategory A).le
      (emptySupportContext A)
      (Site.productContext (inhabitedSupportContext A)
        (inhabitedSupportContext A)) := by
  refine ⟨{
    supportMap := PEmpty.elim
    axisMap := fun _ => (PUnit.unit, PUnit.unit)
    observableRestrict := fun _ => PUnit.unit
  }, ?_⟩
  exact ⟨fun h => False.elim h,
    fun _ => ⟨trivial, trivial⟩,
    fun _ => trivial,
    fun {support} => PEmpty.elim support⟩

/-- The inhabited product has no morphism into an empty support carrier. -/
theorem not_inhabitedProduct_le_emptySupport (A : ArchitectureObject U) :
    ¬ (Site.contextMorphismPreorderCategory A).le
      (Site.productContext (inhabitedSupportContext A)
        (inhabitedSupportContext A))
      (emptySupportContext A) := by
  rintro ⟨f, _hf⟩
  exact PEmpty.elim (f.supportMap (PUnit.unit, PUnit.unit))

/-- The empty-support fixture refines the concrete selected overlap. -/
theorem emptySupport_le_inhabitedOverlap :
    finiteAssembledPackage.core.contextPreorder.le
      (emptySupportContext finiteAssembledPackage.core.object)
      inhabitedOverlap := by
  change finiteAssembledPackage.core.contextPreorder.le
    (emptySupportContext finiteAssembledPackage.core.object)
    (finiteAssembledPackage.geometry.overlap.overlap
      (inhabitedSupportContext finiteAssembledPackage.core.object)
      (inhabitedSupportContext finiteAssembledPackage.core.object)
      (inhabitedSupportContext finiteAssembledPackage.core.object))
  have hpack : finiteAssembledPackage =
      GeometryTransport.FiniteGeometryWitness.package :=
    IndependentGeometryTableAssembly.assemble_read _
  rw [hpack]
  exact emptySupport_le_inhabitedProduct _

/-- The concrete selected overlap cannot refine an empty-support context. -/
theorem not_inhabitedOverlap_le_emptySupport :
    ¬ finiteAssembledPackage.core.contextPreorder.le inhabitedOverlap
      (emptySupportContext finiteAssembledPackage.core.object) := by
  change ¬ finiteAssembledPackage.core.contextPreorder.le
    (finiteAssembledPackage.geometry.overlap.overlap
      (inhabitedSupportContext finiteAssembledPackage.core.object)
      (inhabitedSupportContext finiteAssembledPackage.core.object)
      (inhabitedSupportContext finiteAssembledPackage.core.object))
    (emptySupportContext finiteAssembledPackage.core.object)
  have hpack : finiteAssembledPackage =
      GeometryTransport.FiniteGeometryWitness.package :=
    IndependentGeometryTableAssembly.assemble_read _
  rw [hpack]
  exact not_inhabitedProduct_le_emptySupport _

/-- Add exactly the forbidden forward context point from the selected overlap
to the empty-support fixture. -/
def overlapForwardMutation : Table.{0, 0} FiniteModel.carrier .explicit :=
  setCell (IdentityLocal.tableIdentity .explicit finiteAssembledPackage)
    (.atObjects finiteAssembledPackage.core.object
      finiteAssembledPackage.core.object
      (.context .forward inhabitedOverlap
        (emptySupportContext finiteAssembledPackage.core.object))) true

theorem overlapForwardMutation_object (A B) :
    overlapForwardMutation (.object A B) =
      IdentityLocal.tableIdentity .explicit
        finiteAssembledPackage (.object A B) := by
  simp [overlapForwardMutation, setCell]

theorem overlapForwardMutation_invariant (q) :
    overlapForwardMutation (.invariant q) =
      IdentityLocal.tableIdentity .explicit
        finiteAssembledPackage (.invariant q) := by
  simp [overlapForwardMutation, setCell]

/-- The one-sided overlap mutation as an element of the complete local Hom
quotient. -/
def overlapForwardMutationLocal : InvariantWitness.Local.{0, 0}
    finiteAssembledPackage.core.reading.invariantReading
    finiteAssembledPackage.core.reading.invariantReading
    .explicit :=
  localOfTable .explicit finiteAssembledPackage overlapForwardMutation
    overlapForwardMutation_object overlapForwardMutation_invariant

/-- The full overlap law rejects the added forward context point because the
reverse target-order comparison is concretely impossible. -/
theorem overlapForwardMutation_not_full :
    ¬ FullExplicit.PointLaws finiteObjectData finiteObjectData
      overlapForwardMutationLocal := by
  intro hp
  let W := inhabitedSupportContext finiteAssembledPackage.core.object
  let T := emptySupportContext finiteAssembledPackage.core.object
  have htable :
      (PackageAssembly.retained finiteObjectData.1 finiteObjectData.1
        overlapForwardMutationLocal).table = overlapForwardMutation :=
    localOfTable_table .explicit finiteAssembledPackage overlapForwardMutation
      overlapForwardMutation_object overlapForwardMutation_invariant
  have hW : overlapForwardMutation
      (.atObjects finiteAssembledPackage.core.object
        finiteAssembledPackage.core.object (.context .backward W W)) = true := by
    rw [overlapForwardMutation, setCell_other]
    · simp only [IdentityLocal.tableIdentity, Identity.identityWith]
      rw [NativeReader.liftDependent_active]
      simp [Identity.fullDependentIdentity, Context.identity]
    · simp [W]
  have hR :
      (finiteObjectData.2.1.2.val (.matching W W W inhabitedOverlap)).down = true := by
    rw [← GeometryComponents.read_overlap finiteObjectData]
    simp [IndependentOverlapCandidate.read,
      IndependentOverlapCandidate.ContextMatch.read, W]
  have hT : overlapForwardMutation
      (.atObjects finiteAssembledPackage.core.object
        finiteAssembledPackage.core.object
        (.context .forward inhabitedOverlap T)) = true := by
    simp [overlapForwardMutation, setCell, T]
  have hleft :
      (finiteObjectData.1.val.2.1.val (.le T inhabitedOverlap)).down := by
    rw [← GeometryComponents.read_context finiteObjectData]
    exact emptySupport_le_inhabitedOverlap
  have hright :
      ¬ (finiteObjectData.1.val.2.1.val (.le inhabitedOverlap T)).down := by
    rw [← GeometryComponents.read_context finiteObjectData]
    exact not_inhabitedOverlap_le_emptySupport
  have hoverlap := hp.overlap
  change Overlap.PointLaws finiteObjectData.2.1.2.val
    finiteObjectData.2.1.2.val finiteObjectData.1.val.2.1.val
    (PackageAssembly.retained finiteObjectData.1 finiteObjectData.1
      overlapForwardMutationLocal).table at hoverlap
  rw [htable] at hoverlap
  have hrejected := Overlap.one_sided_order_rejected
    finiteObjectData.2.1.2.val finiteObjectData.2.1.2.val
    finiteObjectData.1.val.2.1.val overlapForwardMutation
    W W W inhabitedOverlap W W W inhabitedOverlap T
    hW hW hW hR hR hT hleft hright
  exact hrejected.2 hoverlap

/-! ## A relation-polynomial mismatch on one complete local Hom table -/

/-- Replace only the raw system by the lawful constant-one relation fixture. -/
def oneRelationPackage (P : AATCorePackage U) (g : SelectedGeometryReading P) :
    GeometryPackage.{u, 0} U where
  core := P
  geometry := g
  Coefficient := ℤ
  coefficientCommRing := inferInstance
  raw := IndependentExplicitRaw.oneRelationRaw g.toAATSite

/-- Source endpoint for the integrated relation-polynomial refutation. -/
noncomputable abbrev polynomialSourcePackage :
    GeometryPackage.{0, 0} FiniteModel.carrier :=
  unitPackage GeometryTransport.FiniteGeometryWitness.package.core
    GeometryTransport.FiniteGeometryWitness.package.geometry ℤ

/-- Target endpoint with the same core, geometry, coefficient ring, and raw
carriers, but with relation polynomial `1`. -/
noncomputable abbrev polynomialTargetPackage :
    GeometryPackage.{0, 0} FiniteModel.carrier :=
  oneRelationPackage GeometryTransport.FiniteGeometryWitness.package.core
    GeometryTransport.FiniteGeometryWitness.package.geometry

noncomputable abbrev polynomialSourceData :
    ObjectData.{0, 0} FiniteModel.carrier :=
  IndependentGeometryTableAssembly.read polynomialSourcePackage

noncomputable abbrev polynomialTargetData :
    ObjectData.{0, 0} FiniteModel.carrier :=
  IndependentGeometryTableAssembly.read polynomialTargetPackage

/-- The independently assembled endpoints retain the same invariant family. -/
theorem polynomialInvariantEq :
    (IndependentGeometryTableAssembly.assemble polynomialSourceData).core.reading.invariantReading =
      (IndependentGeometryTableAssembly.assemble polynomialTargetData).core.reading.invariantReading := by
  rw [polynomialSourceData, polynomialTargetData,
    IndependentGeometryTableAssembly.assemble_read,
    IndependentGeometryTableAssembly.assemble_read]
  rfl

/-- Direct source identity points used as the common table between the two
raw endpoints. -/
def polynomialMismatchTable : Table.{0, 0} FiniteModel.carrier .explicit :=
  IdentityLocal.tableIdentity .explicit
    (IndependentGeometryTableAssembly.assemble polynomialSourceData)

theorem polynomialMismatchTable_object (A B) :
    polynomialMismatchTable (.object A B) =
      IdentityLocal.tableIdentity .explicit
        (IndependentGeometryTableAssembly.assemble polynomialSourceData)
        (.object A B) := rfl

theorem polynomialMismatchTable_invariant (q) :
    polynomialMismatchTable (.invariant q) =
      IdentityLocal.tableIdentity .explicit
        (IndependentGeometryTableAssembly.assemble polynomialSourceData)
        (.invariant q) := rfl

/-- The source direct identity table, regarded between the two endpoint object
readings whose core and invariant family are identical. -/
def polynomialMismatchLocal : InvariantWitness.Local.{0, 0}
    (IndependentGeometryTableAssembly.assemble polynomialSourceData).core.reading.invariantReading
    (IndependentGeometryTableAssembly.assemble polynomialTargetData).core.reading.invariantReading
    .explicit :=
  localOfTableTargetEq .explicit
    (IndependentGeometryTableAssembly.assemble polynomialSourceData)
    (IndependentGeometryTableAssembly.assemble polynomialTargetData).core.reading.invariantReading
    polynomialInvariantEq polynomialMismatchTable
    polynomialMismatchTable_object polynomialMismatchTable_invariant

theorem polynomialMismatchLocal_table :
    (PackageAssembly.retained polynomialSourceData.1 polynomialTargetData.1
      polynomialMismatchLocal).table =
      polynomialMismatchTable :=
  localOfTableTargetEq_table .explicit
    (IndependentGeometryTableAssembly.assemble polynomialSourceData)
    (IndependentGeometryTableAssembly.assemble polynomialTargetData).core.reading.invariantReading
    polynomialInvariantEq polynomialMismatchTable
    polynomialMismatchTable_object polynomialMismatchTable_invariant

/-- The constant-one target relation cannot satisfy the complete explicit Hom
law against the source relation `X`. -/
theorem polynomialMismatch_not_full :
    ¬ FullExplicit.PointLaws polynomialSourceData polynomialTargetData
      polynomialMismatchLocal := by
  intro hp
  let F := FullExplicit.assembleHom polynomialSourceData polynomialTargetData
    polynomialMismatchLocal hp
  let F' : ExplicitExactGeometryHom polynomialSourcePackage
      polynomialTargetPackage := by
    rw [← IndependentGeometryTableAssembly.assemble_read polynomialSourcePackage,
      ← IndependentGeometryTableAssembly.assemble_read polynomialTargetPackage]
    exact F
  let W : polynomialTargetPackage.site.category :=
    ⟨axisFixtureContext polynomialTargetPackage.core.object⟩
  have hpoly := (F'.raw.relation W).polynomial_eq PUnit.unit
  have hconstant := congrArg MvPolynomial.constantCoeff hpoly
  simp [F', unitPackage, oneRelationPackage, IndependentRawLocal.unitRaw,
    IndependentExplicitRaw.oneRelationRaw,
    StructuralRelationFamily.baseChange,
    CoordinateFamilyExactEquiv.polynomialEquiv] at hconstant

/-! ## A variable-image mismatch on one complete local Hom table -/

namespace IdentityImageRaw

open LawAlgebra.FiniteExamples.RawPresheaf

/-- Keep the finite raw coordinate fixed along every selected restriction. -/
def coordinateRestriction {X Y : Site.category} (f : X ⟶ Y) :
    TypedCoordinateRestriction (coordFamily X) (coordFamily Y) ℤ
      (Site.contextPreorder.morphism (CategoryTheory.leOfHom f)) where
  variableImage := fun _ => MvPolynomial.X ()

/-- The corresponding polynomial map is the identity. -/
theorem coordinateRestriction_polynomialMap {X Y : Site.category}
    (f : X ⟶ Y) :
    (coordinateRestriction f).polynomialMap =
      RingHom.id (FreeTypedCommAlg (coordFamily X) ℤ) := by
  apply MvPolynomial.ringHom_ext
  · intro value
    simp [TypedCoordinateRestriction.polynomialMap]
  · intro coordinate
    cases coordinate
    rw [TypedCoordinateRestriction.polynomialMap_X]
    change MvPolynomial.X () = MvPolynomial.X PUnit.unit
    exact congrArg MvPolynomial.X (Subsingleton.elim _ _)

/-- Identity variable images preserve the unchanged structural ideal. -/
def restrictionStable {X Y : Site.category} (f : X ⟶ Y) :
    RestrictionStableStructuralRelations (relationFamily X) (relationFamily Y)
      (Site.contextPreorder.morphism (CategoryTheory.leOfHom f)) where
  restriction := coordinateRestriction f
  maps_JStruct := by
    intro polynomial hpolynomial
    rw [coordinateRestriction_polynomialMap]
    exact hpolynomial

/-- A lawful finite raw system with the same carriers and relation polynomial
as the original fixture, but identity variable images on every arrow. -/
def system : RawAmbientRestrictionSystem Site ℤ where
  coordFamily := coordFamily
  relationFamily := relationFamily
  restrictionStable := restrictionStable
  identity_polynomialMap W := coordinateRestriction_polynomialMap (X := W) (Y := W) (𝟙 W)
  composition_polynomialMap f g := by
    change (coordinateRestriction (f ≫ g)).polynomialMap =
      ((coordinateRestriction f).polynomialMap).comp
        ((coordinateRestriction g).polynomialMap)
    rw [coordinateRestriction_polynomialMap,
      coordinateRestriction_polynomialMap,
      coordinateRestriction_polynomialMap]
    exact (RingHom.id_comp _).symm

@[simp] theorem variableImage {X Y : Site.category} (f : X ⟶ Y) :
    (system.restrictionStable f).restriction.variableImage () =
      MvPolynomial.X () := rfl

end IdentityImageRaw

/-- Target endpoint for the variable-image mutation. -/
def identityImagePackage : GeometryPackage.{0, 0} FiniteModel.carrier where
  core := GeometryTransport.FiniteGeometryWitness.package.core
  geometry := GeometryTransport.FiniteGeometryWitness.package.geometry
  Coefficient := ℤ
  coefficientCommRing := inferInstance
  raw := IdentityImageRaw.system

noncomputable abbrev imageSourceData : ObjectData.{0, 0} FiniteModel.carrier :=
  IndependentGeometryTableAssembly.read
    GeometryTransport.FiniteGeometryWitness.package

noncomputable abbrev imageTargetData : ObjectData.{0, 0} FiniteModel.carrier :=
  IndependentGeometryTableAssembly.read identityImagePackage

theorem imageInvariantEq :
    (IndependentGeometryTableAssembly.assemble imageSourceData).core.reading.invariantReading =
      (IndependentGeometryTableAssembly.assemble imageTargetData).core.reading.invariantReading := by
  rw [imageSourceData, imageTargetData,
    IndependentGeometryTableAssembly.assemble_read,
    IndependentGeometryTableAssembly.assemble_read]
  rfl

def imageMismatchTable : Table.{0, 0} FiniteModel.carrier .explicit :=
  IdentityLocal.tableIdentity .explicit
    (IndependentGeometryTableAssembly.assemble imageSourceData)

theorem imageMismatchTable_object (A B) :
    imageMismatchTable (.object A B) =
      IdentityLocal.tableIdentity .explicit
        (IndependentGeometryTableAssembly.assemble imageSourceData)
        (.object A B) := rfl

theorem imageMismatchTable_invariant (q) :
    imageMismatchTable (.invariant q) =
      IdentityLocal.tableIdentity .explicit
        (IndependentGeometryTableAssembly.assemble imageSourceData)
        (.invariant q) := rfl

def imageMismatchLocal : InvariantWitness.Local.{0, 0}
    (IndependentGeometryTableAssembly.assemble imageSourceData).core.reading.invariantReading
    (IndependentGeometryTableAssembly.assemble imageTargetData).core.reading.invariantReading
    .explicit :=
  localOfTableTargetEq .explicit
    (IndependentGeometryTableAssembly.assemble imageSourceData)
    (IndependentGeometryTableAssembly.assemble imageTargetData).core.reading.invariantReading
    imageInvariantEq imageMismatchTable imageMismatchTable_object
    imageMismatchTable_invariant

theorem imageMismatchLocal_table :
    (PackageAssembly.retained imageSourceData.1 imageTargetData.1
      imageMismatchLocal).table = imageMismatchTable :=
  localOfTableTargetEq_table .explicit
    (IndependentGeometryTableAssembly.assemble imageSourceData)
    (IndependentGeometryTableAssembly.assemble imageTargetData).core.reading.invariantReading
    imageInvariantEq imageMismatchTable imageMismatchTable_object
    imageMismatchTable_invariant

/-- A direct reader lemma for inverse context objects of a completed explicit
Hom. -/
theorem readExplicit_context_backward_point_iff
    {G H : GeometryPackage.{u, v} U} (F : ExplicitExactGeometryHom G H)
    (W : ArchCtx G.core.object) (V : ArchCtx H.core.object) :
    NativeReader.readExplicit F
        (.atObjects G.core.object H.core.object (.context .backward W V)) = true ↔
      ((coreContextInverse F.base).obj ⟨V⟩).ctx = W := by
  simpa [NativeReader.readExplicit] using
    (NativeReader.readWith_context_backward_point_iff .explicit F.base
      F.coefficientHom (ExplicitRaw.readRaw F.base F.coefficientHom F.raw)
      (NativeReader.explicitRealizationRead F.base F.realization) W V)

/-- The complete explicit law rejects the original `X ↦ -X` restriction
against a target system whose same selected arrow sends `X ↦ X`. -/
theorem imageMismatch_not_full :
    ¬ FullExplicit.PointLaws imageSourceData imageTargetData
      imageMismatchLocal := by
  intro hp
  let F := FullExplicit.assembleHom imageSourceData imageTargetData
    imageMismatchLocal hp
  have hsource : IndependentGeometryTableAssembly.assemble imageSourceData =
      GeometryTransport.FiniteGeometryWitness.package :=
    IndependentGeometryTableAssembly.assemble_read _
  have htarget : IndependentGeometryTableAssembly.assemble imageTargetData =
      identityImagePackage := IndependentGeometryTableAssembly.assemble_read _
  let F' : ExplicitExactGeometryHom
      GeometryTransport.FiniteGeometryWitness.package identityImagePackage :=
    castExplicitHom hsource htarget F
  have hread : NativeReader.readExplicit F = imageMismatchTable :=
    (NativeReader.readExplicit_assemble imageSourceData imageTargetData
      imageMismatchLocal hp).trans imageMismatchLocal_table
  have hidentity : imageMismatchTable =
      IdentityLocal.tableIdentity .explicit
        GeometryTransport.FiniteGeometryWitness.package := by
    exact congrArg (IdentityLocal.tableIdentity .explicit) hsource
  have hread' : NativeReader.readExplicit F' =
      IdentityLocal.tableIdentity .explicit
        GeometryTransport.FiniteGeometryWitness.package := by
    exact (readExplicit_castExplicitHom hsource htarget F).trans
      (hread.trans hidentity)
  let left := LawAlgebra.FiniteExamples.RawPresheaf.left.ctx
  let base := FiniteModel.twoPatchBase.ctx
  have hleftCell : NativeReader.readExplicit F'
      (.atObjects GeometryTransport.FiniteGeometryWitness.package.core.object
        identityImagePackage.core.object
        (.context .backward left left)) = true := by
    rw [hread']
    simp [IdentityLocal.tableIdentity, Identity.identityWith,
      identityImagePackage, NativeReader.liftDependent,
      Identity.fullDependentIdentity, Context.identity]
  have hbaseCell : NativeReader.readExplicit F'
      (.atObjects GeometryTransport.FiniteGeometryWitness.package.core.object
        identityImagePackage.core.object
        (.context .backward base base)) = true := by
    rw [hread']
    simp [IdentityLocal.tableIdentity, Identity.identityWith,
      identityImagePackage, NativeReader.liftDependent,
      Identity.fullDependentIdentity, Context.identity]
  have hinverseLeft : ((coreContextInverse F'.base).obj
      LawAlgebra.FiniteExamples.RawPresheaf.left).ctx = left :=
    (readExplicit_context_backward_point_iff F' left left).1 hleftCell
  have hinverseBase : ((coreContextInverse F'.base).obj
      FiniteModel.twoPatchBase).ctx = base :=
    (readExplicit_context_backward_point_iff F' base base).1 hbaseCell
  have hbase_ne_left : base ≠ left := by
    intro h
    have heq := congrArg
      (fun W : Site.ArchitectureContext FiniteModel.corePackage.object =>
        (⟨W.Extension, W.extension⟩ : Sigma fun T : Type => T)) h
    injection heq with _ hindex
    exact FiniteModel.TwoPatchContextIndex.noConfusion hindex
  have hinverseLeft_eq_rawLeft :
      ((coreContextInverse F'.base).obj
        LawAlgebra.FiniteExamples.RawPresheaf.left).ctx =
        LawAlgebra.FiniteExamples.RawPresheaf.left.ctx := by
    simpa [left] using hinverseLeft
  have hbase_ne_rawLeft :
      base ≠ LawAlgebra.FiniteExamples.RawPresheaf.left.ctx := by
    simpa [left] using hbase_ne_left
  have hinverseBase_ne_rawLeft :
      ((coreContextInverse F'.base).obj FiniteModel.twoPatchBase).ctx ≠
        LawAlgebra.FiniteExamples.RawPresheaf.left.ctx := by
    intro h
    exact hbase_ne_rawLeft (hinverseBase.symm.trans h)
  have himage := F'.raw.restriction_polynomial
    LawAlgebra.FiniteExamples.RawPresheaf.leftToBase
    (MvPolynomial.X ())
  simp only [GeometryTransport.FiniteGeometryWitness.package] at himage
  rw [LawAlgebra.FiniteExamples.RawPresheaf.system_restriction] at himage
  have hsourceImage :
      (LawAlgebra.FiniteExamples.RawPresheaf.coordinateRestriction
        ((coreContextInverse F'.base).map
          LawAlgebra.FiniteExamples.RawPresheaf.leftToBase)).polynomialMap
          (MvPolynomial.X ()) = -(MvPolynomial.X ()) := by
    rw [LawAlgebra.FiniteExamples.RawPresheaf.coordinateRestriction_polynomialMap_X]
    simp [LawAlgebra.FiniteExamples.RawPresheaf.gauge,
      hinverseLeft_eq_rawLeft, hinverseBase_ne_rawLeft]
  have htargetMap :
      (identityImagePackage.raw.restrictionStable
        LawAlgebra.FiniteExamples.RawPresheaf.leftToBase).restriction.polynomialMap =
        RingHom.id (FreeTypedCommAlg
          (IdentityImageRaw.system.coordFamily
            LawAlgebra.FiniteExamples.RawPresheaf.left) ℤ) := by
    change (IdentityImageRaw.coordinateRestriction
      LawAlgebra.FiniteExamples.RawPresheaf.leftToBase).polynomialMap = _
    exact IdentityImageRaw.coordinateRestriction_polynomialMap _
  have himage' :
      (F'.raw.coordinate LawAlgebra.FiniteExamples.RawPresheaf.left).polynomialHom
          F'.coefficientHom (-(MvPolynomial.X ())) =
        (F'.raw.coordinate FiniteModel.twoPatchBase).polynomialHom
          F'.coefficientHom (MvPolynomial.X ()) := by
    calc
      _ = (F'.raw.coordinate
            LawAlgebra.FiniteExamples.RawPresheaf.left).polynomialHom
          F'.coefficientHom
          ((LawAlgebra.FiniteExamples.RawPresheaf.coordinateRestriction
            ((coreContextInverse F'.base).map
              LawAlgebra.FiniteExamples.RawPresheaf.leftToBase)).polynomialMap
                (MvPolynomial.X ())) := congrArg _ hsourceImage.symm
      _ = (identityImagePackage.raw.restrictionStable
            LawAlgebra.FiniteExamples.RawPresheaf.leftToBase).restriction.polynomialMap
          ((F'.raw.coordinate FiniteModel.twoPatchBase).polynomialHom
            F'.coefficientHom (MvPolynomial.X ())) := himage
      _ = _ := by rw [htargetMap]; rfl
  have hcoordinateLeft :
      (F'.raw.coordinate LawAlgebra.FiniteExamples.RawPresheaf.left).polynomialHom
        F'.coefficientHom (MvPolynomial.X ()) = MvPolynomial.X () := by
    rw [CoordinateFamilyExactEquiv.polynomialHom_X]
    change MvPolynomial.X _ =
      (MvPolynomial.X () : MvPolynomial Unit ℤ)
    exact congrArg MvPolynomial.X (Subsingleton.elim _ _)
  have hcoordinateBase :
      (F'.raw.coordinate FiniteModel.twoPatchBase).polynomialHom
        F'.coefficientHom (MvPolynomial.X ()) = MvPolynomial.X () := by
    rw [CoordinateFamilyExactEquiv.polynomialHom_X]
    change MvPolynomial.X _ =
      (MvPolynomial.X () : MvPolynomial Unit ℤ)
    exact congrArg MvPolynomial.X (Subsingleton.elim _ _)
  rw [map_neg, hcoordinateLeft, hcoordinateBase] at himage'
  have hcoefficient := congrArg
    (fun p => p.coeff (Finsupp.single () 1)) himage'
  simp at hcoefficient

/-! ## Same base and coefficient action, separated by raw coordinates -/

namespace BoolRaw

abbrev S := GeometryTransport.FiniteGeometryWitness.package.site

/-- Two raw coordinate names with constant labels and one-point local data. -/
def coordFamily (W : S.category) : CoordinateFamily W.ctx where
  Coord := Bool
  label := fun _ => .state
  LocalData := fun _ => PUnit

/-- No structural relation generator is needed for the raw-coordinate
separation fixture. -/
def relationFamily (W : S.category) :
    StructuralRelationFamily (coordFamily W) ℤ where
  Relation := PEmpty
  polynomial := PEmpty.elim

/-- Every restriction fixes each Boolean coordinate variable. -/
def coordinateRestriction {X Y : S.category} (f : X ⟶ Y) :
    TypedCoordinateRestriction (coordFamily X) (coordFamily Y) ℤ
      (S.contextPreorder.morphism (CategoryTheory.leOfHom f)) where
  variableImage := MvPolynomial.X

theorem coordinateRestriction_polynomialMap {X Y : S.category}
    (f : X ⟶ Y) :
    (coordinateRestriction f).polynomialMap =
      RingHom.id (FreeTypedCommAlg (coordFamily X) ℤ) := by
  apply MvPolynomial.ringHom_ext
  · intro value
    simp [TypedCoordinateRestriction.polynomialMap]
  · intro coordinate
    rw [TypedCoordinateRestriction.polynomialMap_X]
    rfl

def restrictionStable {X Y : S.category} (f : X ⟶ Y) :
    RestrictionStableStructuralRelations (relationFamily X)
      (relationFamily Y)
      (S.contextPreorder.morphism (CategoryTheory.leOfHom f)) where
  restriction := coordinateRestriction f
  maps_JStruct := by
    intro polynomial hpolynomial
    rw [coordinateRestriction_polynomialMap]
    exact hpolynomial

/-- A lawful raw restriction system with two globally fixed coordinate
variables. -/
def system : RawAmbientRestrictionSystem S ℤ where
  coordFamily := coordFamily
  relationFamily := relationFamily
  restrictionStable := restrictionStable
  identity_polynomialMap W := coordinateRestriction_polynomialMap (X := W) (Y := W) (𝟙 W)
  composition_polynomialMap f g := by
    change (coordinateRestriction (f ≫ g)).polynomialMap =
      ((coordinateRestriction f).polynomialMap).comp
        ((coordinateRestriction g).polynomialMap)
    rw [coordinateRestriction_polynomialMap,
      coordinateRestriction_polynomialMap,
      coordinateRestriction_polynomialMap]
    exact (RingHom.id_comp _).symm

/-- Boolean negation as a coordinate equivalence. -/
def swapEquiv : Bool ≃ Bool where
  toFun := Bool.not
  invFun := Bool.not
  left_inv b := by cases b <;> rfl
  right_inv b := by cases b <;> rfl

/-- Swap the two coordinate names and keep their dependent one-point data. -/
def swapCoordinate (W : S.category) :
    CoordinateFamilyExactEquiv (coordFamily W) (coordFamily W) where
  coordinateEquiv := swapEquiv
  label_eq := fun _ => rfl
  localDataEquiv := fun _ => Equiv.refl PUnit

/-- The coordinate swap is a lawful raw automorphism with identity coefficient
map and identity context functor. -/
def swapMap : RawAmbientRestrictionSystemExactMapAgainst S S (𝟭 S.category)
    (RingHom.id ℤ) system system where
  coordinate := swapCoordinate
  relation W := {
    relationEquiv := Equiv.refl PEmpty
    polynomial_eq := fun relation => PEmpty.elim relation
  }
  restriction_polynomial {W V} g polynomial := by
    change (swapCoordinate W).polynomialHom (RingHom.id ℤ)
        ((coordinateRestriction ((𝟭 S.category).map g)).polynomialMap polynomial) =
      (coordinateRestriction g).polynomialMap
        ((swapCoordinate V).polynomialHom (RingHom.id ℤ) polynomial)
    rw [coordinateRestriction_polynomialMap,
      coordinateRestriction_polynomialMap]
    rfl

end BoolRaw

/-- Geometry package used to separate raw coordinate action while every other
selected component is fixed. -/
def boolRawPackage : GeometryPackage.{0, 0} FiniteModel.carrier where
  core := GeometryTransport.FiniteGeometryWitness.package.core
  geometry := GeometryTransport.FiniteGeometryWitness.package.geometry
  Coefficient := ℤ
  coefficientCommRing := inferInstance
  raw := BoolRaw.system

/-- The nontrivial raw-coordinate automorphism with the same base, coverage,
overlap, coefficient, and realization components as the identity. -/
def boolRawSwapHom :
    ExplicitExactGeometryHom boolRawPackage boolRawPackage :=
  { ExplicitExactGeometryHom.id boolRawPackage with
    raw := BoolRaw.swapMap }

theorem boolRawSwapHom_base_eq :
    boolRawSwapHom.base =
      (ExplicitExactGeometryHom.id boolRawPackage).base := rfl

theorem boolRawSwapHom_coefficient_eq :
    boolRawSwapHom.coefficientHom =
      (ExplicitExactGeometryHom.id boolRawPackage).coefficientHom := rfl

/-- The two Homs have exactly the same object action. -/
theorem boolRawSwapHom_object_action_eq :
    boolRawSwapHom.base.upper.objectMap =
      (ExplicitExactGeometryHom.id boolRawPackage).base.upper.objectMap := rfl

/-- Swapping `false` and `true` makes the raw automorphism different from the
identity even though base and coefficient actions agree. -/
theorem boolRawSwapHom_ne_identity :
    boolRawSwapHom ≠ ExplicitExactGeometryHom.id boolRawPackage := by
  intro h
  let W : boolRawPackage.site.category :=
    ⟨axisFixtureContext boolRawPackage.core.object⟩
  have hv := congrArg
    (fun F => (F.raw.coordinate W).coordinateEquiv false) h
  change true = false at hv
  exact Bool.noConfusion hv

/-- One explicit common raw-coordinate query at the fixture context. -/
def boolRawSeparationQuery : Query.{0, 0} FiniteModel.carrier .explicit :=
  .atObjects boolRawPackage.core.object boolRawPackage.core.object
    (.raw (.coordinate .forward
      (axisFixtureContext boolRawPackage.core.object)
      (axisFixtureContext boolRawPackage.core.object)
      (.edge Bool Bool false true)))

/-- A common query separates the raw-coordinate swap from the identity while
their base/object and coefficient actions remain equal. -/
theorem boolRawSwapHom_distinct_query :
    NativeReader.readExplicit boolRawSwapHom boolRawSeparationQuery ≠
      NativeReader.readExplicit
        (ExplicitExactGeometryHom.id boolRawPackage) boolRawSeparationQuery := by
  simp only [boolRawSeparationQuery, NativeReader.readExplicit,
    NativeReader.readWith_dependent]
  have hinverse :
      ((coreContextInverse
          (PackageTotalHom.id GeometryTransport.FiniteGeometryWitness.package.core)).obj
        ⟨axisFixtureContext
          GeometryTransport.FiniteGeometryWitness.package.core.object⟩).ctx =
        axisFixtureContext
          GeometryTransport.FiniteGeometryWitness.package.core.object := rfl
  simp only [NativeReader.dependentRead, ExplicitRaw.readRaw,
    ExplicitRaw.readCoordinate, ExplicitRaw.inverse, boolRawSwapHom, BoolRaw.swapMap,
    BoolRaw.swapCoordinate, BoolRaw.swapEquiv, boolRawPackage,
    ExplicitExactGeometryHom.id,
    RawAmbientRestrictionSystemExactMapAgainst.refl,
    InverseRows.fromInverse, hinverse, if_pos,
    IndependentInverseGraph.read]
  intro h
  have hswap :
      IndependentCarrierGraph.read Bool Bool Bool.not
          (.edge Bool Bool false true) = true :=
    (IndependentCarrierGraph.read_edge Bool Bool Bool.not false true).2 rfl
  have hid :
      IndependentCarrierGraph.read Bool Bool (Equiv.refl Bool)
          (.edge Bool Bool false true) = true := h.symm.trans hswap
  exact Bool.noConfusion
    ((IndependentCarrierGraph.read_edge Bool Bool (Equiv.refl Bool)
      false true).1 hid)

end

end AAT.AG.LocalSemanticReconstruction.IndependentHomRefutations

#assert_standard_axioms_only AAT.AG.LocalSemanticReconstruction.IndependentHomRefutations
