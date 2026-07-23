import Formal.AG.LawAlgebra.RawPresheafFiniteExample

noncomputable section

/-!
# Finite atom-to-ringed-site firing example

This module selects a three-patch coverage on the existing finite context
preorder.  Support is read on the left and right patches, witnesses are read
on a selected patch, and signature axes are read on the base patch.  The
boundary and axis clauses force every admissible family to contain the base
identity patch, so the generated Grothendieck topology is bottom.

The bottom-topology equivalence supplies the concrete Mathlib sheafification
adjunction.  The example's nontrivial data comes from the existing `Int`-valued
raw quotient system: its nonzero structural equation and nonidentity descended
restriction are retained when that system is retargeted to the new selected
site sharing the same context category.
-/

namespace AAT.AG.LawAlgebra.FiniteExamples.RingedSite

open CategoryTheory

namespace FiniteModel

open AAT.AG.FiniteModel

/-- R6: support selected for the concrete ringed-site firing example. -/
def supportVisibleOn (W : Site.ArchCtx object) (atom : carrier.Atom) : Prop :=
  (W = twoPatchContext TwoPatchContextIndex.left ∧ atom = FiniteAtom.componentA) ∨
    (W = twoPatchContext TwoPatchContextIndex.right ∧ atom = FiniteAtom.componentB)

/-- R6: coverage requirements whose admissible families must contain the base patch. -/
def coverageRequirements :
    Site.CoverageRequirements object twoPatchCorePackage.equationSystem signature where
  requiredSupport := fun atom =>
    atom = FiniteAtom.componentA ∨ atom = FiniteAtom.componentB
  requiredEquationCoordinate := fun _ => True
  selectedViolationWitness := fun _ => True
  requiredAxis := fun _ => True
  supportVisibleOn := supportVisibleOn
  equationCoordinateVisibleOn := fun W _ =>
    W = twoPatchContext TwoPatchContextIndex.left ∨
      W = twoPatchContext TwoPatchContextIndex.right
  violationWitnessVisibleOn := fun W _ =>
    W = twoPatchContext TwoPatchContextIndex.left ∨
      W = twoPatchContext TwoPatchContextIndex.right
  axisReadableOn := fun W _ => W = twoPatchContext TwoPatchContextIndex.base
  boundaryVisibleOn := fun _ base =>
    base = twoPatchContext TwoPatchContextIndex.base

/-- R6: the selected geometry uses the same generated core and finite context preorder. -/
noncomputable def selectedGeometryReading :
    Site.SelectedGeometryReading twoPatchCorePackage where
  requirements := coverageRequirements
  overlap := twoPatchOverlap

/-- R6: the finite AAT site selected for the concrete ringed presentation. -/
noncomputable abbrev site : Site.AATSite twoPatchCorePackage.object :=
  selectedGeometryReading.toAATSite

/-- Every equation in the generated singleton ringed-site fixture is required. -/
theorem site_equation_required (index : site.equationSystem.Index) :
    site.equationSystem.Required index := by
  cases index
  rfl

/-- Residual vanishing on the generated ringed-site equation is NoCycle. -/
@[simp] theorem site_equationHolds_iff_noCycleLaw
    (A : ArchitectureObject carrier) :
    site.equationSystem.EquationHolds PUnit.unit A ↔ noCycleLaw.holds A := by
  change (equationSystem twoPatchContextPreorder).EquationHolds PUnit.unit A ↔
    noCycleLaw.holds A
  exact equationHolds_iff_noCycleLaw twoPatchContextPreorder A

/-- The generated compatibility law of the ringed-site fixture is NoCycle. -/
@[simp] theorem site_law_eq_noCycleLaw :
    site.equationSystem.toLegacyLawUniverse.law PUnit.unit = noCycleLaw := by
  change (equationSystem twoPatchContextPreorder).toLegacyLawUniverse.law
    PUnit.unit = noCycleLaw
  exact equationSystem_legacy_law_eq_noCycleLaw twoPatchContextPreorder

/-- R6: the concrete base object. -/
def base : site.category :=
  Site.ContextCategoryObject.of twoPatchContextPreorder
    (twoPatchContext TwoPatchContextIndex.base)

/-- R6: left, right, and base patches of the selected admissible family. -/
inductive CoverIndex where
  | left
  | right
  | base
  deriving DecidableEq

/-- Context selected by each concrete cover index. -/
def coverContextIndex : CoverIndex → TwoPatchContextIndex
  | CoverIndex.left => TwoPatchContextIndex.left
  | CoverIndex.right => TwoPatchContextIndex.right
  | CoverIndex.base => TwoPatchContextIndex.base

/-- Context selected by each concrete cover index. -/
def coverPatch (i : CoverIndex) : Site.ArchCtx object :=
  twoPatchContext (coverContextIndex i)

/-- R6: the selected three-patch admissible family. -/
noncomputable def cover :
    Site.AATCoverageFamily coverageRequirements twoPatchOverlap base where
  Index := CoverIndex
  patch := coverPatch
  inclusion := by
    intro i
    exact twoPatchContextLe_sound (by
      cases i <;> simp [coverContextIndex, twoPatchContextIndexLe])
  admissible := {
    atomSupportCoverage := by
      intro atom hreq
      rcases hreq with rfl | rfl
      · exact ⟨CoverIndex.left, by
          simp [coverPatch, coverContextIndex, coverageRequirements, supportVisibleOn]⟩
      · exact ⟨CoverIndex.right, by
          simp [coverPatch, coverContextIndex, coverageRequirements, supportVisibleOn]⟩
    equationCoordinateCoverage := by
      intro _ _
      exact Or.inl ⟨CoverIndex.left, by
        simp [coverPatch, coverContextIndex, coverageRequirements]⟩
    violationWitnessCoverage := by
      intro _ _
      exact Or.inl ⟨CoverIndex.left, by
        simp [coverPatch, coverContextIndex, coverageRequirements]⟩
    signatureAxisCoverage := by
      intro _ _
      exact ⟨CoverIndex.base, by
        simp [coverPatch, coverContextIndex, coverageRequirements]⟩
    boundaryCoverage := by
      intro _ _
      change base.ctx = twoPatchContext TwoPatchContextIndex.base
      rfl
    nonGeneration := by
      intro _ _ _ hselected
      exact AAT.AG.FiniteModel.allFamily_mem _ hselected
  }

/-- Every admissible family has the concrete base as its base context. -/
theorem admissible_base_eq
    {X : site.category}
    (F : Site.AATCoverageFamily coverageRequirements twoPatchOverlap X) :
    X.ctx = twoPatchContext TwoPatchContextIndex.base := by
  rcases F.admissible.signatureAxisCoverage PUnit.unit trivial with ⟨i, hi⟩
  have := F.admissible.boundaryCoverage i i
  simpa [coverageRequirements] using this

/-- Every admissible family contains a patch equal to the concrete base context. -/
theorem admissible_has_base_patch
    {X : site.category}
    (F : Site.AATCoverageFamily coverageRequirements twoPatchOverlap X) :
    ∃ i : F.Index, F.patch i = twoPatchContext TwoPatchContextIndex.base := by
  rcases F.admissible.signatureAxisCoverage PUnit.unit trivial with ⟨i, hi⟩
  exact ⟨i, by simpa [coverageRequirements] using hi⟩

/-- Every admissible presieve contains the identity of its base. -/
theorem admissible_presieve_identity
    {X : site.category}
    (F : Site.AATCoverageFamily coverageRequirements twoPatchOverlap X) :
    F.presieve (𝟙 X) := by
  rcases admissible_has_base_patch F with ⟨i, hi⟩
  have hctx : X.ctx = F.patch i := (admissible_base_eq F).trans hi.symm
  have hobj : X = Site.ContextCategoryObject.of twoPatchContextPreorder (F.patch i) := by
    cases X
    simp only [Site.ContextCategoryObject.of] at hctx ⊢
    congr
  exact Presieve.ofArrows.mk' i hobj (Subsingleton.elim _ _)

/-- Every admissible presieve generates the top sieve. -/
theorem admissible_generate_eq_top
    {X : site.category}
    (F : Site.AATCoverageFamily coverageRequirements twoPatchOverlap X) :
    Sieve.generate F.presieve = ⊤ :=
  Sieve.generate_of_contains_isSplitEpi (𝟙 X) (admissible_presieve_identity F)

/-- The concrete three-patch family is a member of the selected precoverage. -/
theorem cover_mem_precoverage :
    cover.presieve ∈ Site.admissiblePrecoverage coverageRequirements twoPatchOverlap base :=
  ⟨cover, rfl⟩

/-- The concrete cover generates the top sieve because its base patch is the identity. -/
theorem cover_generate_eq_top : Sieve.generate cover.presieve = ⊤ :=
  admissible_generate_eq_top cover

/-- The left patch discharges the selected `componentA` support requirement. -/
theorem cover_reads_componentA :
    ∃ i : cover.Index,
      coverageRequirements.supportVisibleOn (cover.patch i) FiniteAtom.componentA :=
  cover.admissible.atomSupportCoverage FiniteAtom.componentA (Or.inl rfl)

/-- The right patch discharges the selected `componentB` support requirement. -/
theorem cover_reads_componentB :
    ∃ i : cover.Index,
      coverageRequirements.supportVisibleOn (cover.patch i) FiniteAtom.componentB :=
  cover.admissible.atomSupportCoverage FiniteAtom.componentB (Or.inr rfl)

/-- The base patch is proof-used to discharge the selected signature axis. -/
theorem cover_reads_axis_at_base :
    coverageRequirements.axisReadableOn
      (cover.patch CoverIndex.base) PUnit.unit := by
  simp [cover, coverPatch, coverContextIndex, coverageRequirements]

/-- The left patch discharges every selected witness requirement. -/
theorem cover_reads_witness_on_left
    (witness : twoPatchCorePackage.equationSystem.Coordinate) :
    coverageRequirements.violationWitnessVisibleOn
      (cover.patch CoverIndex.left) witness := by
  simp [cover, coverPatch, coverContextIndex, coverageRequirements]

/-- R6: every selected admissible family generates top, so the generated topology is bottom. -/
theorem site_topology_eq_bot : site.topology = ⊥ := by
  rw [Site.SelectedGeometryReading.topology_eq_generated selectedGeometryReading,
    Site.AATGrothendieckTopology, Precoverage.toGrothendieck_eq_sInf]
  apply le_antisymm
  · apply sInf_le
    intro X S hS
    rw [GrothendieckTopology.bot_covering]
    rcases hS with ⟨F, rfl⟩
    exact admissible_generate_eq_top F
  · exact bot_le

/-- R6: sheafification on the selected site is obtained from the bottom-topology equivalence. -/
noncomputable instance hasSheafify :
    HasSheafify site.topology (AATCommAlgCat Int) := by
  rw [site_topology_eq_bot]
  exact HasSheafify.mk' _ _
    (sheafBotEquivalence (AATCommAlgCat Int)).symm.toAdjunction

/-- The existing finite raw restriction system is typed by the same selected context category. -/
def rawSystem : RawAmbientRestrictionSystem site Int :=
  { coordFamily := RawPresheaf.coordFamily
    relationFamily := RawPresheaf.relationFamily
    restrictionStable := RawPresheaf.restrictionStable
    identity_polynomialMap := RawPresheaf.system.identity_polynomialMap
    composition_polynomialMap := RawPresheaf.system.composition_polynomialMap }

/-- The retargeted system has exactly the existing finite coordinate family. -/
theorem rawSystem_coordFamily : rawSystem.coordFamily = RawPresheaf.system.coordFamily :=
  rfl

/-- The retargeted system has exactly the existing finite structural relations. -/
theorem rawSystem_relationFamily :
    HEq rawSystem.relationFamily RawPresheaf.system.relationFamily :=
  HEq.rfl

/-- Each retargeted restriction is the existing finite restriction. -/
theorem rawSystem_restrictionStable
    {X Y : site.category} (f : X ⟶ Y) :
    rawSystem.restrictionStable f = RawPresheaf.system.restrictionStable f :=
  rfl

/-- Retargeting preserves the existing finite algebra-valued presheaf as a whole. -/
theorem rawSystem_toPresheaf_eq_existing :
    rawSystem.toPresheaf = RawPresheaf.system.toPresheaf :=
  rfl

/-- The selected coefficient ring has distinct zero and one. -/
theorem coefficientNontrivial : Nontrivial Int := inferInstance

/-- The selected left patch and base are distinct context objects. -/
theorem left_ne_base : RawPresheaf.left ≠ base := by
  intro h
  have hctx := congrArg Site.ContextCategoryObject.ctx h
  have heq := congrArg
    (fun W : Site.ArchitectureContext corePackage.object =>
      (⟨W.Extension, W.extension⟩ : Sigma fun T : Type => T)) hctx
  injection heq with _ hindex
  exact TwoPatchContextIndex.noConfusion hindex

/-- The selected nonzero equation is killed by the concrete quotient. -/
theorem raw_relation_vanishes :
    (rawSystem.relationFamily RawPresheaf.left).quotientMap
      (MvPolynomial.X () ^ 2 - 1) = 0 :=
  RawPresheaf.relation_vanishes

/-- The selected equation is nonzero before passage to the quotient. -/
theorem raw_relation_polynomial_ne_zero :
    (MvPolynomial.X () ^ 2 - 1 :
      FreeTypedCommAlg (rawSystem.coordFamily RawPresheaf.left) Int) ≠ 0 :=
  RawPresheaf.relation_polynomial_ne_zero

/-- The selected quotient map is not injective. -/
theorem raw_quotientMap_not_injective :
    ¬ Function.Injective
      (rawSystem.relationFamily RawPresheaf.left).quotientMap :=
  RawPresheaf.quotientMap_not_injective

/-- The descended left-to-base restriction changes the selected coordinate class. -/
theorem raw_leftToBase_quotientDesc_X_ne_X :
    (rawSystem.restrictionStable RawPresheaf.leftToBase).quotientDesc
        ((rawSystem.relationFamily base).quotientMap (MvPolynomial.X ())) ≠
      (rawSystem.relationFamily RawPresheaf.left).quotientMap (MvPolynomial.X ()) :=
  RawPresheaf.leftToBase_quotientDesc_X_ne_X

/-- The actual finite detector accepts the selected signed query datum. -/
theorem detector_accepts :
    coreReading.equationReading.circuits.accepts
      PUnit.unit cycleQueryDatum = true :=
  cycleQueryDatum_accepted

/-- The same detector rejects a distinct empty datum. -/
theorem detector_rejects :
    coreReading.equationReading.circuits.accepts
      PUnit.unit ⟨[]⟩ = false :=
  emptyQueryDatum_rejected

/-- Soundness of the accepted detector datum produces the generated law failure. -/
theorem detector_sound :
    ¬ corePackage.algebra.equationSystem.EquationHolds PUnit.unit
      (corePackage.algebra.object corePackage.baseObject) :=
  generatedCycleCircuit_sound

/-- A distinct law reading has a nonempty circuit fiber on the same generated object. -/
theorem second_circuit_fiber_nonempty :
    Nonempty (completeCircuitReading.Circuit corePackage.object PUnit.unit) :=
  completeCircuitReading_nonvacuous.2

/-- The actual configuration morphism sends one selected atom to a distinct atom. -/
theorem operation_atomMap_nonidentity :
    (corePackage.algebra.configurationMap collapseOperation).atomMap
        FiniteAtom.componentA = FiniteAtom.componentB ∧
      FiniteAtom.componentA ≠ FiniteAtom.componentB :=
  collapseOperation_atomMap_nonidentity

/-- The same configuration morphism transports selected family membership. -/
theorem operation_transports_family :
    collapsedObject.configuration.family.mem
      ((corePackage.algebra.configurationMap collapseOperation).atomMap
        FiniteAtom.componentA) :=
  collapseOperation_transports_family

/-- The same configuration morphism transports a selected relation. -/
theorem operation_transports_relation :
    collapsedObject.configuration.relation
      ((corePackage.algebra.configurationMap collapseOperation).atomMap
        FiniteAtom.dependsAB)
      ((corePackage.algebra.configurationMap collapseOperation).atomMap
        FiniteAtom.dependsBC) :=
  collapseOperation_transports_relation

/-- The same configuration morphism transports a selected identification. -/
theorem operation_transports_identification :
    collapsedObject.configuration.identification
      ((corePackage.algebra.configurationMap collapseOperation).atomMap
        FiniteAtom.componentA)
      ((corePackage.algebra.configurationMap collapseOperation).atomMap
        FiniteAtom.componentB) :=
  collapseOperation_transports_identification

/-- The nonidentity configuration morphism belongs to the generated reachable object algebra. -/
theorem reachable_nonidentity_operation :
    ∃ A B : corePackage.algebra.Obj,
      A ≠ B ∧ Nonempty (corePackage.algebra.Op A B) :=
  nonidentity_reachable_operation_fires

/-- R6: concrete end-to-end generation from atoms and laws to a ringed AAT site. -/
noncomputable def ringedSite : RingedAATSite site Int :=
  generateRingedAATSite AAT.AG.FiniteModel.axiomSystem
    AAT.AG.FiniteModel.coreReading selectedGeometryReading Int rawSystem

/-- The concrete presentation stays on the selected finite site. -/
@[simp]
theorem ringedSite_site : ringedSite.site = site :=
  generateRingedAATSite_site AAT.AG.FiniteModel.axiomSystem
    AAT.AG.FiniteModel.coreReading selectedGeometryReading Int rawSystem

/-- The concrete presentation retains the finite quotient-valued raw presheaf. -/
@[simp]
theorem ringedSite_raw : ringedSite.raw = rawSystem.toPresheaf :=
  generateRingedAATSite_raw AAT.AG.FiniteModel.axiomSystem
    AAT.AG.FiniteModel.coreReading selectedGeometryReading Int rawSystem

/-- The concrete ringed presentation directly exposes the existing finite raw presheaf. -/
theorem ringedSite_raw_eq_existing :
    ringedSite.raw = RawPresheaf.system.toPresheaf := by
  rw [ringedSite_raw, rawSystem_toPresheaf_eq_existing]

/-- Its structure sheaf is the Mathlib sheafification of that raw presheaf. -/
@[simp]
theorem ringedSite_structureSheaf :
    ringedSite.structureSheaf =
      (presheafToSheaf site.topology (AATCommAlgCat Int)).obj rawSystem.toPresheaf :=
  generateRingedAATSite_structureSheaf AAT.AG.FiniteModel.axiomSystem
    AAT.AG.FiniteModel.coreReading selectedGeometryReading Int rawSystem

/-- Its canonical morphism is the Mathlib sheafification unit. -/
@[simp]
theorem ringedSite_canonical :
    ringedSite.canonical = toSheafify site.topology rawSystem.toPresheaf :=
  generateRingedAATSite_canonical AAT.AG.FiniteModel.axiomSystem
    AAT.AG.FiniteModel.coreReading selectedGeometryReading Int rawSystem

/-- The generated presentation carries the architecture object generated from the same atoms. -/
@[simp]
theorem ringedSite_architectureObject :
    ringedSite.architectureObject =
      (AATCorePackage.generate AAT.AG.FiniteModel.axiomSystem
        AAT.AG.FiniteModel.coreReading).object :=
  generateRingedAATSite_architectureObject AAT.AG.FiniteModel.axiomSystem
    AAT.AG.FiniteModel.coreReading selectedGeometryReading Int rawSystem

end FiniteModel

end AAT.AG.LawAlgebra.FiniteExamples.RingedSite
