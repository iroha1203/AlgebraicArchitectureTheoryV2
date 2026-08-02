import ResearchLean.AG.AtomFoundation.RefinementSupplyObstruction

/-!
# Concrete positive refinement-extension supply

The strict finite refinement already used for the exact-lift obstruction also
admits a different, generated target once genuinely new composition and
equation data are supplied.  This module constructs that lower-level supply,
derives the positive lift, and pairs it with the existing all-reject target for
which the same fixed-target supply predicate is false.
-/

namespace AAT.AG.AtomFoundation

open CategoryTheory

/-- Collapse the newly admitted component into an existing source component. -/
def refinementCollapseAtom : FiniteModel.carrier.Atom → FiniteModel.carrier.Atom
  | FiniteModel.FiniteAtom.componentC => FiniteModel.FiniteAtom.componentA
  | atom => atom

/-- The collapse map never returns the source-excluded component. -/
theorem refinementCollapseAtom_ne_componentC
    (atom : FiniteModel.carrier.Atom) :
    refinementCollapseAtom atom ≠ FiniteModel.FiniteAtom.componentC := by
  cases atom <;> simp [refinementCollapseAtom]

/-- The expanded strict-refinement family has an explicit finite enumeration. -/
theorem finiteExtractionRefinement_liftFamily_listFinite :
    (refinementLiftFamily refinementSourcePackage
      finiteExtractionRefinement).ListFinite := by
  exact ⟨FiniteModel.FiniteAtom.all,
    fun atom _hmem => FiniteModel.FiniteAtom.mem_all atom⟩

/--
Concrete operation from the expanded refinement base to the transported source
base.  Its only new action collapses `componentC` to `componentA`.
-/
noncomputable def finiteExtractionRefinement_baseOperation :
    (transportOperationReading finiteExtractionRefinement.atomEquiv
      refinementSourcePackage.reading.operationReading).Op
        (refinementLiftObject refinementSourcePackage finiteExtractionRefinement
          finiteExtractionRefinement_liftFamily_listFinite)
        (transportArchitectureObject finiteExtractionRefinement.atomEquiv
          refinementSourcePackage.object) := by
  refine {
    atomMap := refinementCollapseAtom
    maps_family := ?_
    maps_relation := ?_
    maps_identification := ?_
  }
  · intro atom _hmem
    have htarget :
        FiniteModel.allFamily.mem (refinementCollapseAtom atom) :=
      FiniteModel.allFamily_mem _
        (refinementCollapseAtom_ne_componentC atom)
    simpa only [transportArchitectureObject_equiv_symm] using htarget
  · intro atom₁ atom₂ hrelation
    cases atom₁ <;> cases atom₂ <;>
      simp_all [refinementLiftObject, refinementLiftConfiguration,
        refinementLiftFamily, refinementSourcePackage,
        FiniteModel.corePackage, FiniteModel.corePackageFor,
        AATCorePackage.generate, AATCorePackage.object,
        AATCorePackage.configuration, AATCorePackage.family,
        FiniteModel.coreReadingFor, finiteExtractionRefinement,
        refinementTargetDoctrine, refinementAtomMap, refinementAtomEquiv,
        FiniteModel.extractionDoctrine, ExtractionDoctrine.atomize,
        ExtractionDoctrine.extracts,
        transportObjectReading, transportArchitectureObject,
        transportCompositionReading, refinementCollapseAtom,
        FiniteModel.objectReading, FiniteModel.objectOfConfiguration,
        FiniteModel.compositionReading, FiniteModel.cycleRelation,
        FiniteModel.substitutionRelation]
  · intro atom₁ atom₂ hidentification
    cases atom₁ <;> cases atom₂ <;>
      simp_all [refinementLiftObject, refinementLiftConfiguration,
        refinementLiftFamily, refinementSourcePackage,
        FiniteModel.corePackage, FiniteModel.corePackageFor,
        AATCorePackage.generate, AATCorePackage.object,
        AATCorePackage.configuration, AATCorePackage.family,
        FiniteModel.coreReadingFor, finiteExtractionRefinement,
        refinementTargetDoctrine, refinementAtomMap, refinementAtomEquiv,
        FiniteModel.extractionDoctrine, ExtractionDoctrine.atomize,
        ExtractionDoctrine.extracts,
        transportObjectReading, transportArchitectureObject,
        transportCompositionReading, refinementCollapseAtom,
        FiniteModel.objectReading, FiniteModel.objectOfConfiguration,
        FiniteModel.compositionReading]

/-- The generated expanded object on which the positive equation supply lives. -/
noncomputable abbrev finiteExtractionRefinement_suppliedObject :
    ArchitectureObject FiniteModel.carrier :=
  refinementLiftObject refinementSourcePackage finiteExtractionRefinement
    finiteExtractionRefinement_liftFamily_listFinite

/-- The strict refinement fixes the first dependency Atom. -/
@[simp]
theorem finiteExtractionRefinement_atomEquiv_dependsAB :
    finiteExtractionRefinement.atomEquiv FiniteModel.FiniteAtom.dependsAB =
      FiniteModel.FiniteAtom.dependsAB := by
  classical
  rw [RefinementDoctrineHom.atomEquiv_apply]
  exact Equiv.swap_apply_of_ne_of_ne
    (by exact FiniteModel.FiniteAtom.noConfusion)
    (by exact FiniteModel.FiniteAtom.noConfusion)

/-- The strict refinement fixes the second dependency Atom. -/
@[simp]
theorem finiteExtractionRefinement_atomEquiv_dependsBC :
    finiteExtractionRefinement.atomEquiv FiniteModel.FiniteAtom.dependsBC =
      FiniteModel.FiniteAtom.dependsBC := by
  classical
  rw [RefinementDoctrineHom.atomEquiv_apply]
  exact Equiv.swap_apply_of_ne_of_ne
    (by exact FiniteModel.FiniteAtom.noConfusion)
    (by exact FiniteModel.FiniteAtom.noConfusion)

/-- The strict refinement fixes the third dependency Atom. -/
@[simp]
theorem finiteExtractionRefinement_atomEquiv_dependsCA :
    finiteExtractionRefinement.atomEquiv FiniteModel.FiniteAtom.dependsCA =
      FiniteModel.FiniteAtom.dependsCA := by
  classical
  rw [RefinementDoctrineHom.atomEquiv_apply]
  exact Equiv.swap_apply_of_ne_of_ne
    (by exact FiniteModel.FiniteAtom.noConfusion)
    (by exact FiniteModel.FiniteAtom.noConfusion)

/-- The strict refinement fixes every Atom occurring in the cycle detector. -/
@[simp]
theorem finiteExtractionRefinement_cycleQueryDatum_transport :
    FiniteModel.cycleQueryDatum.transport finiteExtractionRefinement.atomEquiv =
      FiniteModel.cycleQueryDatum := by
  classical
  apply FiniteCircuitDatum.ext
  change [
      (.relationPresent
        (finiteExtractionRefinement.atomEquiv FiniteModel.FiniteAtom.dependsAB)
        (finiteExtractionRefinement.atomEquiv FiniteModel.FiniteAtom.dependsBC), true),
      (.relationPresent
        (finiteExtractionRefinement.atomEquiv FiniteModel.FiniteAtom.dependsBC)
        (finiteExtractionRefinement.atomEquiv FiniteModel.FiniteAtom.dependsCA), true),
      (.relationPresent
        (finiteExtractionRefinement.atomEquiv FiniteModel.FiniteAtom.dependsCA)
        (finiteExtractionRefinement.atomEquiv FiniteModel.FiniteAtom.dependsAB), true)
    ] = FiniteModel.cycleQueryDatum.queries
  rw [finiteExtractionRefinement_atomEquiv_dependsAB,
    finiteExtractionRefinement_atomEquiv_dependsBC,
    finiteExtractionRefinement_atomEquiv_dependsCA]
  rfl

/-- A concrete readable context for the expanded strict-refinement object. -/
noncomputable def finiteExtractionRefinement_probeContext :
    Site.ArchCtx finiteExtractionRefinement_suppliedObject where
  minimal := {
    Support := PUnit
    Axis := PUnit
    Observable := PUnit
    supportReads := fun _ atom =>
      finiteExtractionRefinement_suppliedObject.configuration.family.mem atom
    supportReads_objectFamily := fun h => h
    axisReads := fun _ => True
    observableReads := fun _ => True
  }
  Extension := PUnit
  extension := PUnit.unit

/--
NoCycle equation semantics on the expanded strict-refinement object.

The residual is computed from the target object itself; it is not a lift or
acceptance certificate.
-/
noncomputable def finiteExtractionRefinement_equationSystem :
    ArchitecturalEquationSystem
      (Site.contextMorphismPreorderCategory
        finiteExtractionRefinement_suppliedObject) where
  Index := PUnit
  role _ := EquationRole.required
  Observable := fun _ => Int
  observableCommRing := fun _ => inferInstance
  restrict := fun _ => RingHom.id Int
  restrict_id := by intros; rfl
  restrict_comp := by intros; rfl
  violationCoordinate := fun _ _ _ => 2
  violationCoordinate_restrict := by intros; rfl
  equationResidual := fun _ A _ _ => FiniteModel.noCycleResidual A
  equationResidual_restrict := by intros; rfl

/-- The supplied target equation holds exactly on objects without the concrete cycle. -/
theorem finiteExtractionRefinement_equationHolds_iff_noCycle
    (A : ArchitectureObject FiniteModel.carrier) :
    finiteExtractionRefinement_equationSystem.EquationHolds PUnit.unit A ↔
      ¬ FiniteModel.hasDependencyCycle A := by
  constructor
  · intro hholds hcycle
    have hzero := hholds
      (Site.ContextCategoryObject.of
        (Site.contextMorphismPreorderCategory
          finiteExtractionRefinement_suppliedObject)
        finiteExtractionRefinement_probeContext)
      FiniteModel.FiniteAtom.componentA
    simp [finiteExtractionRefinement_equationSystem,
      FiniteModel.noCycleResidual, hcycle] at hzero
  · intro hnoCycle _context _atom
    simp [finiteExtractionRefinement_equationSystem,
      FiniteModel.noCycleResidual, FiniteModel.hasDependencyCycle] at hnoCycle ⊢
    exact hnoCycle

/-- The source package exposes the concrete exact cycle detector. -/
theorem refinementSourcePackage_circuit_code :
    refinementSourcePackage.algebra.circuits.code PUnit.unit =
      .exact FiniteModel.cycleQueryDatum := by
  simpa [refinementSourcePackage, FiniteModel.corePackage,
    FiniteModel.corePackageFor, FiniteModel.coreReading] using
      FiniteModel.coreReading_circuit_code PUnit.unit

/-- Canonically transported source detector syntax is sound for the supplied target equation. -/
theorem finiteExtractionRefinement_circuitSound :
    ({ code := fun index =>
        (refinementSourcePackage.algebra.circuits.code
          ((Equiv.refl PUnit).symm index)).transport
            finiteExtractionRefinement.atomEquiv }
      : EquationCircuitReading finiteExtractionRefinement_equationSystem).Sound := by
  intro index A datum hmatches haccepts
  cases index
  change
    ((refinementSourcePackage.algebra.circuits.code PUnit.unit).transport
      finiteExtractionRefinement.atomEquiv).eval datum = true at haccepts
  rw [refinementSourcePackage_circuit_code] at haccepts
  change
    (CircuitDetectorCode.exact
      (FiniteModel.cycleQueryDatum.transport
        finiteExtractionRefinement.atomEquiv)).eval datum = true at haccepts
  rw [finiteExtractionRefinement_cycleQueryDatum_transport] at haccepts
  have hdatum : FiniteModel.cycleQueryDatum = datum :=
    (CircuitDetectorCode.eval_exact_eq_true_iff
      FiniteModel.cycleQueryDatum datum).mp haccepts
  subst datum
  have hab :
      A.configuration.relation FiniteModel.FiniteAtom.dependsAB
        FiniteModel.FiniteAtom.dependsBC :=
    ((hmatches
      (.relationPresent FiniteModel.FiniteAtom.dependsAB
        FiniteModel.FiniteAtom.dependsBC) true
      (by simp [FiniteModel.cycleQueryDatum])).mpr rfl).2.2
  have hbc :
      A.configuration.relation FiniteModel.FiniteAtom.dependsBC
        FiniteModel.FiniteAtom.dependsCA :=
    ((hmatches
      (.relationPresent FiniteModel.FiniteAtom.dependsBC
        FiniteModel.FiniteAtom.dependsCA) true
      (by simp [FiniteModel.cycleQueryDatum])).mpr rfl).2.2
  have hca :
      A.configuration.relation FiniteModel.FiniteAtom.dependsCA
        FiniteModel.FiniteAtom.dependsAB :=
    ((hmatches
      (.relationPresent FiniteModel.FiniteAtom.dependsCA
        FiniteModel.FiniteAtom.dependsAB) true
      (by simp [FiniteModel.cycleQueryDatum])).mpr rfl).2.2
  intro hequation
  exact (finiteExtractionRefinement_equationHolds_iff_noCycle A).mp
    hequation ⟨hab, hbc, hca⟩

/-- Lower-level equation-system supply for the strict finite refinement. -/
noncomputable def finiteExtractionRefinement_equationSupply :
    RefinementEquationSupply refinementSourcePackage finiteExtractionRefinement
      finiteExtractionRefinement_liftFamily_listFinite where
  equationSystem := finiteExtractionRefinement_equationSystem
  indexEquiv := Equiv.refl PUnit
  circuitSound := finiteExtractionRefinement_circuitSound

/-- Concrete lower-level composition and equation supply for the strict refinement. -/
noncomputable def finiteExtractionRefinement_extensionSupply :
    RefinementExtensionSupply refinementSourcePackage finiteExtractionRefinement where
  targetFamily_listFinite :=
    finiteExtractionRefinement_liftFamily_listFinite
  baseOperation := finiteExtractionRefinement_baseOperation
  equationSupply := finiteExtractionRefinement_equationSupply

/-- Target package generated from the strict refinement and its concrete supply. -/
noncomputable def finiteExtractionRefinement_suppliedPackage :
    AATCorePackage FiniteModel.carrier :=
  refinementPackageOfSupply refinementSourcePackage finiteExtractionRefinement
    finiteExtractionRefinement_extensionSupply

/-- The generated positive target satisfies the fixed-target supply predicate. -/
theorem finiteExtractionRefinement_hasExtensionSupply :
    HasRefinementExtensionSupply refinementSourcePackage
      finiteExtractionRefinement_suppliedPackage finiteExtractionRefinement :=
  ⟨finiteExtractionRefinement_extensionSupply, rfl⟩

/-- The satisfying supply instance generates an actual positive refinement lift. -/
theorem finiteExtractionRefinement_hasPositiveLift :
    ∃ F : PositiveCoreReadingHom refinementSourcePackage
        finiteExtractionRefinement_suppliedPackage,
      F.atomMap = finiteExtractionRefinement.atomMap :=
  HasRefinementExtensionSupply.lift refinementSourcePackage
    finiteExtractionRefinement_suppliedPackage finiteExtractionRefinement
    finiteExtractionRefinement_hasExtensionSupply

/-- The supplied target equation index is concretely inhabited. -/
theorem finiteExtractionRefinement_suppliedIndex_nonempty :
    Nonempty
      finiteExtractionRefinement_suppliedPackage.algebra.equationSystem.Index :=
  ⟨PUnit.unit⟩

/-- The transported cycle datum matches the reachable transported source object. -/
theorem finiteExtractionRefinement_transportedCycle_matches :
    (refinementQueryMap finiteExtractionRefinement
      FiniteModel.cycleQueryDatum).Matches
        (transportArchitectureObject finiteExtractionRefinement.atomEquiv
          refinementSourcePackage.object) := by
  exact refinementQueryMap_matches finiteExtractionRefinement
    FiniteModel.cycleQueryDatum refinementSourcePackage.object
    FiniteModel.cycleQueryDatum_matches_core

/-- The generated target detector accepts the transported concrete cycle datum. -/
theorem finiteExtractionRefinement_transportedCycle_accepted :
    finiteExtractionRefinement_suppliedPackage.algebra.circuits.accepts
        PUnit.unit
        (refinementQueryMap finiteExtractionRefinement
          FiniteModel.cycleQueryDatum) = true := by
  simpa [finiteExtractionRefinement_suppliedPackage,
    finiteExtractionRefinement_extensionSupply,
    finiteExtractionRefinement_equationSupply,
    refinementPackageOfSupply, refinementCoreReadingOfSupply,
    refinementEquationReadingOfSupply] using
      refinementQueryMap_accepts refinementSourcePackage
        finiteExtractionRefinement finiteExtractionRefinement_extensionSupply
        PUnit.unit FiniteModel.cycleQueryDatum
        FiniteModel.cycleQueryDatum_accepted

end AAT.AG.AtomFoundation

#assert_standard_axioms_only AAT.AG.AtomFoundation
