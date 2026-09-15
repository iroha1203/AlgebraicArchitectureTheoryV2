import ResearchLean.AG.RealizationReconstruction.FiniteAxisFoldResidualCoreRigidity
import Formal.Util.AssertStandardAxioms

/-!
# Atom rigidity of the finite-axis-fold support and actual endpoint

This module analyzes the primitive Atom equivalence of an arbitrary exact
endomorphism of the fixed support package.  The fixed ordered identification
and detector readings, the asymmetric substitution graph, and bijectivity fix
all nine Atoms pointwise; no finite Atom symmetry is inserted as a semantic
input.  It then computes those same readings through the fixed exact left-pull
and top-transport construction, proves arbitrary exact endomorphisms of the
actual direct endpoint Atom-trivial, and applies that stronger result to every
element of the residual axis-and-signature kernel.
-/

namespace AAT.AG.RealizationReconstruction

open CategoryTheory AtomFoundation DoctrineFiberProduct GeometryTransport
open TransportCoherence FullGeometryNormalization CrossStageCoherence

noncomputable section

local instance finiteAxisFoldResidualAtomDecidableEq :
    DecidableEq FiniteModel.carrier.Atom := by
  change DecidableEq FiniteModel.FiniteAtom
  infer_instance

private theorem finiteAxisFoldSupport_componentIdentification
    (hom : SignedExactCoreReadingHom finiteAxisFoldSupportPackage
      finiteAxisFoldSupportPackage) :
    (finiteAxisFoldSupportPackage.reading.composition.compose
      (FiniteModel.allFamily.transport hom.atomEquiv)
      (FiniteModel.allFamily_listFinite.transport hom.atomEquiv)).identification
        (hom.atomEquiv FiniteModel.FiniteAtom.componentA)
        (hom.atomEquiv FiniteModel.FiniteAtom.componentB) := by
  rw [hom.composition_eq FiniteModel.allFamily FiniteModel.allFamily_listFinite]
  exact ⟨FiniteModel.FiniteAtom.componentA,
    FiniteModel.FiniteAtom.componentB, by
      simp [finiteAxisFoldSupportPackage, transportAlong, transportCoreReading,
        finiteWitnessSourcePackage, finiteWitnessSourceReading,
        transportCompositionReading, finiteModelDoctrineFromFixture,
        AATCorePackage.generate, FiniteModel.coreReading,
        FiniteModel.coreReadingFor, FiniteModel.compositionReading,
        AtomConfiguration.transport, FiniteModel.allFamily]
      exact ⟨FiniteModel.allFamily_mem _ (by simp),
        FiniteModel.allFamily_mem _ (by simp)⟩,
    rfl, rfl⟩

private noncomputable def finiteAxisFoldSupportEquationIndex :
    finiteAxisFoldSupportPackage.algebra.equationSystem.Index :=
  (transportAlongUpper finiteWitnessSourcePackage
    finiteModelDoctrineFromFixture).equationMap PUnit.unit

private theorem finiteAxisFoldSupportEquationIndex_unique
  (i : finiteAxisFoldSupportPackage.algebra.equationSystem.Index) :
    i = finiteAxisFoldSupportEquationIndex := by
  apply (transportAlongUpper finiteWitnessSourcePackage
    finiteModelDoctrineFromFixture).equationTransport.equationEquiv.symm.injective
  change PUnit.unit = PUnit.unit
  rfl

private theorem finiteAxisFoldSupport_detectorCode :
    finiteAxisFoldSupportPackage.algebra.circuits.code
        finiteAxisFoldSupportEquationIndex =
      .exact FiniteModel.cycleQueryDatum := by
  have h := transportAlong_detectorCode_eq
    finiteWitnessSourcePackage finiteModelDoctrineFromFixture PUnit.unit
  simpa [finiteAxisFoldSupportPackage, finiteWitnessSourcePackage,
    finiteWitnessSourceReading, FiniteModel.coreReading,
    FiniteModel.coreReadingFor, FiniteModel.equationReading,
    FiniteModel.equationCircuitReading, finiteModelDoctrineFromFixture] using h

private theorem finiteAxisFoldSupport_detectorCode_all
    (i : finiteAxisFoldSupportPackage.algebra.equationSystem.Index) :
    finiteAxisFoldSupportPackage.algebra.circuits.code i =
      .exact FiniteModel.cycleQueryDatum := by
  rw [finiteAxisFoldSupportEquationIndex_unique i,
    finiteAxisFoldSupport_detectorCode]

private theorem finiteAxisFoldSupport_cycleQueryDatum_transport
    (hom : SignedExactCoreReadingHom finiteAxisFoldSupportPackage
      finiteAxisFoldSupportPackage) :
    FiniteModel.cycleQueryDatum.transport hom.atomEquiv =
      FiniteModel.cycleQueryDatum := by
  have h := hom.detectorCode_eq finiteAxisFoldSupportEquationIndex
  rw [finiteAxisFoldSupport_detectorCode] at h
  rw [finiteAxisFoldSupportEquationIndex_unique
    (hom.equationTransport.equationMap finiteAxisFoldSupportEquationIndex),
    finiteAxisFoldSupport_detectorCode] at h
  exact (CircuitDetectorCode.exact.inj
    (by simpa [CircuitDetectorCode.transport] using h)).symm

private theorem finiteAxisFoldSupport_detector_fixes
    (hom : SignedExactCoreReadingHom finiteAxisFoldSupportPackage
      finiteAxisFoldSupportPackage) :
    hom.atomEquiv FiniteModel.FiniteAtom.dependsAB =
        FiniteModel.FiniteAtom.dependsAB ∧
      hom.atomEquiv FiniteModel.FiniteAtom.dependsBC =
        FiniteModel.FiniteAtom.dependsBC ∧
      hom.atomEquiv FiniteModel.FiniteAtom.dependsCA =
        FiniteModel.FiniteAtom.dependsCA := by
  have h := congrArg FiniteCircuitDatum.queries
    (finiteAxisFoldSupport_cycleQueryDatum_transport hom)
  simp [FiniteModel.cycleQueryDatum, FiniteCircuitDatum.transport,
    CircuitQuery.transport] at h
  exact ⟨h.1.1, h.1.2, h.2.1.2⟩

private theorem finiteAxisFoldSupport_preserves_relation
    (hom : SignedExactCoreReadingHom finiteAxisFoldSupportPackage
      finiteAxisFoldSupportPackage)
    {a b : FiniteModel.FiniteAtom}
    (hab : FiniteModel.cycleRelation a b ∨
      FiniteModel.substitutionRelation a b) :
    FiniteModel.cycleRelation (hom.atomEquiv a) (hom.atomEquiv b) ∨
      FiniteModel.substitutionRelation (hom.atomEquiv a) (hom.atomEquiv b) := by
  have hcomp := hom.composition_eq
    FiniteModel.allFamily FiniteModel.allFamily_listFinite
  have hr :
      ((finiteAxisFoldSupportPackage.reading.composition.compose
        FiniteModel.allFamily FiniteModel.allFamily_listFinite).transport
          hom.atomEquiv).relation (hom.atomEquiv a) (hom.atomEquiv b) := by
    refine ⟨a, b, ?_, rfl, rfl⟩
    simp [finiteAxisFoldSupportPackage, transportAlong, transportCoreReading,
      finiteWitnessSourcePackage, finiteWitnessSourceReading,
      transportCompositionReading, finiteModelDoctrineFromFixture,
      AATCorePackage.generate, FiniteModel.coreReading,
      FiniteModel.coreReadingFor, FiniteModel.compositionReading,
      AtomConfiguration.transport, AtomFamily.transport,
      FiniteModel.allFamily]
    refine ⟨hab, ?_⟩
    cases a <;> cases b <;>
      simp_all [FiniteModel.cycleRelation, FiniteModel.substitutionRelation,
        FiniteModel.extractionDoctrine, ExtractionDoctrine.atomize,
        ExtractionDoctrine.extracts]
  rw [← hcomp] at hr
  simp [finiteAxisFoldSupportPackage, transportAlong, transportCoreReading,
    finiteWitnessSourcePackage, finiteWitnessSourceReading,
    transportCompositionReading, finiteModelDoctrineFromFixture,
    AATCorePackage.generate, FiniteModel.coreReading,
    FiniteModel.coreReadingFor, FiniteModel.compositionReading,
    AtomConfiguration.transport, AtomFamily.transport,
    FiniteModel.allFamily] at hr
  exact hr.1

set_option maxHeartbeats 800000 in
private theorem finiteAxisFoldSupport_substitution_fixes
    (hom : SignedExactCoreReadingHom finiteAxisFoldSupportPackage
      finiteAxisFoldSupportPackage) :
    hom.atomEquiv FiniteModel.FiniteAtom.substitutesImplBase =
        FiniteModel.FiniteAtom.substitutesImplBase ∧
      hom.atomEquiv FiniteModel.FiniteAtom.contractImpl =
        FiniteModel.FiniteAtom.contractImpl ∧
      hom.atomEquiv FiniteModel.FiniteAtom.contractBase =
        FiniteModel.FiniteAtom.contractBase := by
  let e := hom.atomEquiv
  let S := FiniteModel.FiniteAtom.substitutesImplBase
  let I := FiniteModel.FiniteAtom.contractImpl
  let B := FiniteModel.FiniteAtom.contractBase
  have hSI := finiteAxisFoldSupport_preserves_relation hom
    (a := S) (b := I) (Or.inr trivial)
  have hSB := finiteAxisFoldSupport_preserves_relation hom
    (a := S) (b := B) (Or.inr trivial)
  have hIB := finiteAxisFoldSupport_preserves_relation hom
    (a := I) (b := B) (Or.inr trivial)
  have hSIne : e S ≠ e I := fun q => (by decide : S ≠ I) (e.injective q)
  have hSBne : e S ≠ e B := fun q => (by decide : S ≠ B) (e.injective q)
  have hIBne : e I ≠ e B := fun q => (by decide : I ≠ B) (e.injective q)
  generalize hs : e S = s at hSI hSB hSIne hSBne ⊢
  generalize hi : e I = i at hSI hIB hSIne hIBne ⊢
  generalize hb : e B = b at hSB hIB hSBne hIBne ⊢
  letI : Fintype FiniteModel.carrier.Atom := by
    change Fintype FiniteModel.FiniteAtom
    infer_instance
  fin_cases s <;> fin_cases i <;> fin_cases b <;>
    simp_all [e, S, I, B, FiniteModel.cycleRelation,
      FiniteModel.substitutionRelation]

/-- The ordered identification predicate fixes its first distinguished Atom. -/
theorem finiteAxisFoldSupport_atomEquiv_componentA
    (hom : SignedExactCoreReadingHom finiteAxisFoldSupportPackage
      finiteAxisFoldSupportPackage) :
    hom.atomEquiv FiniteModel.FiniteAtom.componentA =
      FiniteModel.FiniteAtom.componentA := by
  have identification := finiteAxisFoldSupport_componentIdentification
    hom
  simp [finiteAxisFoldSupportPackage, transportAlong, transportCoreReading,
    finiteWitnessSourcePackage, finiteWitnessSourceReading,
    transportCompositionReading, finiteModelDoctrineFromFixture,
    AATCorePackage.generate, FiniteModel.coreReading,
    FiniteModel.coreReadingFor, FiniteModel.compositionReading,
    AtomConfiguration.transport, FiniteModel.allFamily] at identification
  exact identification.2.1.symm

/-- The ordered identification predicate fixes its second distinguished Atom. -/
theorem finiteAxisFoldSupport_atomEquiv_componentB
    (hom : SignedExactCoreReadingHom finiteAxisFoldSupportPackage
      finiteAxisFoldSupportPackage) :
    hom.atomEquiv FiniteModel.FiniteAtom.componentB =
      FiniteModel.FiniteAtom.componentB := by
  have identification := finiteAxisFoldSupport_componentIdentification
    hom
  simp [finiteAxisFoldSupportPackage, transportAlong, transportCoreReading,
    finiteWitnessSourcePackage, finiteWitnessSourceReading,
    transportCompositionReading, finiteModelDoctrineFromFixture,
    AATCorePackage.generate, FiniteModel.coreReading,
    FiniteModel.coreReadingFor, FiniteModel.compositionReading,
    AtomConfiguration.transport, FiniteModel.allFamily] at identification
  exact identification.2.2.symm

/-- Every exact endomorphism of the independently fixed support package fixes
all nine primitive Atoms.  The proof uses the ordered identification, ordered
detector syntax, substitution graph, and finally bijectivity for the one
remaining Atom. -/
theorem finiteAxisFoldSupport_atomEquiv_eq_refl
    (hom : SignedExactCoreReadingHom finiteAxisFoldSupportPackage
      finiteAxisFoldSupportPackage) :
    hom.atomEquiv = Equiv.refl FiniteModel.carrier.Atom := by
  have hA := finiteAxisFoldSupport_atomEquiv_componentA hom
  have hB := finiteAxisFoldSupport_atomEquiv_componentB hom
  have hdependency := finiteAxisFoldSupport_detector_fixes hom
  have hsubstitution := finiteAxisFoldSupport_substitution_fixes hom
  have hC : hom.atomEquiv FiniteModel.FiniteAtom.componentC =
      FiniteModel.FiniteAtom.componentC := by
    have hCA :
        hom.atomEquiv FiniteModel.FiniteAtom.componentC ≠
          hom.atomEquiv FiniteModel.FiniteAtom.componentA :=
      fun q => (show FiniteModel.FiniteAtom.componentC ≠
        FiniteModel.FiniteAtom.componentA from by decide) (hom.atomEquiv.injective q)
    have hCB :
        hom.atomEquiv FiniteModel.FiniteAtom.componentC ≠
          hom.atomEquiv FiniteModel.FiniteAtom.componentB :=
      fun q => (show FiniteModel.FiniteAtom.componentC ≠
        FiniteModel.FiniteAtom.componentB from by decide) (hom.atomEquiv.injective q)
    have hCDAB :
        hom.atomEquiv FiniteModel.FiniteAtom.componentC ≠
          hom.atomEquiv FiniteModel.FiniteAtom.dependsAB :=
      fun q => (show FiniteModel.FiniteAtom.componentC ≠
        FiniteModel.FiniteAtom.dependsAB from by decide) (hom.atomEquiv.injective q)
    have hCDBC :
        hom.atomEquiv FiniteModel.FiniteAtom.componentC ≠
          hom.atomEquiv FiniteModel.FiniteAtom.dependsBC :=
      fun q => (show FiniteModel.FiniteAtom.componentC ≠
        FiniteModel.FiniteAtom.dependsBC from by decide) (hom.atomEquiv.injective q)
    have hCDCA :
        hom.atomEquiv FiniteModel.FiniteAtom.componentC ≠
          hom.atomEquiv FiniteModel.FiniteAtom.dependsCA :=
      fun q => (show FiniteModel.FiniteAtom.componentC ≠
        FiniteModel.FiniteAtom.dependsCA from by decide) (hom.atomEquiv.injective q)
    have hCCB :
        hom.atomEquiv FiniteModel.FiniteAtom.componentC ≠
          hom.atomEquiv FiniteModel.FiniteAtom.contractBase :=
      fun q => (show FiniteModel.FiniteAtom.componentC ≠
        FiniteModel.FiniteAtom.contractBase from by decide) (hom.atomEquiv.injective q)
    have hCCI :
        hom.atomEquiv FiniteModel.FiniteAtom.componentC ≠
          hom.atomEquiv FiniteModel.FiniteAtom.contractImpl :=
      fun q => (show FiniteModel.FiniteAtom.componentC ≠
        FiniteModel.FiniteAtom.contractImpl from by decide) (hom.atomEquiv.injective q)
    have hCS :
        hom.atomEquiv FiniteModel.FiniteAtom.componentC ≠
          hom.atomEquiv FiniteModel.FiniteAtom.substitutesImplBase :=
      fun q => (show FiniteModel.FiniteAtom.componentC ≠
        FiniteModel.FiniteAtom.substitutesImplBase from by decide)
          (hom.atomEquiv.injective q)
    generalize hc : hom.atomEquiv FiniteModel.FiniteAtom.componentC = c at hCA hCB hCDAB hCDBC hCDCA hCCB hCCI hCS ⊢
    letI : Fintype FiniteModel.carrier.Atom := by
      change Fintype FiniteModel.FiniteAtom
      infer_instance
    fin_cases c <;> simp_all
  apply Equiv.ext
  intro atom
  cases atom <;>
    simp_all

private noncomputable abbrev FiniteAxisFoldDirectEndpointCore :=
  finiteAxisFoldActualDirectAdmissibleGeometry.obj.core

private theorem finiteAxisFoldLeftInput_atomEquiv :
    (authoredExactLeftInput finiteAxisFoldBCDatumSquare).semantic.hom.doctrineHom.atomEquiv =
      Equiv.refl FiniteModel.carrier.Atom := by
  rfl

private theorem finiteAxisFoldTopInput_atomEquiv :
    (authoredExactTopInput finiteAxisFoldBCDatumSquare).semantic.hom.doctrineHom.atomEquiv =
      Equiv.refl FiniteModel.carrier.Atom := by
  rfl

private theorem finiteAxisFoldLeftPullBase_atomEquiv :
    (exactGeometryPullBaseHom
      (authoredExactLeftInput finiteAxisFoldBCDatumSquare)
      (authoredSouthwestGeometryFiberAt finiteAxisFoldBCDatumSquare
        (Discrete.mk DoubleDiamondTwoCell.second) Int
        (finiteAxisFoldFixedCoefficientGeometryFamily
          (Discrete.mk DoubleDiamondTwoCell.second)))).doctrineHom.atomEquiv =
      Equiv.refl FiniteModel.carrier.Atom := by
  simpa [exactGeometryPullBaseHom, ExtInstHom.comp,
    ExactDoctrineHom.comp] using finiteAxisFoldLeftInput_atomEquiv

private theorem finiteAxisFoldTopPushBase_atomEquiv :
    (geomFiberBaseHom
      finiteAxisFoldBCDatumSquare.context.square.semantic.square.top
      (authoredExactLeftPulledGeometryAt finiteAxisFoldBCDatumSquare
        (Discrete.mk DoubleDiamondTwoCell.second) Int
        (finiteAxisFoldFixedCoefficientGeometryFamily
          (Discrete.mk DoubleDiamondTwoCell.second)))).doctrineHom.atomEquiv =
      Equiv.refl FiniteModel.carrier.Atom := by
  simpa [geomFiberBaseHom, ExtInstHom.comp,
    ExactDoctrineHom.comp] using finiteAxisFoldTopInput_atomEquiv

private theorem finiteAxisFoldDirectEndpointCore_composition
    (F : AtomFamily FiniteModel.carrier) (hF : F.ListFinite) :
    FiniteAxisFoldDirectEndpointCore.reading.composition.compose F hF =
      FiniteModel.compositionReading.compose F hF := by
  change (transportCompositionReading _
    (transportCompositionReading _
      finiteAxisFoldSupportPackage.reading.composition)).compose F hF = _
  rw [finiteAxisFoldTopPushBase_atomEquiv,
    finiteAxisFoldLeftPullBase_atomEquiv]
  simp [transportCompositionReading, finiteAxisFoldSupportPackage,
    transportAlong, transportCoreReading, finiteWitnessSourcePackage,
    finiteWitnessSourceReading, finiteModelDoctrineFromFixture,
    AATCorePackage.generate, FiniteModel.coreReading,
    FiniteModel.coreReadingFor,
    AtomConfiguration.transport, AtomFamily.transport,
    FiniteModel.compositionReading]
  funext a b
  apply propext
  constructor
  · rintro ⟨⟨ha, hb⟩, hA, hB⟩
    subst a
    subst b
    exact ⟨rfl, rfl, ha, hb⟩
  · rintro ⟨hA, hB, ha, hb⟩
    subst a
    subst b
    exact ⟨⟨ha, hb⟩, rfl, rfl⟩

private theorem finiteAxisFoldDirectEndpointCore_detector
    (i : FiniteAxisFoldDirectEndpointCore.algebra.equationSystem.Index) :
    FiniteAxisFoldDirectEndpointCore.algebra.circuits.code i =
      .exact FiniteModel.cycleQueryDatum := by
  let southwest := authoredSouthwestGeometryFiberAt finiteAxisFoldBCDatumSquare
    (Discrete.mk DoubleDiamondTwoCell.second) Int
    (finiteAxisFoldFixedCoefficientGeometryFamily
      (Discrete.mk DoubleDiamondTwoCell.second))
  let leftData := exactGeometryPullBaseHom
    (authoredExactLeftInput finiteAxisFoldBCDatumSquare) southwest
  let pulled := inverseCorePackage southwest.1.core leftData
  let topData := geomFiberBaseHom
    finiteAxisFoldBCDatumSquare.context.square.semantic.square.top
    (authoredExactLeftPulledGeometryAt finiteAxisFoldBCDatumSquare
      (Discrete.mk DoubleDiamondTwoCell.second) Int
      (finiteAxisFoldFixedCoefficientGeometryFamily
        (Discrete.mk DoubleDiamondTwoCell.second)))
  let outer := transportAlongUpper pulled topData.doctrineHom
  change (transportAlong pulled topData.doctrineHom).algebra.circuits.code i = _
  rcases outer.equationTransport.equationEquiv.surjective i with ⟨j, rfl⟩
  rw [outer.detectorCode_eq]
  change (pulled.algebra.circuits.code j).transport
    topData.doctrineHom.atomEquiv = _
  rw [show topData.doctrineHom.atomEquiv = Equiv.refl _ by
    exact finiteAxisFoldTopPushBase_atomEquiv]
  simp only [CircuitDetectorCode.transport_refl]
  let backward := inverseCorePackageBackwardUpper southwest.1.core leftData
  rcases backward.equationTransport.equationEquiv.surjective j with ⟨k, rfl⟩
  rw [backward.detectorCode_eq]
  change (southwest.1.core.algebra.circuits.code k).transport
    backward.atomEquiv = _
  rw [show backward.atomEquiv = Equiv.refl _ by
    apply Equiv.ext
    intro atom
    change leftData.doctrineHom.atomEquiv.symm atom = atom
    rw [show leftData.doctrineHom.atomEquiv = Equiv.refl _ by
      exact finiteAxisFoldLeftPullBase_atomEquiv]
    rfl]
  simp only [CircuitDetectorCode.transport_refl]
  exact finiteAxisFoldSupport_detectorCode_all k

private noncomputable def finiteAxisFoldDirectEndpointEquationIndex :
    FiniteAxisFoldDirectEndpointCore.algebra.equationSystem.Index := by
  let southwest := authoredSouthwestGeometryFiberAt finiteAxisFoldBCDatumSquare
    (Discrete.mk DoubleDiamondTwoCell.second) Int
    (finiteAxisFoldFixedCoefficientGeometryFamily
      (Discrete.mk DoubleDiamondTwoCell.second))
  let leftData := exactGeometryPullBaseHom
    (authoredExactLeftInput finiteAxisFoldBCDatumSquare) southwest
  let pulled := inverseCorePackage southwest.1.core leftData
  let topData := geomFiberBaseHom
    finiteAxisFoldBCDatumSquare.context.square.semantic.square.top
    (authoredExactLeftPulledGeometryAt finiteAxisFoldBCDatumSquare
      (Discrete.mk DoubleDiamondTwoCell.second) Int
      (finiteAxisFoldFixedCoefficientGeometryFamily
        (Discrete.mk DoubleDiamondTwoCell.second)))
  exact (transportAlongUpper pulled topData.doctrineHom).equationMap
    ((inverseCorePackageBackwardUpper southwest.1.core leftData).equationMap
      finiteAxisFoldSupportEquationIndex)

private theorem finiteAxisFoldDirectEndpoint_component_fixes
    (hom : SignedExactCoreReadingHom FiniteAxisFoldDirectEndpointCore
      FiniteAxisFoldDirectEndpointCore) :
    hom.atomEquiv FiniteModel.FiniteAtom.componentA =
        FiniteModel.FiniteAtom.componentA ∧
      hom.atomEquiv FiniteModel.FiniteAtom.componentB =
        FiniteModel.FiniteAtom.componentB := by
  have hcomp := hom.composition_eq
    FiniteModel.allFamily FiniteModel.allFamily_listFinite
  rw [finiteAxisFoldDirectEndpointCore_composition,
    finiteAxisFoldDirectEndpointCore_composition] at hcomp
  have hid :
      ((FiniteModel.compositionReading.compose
        FiniteModel.allFamily FiniteModel.allFamily_listFinite).transport
          hom.atomEquiv).identification
            (hom.atomEquiv FiniteModel.FiniteAtom.componentA)
            (hom.atomEquiv FiniteModel.FiniteAtom.componentB) :=
    ⟨FiniteModel.FiniteAtom.componentA,
      FiniteModel.FiniteAtom.componentB, by
        simp [FiniteModel.compositionReading, FiniteModel.allFamily]
        exact ⟨FiniteModel.allFamily_mem _ (by simp),
          FiniteModel.allFamily_mem _ (by simp)⟩, rfl, rfl⟩
  rw [← hcomp] at hid
  simp [FiniteModel.compositionReading, AtomFamily.transport,
    FiniteModel.allFamily] at hid
  exact ⟨hid.1, hid.2.1⟩

private theorem finiteAxisFoldDirectEndpoint_detector_fixes
    (hom : SignedExactCoreReadingHom FiniteAxisFoldDirectEndpointCore
      FiniteAxisFoldDirectEndpointCore) :
    hom.atomEquiv FiniteModel.FiniteAtom.dependsAB =
        FiniteModel.FiniteAtom.dependsAB ∧
      hom.atomEquiv FiniteModel.FiniteAtom.dependsBC =
        FiniteModel.FiniteAtom.dependsBC ∧
      hom.atomEquiv FiniteModel.FiniteAtom.dependsCA =
        FiniteModel.FiniteAtom.dependsCA := by
  have hcode := hom.detectorCode_eq finiteAxisFoldDirectEndpointEquationIndex
  rw [finiteAxisFoldDirectEndpointCore_detector,
    finiteAxisFoldDirectEndpointCore_detector] at hcode
  have h := congrArg
    (fun code => match code with | .exact datum => datum.queries | _ => []) hcode
  simp [FiniteModel.cycleQueryDatum, CircuitDetectorCode.transport,
    FiniteCircuitDatum.transport, CircuitQuery.transport] at h
  exact ⟨h.1.1.symm, h.1.2.symm, h.2.1.2.symm⟩

private theorem finiteAxisFoldDirectEndpoint_preserves_relation
    (hom : SignedExactCoreReadingHom FiniteAxisFoldDirectEndpointCore
      FiniteAxisFoldDirectEndpointCore)
    {a b : FiniteModel.FiniteAtom}
    (hab : FiniteModel.cycleRelation a b ∨
      FiniteModel.substitutionRelation a b) :
    FiniteModel.cycleRelation (hom.atomEquiv a) (hom.atomEquiv b) ∨
      FiniteModel.substitutionRelation (hom.atomEquiv a) (hom.atomEquiv b) := by
  have hcomp := hom.composition_eq
    FiniteModel.allFamily FiniteModel.allFamily_listFinite
  rw [finiteAxisFoldDirectEndpointCore_composition,
    finiteAxisFoldDirectEndpointCore_composition] at hcomp
  have hr :
      ((FiniteModel.compositionReading.compose
        FiniteModel.allFamily FiniteModel.allFamily_listFinite).transport
          hom.atomEquiv).relation (hom.atomEquiv a) (hom.atomEquiv b) := by
    refine ⟨a, b, ?_, rfl, rfl⟩
    simp [FiniteModel.compositionReading, FiniteModel.allFamily]
    refine ⟨hab, ?_⟩
    cases a <;> cases b <;>
      simp_all [FiniteModel.cycleRelation, FiniteModel.substitutionRelation,
        FiniteModel.extractionDoctrine, ExtractionDoctrine.atomize,
        ExtractionDoctrine.extracts]
  rw [← hcomp] at hr
  simp [FiniteModel.compositionReading, AtomFamily.transport,
    FiniteModel.allFamily] at hr
  exact hr.1

set_option maxHeartbeats 800000 in
private theorem finiteAxisFoldDirectEndpoint_substitution_fixes
    (hom : SignedExactCoreReadingHom FiniteAxisFoldDirectEndpointCore
      FiniteAxisFoldDirectEndpointCore) :
    hom.atomEquiv FiniteModel.FiniteAtom.substitutesImplBase =
        FiniteModel.FiniteAtom.substitutesImplBase ∧
      hom.atomEquiv FiniteModel.FiniteAtom.contractImpl =
        FiniteModel.FiniteAtom.contractImpl ∧
      hom.atomEquiv FiniteModel.FiniteAtom.contractBase =
        FiniteModel.FiniteAtom.contractBase := by
  let e := hom.atomEquiv
  let S := FiniteModel.FiniteAtom.substitutesImplBase
  let I := FiniteModel.FiniteAtom.contractImpl
  let B := FiniteModel.FiniteAtom.contractBase
  have hSI := finiteAxisFoldDirectEndpoint_preserves_relation hom
    (a := S) (b := I) (Or.inr trivial)
  have hSB := finiteAxisFoldDirectEndpoint_preserves_relation hom
    (a := S) (b := B) (Or.inr trivial)
  have hIB := finiteAxisFoldDirectEndpoint_preserves_relation hom
    (a := I) (b := B) (Or.inr trivial)
  have hSIne : e S ≠ e I := fun q => (by decide : S ≠ I) (e.injective q)
  have hSBne : e S ≠ e B := fun q => (by decide : S ≠ B) (e.injective q)
  have hIBne : e I ≠ e B := fun q => (by decide : I ≠ B) (e.injective q)
  generalize hs : e S = s at hSI hSB hSIne hSBne ⊢
  generalize hi : e I = i at hSI hIB hSIne hIBne ⊢
  generalize hb : e B = b at hSB hIB hSBne hIBne ⊢
  letI : Fintype FiniteModel.carrier.Atom := by
    change Fintype FiniteModel.FiniteAtom
    infer_instance
  fin_cases s <;> fin_cases i <;> fin_cases b <;>
    simp_all [e, S, I, B, FiniteModel.cycleRelation,
      FiniteModel.substitutionRelation]

/-- The exact pull--push construction preserves enough of the fixed ordered
reading that every exact endomorphism of its actual endpoint fixes all nine
primitive Atoms. -/
theorem finiteAxisFoldDirectEndpoint_atomEquiv_eq_refl
    (hom : SignedExactCoreReadingHom FiniteAxisFoldDirectEndpointCore
      FiniteAxisFoldDirectEndpointCore) :
    hom.atomEquiv = Equiv.refl FiniteModel.carrier.Atom := by
  have hcomponent := finiteAxisFoldDirectEndpoint_component_fixes hom
  have hdependency := finiteAxisFoldDirectEndpoint_detector_fixes hom
  have hsubstitution := finiteAxisFoldDirectEndpoint_substitution_fixes hom
  have hC : hom.atomEquiv FiniteModel.FiniteAtom.componentC =
      FiniteModel.FiniteAtom.componentC := by
    rcases hom.atomEquiv.surjective FiniteModel.FiniteAtom.componentC with
      ⟨source, hsource⟩
    have source_eq : source = FiniteModel.FiniteAtom.componentC := by
      cases source <;> simp_all
    subst source
    exact hsource
  apply Equiv.ext
  intro atom
  cases atom <;> simp_all

/-- Every element of the full residual axis--signature kernel fixes the Atom
equivalence of the actual normalized direct endpoint.  Kernel membership is
not used to shrink the quantifier: the stronger endpoint rigidity theorem is
applied to its complete underlying exact core endomorphism. -/
theorem finiteAxisFoldResidual_atomEquiv_eq_refl
    (remainder : FiniteAxisFoldNormalizedAxisSignatureKernel) :
    remainder.1.1.hom.f.hom.base.upper.atomEquiv =
      Equiv.refl FiniteModel.carrier.Atom := by
  exact finiteAxisFoldDirectEndpoint_atomEquiv_eq_refl
    remainder.1.1.hom.f.hom.base.upper


end


end AAT.AG.RealizationReconstruction

#assert_standard_axioms_only AAT.AG.RealizationReconstruction
