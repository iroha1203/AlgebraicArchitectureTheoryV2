import ResearchLean.AG.AtomFoundation.RefinementObstruction

/-!
# Composition and equation supply for refinement lifts

A strict doctrine refinement cannot have a `SignedExactCoreReadingHom`: its
target family may contain newly admitted Atoms.  The appropriate forward lift
is therefore the existing `PositiveCoreReadingHom`.

This module isolates the genuinely additional raw data.  The supply contains a
finite expanded family input, one actual operation out of the expanded base,
and a target equation system with an index equivalence.  Detector syntax and
all positive preservation laws are generated below.  The supply does not
contain a target package, a completed core hom, a lift certificate, or any
universal property.
-/

namespace AAT.AG.AtomFoundation

universe u

/-- The canonical expanded family selected by a pointed refinement. -/
def refinementLiftFamily {U : AtomCarrier.{u}}
    (P : AATCorePackage U)
    {E : ExtractionDoctrine U}
    (r : RefinementDoctrineHom P.reading.doctrine E) : AtomFamily U :=
  E.atomize (r.sourceMap P.reading.source)

/-- Canonical composition on the expanded refinement family. -/
noncomputable def refinementLiftConfiguration {U : AtomCarrier.{u}}
    (P : AATCorePackage U)
    {E : ExtractionDoctrine U}
    (r : RefinementDoctrineHom P.reading.doctrine E)
    (hfinite : (refinementLiftFamily P r).ListFinite) : AtomConfiguration U :=
  (transportCompositionReading r.atomEquiv P.reading.composition).compose
    (refinementLiftFamily P r) hfinite

/-- The architecture object generated from the expanded composition input. -/
noncomputable def refinementLiftObject {U : AtomCarrier.{u}}
    (P : AATCorePackage U)
    {E : ExtractionDoctrine U}
    (r : RefinementDoctrineHom P.reading.doctrine E)
    (hfinite : (refinementLiftFamily P r).ListFinite) : ArchitectureObject U :=
  (transportObjectReading r.atomEquiv P.reading.objectReading).object
    (refinementLiftConfiguration P r hfinite)

/--
Lower-level equation data for an expanded refinement object.

The target equation system and index equivalence are executable semantic data.
Detector syntax is fixed canonically by transporting the source code, and its
soundness is proved here without storing any positive-hom preservation field.
-/
structure RefinementEquationSupply {U : AtomCarrier.{u}}
    (P : AATCorePackage U)
    {E : ExtractionDoctrine U}
    (r : RefinementDoctrineHom P.reading.doctrine E)
    (hfinite : (refinementLiftFamily P r).ListFinite) where
  /-- Target equation semantics on the expanded refinement object. -/
  equationSystem : ArchitecturalEquationSystem
    (Site.contextMorphismPreorderCategory
      (refinementLiftObject P r hfinite))
  /-- Source equation indices correspond bijectively to target indices. -/
  indexEquiv : P.algebra.equationSystem.Index ≃ equationSystem.Index
  /-- Canonically transported detector syntax is sound for the target semantics. -/
  circuitSound :
    ({ code := fun index =>
        (P.algebra.circuits.code (indexEquiv.symm index)).transport r.atomEquiv }
      : EquationCircuitReading equationSystem).Sound

/--
Raw composition and equation-system data for Atoms newly admitted by a
refinement.

The `baseOperation` is executable operation data, not a reachability proof.
Target detector syntax, query transport, and all positive preservation laws are
derived below from `equationSupply`, `P`, and `r`.
-/
structure RefinementExtensionSupply {U : AtomCarrier.{u}}
    (P : AATCorePackage U)
    {E : ExtractionDoctrine U}
    (r : RefinementDoctrineHom P.reading.doctrine E) where
  /-- The expanded target atomization is a concrete finite composition input. -/
  targetFamily_listFinite : (refinementLiftFamily P r).ListFinite
  /-- An actual operation from the expanded base to the direct-image source base. -/
  baseOperation :
    (transportOperationReading r.atomEquiv P.reading.operationReading).Op
      (refinementLiftObject P r targetFamily_listFinite)
      (transportArchitectureObject r.atomEquiv P.object)
  /-- Lower-level target equation semantics and index correspondence. -/
  equationSupply :
    RefinementEquationSupply P r targetFamily_listFinite

/-- Build the target equation reading from the lower-level supply. -/
noncomputable def refinementEquationReadingOfSupply {U : AtomCarrier.{u}}
    (P : AATCorePackage U)
    {E : ExtractionDoctrine U}
    (r : RefinementDoctrineHom P.reading.doctrine E)
    (H : RefinementExtensionSupply P r) :
    EquationReading (refinementLiftObject P r H.targetFamily_listFinite) where
  contextPreorder := Site.contextMorphismPreorderCategory _
  equationSystem := H.equationSupply.equationSystem
  circuits := {
    code := fun index =>
      (P.algebra.circuits.code
        (H.equationSupply.indexEquiv.symm index)).transport r.atomEquiv
  }
  circuitSound := H.equationSupply.circuitSound

/-- Canonical signed-query transport used by every supplied refinement lift. -/
noncomputable def refinementQueryMap {U : AtomCarrier.{u}}
    {D E : ExtractionDoctrine U} (r : RefinementDoctrineHom D E)
    (datum : FiniteCircuitDatum U) : FiniteCircuitDatum U :=
  datum.transport r.atomEquiv

/-- Canonical refinement query transport preserves positive polarity. -/
theorem refinementQueryMap_positive {U : AtomCarrier.{u}}
    {D E : ExtractionDoctrine U} (r : RefinementDoctrineHom D E)
    (datum : FiniteCircuitDatum U) (hpositive : datum.Positive) :
    (refinementQueryMap r datum).Positive := by
  intro query expected hmem
  rcases List.mem_map.mp hmem with ⟨pair, hpair, hpair_eq⟩
  have hexpected := hpositive pair.1 pair.2 hpair
  have hsecond : pair.2 = expected := congrArg Prod.snd hpair_eq
  exact hsecond.symm.trans hexpected

/-- Canonical refinement query transport preserves matching on transported objects. -/
theorem refinementQueryMap_matches {U : AtomCarrier.{u}}
    {D E : ExtractionDoctrine U} (r : RefinementDoctrineHom D E)
    (datum : FiniteCircuitDatum U) (A : ArchitectureObject U)
    (hmatches : datum.Matches A) :
    (refinementQueryMap r datum).Matches
      (transportArchitectureObject r.atomEquiv A) := by
  exact (FiniteCircuitDatum.transport_matches_iff r.atomEquiv datum A
    (transportArchitectureObject r.atomEquiv A) rfl).mp hmatches

/-- Canonical detector construction derives one-way acceptance preservation. -/
theorem refinementQueryMap_accepts {U : AtomCarrier.{u}}
    (P : AATCorePackage U)
    {E : ExtractionDoctrine U}
    (r : RefinementDoctrineHom P.reading.doctrine E)
    (H : RefinementExtensionSupply P r)
    (index : P.algebra.equationSystem.Index)
    (datum : FiniteCircuitDatum U)
    (haccepts : P.algebra.circuits.accepts index datum = true) :
    (refinementEquationReadingOfSupply P r H).circuits.accepts
        (H.equationSupply.indexEquiv index)
        (refinementQueryMap r datum) = true := by
  rw [EquationCircuitReading.accepts_eq_eval]
  change
    ((P.algebra.circuits.code
      (H.equationSupply.indexEquiv.symm
        (H.equationSupply.indexEquiv index))).transport r.atomEquiv).eval
        (datum.transport r.atomEquiv) = true
  rw [H.equationSupply.indexEquiv.symm_apply_apply]
  rw [CircuitDetectorCode.eval_transport]
  rw [EquationCircuitReading.accepts_eq_eval] at haccepts
  exact haccepts

/-- The target core reading generated from raw refinement supply. -/
noncomputable def refinementCoreReadingOfSupply {U : AtomCarrier.{u}}
    (P : AATCorePackage U)
    {E : ExtractionDoctrine U}
    (r : RefinementDoctrineHom P.reading.doctrine E)
    (H : RefinementExtensionSupply P r) : CoreReading U where
  doctrine := E
  source := r.sourceMap P.reading.source
  family_listFinite := H.targetFamily_listFinite
  composition := transportCompositionReading r.atomEquiv P.reading.composition
  objectReading := transportObjectReading r.atomEquiv P.reading.objectReading
  equationReading := refinementEquationReadingOfSupply P r H
  invariantReading := transportInvariantFamily r.atomEquiv P.reading.invariantReading
  signatureReading :=
    transportArchitectureSignature r.atomEquiv P.reading.signatureReading
  operationReading := transportOperationReading r.atomEquiv P.reading.operationReading

/-- The mapped target package generated from the source, refinement, and raw supply. -/
noncomputable def refinementPackageOfSupply {U : AtomCarrier.{u}}
    (P : AATCorePackage U)
    {E : ExtractionDoctrine U}
    (r : RefinementDoctrineHom P.reading.doctrine E)
    (H : RefinementExtensionSupply P r) : AATCorePackage U :=
  AATCorePackage.generate P.axioms (refinementCoreReadingOfSupply P r H)

/-- The generated package lies over the mapped target point. -/
@[simp]
theorem refinementPackageOfSupply_point {U : AtomCarrier.{u}}
    (P : AATCorePackage U)
    {E : ExtractionDoctrine U}
    (r : RefinementDoctrineHom P.reading.doctrine E)
    (H : RefinementExtensionSupply P r) :
    packagePoint (refinementPackageOfSupply P r H) =
      ({ doctrine := E, source := r.sourceMap P.reading.source } :
        ExtractionInstance U) :=
  rfl

/-- The refinement forward law supplies inclusion of the transported source family. -/
private theorem refinementExtraction_mono {U : AtomCarrier.{u}}
    (P : AATCorePackage U)
    {E : ExtractionDoctrine U}
    (r : RefinementDoctrineHom P.reading.doctrine E)
    (H : RefinementExtensionSupply P r) :
    (P.family.transport r.atomMap).Subset (refinementPackageOfSupply P r H).family := by
  intro target htarget
  rcases htarget with ⟨source, hsource, rfl⟩
  apply ((refinementPackageOfSupply P r H).family_mem_iff_extracts _).mpr
  exact r.extraction_forward P.reading.source source
    ((P.family_mem_iff_extracts source).mp hsource)

/-- Canonical configuration transport into the generated target composition. -/
private noncomputable def refinementCompositionMap {U : AtomCarrier.{u}}
    (P : AATCorePackage U)
    {E : ExtractionDoctrine U}
    (r : RefinementDoctrineHom P.reading.doctrine E)
    (F : AtomFamily U) (hF : F.ListFinite) :
    ConfigurationHom
      (P.reading.composition.compose F hF)
      ((transportCompositionReading r.atomEquiv P.reading.composition).compose
        (F.transport r.atomMap) (hF.transport r.atomMap)) :=
  castConfigurationHom rfl
    (transportCompositionReading_compose_transport
      r.atomEquiv P.reading.composition F hF).symm
    (AtomConfiguration.transportHom r.atomEquiv
      (P.reading.composition.compose F hF))

/-- The raw supply constructs a complete forward-positive core refinement lift. -/
noncomputable def refinementPositiveLiftOfSupply {U : AtomCarrier.{u}}
    (P : AATCorePackage U)
    {E : ExtractionDoctrine U}
    (r : RefinementDoctrineHom P.reading.doctrine E)
    (H : RefinementExtensionSupply P r) :
    PositiveCoreReadingHom P (refinementPackageOfSupply P r H) where
  atomMap := r.atomMap
  extraction_mono := refinementExtraction_mono P r H
  compositionMap := refinementCompositionMap P r
  compositionMap_atomMap := by
    intro F hF
    rw [refinementCompositionMap, castConfigurationHom_atomMap,
      AtomConfiguration.transportHom_atomMap]
    funext atom
    exact r.atomEquiv_apply atom
  objectMap := transportArchitectureObject r.atomEquiv
  object_formation_eq := transportObjectReading_object_transport
    r.atomEquiv P.reading.objectReading
  base_reachable := OperationReading.Reachable.step
    OperationReading.Reachable.base H.baseOperation
  configurationMap A := AtomConfiguration.transportHom r.atomEquiv A.configuration
  configurationMap_atomMap := by
    intro A
    funext atom
    exact r.atomEquiv_apply atom
  operationMap := transportOperation r.atomEquiv P.reading.operationReading
  operation_naturality := transportOperation_naturality
    r.atomEquiv P.reading.operationReading
  equationMap := H.equationSupply.indexEquiv
  queryMap := refinementQueryMap r
  positive_preserved := refinementQueryMap_positive r
  matches_of_positive := by
    intro datum A _hpositive hmatches
    exact refinementQueryMap_matches r datum A hmatches
  accepts_mono := by
    intro index datum _hpositive haccepts
    exact refinementQueryMap_accepts P r H index datum haccepts

/-- The generated positive lift uses exactly the refinement's specified Atom map. -/
@[simp]
theorem refinementPositiveLiftOfSupply_atomMap {U : AtomCarrier.{u}}
    (P : AATCorePackage U)
    {E : ExtractionDoctrine U}
    (r : RefinementDoctrineHom P.reading.doctrine E)
    (H : RefinementExtensionSupply P r) :
    (refinementPositiveLiftOfSupply P r H).atomMap = r.atomMap :=
  rfl

/-- A target package and its constructed forward-positive refinement hom. -/
structure PositiveRefinementLift {U : AtomCarrier.{u}}
    (P : AATCorePackage U)
    {E : ExtractionDoctrine U}
    (r : RefinementDoctrineHom P.reading.doctrine E) where
  target : AATCorePackage U
  point_eq :
    packagePoint target =
      ({ doctrine := E, source := r.sourceMap P.reading.source } :
        ExtractionInstance U)
  hom : PositiveCoreReadingHom P target
  atomMap_eq : hom.atomMap = r.atomMap

/-- Raw supply is sufficient to construct the target and forward-positive lift. -/
noncomputable def refinementLiftOfSupply {U : AtomCarrier.{u}}
    (P : AATCorePackage U)
    {E : ExtractionDoctrine U}
    (r : RefinementDoctrineHom P.reading.doctrine E)
    (H : RefinementExtensionSupply P r) : PositiveRefinementLift P r where
  target := refinementPackageOfSupply P r H
  point_eq := refinementPackageOfSupply_point P r H
  hom := refinementPositiveLiftOfSupply P r H
  atomMap_eq := refinementPositiveLiftOfSupply_atomMap P r H

/-- A fixed target package is generated by some raw refinement supply. -/
def HasRefinementExtensionSupply {U : AtomCarrier.{u}}
    (P Q : AATCorePackage U)
    {E : ExtractionDoctrine U}
    (r : RefinementDoctrineHom P.reading.doctrine E) : Prop :=
  ∃ H : RefinementExtensionSupply P r, refinementPackageOfSupply P r H = Q

/-- A raw supply for a fixed target is sufficient for a positive refinement lift. -/
theorem HasRefinementExtensionSupply.lift {U : AtomCarrier.{u}}
    (P Q : AATCorePackage U)
    {E : ExtractionDoctrine U}
    (r : RefinementDoctrineHom P.reading.doctrine E)
    (hSupply : HasRefinementExtensionSupply P Q r) :
    ∃ F : PositiveCoreReadingHom P Q, F.atomMap = r.atomMap := by
  rcases hSupply with ⟨H, rfl⟩
  exact ⟨refinementPositiveLiftOfSupply P r H,
    refinementPositiveLiftOfSupply_atomMap P r H⟩

end AAT.AG.AtomFoundation

#assert_standard_axioms_only AAT.AG.AtomFoundation
