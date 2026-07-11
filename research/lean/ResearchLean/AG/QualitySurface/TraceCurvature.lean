import ResearchLean.AG.QualitySurface.TraceLocus

/-!
Cycle 7 evidence for `G-aat-quality-surface-01`.

This file adds a finite trace-curvature detector. Two path-ordered trace
transports can reach the same visible scalar, verdict, and support at the
upper-right profile while disagreeing on the trace locus and exact repair
frontier.
-/

namespace ResearchLean.AG
namespace QualitySurface
namespace TraceCurvature

/-! ## Profile square and trace certificates -/

/-- Four vertices of the finite trace-curvature square. -/
inductive TraceProfile where
  | lowerLeft
  | lowerRight
  | upperLeft
  | upperRight
  deriving DecidableEq, Fintype

/-- Named certificates carried by the trace-curvature square. -/
inductive TraceCertificateName where
  | seed
  | lawStage
  | coverStage
  | lawThenCoverResult
  | coverThenLawResult
  deriving DecidableEq, Fintype

open TraceProfile TraceCertificateName
open TraceLocus

/-- The selected support shared by all trace-curvature certificates. -/
def sharedSupport : Set LocusAtom :=
  selectedSupport

/-- A trace field with no missing trace on the shared support. -/
def tracedField : LocusAtom -> Option LocusTraceToken :=
  fullTraceField

/-- A trace field whose database atom is missing on the shared support. -/
def curvedTraceField : LocusAtom -> Option LocusTraceToken :=
  partialTraceField

/-- No repair is required while the trace locus is full. -/
def emptyRepairFrontier : Set LocusAtom :=
  fun _ => False

/-- The database repair frontier records the trace gap in the curved path. -/
def curvedRepairFrontier : Set LocusAtom :=
  databaseRepairFrontier

/-- Tuple carried by each named trace certificate. -/
structure TraceSquareCertificate where
  visibleScalarReading : Nat
  verdict : StateSeparation.StateVerdict
  selectedSupport : Set LocusAtom
  traceField : LocusAtom -> Option LocusTraceToken
  repairFrontier : Set LocusAtom

/-- The seed certificate starts with full trace coverage. -/
def seedTraceTuple : TraceSquareCertificate where
  visibleScalarReading := 0
  verdict := StateSeparation.StateVerdict.acceptable
  selectedSupport := sharedSupport
  traceField := tracedField
  repairFrontier := emptyRepairFrontier

/-- Law strengthening alone preserves trace coverage. -/
def lawStageTraceTuple : TraceSquareCertificate where
  visibleScalarReading := 1
  verdict := StateSeparation.StateVerdict.acceptable
  selectedSupport := sharedSupport
  traceField := tracedField
  repairFrontier := emptyRepairFrontier

/-- Cover refinement alone preserves trace coverage. -/
def coverStageTraceTuple : TraceSquareCertificate where
  visibleScalarReading := 1
  verdict := StateSeparation.StateVerdict.acceptable
  selectedSupport := sharedSupport
  traceField := tracedField
  repairFrontier := emptyRepairFrontier

/-- The law-then-cover path remains trace complete at the upper-right profile. -/
def lawThenCoverTraceTuple : TraceSquareCertificate where
  visibleScalarReading := 1
  verdict := StateSeparation.StateVerdict.acceptable
  selectedSupport := sharedSupport
  traceField := tracedField
  repairFrontier := emptyRepairFrontier

/-- The cover-then-law path reaches the same visible surface but loses database trace. -/
def coverThenLawTraceTuple : TraceSquareCertificate where
  visibleScalarReading := 1
  verdict := StateSeparation.StateVerdict.acceptable
  selectedSupport := sharedSupport
  traceField := curvedTraceField
  repairFrontier := curvedRepairFrontier

/-- Read the tuple carried by a named trace certificate. -/
def traceTuple : TraceCertificateName -> TraceSquareCertificate
  | seed => seedTraceTuple
  | lawStage => lawStageTraceTuple
  | coverStage => coverStageTraceTuple
  | lawThenCoverResult => lawThenCoverTraceTuple
  | coverThenLawResult => coverThenLawTraceTuple

/-- Profile vertex where a named trace certificate lives. -/
def profileOf : TraceCertificateName -> TraceProfile
  | seed => lowerLeft
  | lawStage => lowerRight
  | coverStage => upperLeft
  | lawThenCoverResult => upperRight
  | coverThenLawResult => upperRight

/-- Certificates typed by the profile vertex where they live. -/
def CertificateAt (p : TraceProfile) : Type :=
  { c : TraceCertificateName // profileOf c = p }

/-- The seed trace certificate at the lower-left vertex. -/
def seedAt : CertificateAt lowerLeft :=
  ⟨seed, rfl⟩

/-! ## Typed path transports -/

/-- A typed edge transport along the trace profile square. -/
structure EdgeTransport (source target : TraceProfile) where
  map : CertificateAt source -> CertificateAt target

/-- Bottom edge: strengthen law first. -/
def transportLawBottom : EdgeTransport lowerLeft lowerRight where
  map := fun _ => ⟨lawStage, rfl⟩

/-- Right edge: refine cover after law strengthening. -/
def transportCoverRight : EdgeTransport lowerRight upperRight where
  map := fun _ => ⟨lawThenCoverResult, rfl⟩

/-- Left edge: refine cover first. -/
def transportCoverLeft : EdgeTransport lowerLeft upperLeft where
  map := fun _ => ⟨coverStage, rfl⟩

/-- Top edge: strengthen law after cover refinement. -/
def transportLawTop : EdgeTransport upperLeft upperRight where
  map := fun _ => ⟨coverThenLawResult, rfl⟩

/-- The path that strengthens law before cover refinement. -/
def lawThenCover (c : CertificateAt lowerLeft) : CertificateAt upperRight :=
  transportCoverRight.map (transportLawBottom.map c)

/-- The path that refines cover before law strengthening. -/
def coverThenLaw (c : CertificateAt lowerLeft) : CertificateAt upperRight :=
  transportLawTop.map (transportCoverLeft.map c)

/-- The law-then-cover path reaches its named upper-right certificate. -/
theorem lawThenCover_seed :
    (lawThenCover seedAt).val = lawThenCoverResult :=
  rfl

/-- The cover-then-law path reaches its named upper-right certificate. -/
theorem coverThenLaw_seed :
    (coverThenLaw seedAt).val = coverThenLawResult :=
  rfl

/-! ## Visible projection and trace curvature -/

/-- Visible scalar reading selected from a trace certificate. -/
def scalarReading (c : TraceCertificateName) : Nat :=
  (traceTuple c).visibleScalarReading

/-- Selected verdict component. -/
def verdict (c : TraceCertificateName) : StateSeparation.StateVerdict :=
  (traceTuple c).verdict

/-- Selected support carried by a trace certificate. -/
def support (c : TraceCertificateName) : Set LocusAtom :=
  (traceTuple c).selectedSupport

/-- Trace missing locus of a named trace certificate. -/
def traceMissingLocus (c : TraceCertificateName) : Set LocusAtom :=
  fun atom => support c atom ∧ (traceTuple c).traceField atom = none

/-- Trace repair frontier of a named trace certificate. -/
def repairFrontier (c : TraceCertificateName) : Set LocusAtom :=
  (traceTuple c).repairFrontier

/-- The visible upper-right scalar agrees along the two paths. -/
theorem same_scalar_after_trace_paths :
    scalarReading (lawThenCover seedAt).val =
      scalarReading (coverThenLaw seedAt).val :=
  rfl

/-- The visible upper-right verdict agrees along the two paths. -/
theorem same_verdict_after_trace_paths :
    verdict (lawThenCover seedAt).val =
      verdict (coverThenLaw seedAt).val :=
  rfl

/-- The selected upper-right support agrees along the two paths. -/
theorem same_support_after_trace_paths :
    support (lawThenCover seedAt).val =
      support (coverThenLaw seedAt).val :=
  rfl

/-- The law-then-cover path remains trace complete at upper-right. -/
theorem lawThenCover_trace_available :
    TraceTransport.TraceAvailableOn
      (support (lawThenCover seedAt).val)
      (traceTuple (lawThenCover seedAt).val).traceField :=
  TraceLocus.fullTrace_available_on_support

/-- The cover-then-law path has a missing database trace at upper-right. -/
theorem coverThenLaw_trace_missing :
    TraceTransport.TraceMissingOn
      (support (coverThenLaw seedAt).val)
      (traceTuple (coverThenLaw seedAt).val).traceField :=
  TraceLocus.partialTrace_missing_on_support

/-- The law-then-cover path has no database repair frontier at upper-right. -/
theorem lawThenCover_no_database_repair :
    ¬ repairFrontier (lawThenCover seedAt).val LocusAtom.database :=
  TraceLocus.fullTrace_repair_frontier_excludes_database

/-- The cover-then-law path forces the database repair frontier at upper-right. -/
theorem coverThenLaw_forces_database_repair :
    repairFrontier (coverThenLaw seedAt).val LocusAtom.database :=
  TraceLocus.partialTrace_forces_database_repair

/-- The cover-then-law repair frontier matches its missing trace locus. -/
theorem coverThenLaw_repair_frontier_matches_missing_locus :
    ∀ atom,
      repairFrontier (coverThenLaw seedAt).val atom ↔
        traceMissingLocus (coverThenLaw seedAt).val atom :=
  TraceLocus.partialTrace_repair_frontier_matches_missing_locus

/-- Faithfulness of visible upper-right surface to path-ordered trace locus. -/
def TraceSquareFaithfulToTraceLocus : Prop :=
  ∀ c₁ c₂ : CertificateAt upperRight,
    scalarReading c₁.val = scalarReading c₂.val ->
      verdict c₁.val = verdict c₂.val ->
        support c₁.val = support c₂.val ->
          ∀ atom,
            (traceMissingLocus c₁.val atom ↔
              traceMissingLocus c₂.val atom)

/-- Faithfulness of visible upper-right surface to path-ordered repair frontier. -/
def TraceSquareFaithfulToRepairFrontier : Prop :=
  ∀ c₁ c₂ : CertificateAt upperRight,
    scalarReading c₁.val = scalarReading c₂.val ->
      verdict c₁.val = verdict c₂.val ->
        support c₁.val = support c₂.val ->
          ∀ atom,
            (repairFrontier c₁.val atom ↔ repairFrontier c₂.val atom)

/-- The visible upper-right surface cannot recover path-ordered trace locus. -/
theorem trace_square_not_faithful_to_trace_locus :
    ¬ TraceSquareFaithfulToTraceLocus := by
  intro hfaithful
  have hiff :=
    hfaithful (lawThenCover seedAt) (coverThenLaw seedAt)
      rfl rfl rfl LocusAtom.database
  have hmissingLawThenCover :
      traceMissingLocus (lawThenCover seedAt).val LocusAtom.database :=
    hiff.mpr TraceLocus.partialTrace_database_missing_locus
  exact TraceLocus.fullTrace_has_no_missing_locus
    ⟨LocusAtom.database, hmissingLawThenCover⟩

/-- The visible upper-right surface also cannot recover path-ordered repair frontier. -/
theorem trace_square_not_faithful_to_repair_frontier :
    ¬ TraceSquareFaithfulToRepairFrontier := by
  intro hfaithful
  have hiff :=
    hfaithful (lawThenCover seedAt) (coverThenLaw seedAt)
      rfl rfl rfl LocusAtom.database
  have hrepairLawThenCover :
      repairFrontier (lawThenCover seedAt).val LocusAtom.database :=
    hiff.mpr coverThenLaw_forces_database_repair
  exact lawThenCover_no_database_repair hrepairLawThenCover

/-- Path-ordered trace curvature at a profile square. -/
def TraceCurvatureCell : Prop :=
  scalarReading (lawThenCover seedAt).val =
      scalarReading (coverThenLaw seedAt).val ∧
    verdict (lawThenCover seedAt).val =
      verdict (coverThenLaw seedAt).val ∧
    support (lawThenCover seedAt).val =
      support (coverThenLaw seedAt).val ∧
    TraceTransport.TraceAvailableOn
      (support (lawThenCover seedAt).val)
      (traceTuple (lawThenCover seedAt).val).traceField ∧
    TraceTransport.TraceMissingOn
      (support (coverThenLaw seedAt).val)
      (traceTuple (coverThenLaw seedAt).val).traceField ∧
    ¬ repairFrontier (lawThenCover seedAt).val LocusAtom.database ∧
    repairFrontier (coverThenLaw seedAt).val LocusAtom.database ∧
    (∀ atom,
      repairFrontier (coverThenLaw seedAt).val atom ↔
        traceMissingLocus (coverThenLaw seedAt).val atom) ∧
    ¬ TraceSquareFaithfulToTraceLocus ∧
    ¬ TraceSquareFaithfulToRepairFrontier

/-- The finite trace square is curved in trace-locus / repair-frontier data. -/
theorem trace_curvature_cell :
    TraceCurvatureCell := by
  exact ⟨same_scalar_after_trace_paths,
    same_verdict_after_trace_paths,
    same_support_after_trace_paths,
    lawThenCover_trace_available,
    coverThenLaw_trace_missing,
    lawThenCover_no_database_repair,
    coverThenLaw_forces_database_repair,
    coverThenLaw_repair_frontier_matches_missing_locus,
    trace_square_not_faithful_to_trace_locus,
    trace_square_not_faithful_to_repair_frontier⟩

end TraceCurvature
end QualitySurface
end ResearchLean.AG
