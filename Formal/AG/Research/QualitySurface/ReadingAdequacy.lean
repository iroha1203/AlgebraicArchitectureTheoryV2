import Formal.AG.Research.QualitySurface.TraceCurvature

/-!
Cycle 8 evidence for `G-aat-quality-surface-01`.

This file organizes the earlier Quality Surface finite witnesses as a declared
reading chain. It separates visible/support readings from protected trace-locus
and repair-frontier data, and proves that exact trace-repair certificates become
repair-frontier faithful once the reading includes the trace missing locus.
-/

namespace Formal.AG.Research
namespace QualitySurface
namespace ReadingAdequacy

universe u

/-! ## Reading refinement and faithfulness -/

/-- A reading is an observational equivalence relation on certificates. -/
structure Reading (Cert : Type u) where
  Equivalent : Cert -> Cert -> Prop

/-- `fine` refines `coarse` when fine equivalence implies coarse equivalence. -/
def ReadingRefines {Cert : Type u} (fine coarse : Reading Cert) : Prop :=
  ∀ {c₁ c₂ : Cert}, fine.Equivalent c₁ c₂ -> coarse.Equivalent c₁ c₂

/-- A reading is faithful to an invariant if equivalent certificates have the same invariant. -/
def FaithfulToInvariant {Cert : Type u}
    (reading : Reading Cert) (SameInvariant : Cert -> Cert -> Prop) : Prop :=
  ∀ c₁ c₂ : Cert, reading.Equivalent c₁ c₂ -> SameInvariant c₁ c₂

/-- Restricted faithfulness on a certificate subregime. -/
def FaithfulToInvariantOn {Cert : Type u} (Domain : Cert -> Prop)
    (reading : Reading Cert) (SameInvariant : Cert -> Cert -> Prop) : Prop :=
  ∀ c₁ c₂ : Cert,
    Domain c₁ -> Domain c₂ -> reading.Equivalent c₁ c₂ -> SameInvariant c₁ c₂

/-- Faithfulness is preserved when the reading is refined. -/
theorem reading_refinement_preserves_faithfulness {Cert : Type u}
    {fine coarse : Reading Cert} {SameInvariant : Cert -> Cert -> Prop}
    (hrefines : ReadingRefines fine coarse)
    (hfaithful : FaithfulToInvariant coarse SameInvariant) :
    FaithfulToInvariant fine SameInvariant := by
  intro c₁ c₂ heq
  exact hfaithful c₁ c₂ (hrefines heq)

/-- Restricted faithfulness is also preserved when the reading is refined. -/
theorem reading_refinement_preserves_faithfulness_on {Cert : Type u}
    {Domain : Cert -> Prop} {fine coarse : Reading Cert}
    {SameInvariant : Cert -> Cert -> Prop}
    (hrefines : ReadingRefines fine coarse)
    (hfaithful : FaithfulToInvariantOn Domain coarse SameInvariant) :
    FaithfulToInvariantOn Domain fine SameInvariant := by
  intro c₁ c₂ hc₁ hc₂ heq
  exact hfaithful c₁ c₂ hc₁ hc₂ (hrefines heq)

/-! ## The finite trace-locus reading chain -/

abbrev TraceCert :=
  TraceLocus.TraceLocusCertificate

/-- Same visible scalar and selected verdict. -/
def SameVisibleSurface (c₁ c₂ : TraceCert) : Prop :=
  c₁.visibleScalarReading = c₂.visibleScalarReading ∧
    c₁.verdict = c₂.verdict

/-- Same selected support, stated pointwise to avoid extensionality axioms. -/
def SameSelectedSupport (c₁ c₂ : TraceCert) : Prop :=
  ∀ atom, c₁.selectedSupport atom ↔ c₂.selectedSupport atom

/-- Same trace missing locus. -/
def SameTraceMissingLocus (c₁ c₂ : TraceCert) : Prop :=
  ∀ atom,
    TraceLocus.TraceMissingLocus c₁ atom ↔
      TraceLocus.TraceMissingLocus c₂ atom

/-- Same repair frontier. -/
def SameRepairFrontier (c₁ c₂ : TraceCert) : Prop :=
  ∀ atom, c₁.repairFrontier atom ↔ c₂.repairFrontier atom

/-- Reading that keeps only the visible surface. -/
def visibleSurfaceReading : Reading TraceCert where
  Equivalent := SameVisibleSurface

/-- Reading that keeps visible surface and selected support. -/
def supportSurfaceReading : Reading TraceCert where
  Equivalent := fun c₁ c₂ =>
    SameVisibleSurface c₁ c₂ ∧ SameSelectedSupport c₁ c₂

/-- Reading that also keeps the trace missing locus. -/
def traceLocusAwareReading : Reading TraceCert where
  Equivalent := fun c₁ c₂ =>
    supportSurfaceReading.Equivalent c₁ c₂ ∧ SameTraceMissingLocus c₁ c₂

/-- Reading that also keeps the repair frontier. -/
def repairAwareReading : Reading TraceCert where
  Equivalent := fun c₁ c₂ =>
    traceLocusAwareReading.Equivalent c₁ c₂ ∧ SameRepairFrontier c₁ c₂

/-- The support surface reading refines the visible surface reading. -/
theorem supportSurface_refines_visibleSurface :
    ReadingRefines supportSurfaceReading visibleSurfaceReading := by
  intro c₁ c₂ heq
  exact heq.1

/-- The trace-locus-aware reading refines the support surface reading. -/
theorem traceLocusAware_refines_supportSurface :
    ReadingRefines traceLocusAwareReading supportSurfaceReading := by
  intro c₁ c₂ heq
  exact heq.1

/-- The repair-aware reading refines the trace-locus-aware reading. -/
theorem repairAware_refines_traceLocusAware :
    ReadingRefines repairAwareReading traceLocusAwareReading := by
  intro c₁ c₂ heq
  exact heq.1

/-! ## Strictness: support surface is not trace / repair adequate -/

/-- The full and partial trace certificates agree at the support surface reading. -/
theorem full_partial_supportSurface_equivalent :
    supportSurfaceReading.Equivalent
      TraceLocus.fullTraceCert TraceLocus.partialTraceCert := by
  constructor
  · exact ⟨rfl, rfl⟩
  · intro atom
    constructor <;> intro _ <;> trivial

/--
Even after selected support is visible, the reading does not recover the trace
missing locus.
-/
theorem surfaceSupport_not_faithful_to_traceMissingLocus :
    ¬ FaithfulToInvariant supportSurfaceReading SameTraceMissingLocus := by
  intro hfaithful
  have hsame :=
    hfaithful TraceLocus.fullTraceCert TraceLocus.partialTraceCert
      full_partial_supportSurface_equivalent
  have hmissingFull :
      TraceLocus.TraceMissingLocus TraceLocus.fullTraceCert
        TraceLocus.LocusAtom.database :=
    (hsame TraceLocus.LocusAtom.database).mpr
      TraceLocus.partialTrace_database_missing_locus
  exact TraceLocus.fullTrace_has_no_missing_locus
    ⟨TraceLocus.LocusAtom.database, hmissingFull⟩

/-- The full trace certificate has exact repair frontier: no missing trace, no repair. -/
theorem fullTrace_repairFrontierExact :
    (∀ atom,
      TraceLocus.fullTraceCert.repairFrontier atom ↔
        TraceLocus.TraceMissingLocus TraceLocus.fullTraceCert atom) := by
  intro atom
  constructor
  · intro hrepair
    exact False.elim hrepair
  · intro hmissing
    exact TraceLocus.fullTrace_has_no_missing_locus ⟨atom, hmissing⟩

/-- The partial trace certificate has exact repair frontier at the missing trace locus. -/
theorem partialTrace_repairFrontierExact :
    (∀ atom,
      TraceLocus.partialTraceCert.repairFrontier atom ↔
        TraceLocus.TraceMissingLocus TraceLocus.partialTraceCert atom) :=
  TraceLocus.partialTrace_repair_frontier_matches_missing_locus

/-- Certificates whose repair frontier is exactly their trace missing locus. -/
def RepairFrontierExact (c : TraceCert) : Prop :=
  ∀ atom, c.repairFrontier atom ↔ TraceLocus.TraceMissingLocus c atom

/--
Inside the exact trace-repair regime, the support surface reading is still not
faithful to the repair frontier.
-/
theorem surfaceSupport_not_faithful_to_exactRepairFrontier :
    ¬ FaithfulToInvariantOn RepairFrontierExact
      supportSurfaceReading SameRepairFrontier := by
  intro hfaithful
  have hsame :=
    hfaithful TraceLocus.fullTraceCert TraceLocus.partialTraceCert
      fullTrace_repairFrontierExact partialTrace_repairFrontierExact
      full_partial_supportSurface_equivalent
  have hrepairFull :
      TraceLocus.fullTraceCert.repairFrontier TraceLocus.LocusAtom.database :=
    (hsame TraceLocus.LocusAtom.database).mpr
      TraceLocus.partialTrace_forces_database_repair
  exact TraceLocus.fullTrace_repair_frontier_excludes_database hrepairFull

/-! ## Adequacy under exact trace-repair -/

/--
In the exact trace-repair regime, a trace-locus-aware reading is faithful to the
repair frontier.
-/
theorem traceLocusAware_faithful_to_repairFrontier_of_exact :
    FaithfulToInvariantOn RepairFrontierExact
      traceLocusAwareReading SameRepairFrontier := by
  intro c₁ c₂ hexact₁ hexact₂ heq atom
  have hmissing := heq.2 atom
  constructor
  · intro hrepair₁
    have hmissing₁ : TraceLocus.TraceMissingLocus c₁ atom :=
      (hexact₁ atom).mp hrepair₁
    have hmissing₂ : TraceLocus.TraceMissingLocus c₂ atom :=
      hmissing.mp hmissing₁
    exact (hexact₂ atom).mpr hmissing₂
  · intro hrepair₂
    have hmissing₂ : TraceLocus.TraceMissingLocus c₂ atom :=
      (hexact₂ atom).mp hrepair₂
    have hmissing₁ : TraceLocus.TraceMissingLocus c₁ atom :=
      hmissing.mpr hmissing₂
    exact (hexact₁ atom).mpr hmissing₁

/--
The cycle-6 witness is exactly the adequacy gap: support surface agrees, but
trace locus and exact repair frontier do not.
-/
theorem same_surface_support_but_trace_locus_adequacy_gap :
    supportSurfaceReading.Equivalent
      TraceLocus.fullTraceCert TraceLocus.partialTraceCert ∧
      ¬ SameTraceMissingLocus
        TraceLocus.fullTraceCert TraceLocus.partialTraceCert ∧
      RepairFrontierExact TraceLocus.fullTraceCert ∧
      RepairFrontierExact TraceLocus.partialTraceCert ∧
      ¬ SameRepairFrontier
        TraceLocus.fullTraceCert TraceLocus.partialTraceCert := by
  constructor
  · exact full_partial_supportSurface_equivalent
  constructor
  · intro hsame
    have hmissingFull :
        TraceLocus.TraceMissingLocus TraceLocus.fullTraceCert
          TraceLocus.LocusAtom.database :=
      (hsame TraceLocus.LocusAtom.database).mpr
        TraceLocus.partialTrace_database_missing_locus
    exact TraceLocus.fullTrace_has_no_missing_locus
      ⟨TraceLocus.LocusAtom.database, hmissingFull⟩
  constructor
  · exact fullTrace_repairFrontierExact
  constructor
  · exact partialTrace_repairFrontierExact
  · intro hrepair
    have hrepairFull :
        TraceLocus.fullTraceCert.repairFrontier TraceLocus.LocusAtom.database :=
      (hrepair TraceLocus.LocusAtom.database).mpr
        TraceLocus.partialTrace_forces_database_repair
    exact TraceLocus.fullTrace_repair_frontier_excludes_database hrepairFull

/-! ## Cycle-7 path-ordered trace adequacy gap -/

abbrev TraceUpperRightCert :=
  TraceCurvature.CertificateAt TraceCurvature.TraceProfile.upperRight

/-- Same visible upper-right trace surface and selected support. -/
def SameUpperRightTraceSupportSurface
    (c₁ c₂ : TraceUpperRightCert) : Prop :=
  TraceCurvature.scalarReading c₁.val =
      TraceCurvature.scalarReading c₂.val ∧
    TraceCurvature.verdict c₁.val = TraceCurvature.verdict c₂.val ∧
    TraceCurvature.support c₁.val = TraceCurvature.support c₂.val

/-- Same path-ordered repair frontier at the upper-right trace profile. -/
def SameUpperRightRepairFrontier
    (c₁ c₂ : TraceUpperRightCert) : Prop :=
  ∀ atom,
    TraceCurvature.repairFrontier c₁.val atom ↔
      TraceCurvature.repairFrontier c₂.val atom

/--
The cycle-7 trace-curvature cell has the same visible upper-right support
surface along both paths, but not the same path-ordered repair frontier.
-/
theorem traceCurvature_surfaceSupport_not_pathOrderedRepairAdequate :
    ¬ (∀ c₁ c₂ : TraceUpperRightCert,
      SameUpperRightTraceSupportSurface c₁ c₂ ->
        SameUpperRightRepairFrontier c₁ c₂) := by
  intro hfaithful
  have hsameSurface :
      SameUpperRightTraceSupportSurface
        (TraceCurvature.lawThenCover TraceCurvature.seedAt)
        (TraceCurvature.coverThenLaw TraceCurvature.seedAt) :=
    ⟨TraceCurvature.same_scalar_after_trace_paths,
      TraceCurvature.same_verdict_after_trace_paths,
      TraceCurvature.same_support_after_trace_paths⟩
  have hrepairSame :=
    hfaithful
      (TraceCurvature.lawThenCover TraceCurvature.seedAt)
      (TraceCurvature.coverThenLaw TraceCurvature.seedAt)
      hsameSurface
  have hrepairLawThenCover :
      TraceCurvature.repairFrontier
        (TraceCurvature.lawThenCover TraceCurvature.seedAt).val
        TraceLocus.LocusAtom.database :=
    (hrepairSame TraceLocus.LocusAtom.database).mpr
      TraceCurvature.coverThenLaw_forces_database_repair
  exact TraceCurvature.lawThenCover_no_database_repair hrepairLawThenCover

end ReadingAdequacy
end QualitySurface
end Formal.AG.Research
