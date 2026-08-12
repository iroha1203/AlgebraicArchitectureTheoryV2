import ResearchLean.AG.UniformInvariance.ConditionCAllABridge
import ResearchLean.AG.UniformInvariance.ConditionCAllAChecker
import ResearchLean.AG.UniformInvariance.UniformPresentationDecider
import Formal.Util.AssertStandardAxioms

/-!
# A uniform comparison outside the C4 locus

This module formalizes the exact `C4_not_necessary` fixture from the bounded
R1 necessity map for `G-107-aat-uniform-invariance-characterization`.  The
parent R1 payload has SHA-256
`ff2d9fa12eb64bf343d3148f081e1164d4216d8548e53d90550eb53886dd359a`,
and the canonical name-free serializer recomputes SHA-256
`5e6e1cb8fdaf2e0015007e80f029528455c587d56a40a47299d075323e366a74`.

Both nerves have two charts and the same two self-loops.  The coarse nerve has
two repeated faces with boundary `(1,1,1)`, while the fine nerve has only one,
mapped to the first coarse face.  Hence the second coarse face has no fine
lift on the full target subset.  The repeated face kills only the chart-one
self-loop in H¹ on either side; the chart-zero self-loop survives, so the
actual comparison is bijective on every target subset and both full-subset H¹
spaces are nonzero.

The finite presentation stores only raw readings, incidence, support, partial
cell maps, and their well-formedness proofs.  It stores no factor, lift,
matrix, rank, cohomology class, defect, condition result, checker result, or
uniformity certificate.  The experiment payload directly fixes the factor,
target counts, nerves, supports, and cell maps.  The `Fin 3` source and the two
reading tables below form the canonical finite realization of that factor;
they are not fields copied from the payload.  The artifact is provenance for
this directly fixed geometry and its canonical realization, not a premise of
a Lean theorem below.
-/

namespace AAT.AG.ResolutionInvariance

open CanonicalResolution Cohomology TwoPhase

namespace R1ConditionC4Witness

/-! ## Exact raw R1 presentation -/

/-- The proper coarse reading table `[0,0,1]`.  This is raw fixture input, not
a supplied comparison factor. -/
def coarseRead (source : Fin 3) : Fin 2 :=
  if source = 2 then 1 else 0

/-- Coarse chart supports `[{0},{1}]`.  This raw table contains no C4 result. -/
def coarseChartSupport (chart : Fin 2) : Finset (Fin 2) :=
  if chart = 0 then {0} else {1}

/-- Fine chart supports `[{0,1},{2}]`.  This raw table realizes the proper
reading factor without storing it. -/
def fineChartSupport (chart : Fin 2) : Finset (Fin 3) :=
  if chart = 0 then {0, 1} else {2}

/-- Exact finite R1 C4 presentation.  Its two coarse faces and one fine face
are raw incidence data; no face-lift, H¹, rank, or truth certificate is stored. -/
def presentation : FiniteComparisonPresentation where
  Source := Fin 3
  sourceFintype := inferInstance
  sourceDecidableEq := inferInstance
  sourceDefault := 0
  sourceEntries := [0, 1, 2]
  source_mem_sourceEntries := by intro source; fin_cases source <;> simp
  CoarseTarget := Fin 2
  coarseTargetFintype := inferInstance
  coarseTargetDecidableEq := inferInstance
  coarseTargetEntries := [0, 1]
  coarseTarget_mem_coarseTargetEntries := by intro target; fin_cases target <;> simp
  FineTarget := Fin 3
  fineTargetFintype := inferInstance
  fineTargetDecidableEq := inferInstance
  coarseRead := coarseRead
  fineRead := id
  coarseRead_surjective := by
    intro target
    fin_cases target
    · exact ⟨0, by simp [coarseRead]⟩
    · exact ⟨2, by simp [coarseRead]⟩
  fineRead_surjective := Function.surjective_id
  rawCoarserThan := by
    intro left right hequal
    simpa only [id_eq] using congrArg coarseRead hequal
  CoarseChart := Fin 2
  coarseChartFintype := inferInstance
  coarseChartDecidableEq := inferInstance
  coarseChartEntries := List.finRange 2
  coarseChart_mem_coarseChartEntries := by intro chart; simp
  CoarseEdge := Fin 2
  coarseEdgeFintype := inferInstance
  coarseEdgeDecidableEq := inferInstance
  coarseEdgeEntries := List.finRange 2
  coarseEdge_mem_coarseEdgeEntries := by intro edge; simp
  CoarseFace := Fin 2
  coarseFaceFintype := inferInstance
  coarseFaceDecidableEq := inferInstance
  coarseFaceEntries := List.finRange 2
  coarseFace_mem_coarseFaceEntries := by intro face; simp
  coarseEdgeLeft := id
  coarseEdgeRight := id
  coarseFaceEdge0 := fun _ => 1
  coarseFaceEdge1 := fun _ => 1
  coarseFaceEdge2 := fun _ => 1
  coarseFaceEdge0_left := by intro face; rfl
  coarseFaceEdge0_right := by intro face; rfl
  coarseFaceEdge1_right := by intro face; rfl
  coarseChartSupport := coarseChartSupport
  coarseChartSupport_nonempty := by
    intro chart
    fin_cases chart <;> simp [coarseChartSupport]
  FineChart := Fin 2
  fineChartFintype := inferInstance
  fineChartDecidableEq := inferInstance
  fineChartEntries := List.finRange 2
  fineChart_mem_fineChartEntries := by intro chart; simp
  FineEdge := Fin 2
  fineEdgeFintype := inferInstance
  fineEdgeDecidableEq := inferInstance
  fineEdgeEntries := List.finRange 2
  fineEdge_mem_fineEdgeEntries := by intro edge; simp
  FineFace := Fin 1
  fineFaceFintype := inferInstance
  fineFaceDecidableEq := inferInstance
  fineFaceEntries := List.finRange 1
  fineFace_mem_fineFaceEntries := by intro face; simp
  fineEdgeLeft := id
  fineEdgeRight := id
  fineFaceEdge0 := fun _ => 1
  fineFaceEdge1 := fun _ => 1
  fineFaceEdge2 := fun _ => 1
  fineFaceEdge0_left := by intro face; rfl
  fineFaceEdge0_right := by intro face; rfl
  fineFaceEdge1_right := by intro face; rfl
  fineChartSupport := fineChartSupport
  fineChartSupport_nonempty := by
    intro chart
    fin_cases chart <;> simp [fineChartSupport]
  chartMap := id
  edgeMap := some
  faceMap := fun _ => some 0
  edge_some_left := by
    intro fineEdge coarseEdge hmap
    exact Option.some.inj hmap
  edge_some_right := by
    intro fineEdge coarseEdge hmap
    exact Option.some.inj hmap
  edge_none_fiber := by intro fineEdge hmap; simp at hmap
  face_some_edge0 := by
    intro fineFace coarseFace hmap
    fin_cases fineFace
    fin_cases coarseFace <;> simp at hmap
    rfl
  face_some_edge1 := by
    intro fineFace coarseFace hmap
    fin_cases fineFace
    fin_cases coarseFace <;> simp at hmap
    rfl
  face_some_edge2 := by
    intro fineFace coarseFace hmap
    fin_cases fineFace
    fin_cases coarseFace <;> simp at hmap
    rfl
  face_none_edge0 := by intro fineFace hmap; simp at hmap
  face_none_edge1 := by intro fineFace hmap; simp at hmap
  face_none_edge2 := by intro fineFace hmap; simp at hmap
  chartSupport_compatible_source := by
    intro fineChart source hsource
    fin_cases fineChart <;> fin_cases source <;>
      simp [fineChartSupport, coarseChartSupport, coarseRead] at hsource ⊢

/-! ## Canonical factor and raw degree-one comparison -/

/-- The executable factor is `[0,0,1]`, generated from the source enumeration
and the two raw readings. -/
theorem computedFactor_eq_coarseRead : presentation.computedFactor = coarseRead := by
  funext target
  fin_cases target <;> decide

/-- The semantic canonical factor is the same table by generic uniqueness. -/
theorem comparisonFactor_eq_coarseRead :
    comparisonFactor presentation.coarseReading presentation.fineReading
      presentation.coarserThan = coarseRead := by
  rw [← presentation.computedFactor_eq_comparisonFactor]
  exact computedFactor_eq_coarseRead

/-- Selected fine and coarse edge tables coincide for every coarse target
subset.  This is derived solely from supports and the computed factor. -/
theorem fineEdgesIn_eq_coarseEdgesIn (A : Finset (Fin 2)) :
    presentation.fineEdgesIn A = presentation.coarseEdgesIn A := by
  ext edge
  rw [presentation.mem_fineEdgesIn_iff_raw,
    presentation.mem_coarseEdgesIn_iff_raw, computedFactor_eq_coarseRead]
  simp only [presentation.mem_fineEdgeSupportFinset_iff_raw,
    presentation.mem_coarseEdgeSupportFinset_iff_raw]
  fin_cases edge <;>
    simp [presentation, fineChartSupport, coarseChartSupport, coarseRead]

/-- Forgetting selection proofs identifies selected fine and coarse edges. -/
def selectedEdgeEquiv (A : Finset (Fin 2)) :
    presentation.FineEdgeIn A ≃ presentation.CoarseEdgeIn A where
  toFun edge := ⟨edge.1, by
    rw [← fineEdgesIn_eq_coarseEdgesIn A]
    exact edge.2⟩
  invFun edge := ⟨edge.1, by
    rw [fineEdgesIn_eq_coarseEdgesIn A]
    exact edge.2⟩
  left_inv edge := Subtype.ext rfl
  right_inv edge := Subtype.ext rfl

/-- Reindex coarse edge cochains through the selected raw edge identity. -/
def rawEdgeCochainEquiv (A : Finset (Fin 2)) :
    (presentation.CoarseEdgeIn A → ℚ) ≃ₗ[ℚ]
      (presentation.FineEdgeIn A → ℚ) :=
  cochainEquivOfIndexEquiv (selectedEdgeEquiv A)

/-- The selected raw edge map is exactly the selected-edge equivalence. -/
theorem edgeMapOptionIn_eq_some_selected (A : Finset (Fin 2))
    (edge : presentation.FineEdgeIn A) :
    presentation.edgeMapOptionIn A edge = some (selectedEdgeEquiv A edge) := by
  exact (presentation.edgeMapOptionIn_eq_some_iff A edge
    (selectedEdgeEquiv A edge)).2 rfl

/-- Raw degree-one pullback is the edge reindexing induced by the identity
edge table. -/
theorem edgePullback1_eq_rawEdgeCochainEquiv (A : Finset (Fin 2))
    (cochain : presentation.CoarseEdgeIn A → ℚ) :
    presentation.edgePullback1LinearMap A cochain =
      rawEdgeCochainEquiv A cochain := by
  funext edge
  rw [presentation.edgePullback1LinearMap_apply,
    edgeMapOptionIn_eq_some_selected]
  rfl

/-! ## Raw repeated-face cocycle transport -/

/-- Every coarse repeated face is selected exactly when target one is
selected.  The face index itself is immaterial because both supports agree. -/
theorem coarseFace_mem_iff_one_mem (A : Finset (Fin 2)) (face : Fin 2) :
    face ∈ presentation.coarseFacesIn A ↔ (1 : Fin 2) ∈ A := by
  rw [presentation.mem_coarseFacesIn_iff_raw]
  simp only [presentation.mem_coarseFaceSupportFinset_iff_raw,
    presentation.mem_coarseEdgeSupportFinset_iff_raw]
  fin_cases face <;> simp [presentation, coarseChartSupport]

/-- The unique fine repeated face is selected exactly when target one is
selected, after computing the canonical preimage. -/
theorem fineFace_mem_iff_one_mem (A : Finset (Fin 2)) :
    (0 : Fin 1) ∈ presentation.fineFacesIn A ↔ (1 : Fin 2) ∈ A := by
  rw [presentation.mem_fineFacesIn_iff_raw, computedFactor_eq_coarseRead]
  simp only [presentation.mem_fineFaceSupportFinset_iff_raw,
    presentation.mem_fineEdgeSupportFinset_iff_raw]
  simp [presentation, fineChartSupport, coarseRead]

/-- A selected coarse repeated face canonically supplies the unique selected
fine repeated face.  This is raw cell data, not a face-lift certificate. -/
def fineFaceOfCoarse (A : Finset (Fin 2))
    (face : presentation.CoarseFaceIn A) : presentation.FineFaceIn A :=
  ⟨(show presentation.FineFace from (0 : Fin 1)),
    (fineFace_mem_iff_one_mem A).2
    ((coarseFace_mem_iff_one_mem A face.1).1 face.2)⟩

/-- Vanishing of the fine raw degree-one differential forces vanishing of the
coarse raw differential.  Both repeated-face tables evaluate the same
edge-one coefficient, so the extra coarse face adds no new cocycle equation. -/
theorem coarseD1_eq_zero_of_fineD1_eq_zero (A : Finset (Fin 2))
    (cochain : presentation.CoarseEdgeIn A → ℚ)
    (hfine : presentation.fineD1LinearMap A
      (rawEdgeCochainEquiv A cochain) = 0) :
    presentation.coarseD1LinearMap A cochain = 0 := by
  funext coarseFace
  let fineFace := fineFaceOfCoarse A coarseFace
  have hvalue := congrFun hfine fineFace
  rw [presentation.fineD1LinearMap_apply] at hvalue
  simp only [Pi.zero_apply] at hvalue
  rw [presentation.coarseD1LinearMap_apply]
  have hedge0 :
      selectedEdgeEquiv A (presentation.fineFaceEdge0In A fineFace) =
        presentation.coarseFaceEdge0In A coarseFace := by
    apply Subtype.ext
    rfl
  have hedge1 :
      selectedEdgeEquiv A (presentation.fineFaceEdge1In A fineFace) =
        presentation.coarseFaceEdge1In A coarseFace := by
    apply Subtype.ext
    rfl
  have hedge2 :
      selectedEdgeEquiv A (presentation.fineFaceEdge2In A fineFace) =
        presentation.coarseFaceEdge2In A coarseFace := by
    apply Subtype.ext
    rfl
  change
    cochain (selectedEdgeEquiv A (presentation.fineFaceEdge0In A fineFace)) -
          cochain (selectedEdgeEquiv A (presentation.fineFaceEdge1In A fineFace)) +
        cochain (selectedEdgeEquiv A
          (presentation.fineFaceEdge2In A fineFace)) = 0 at hvalue
  simpa [hedge0, hedge1, hedge2] using hvalue

/-! ## Actual H¹ comparison on every target subset -/

/-- The actual coarse constant-rational A-subnerve complex. -/
abbrev coarseComplex (A : Finset (Fin 2)) : ThreeCochainComplex ℚ :=
  presentation.coarseSupportedNerve.targetSubsetComplex (↑A : Set (Fin 2))

/-- The actual fine complex on the canonical preimage of `A`. -/
abbrev fineComplex (A : Finset (Fin 2)) : ThreeCochainComplex ℚ :=
  presentation.fineSupportedNerve.targetSubsetComplex
    (presentation.canonicalFinePreimage A)

/-- Degree-one equivalence between the actual selected edge cochains. -/
noncomputable def semanticEdgeCochainEquiv (A : Finset (Fin 2)) :
    (coarseComplex A).C1 ≃ₗ[ℚ] (fineComplex A).C1 :=
  (presentation.coarseEdgeCochainEquiv A).trans
    ((rawEdgeCochainEquiv A).trans
      (presentation.fineEdgeCochainEquiv A).symm)

/-- The actual comparison's degree-one map is the constructed edge-cochain
equivalence, by the raw partial-edge table. -/
theorem aSubnerveComparisonHom_f1_eq_semanticEquiv
    (A : Finset (Fin 2)) (cochain : (coarseComplex A).C1) :
    (presentation.toGeometry.aSubnerveComparisonHom
        (↑A : Set (Fin 2))).f1 cochain =
      semanticEdgeCochainEquiv A cochain := by
  apply (presentation.fineEdgeCochainEquiv A).injective
  rw [← presentation.edgePullback1_commutes A cochain]
  simp only [semanticEdgeCochainEquiv, LinearEquiv.trans_apply]
  exact edgePullback1_eq_rawEdgeCochainEquiv A
    (presentation.coarseEdgeCochainEquiv A cochain)

/-- Every fine degree-zero boundary vanishes because every selected fine edge
is a self-loop. -/
theorem fine_d0_zero (A : Finset (Fin 2)) (cochain : (fineComplex A).C0) :
    (fineComplex A).d0 cochain = 0 := by
  funext edge
  rw [TargetSupportedNerve.targetSubsetComplex_d0_apply]
  have hloop :
      presentation.fineSupportedNerve.targetSubsetEdgeRight
          (presentation.canonicalFinePreimage A) edge =
        presentation.fineSupportedNerve.targetSubsetEdgeLeft
          (presentation.canonicalFinePreimage A) edge := by
    apply Subtype.ext
    rfl
  rw [hloop, sub_self]
  rfl

/-- A fine actual cocycle pulls back through the edge equivalence to a coarse
actual cocycle.  The proof uses the raw repeated-face equality rather than a
stored cocycle certificate. -/
theorem coarse_cycle_of_fine_cycle (A : Finset (Fin 2))
    (cochain : (coarseComplex A).C1)
    (hfine : (fineComplex A).d1 (semanticEdgeCochainEquiv A cochain) = 0) :
    (coarseComplex A).d1 cochain = 0 := by
  have hfineRaw :
      presentation.fineD1LinearMap A
        (rawEdgeCochainEquiv A
          (presentation.coarseEdgeCochainEquiv A cochain)) = 0 := by
    have hcomm := presentation.fineD1_commutes A
      (semanticEdgeCochainEquiv A cochain)
    calc
      presentation.fineD1LinearMap A
          (rawEdgeCochainEquiv A
            (presentation.coarseEdgeCochainEquiv A cochain)) =
        presentation.fineFaceCochainEquiv A
          ((fineComplex A).d1 (semanticEdgeCochainEquiv A cochain)) := by
            simpa only [semanticEdgeCochainEquiv, LinearEquiv.trans_apply,
              LinearEquiv.apply_symm_apply] using hcomm
      _ = 0 := by rw [hfine, map_zero]
  have hcoarseRaw := coarseD1_eq_zero_of_fineD1_eq_zero A
    (presentation.coarseEdgeCochainEquiv A cochain) hfineRaw
  have hcomm := presentation.coarseD1_commutes A cochain
  apply (presentation.coarseFaceCochainEquiv A).injective
  rw [map_zero]
  calc
    presentation.coarseFaceCochainEquiv A ((coarseComplex A).d1 cochain) =
        presentation.coarseD1LinearMap A
          (presentation.coarseEdgeCochainEquiv A cochain) := by
            simpa only [] using hcomm.symm
    _ = 0 := hcoarseRaw

/-- The actual canonical H¹ comparison is bijective on every finite target
subset.  Injectivity uses zero fine boundaries and the edge equivalence;
surjectivity pulls fine cycles back and applies repeated-face cocycle transport. -/
theorem aSubnerveComparisonHom_h1Map_bijective (A : Finset (Fin 2)) :
    Function.Bijective
      (presentation.toGeometry.aSubnerveComparisonHom
        (↑A : Set (Fin 2))).h1Map := by
  constructor
  · intro left right hequal
    obtain ⟨leftCycle, rfl⟩ :=
      (LinearMap.range (coarseComplex A).boundaryToCycles).mkQ_surjective left
    obtain ⟨rightCycle, rfl⟩ :=
      (LinearMap.range (coarseComplex A).boundaryToCycles).mkQ_surjective right
    rw [ThreeCochainComplex.Hom.h1Map_mk,
      ThreeCochainComplex.Hom.h1Map_mk] at hequal
    have hquotientZero :
        (LinearMap.range (fineComplex A).boundaryToCycles).mkQ
            ((presentation.toGeometry.aSubnerveComparisonHom
              (↑A : Set (Fin 2))).cyclesMap leftCycle -
              (presentation.toGeometry.aSubnerveComparisonHom
                (↑A : Set (Fin 2))).cyclesMap rightCycle) = 0 := by
      rw [map_sub, hequal, sub_self]
    have hequalMem :=
      (Submodule.Quotient.mk_eq_zero
        (LinearMap.range (fineComplex A).boundaryToCycles)).1 hquotientZero
    rcases hequalMem with ⟨fineCochain, hfineCochain⟩
    have hvalues := congrArg Subtype.val hfineCochain
    simp only [ThreeCochainComplex.boundaryToCycles_apply,
      ThreeCochainComplex.Hom.cyclesMap_sub_apply] at hvalues
    rw [fine_d0_zero] at hvalues
    have hdiff : leftCycle.1 - rightCycle.1 = 0 := by
      apply (semanticEdgeCochainEquiv A).injective
      rw [map_sub, map_zero]
      rw [← aSubnerveComparisonHom_f1_eq_semanticEquiv,
        ← aSubnerveComparisonHom_f1_eq_semanticEquiv]
      exact hvalues.symm
    have hcycles : leftCycle = rightCycle := by
      apply Subtype.ext
      exact sub_eq_zero.mp hdiff
    rw [hcycles]
  · intro targetClass
    obtain ⟨targetCycle, rfl⟩ :=
      (LinearMap.range (fineComplex A).boundaryToCycles).mkQ_surjective targetClass
    let sourceCochain : (coarseComplex A).C1 :=
      (semanticEdgeCochainEquiv A).symm targetCycle.1
    have hfineCycle :
        (fineComplex A).d1 (semanticEdgeCochainEquiv A sourceCochain) = 0 := by
      rw [(semanticEdgeCochainEquiv A).apply_symm_apply]
      exact targetCycle.2
    have hcycle : (coarseComplex A).d1 sourceCochain = 0 :=
      coarse_cycle_of_fine_cycle A sourceCochain hfineCycle
    let sourceCycle : LinearMap.ker (coarseComplex A).d1 :=
      ⟨sourceCochain, hcycle⟩
    refine ⟨(LinearMap.range (coarseComplex A).boundaryToCycles).mkQ
      sourceCycle, ?_⟩
    rw [ThreeCochainComplex.Hom.h1Map_mk]
    apply congrArg (LinearMap.range (fineComplex A).boundaryToCycles).mkQ
    apply Subtype.ext
    rw [ThreeCochainComplex.Hom.cyclesMap_apply]
    rw [aSubnerveComparisonHom_f1_eq_semanticEquiv]
    exact (semanticEdgeCochainEquiv A).apply_symm_apply targetCycle.1

/-! ## Exact uniformity and direct C4 failure -/

/-- Every executable A-subnerve defect is `(0,0)`, through the generic
raw-to-actual theorem and the actual H¹ bijectivity proof above. -/
theorem all_computedASubnerveDefects_zero (A : Finset (Fin 2)) :
    presentation.computedASubnerveDefect A = (0, 0) := by
  rw [presentation.computedASubnerveDefect_eq_aSubnerveDefect]
  exact
    (presentation.toGeometry.aSubnerveDefect_eq_zero_iff_bijective
      (↑A : Set (Fin 2))).2
      (aSubnerveComparisonHom_h1Map_bijective A)

/-- The generic all-subset uniformity checker accepts the raw C4 fixture. -/
theorem uniformPresentationCheck_true :
    presentation.uniformPresentationCheck = true := by
  apply
    (presentation.uniformPresentationCheck_eq_true_iff_allNonemptyDefects).2
  intro A _hA
  exact all_computedASubnerveDefects_zero A

/-- The exact R1 presentation is semantically uniformly invariant, with all
law families and adequacy proofs still quantified internally. -/
theorem uniformPresentation : UniformPresentation presentation :=
  presentation.uniformPresentationCheck_eq_true_iff.mp
    uniformPresentationCheck_true

/-- The full coarse target subset.  It contains both the missing-face C4
obstruction and the common nonzero chart-zero H¹ loop. -/
def targetFull : Finset (Fin 2) := Finset.univ

/-- The full target subset is nonempty. -/
theorem targetFull_nonempty :
    (↑targetFull : Set (Fin 2)).Nonempty :=
  ⟨0, by simp [targetFull]⟩

/-- The second coarse repeated face, selected on the full target subset. -/
def coarseFaceOne : presentation.CoarseFaceIn targetFull :=
  ⟨(show presentation.CoarseFace from (1 : Fin 2)), by decide⟩

/-- Raw C4 fails on the full target subset because the unique fine face maps
to coarse face zero, never to the displayed coarse face one. -/
theorem not_rawConditionC4At :
    ¬ presentation.RawConditionC4At targetFull := by
  intro hC4
  obtain ⟨fineFace, hmap⟩ := hC4 coarseFaceOne
  have hfine : fineFace.1 =
      (show presentation.FineFace from (0 : Fin 1)) :=
    by
      change (fineFace.1 : Fin 1) = (0 : Fin 1)
      exact Fin.ext (by omega)
  simp [presentation, hfine, coarseFaceOne] at hmap

/-- The executable C4 checker returns false on the same full target subset. -/
theorem conditionC4AtTargetSubsetCheck_false :
    presentation.conditionC4AtTargetSubsetCheck targetFull = false := by
  apply Bool.eq_false_of_not_eq_true
  intro htrue
  exact not_rawConditionC4At (of_decide_eq_true htrue)

/-- Semantic C4 fails on the actual full A-subnerve under the canonical
raw/semantic face equivalences. -/
theorem not_conditionC4AtTargetSubset :
    ¬ presentation.toGeometry.ConditionC4AtTargetSubset
      (↑targetFull : Set (Fin 2)) := by
  intro hC4
  exact not_rawConditionC4At
    ((presentation.rawConditionC4At_iff_conditionC4AtTargetSubset
      targetFull).mpr hC4)

/-- `ConditionCAllA` fails directly at its C4 projection on the same nonempty
full subset. -/
theorem not_conditionCAllA :
    ¬ presentation.toGeometry.ConditionCAllA := by
  intro hAllA
  exact not_conditionC4AtTargetSubset
    (hAllA.conditionC4At presentation.toGeometry
      (↑targetFull : Set (Fin 2)) targetFull_nonempty)

/-- The generic all-subset Condition C checker is false by semantic
soundness and the direct full-subset C4 obstruction. -/
theorem conditionCAllACheck_false :
    presentation.conditionCAllACheck = false := by
  apply Bool.eq_false_of_not_eq_true
  intro htrue
  exact not_conditionCAllA
    (presentation.conditionCAllACheck_eq_true_iff.mp htrue)

/-! ## Law-indexed C4 failure on the same label fiber -/

/-- The canonical Boolean indicator family of the full target subset.  Its
constant true value is permitted by the fixed C4 witness specification;
nonvacuity comes from the proper factor, missing face lift, and nonzero H¹. -/
noncomputable def indicatorLaws : FiniteLawFamily presentation.Source :=
  indicatorLawFamily presentation.coarseReading
    (↑targetFull : Set (Fin 2))

/-- Canonical adequacy of the full-subset indicator for the coarse reading. -/
theorem indicatorCoarseAdequate :
    indicatorLaws.Adequate presentation.coarseReading :=
  indicatorLawFamily_adequate presentation.coarseReading
    (↑targetFull : Set (Fin 2))

/-- Canonical adequacy of the same indicator for the fine reading. -/
theorem indicatorFineAdequate :
    indicatorLaws.Adequate presentation.fineReading :=
  indicatorLawFamily_adequate_of_coarserThan presentation.coarseReading
    presentation.fineReading presentation.coarserThan
    (↑targetFull : Set (Fin 2))

/-- The source-generated true label of the full-subset indicator. -/
noncomputable def indicatorLabel : LawValueLabel indicatorLaws :=
  indicatorLawFamilyTrueLabel presentation.coarseReading
    (↑targetFull : Set (Fin 2)) targetFull_nonempty

/-- The generated label fiber is exactly the full target subset. -/
theorem indicatorFiber_eq_targetFull :
    labelValueFiber indicatorLaws presentation.coarseReading
        indicatorCoarseAdequate indicatorLabel =
      (↑targetFull : Set (Fin 2)) :=
  indicatorLawFamily_trueFiber_eq presentation.coarseReading
    (↑targetFull : Set (Fin 2)) targetFull_nonempty

/-- Law-block C4 at the generated label would transport back to the directly
refuted actual full-subset C4 proposition. -/
theorem indicator_not_conditionC4At :
    ¬ presentation.toGeometry.ConditionC4At indicatorLaws
      indicatorCoarseAdequate indicatorFineAdequate indicatorLabel := by
  intro hC4
  apply not_conditionC4AtTargetSubset
  rw [← indicatorFiber_eq_targetFull]
  exact
    presentation.toGeometry.conditionC4AtTargetSubset_of_conditionC4At_labelValueFiber
      indicatorLaws indicatorCoarseAdequate indicatorFineAdequate
      indicatorLabel hC4

/-- The law-indexed C4 package fails at the generated true label. -/
theorem indicator_not_conditionC4 :
    ¬ presentation.toGeometry.ConditionC4 indicatorLaws
      indicatorCoarseAdequate indicatorFineAdequate := by
  intro hC4
  exact indicator_not_conditionC4At (hC4 indicatorLabel)

/-- The complete G-104 Condition C package fails by its C4 field. -/
theorem indicator_not_conditionC :
    ¬ presentation.toGeometry.ConditionC indicatorLaws
      indicatorCoarseAdequate indicatorFineAdequate := by
  intro hC
  exact indicator_not_conditionC4 hC.c4

/-! ## Nonzero H¹ on the full block meeting the C4 failure subset -/

/-- The actual coarse full-target complex. -/
abbrev coarseTargetFullComplex : ThreeCochainComplex ℚ :=
  coarseComplex targetFull

/-- The actual fine complex on the canonical preimage of the full target. -/
abbrev fineTargetFullComplex : ThreeCochainComplex ℚ :=
  fineComplex targetFull

/-- The raw coarse chart-zero self-loop selected by the full target. -/
def coarseEdgeZero : presentation.CoarseEdgeIn targetFull :=
  ⟨(show presentation.CoarseEdge from (0 : Fin 2)), by decide⟩

/-- The corresponding actual A-subnerve self-loop. -/
def coarseActualEdgeZero :
    presentation.coarseSupportedNerve.EdgeInTargetSubset
      (↑targetFull : Set (Fin 2)) :=
  presentation.coarseEdgeEquiv targetFull coarseEdgeZero

/-- Evaluation on the actual chart-zero self-loop. -/
def coarseTargetFullPeriod (cochain : coarseTargetFullComplex.C1) : ℚ :=
  cochain coarseActualEdgeZero

/-- Public evaluation rule for the period functional. -/
@[simp]
theorem coarseTargetFullPeriod_apply (cochain : coarseTargetFullComplex.C1) :
    coarseTargetFullPeriod cochain = cochain coarseActualEdgeZero :=
  rfl

/-- Every coarse coboundary has zero chart-zero loop period. -/
theorem coarseTargetFullPeriod_boundary_zero
    (cochain : coarseTargetFullComplex.C0) :
    coarseTargetFullPeriod (coarseTargetFullComplex.d0 cochain) = 0 := by
  rw [coarseTargetFullPeriod_apply,
    TargetSupportedNerve.targetSubsetComplex_d0_apply]
  have hloop :
      presentation.coarseSupportedNerve.targetSubsetEdgeRight
          (↑targetFull : Set (Fin 2)) coarseActualEdgeZero =
        presentation.coarseSupportedNerve.targetSubsetEdgeLeft
          (↑targetFull : Set (Fin 2)) coarseActualEdgeZero := by
    apply Subtype.ext
    rfl
  rw [hloop]
  ring

/-- The raw cochain which is one on the chart-zero edge and zero on the
chart-one edge.  It is explicit proof data, not a presentation field. -/
def coarseTargetFullRawCochain :
    presentation.CoarseEdgeIn targetFull → ℚ :=
  fun edge =>
    if edge.1 = (show presentation.CoarseEdge from (0 : Fin 2)) then 1 else 0

/-- The same cochain on the actual A-subnerve, obtained through the canonical
raw/semantic edge equivalence. -/
noncomputable def coarseTargetFullCochain : coarseTargetFullComplex.C1 :=
  (presentation.coarseEdgeCochainEquiv targetFull).symm
    coarseTargetFullRawCochain

/-- The raw loop cochain is a cocycle for both repeated coarse faces. -/
theorem coarseTargetFullRawCochain_cocycle :
    presentation.coarseD1LinearMap targetFull
      coarseTargetFullRawCochain = 0 := by
  funext face
  rw [presentation.coarseD1LinearMap_apply]
  have hedge0 :
      (presentation.coarseFaceEdge0In targetFull face).1 =
        (show presentation.CoarseEdge from (1 : Fin 2)) := rfl
  have hedge1 :
      (presentation.coarseFaceEdge1In targetFull face).1 =
        (show presentation.CoarseEdge from (1 : Fin 2)) := rfl
  have hedge2 :
      (presentation.coarseFaceEdge2In targetFull face).1 =
        (show presentation.CoarseEdge from (1 : Fin 2)) := rfl
  change
    (if (presentation.coarseFaceEdge0In targetFull face).1 =
          (show presentation.CoarseEdge from (0 : Fin 2)) then 1 else 0) -
        (if (presentation.coarseFaceEdge1In targetFull face).1 =
          (show presentation.CoarseEdge from (0 : Fin 2)) then 1 else 0) +
      (if (presentation.coarseFaceEdge2In targetFull face).1 =
        (show presentation.CoarseEdge from (0 : Fin 2)) then 1 else 0) = 0
  rw [hedge0, hedge1, hedge2]
  have hne :
      (show presentation.CoarseEdge from (1 : Fin 2)) ≠
        (show presentation.CoarseEdge from (0 : Fin 2)) := by decide
  simp [hne]

/-- The explicit loop cochain is a cocycle: every coarse face has boundary
`(1,1,1)`, on which the cochain vanishes. -/
theorem coarseTargetFullCochain_cocycle :
    coarseTargetFullComplex.d1 coarseTargetFullCochain = 0 := by
  apply (presentation.coarseFaceCochainEquiv targetFull).injective
  rw [map_zero]
  calc
    presentation.coarseFaceCochainEquiv targetFull
        (coarseTargetFullComplex.d1 coarseTargetFullCochain) =
      presentation.coarseD1LinearMap targetFull
        (presentation.coarseEdgeCochainEquiv targetFull
          coarseTargetFullCochain) := by
            simpa only [] using
              (presentation.coarseD1_commutes targetFull
                coarseTargetFullCochain).symm
    _ = presentation.coarseD1LinearMap targetFull
        coarseTargetFullRawCochain := by
          simp only [coarseTargetFullCochain,
            LinearEquiv.apply_symm_apply]
    _ = 0 := coarseTargetFullRawCochain_cocycle

/-- The explicit loop cocycle in the actual degree-one kernel. -/
noncomputable def coarseTargetFullCycle :
    LinearMap.ker coarseTargetFullComplex.d1 :=
  ⟨coarseTargetFullCochain, coarseTargetFullCochain_cocycle⟩

/-- The literal quotient-H¹ class of the chart-zero loop. -/
noncomputable def coarseTargetFullClass : coarseTargetFullComplex.H1 :=
  (LinearMap.range coarseTargetFullComplex.boundaryToCycles).mkQ
    coarseTargetFullCycle

/-- The displayed cocycle has unit period. -/
theorem coarseTargetFullPeriod_cycle :
    coarseTargetFullPeriod coarseTargetFullCycle.1 = 1 := by
  have happly := congrFun
    ((presentation.coarseEdgeCochainEquiv targetFull).apply_symm_apply
      coarseTargetFullRawCochain) coarseEdgeZero
  change coarseTargetFullCochain
      (presentation.coarseEdgeEquiv targetFull coarseEdgeZero) = 1
  change coarseTargetFullCochain
      (presentation.coarseEdgeEquiv targetFull coarseEdgeZero) =
    coarseTargetFullRawCochain coarseEdgeZero at happly
  calc
    coarseTargetFullCochain
        (presentation.coarseEdgeEquiv targetFull coarseEdgeZero) =
      coarseTargetFullRawCochain coarseEdgeZero := happly
    _ = 1 := by rfl

/-- The coarse full-target quotient class is nonzero because boundaries have
zero period while the explicit loop cocycle has period one. -/
theorem coarseTargetFullClass_ne_zero : coarseTargetFullClass ≠ 0 := by
  intro hzero
  have hmem := (Submodule.Quotient.mk_eq_zero
    (LinearMap.range coarseTargetFullComplex.boundaryToCycles)).1 hzero
  rcases hmem with ⟨cochain, hcochain⟩
  have hperiod := congrArg
    (fun cycle : LinearMap.ker coarseTargetFullComplex.d1 =>
      coarseTargetFullPeriod cycle.1) hcochain
  change coarseTargetFullPeriod
      (coarseTargetFullComplex.boundaryToCycles cochain).1 =
    coarseTargetFullPeriod coarseTargetFullCycle.1 at hperiod
  rw [ThreeCochainComplex.boundaryToCycles_apply] at hperiod
  rw [coarseTargetFullPeriod_boundary_zero,
    coarseTargetFullPeriod_cycle] at hperiod
  exact zero_ne_one hperiod

/-- The coarse full-target H¹ space has positive dimension. -/
theorem targetFull_coarse_h1_pos :
    0 < Module.finrank ℚ coarseTargetFullComplex.H1 :=
  Module.finrank_pos_iff_exists_ne_zero.mpr
    ⟨coarseTargetFullClass, coarseTargetFullClass_ne_zero⟩

/-- The corresponding fine class is the actual canonical H¹ image. -/
noncomputable def fineTargetFullClass : fineTargetFullComplex.H1 :=
  (presentation.toGeometry.aSubnerveComparisonHom
    (↑targetFull : Set (Fin 2))).h1Map coarseTargetFullClass

/-- The fine image class is nonzero by actual-map injectivity. -/
theorem fineTargetFullClass_ne_zero : fineTargetFullClass ≠ 0 := by
  intro hzero
  apply coarseTargetFullClass_ne_zero
  apply (aSubnerveComparisonHom_h1Map_bijective targetFull).1
  simpa only [fineTargetFullClass, map_zero] using hzero

/-- The fine full-target H¹ space has positive dimension. -/
theorem targetFull_fine_h1_pos :
    0 < Module.finrank ℚ fineTargetFullComplex.H1 :=
  Module.finrank_pos_iff_exists_ne_zero.mpr
    ⟨fineTargetFullClass, fineTargetFullClass_ne_zero⟩

/-- Both actual H¹ spaces on the same full subset meeting the C4 failure are
nonzero. -/
theorem targetFull_both_h1_pos :
    0 < Module.finrank ℚ coarseTargetFullComplex.H1 ∧
      0 < Module.finrank ℚ fineTargetFullComplex.H1 :=
  ⟨targetFull_coarse_h1_pos, targetFull_fine_h1_pos⟩

/-! ## Bounded R1 necessity conclusion -/

/-- Exact C4 non-necessity witness: the raw presentation is uniformly
invariant, fails C4 law-indexedly and on the actual full A-subnerve, fails
ConditionCAllA directly, and has nonzero actual H¹ on both sides of that same
failure subset. -/
theorem c4_not_necessary :
    UniformPresentation presentation ∧
      ¬ presentation.toGeometry.ConditionC indicatorLaws
        indicatorCoarseAdequate indicatorFineAdequate ∧
      ¬ presentation.toGeometry.ConditionC4 indicatorLaws
        indicatorCoarseAdequate indicatorFineAdequate ∧
      ¬ presentation.toGeometry.ConditionC4AtTargetSubset
        (↑targetFull : Set (Fin 2)) ∧
      ¬ presentation.toGeometry.ConditionCAllA ∧
      0 < Module.finrank ℚ coarseTargetFullComplex.H1 ∧
      0 < Module.finrank ℚ fineTargetFullComplex.H1 :=
  ⟨uniformPresentation, indicator_not_conditionC, indicator_not_conditionC4,
    not_conditionC4AtTargetSubset, not_conditionCAllA,
    targetFull_coarse_h1_pos, targetFull_fine_h1_pos⟩

end R1ConditionC4Witness

end AAT.AG.ResolutionInvariance

#assert_standard_axioms_only AAT.AG.ResolutionInvariance.R1ConditionC4Witness
