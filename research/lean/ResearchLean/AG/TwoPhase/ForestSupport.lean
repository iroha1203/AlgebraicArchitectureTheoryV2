import ResearchLean.AG.TwoPhase.CohomologyComparison
import Formal.Util.AssertStandardAxioms

/-!
# Forest support corollary for the two-phase obstruction theorem

This module discharges stage E3 of `G-102-aat-two-phase-obstruction`.
An actual leaf-pruning order covering the structural edges of the expanded
Atom-indexed nerve, together with structurality of each chosen leaf endpoint,
constructs a normalizing structural degree-zero cochain.  Semantic edges are
not constrained by this order and may retain cycles.  The normalization is then
used to build the reviewed finite edge-absorption certificate internally.  The
reviewed `forestVanishing` theorem supplies structural `H^1` vanishing, which
feeds the E2 canonical semantic-quotient injection theorem.

No vanishing, global differential surjectivity, right inverse, injectivity, or
nonzero-image conclusion is an input field.  The only inputs are the actual
structural-edge leaf order, its no-face premise, and the local structural
endpoint condition that realizes scalar restriction surjectivity.
-/

noncomputable section

namespace AAT.AG.TwoPhase

open Cohomology

universe u n v w r

/-- An edge is face-free when it occurs in none of the three boundary positions of a face. -/
def FaceFreeEdge (N : CoverNerve.{r}) (edge : N.EdgeComponent) : Prop :=
  ∀ face : N.FaceComponent,
    edge ≠ N.faceEdge0 face ∧ edge ≠ N.faceEdge1 face ∧ edge ≠ N.faceEdge2 face

/-- Absence of face components makes every actual edge face-free. -/
theorem faceFreeEdge_of_isEmpty
    (N : CoverNerve.{r}) (hfaces : IsEmpty N.FaceComponent)
    (edge : N.EdgeComponent) : FaceFreeEdge N edge := by
  intro face
  exact (hfaces.false face).elim

/-- An actual boundary edge of a face is not face-free. -/
theorem not_faceFreeEdge_faceEdge0
    (N : CoverNerve.{r}) (face : N.FaceComponent) :
    ¬ FaceFreeEdge N (N.faceEdge0 face) := by
  intro hfree
  exact (hfree face).1 rfl

/-- Canonical universe lift of every component and incidence map of a cover nerve. -/
def liftCoverNerve (N : CoverNerve.{r}) : CoverNerve.{max r w} where
  Chart := ULift.{w, r} N.Chart
  EdgeComponent := ULift.{w, r} N.EdgeComponent
  FaceComponent := ULift.{w, r} N.FaceComponent
  edgeLeft := fun edge => ULift.up (N.edgeLeft edge.down)
  edgeRight := fun edge => ULift.up (N.edgeRight edge.down)
  faceEdge0 := fun face => ULift.up (N.faceEdge0 face.down)
  faceEdge1 := fun face => ULift.up (N.faceEdge1 face.down)
  faceEdge2 := fun face => ULift.up (N.faceEdge2 face.down)
  edgeOverlapComponent := fun edge => N.edgeOverlapComponent edge.down
  faceTripleOverlapComponent := fun face =>
    N.faceTripleOverlapComponent face.down
  edgeOverlapComponent_holds := fun edge =>
    N.edgeOverlapComponent_holds edge.down
  faceTripleOverlapComponent_holds := fun face =>
    N.faceTripleOverlapComponent_holds face.down

namespace AtomIndexedCoefficientComplex

variable {U : AtomCarrier.{u}} {D : ExtractionDoctrine U}
variable {family : DeclaredSemanticFamily D}
variable {N : CoverNerve.{n}} {k : Type v} [Field k]

/-- Structural `H^1` canonically lifted to the expanded-nerve common universe. -/
abbrev LiftedStructuralH1
    (P : AtomIndexedCoefficientComplex.{u, n, v, w} D family N k)
    (hE : P.ConditionE) : Type (max (max n u) w) :=
  ULift.{max n u, w} (P.structuralComplex hE).H1

/-- One actual edge and its chosen leaf endpoint in a forest-pruning order. -/
structure StructuralForestPruningEntry
    (P : AtomIndexedCoefficientComplex.{u, n, v, w} D family N k) where
  edge : P.indexing.expandedNerve.EdgeComponent
  leaf : P.indexing.expandedNerve.Chart
  /-- Computational orientation of the chosen leaf endpoint. -/
  leafOnRight : Bool
  /-- The chosen leaf is the endpoint selected by `leafOnRight`. -/
  leaf_eq_endpoint :
    if leafOnRight then
      leaf = P.indexing.expandedNerve.edgeRight edge
    else
      leaf = P.indexing.expandedNerve.edgeLeft edge
  /-- The chosen leaf is not the opposite endpoint; in particular this is not a loop. -/
  leaf_ne_opposite :
    if leafOnRight then
      leaf ≠ P.indexing.expandedNerve.edgeLeft edge
    else
      leaf ≠ P.indexing.expandedNerve.edgeRight edge
  /-- Actual `F_struct` endpoint restriction is available for every structural edge. -/
  leaf_structural :
    family.Structural (P.indexing.edgePairAt edge) →
      family.Structural (P.indexing.chartPairAt leaf)

namespace StructuralForestPruningEntry

variable {P : AtomIndexedCoefficientComplex.{u, n, v, w} D family N k}

/-- Earlier pruned leaves occur in no endpoint of any later edge. -/
def Fresh (earlier later : StructuralForestPruningEntry P) : Prop :=
  earlier.leaf ≠ P.indexing.expandedNerve.edgeLeft later.edge ∧
    earlier.leaf ≠ P.indexing.expandedNerve.edgeRight later.edge

end StructuralForestPruningEntry

/--
Concrete forest/no-face/local-restriction data on the actual expanded nerve.

`entries` is a leaf-removal order for face-free structural support: each earlier
leaf is absent from every later listed edge, and every face-free structural
expanded edge occurs in the list.  The no-triple-face premise is therefore what
promotes this local coverage to every structural edge.  Semantic edges need not
occur, so semantic cycles remain possible.  The local structural endpoint
condition is part of each entry; no all-phase `d0` surjectivity is supplied.
-/
structure StructuralForestPruning
    (P : AtomIndexedCoefficientComplex.{u, n, v, w} D family N k)
    (hE : P.ConditionE) where
  entries : List (StructuralForestPruningEntry P)
  all_faceFree_structural_edges :
    ∀ edge : P.indexing.expandedNerve.EdgeComponent,
      FaceFreeEdge P.indexing.expandedNerve edge →
      family.Structural (P.indexing.edgePairAt edge) →
      edge ∈ entries.map StructuralForestPruningEntry.edge
  leafOrder : entries.Pairwise StructuralForestPruningEntry.Fresh
  noTripleFaces : IsEmpty P.indexing.expandedNerve.FaceComponent

namespace StructuralForestPruning

variable
    {P : AtomIndexedCoefficientComplex.{u, n, v, w} D family N k}
    {hE : P.ConditionE}

/-- The scalar endpoint restriction on the actual structural chart subspace. -/
def leafRestriction
    (entry : StructuralForestPruningEntry P) :
    P.structural0 →ₗ[k] k where
  toFun c := P.all.zeroCochainCoordinates c.1 entry.leaf
  map_add' x y := by simp
  map_smul' scalar x := by simp

/-- The chosen structural endpoint makes the actual scalar restriction surjective. -/
theorem leafRestriction_surjective
    (entry : StructuralForestPruningEntry P)
    (hedge : family.Structural (P.indexing.edgePairAt entry.edge)) :
    Function.Surjective (leafRestriction entry) := by
  classical
  intro scalar
  let coords : P.indexing.expandedNerve.Chart → k :=
    scalar • coordinateVector entry.leaf
  have hsupport :
      P.all.zeroCochainCoordinates.symm coords ∈ P.structural0 := by
    rw [P.mem_structural0_iff]
    intro chart hchart
    have hleaf := entry.leaf_structural hedge
    have hne : entry.leaf ≠ chart := by
      intro h
      exact hchart (h ▸ hleaf)
    simp [coords, coordinateVector, hne]
  refine ⟨⟨P.all.zeroCochainCoordinates.symm coords, hsupport⟩, ?_⟩
  simp [leafRestriction, coords, coordinateVector]

/-- Incidence value of chart coordinates on an actual expanded edge. -/
def incidenceCoordinate
    (coords : P.indexing.expandedNerve.Chart → k)
    (edge : P.indexing.expandedNerve.EdgeComponent) : k :=
  coords (P.indexing.expandedNerve.edgeRight edge) -
    coords (P.indexing.expandedNerve.edgeLeft edge)

/-- The private tail-first coordinate trace used only inside the reviewed certificate. -/
private noncomputable def solveCoordinates :
    List (StructuralForestPruningEntry P) →
      (P.indexing.expandedNerve.EdgeComponent → k) →
      (P.indexing.expandedNerve.Chart → k)
  | [], _values => 0
  | entry :: tail, values =>
      let tailSolution := solveCoordinates tail values
      @ite _ (family.Structural (P.indexing.edgePairAt entry.edge))
        (Classical.propDecidable _) (
          if entry.leafOnRight then
            tailSolution +
              (values entry.edge - incidenceCoordinate tailSolution entry.edge) •
                coordinateVector entry.leaf
          else
            tailSolution +
              (incidenceCoordinate tailSolution entry.edge - values entry.edge) •
                coordinateVector entry.leaf)
        tailSolution

/-- The private solver stays inside structural chart support, as required by Condition E. -/
private theorem solveCoordinates_supported
    (entries : List (StructuralForestPruningEntry P))
    (values : P.indexing.expandedNerve.EdgeComponent → k)
    (chart : P.indexing.expandedNerve.Chart)
    (hchart : ¬ family.Structural (P.indexing.chartPairAt chart)) :
    solveCoordinates entries values chart = 0 := by
  classical
  induction entries with
  | nil => simp [solveCoordinates]
  | cons entry tail ih =>
      by_cases hedge : family.Structural (P.indexing.edgePairAt entry.edge)
      · have hleaf := entry.leaf_structural hedge
        have hne : entry.leaf ≠ chart := by
          intro h
          exact hchart (h ▸ hleaf)
        cases hside : entry.leafOnRight <;>
          simp [solveCoordinates, hedge, hside, ih, coordinateVector, hne]
      · simp [solveCoordinates, hedge, ih]

/-- One private correction matches only the pivot at the head of the current suffix. -/
private theorem solveCoordinates_head_matches
    (entry : StructuralForestPruningEntry P)
    (tail : List (StructuralForestPruningEntry P))
    (values : P.indexing.expandedNerve.EdgeComponent → k)
    (hedge : family.Structural (P.indexing.edgePairAt entry.edge)) :
    incidenceCoordinate (solveCoordinates (entry :: tail) values) entry.edge =
      values entry.edge := by
  classical
  cases hside : entry.leafOnRight
  · have heq := entry.leaf_eq_endpoint
    have hne := entry.leaf_ne_opposite
    simp only [hside, Bool.false_eq_true, ↓reduceIte] at heq hne
    have hend :
        P.indexing.expandedNerve.edgeLeft entry.edge ≠
          P.indexing.expandedNerve.edgeRight entry.edge := by
      simpa [heq] using hne
    simp [solveCoordinates, hedge, hside, incidenceCoordinate,
      coordinateVector, heq, hend]
    ring
  · have heq := entry.leaf_eq_endpoint
    have hne := entry.leaf_ne_opposite
    simp only [hside, ↓reduceIte] at heq hne
    have hend :
        P.indexing.expandedNerve.edgeRight entry.edge ≠
          P.indexing.expandedNerve.edgeLeft entry.edge := by
      simpa [heq] using hne
    simp [solveCoordinates, hedge, hside, incidenceCoordinate,
      coordinateVector, heq, hend]
    ring

/-- Pairwise pruning freshness makes every prefix entry fresh for the selected pivot. -/
private theorem pairwise_prefix_fresh
    (before : List (StructuralForestPruningEntry P))
    (entry : StructuralForestPruningEntry P)
    (tail : List (StructuralForestPruningEntry P))
    (horder : (before ++ entry :: tail).Pairwise
      StructuralForestPruningEntry.Fresh) :
    ∀ earlier ∈ before, StructuralForestPruningEntry.Fresh earlier entry := by
  induction before with
  | nil => simp
  | cons head rest ih =>
      have hpair := List.pairwise_cons.mp horder
      intro earlier hmem
      rcases List.mem_cons.mp hmem with rfl | hmem
      · exact hpair.1 entry (by simp)
      · exact ih hpair.2 earlier hmem

/-- Later private corrections preserve the pivot coordinate already solved in the suffix. -/
private theorem solveCoordinates_prefix_preserves
    (before : List (StructuralForestPruningEntry P))
    (entry : StructuralForestPruningEntry P)
    (tail : List (StructuralForestPruningEntry P))
    (values : P.indexing.expandedNerve.EdgeComponent → k)
    (hfresh : ∀ earlier ∈ before,
      StructuralForestPruningEntry.Fresh earlier entry) :
    incidenceCoordinate
        (solveCoordinates (before ++ entry :: tail) values) entry.edge =
      incidenceCoordinate (solveCoordinates (entry :: tail) values) entry.edge := by
  classical
  induction before with
  | nil => rfl
  | cons head rest ih =>
      have hhead := hfresh head (by simp)
      have hrest : ∀ earlier ∈ rest,
          StructuralForestPruningEntry.Fresh earlier entry := by
        intro earlier hmem
        exact hfresh earlier (by simp [hmem])
      by_cases hedge : family.Structural (P.indexing.edgePairAt head.edge)
      · cases hside : head.leafOnRight <;>
          simpa [solveCoordinates, hedge, hside, incidenceCoordinate,
            coordinateVector, hhead.1, hhead.2] using ih hrest
      · simpa [solveCoordinates, hedge] using ih hrest

/-- A listed pruning entry determines an actual prefix-and-suffix split of the list. -/
private theorem exists_split_of_mem
    {entry : StructuralForestPruningEntry P}
    {entries : List (StructuralForestPruningEntry P)}
    (hmem : entry ∈ entries) :
    ∃ before tail, entries = before ++ entry :: tail := by
  induction entries with
  | nil => simp at hmem
  | cons head rest ih =>
      rcases List.mem_cons.mp hmem with rfl | hmem
      · exact ⟨[], rest, rfl⟩
      · rcases ih hmem with ⟨before, tail, rfl⟩
        exact ⟨head :: before, tail, by simp⟩

/-- The private structural degree-zero correction generated for one pruning suffix. -/
private def primitiveFor
    (entries : List (StructuralForestPruningEntry P))
    (y : P.structural1) : P.structural0 :=
  ⟨P.all.zeroCochainCoordinates.symm
      (solveCoordinates entries (P.all.oneCochainCoordinates y.1)), by
    rw [P.mem_structural0_iff]
    intro chart hchart
    simpa using
      solveCoordinates_supported entries
        (P.all.oneCochainCoordinates y.1) chart hchart⟩

/-- The suffix correction realizes the requested coordinate only at its head pivot. -/
private theorem structuralD0_primitiveFor_head_coordinate
    (entry : StructuralForestPruningEntry P)
    (tail : List (StructuralForestPruningEntry P))
    (y : P.structural1)
    (hedge : family.Structural (P.indexing.edgePairAt entry.edge)) :
    P.all.oneCochainCoordinates
        (P.structuralD0 hE (primitiveFor (entry :: tail) y)).1 entry.edge =
      P.all.oneCochainCoordinates y.1 entry.edge := by
  change P.all.oneCochainCoordinates
      (P.all.d0 (primitiveFor (entry :: tail) y).1) entry.edge =
    P.all.oneCochainCoordinates y.1 entry.edge
  rw [P.d0_coordinate]
  simpa [primitiveFor, incidenceCoordinate] using
    solveCoordinates_head_matches entry tail
      (P.all.oneCochainCoordinates y.1) hedge

/-- A private cycle representative used to build the certificate's step-local trace. -/
private def h1Representative
    (x : (P.structuralComplex hE).H1) :
    LinearMap.ker (P.structuralComplex hE).d1 :=
  Classical.choose
    ((LinearMap.range (P.structuralComplex hE).boundaryToCycles).mkQ_surjective x)

/-- The private chosen cycle represents the supplied structural cohomology class. -/
private theorem h1Representative_class
    (x : (P.structuralComplex hE).H1) :
    (LinearMap.range (P.structuralComplex hE).boundaryToCycles).mkQ
        (h1Representative x) = x :=
  Classical.choose_spec
    ((LinearMap.range (P.structuralComplex hE).boundaryToCycles).mkQ_surjective x)

/-- The private representative after subtracting the boundary generated by one suffix. -/
private def normalizedFor
    (entries : List (StructuralForestPruningEntry P))
    (x : (P.structuralComplex hE).H1) :
    LinearMap.ker (P.structuralComplex hE).d1 :=
  ⟨(h1Representative x).1 -
      (P.structuralComplex hE).d0
        (primitiveFor entries (h1Representative x).1), by
    simp [(P.structuralComplex hE).d1_comp_d0]⟩

/-- The representative normalized for a suffix has zero coordinate at that suffix's head. -/
private theorem normalizedFor_head_coordinate_zero
    (entry : StructuralForestPruningEntry P)
    (tail : List (StructuralForestPruningEntry P))
    (x : (P.structuralComplex hE).H1)
    (hedge : family.Structural (P.indexing.edgePairAt entry.edge)) :
    P.all.oneCochainCoordinates
        (normalizedFor (entry :: tail) x).1.1 entry.edge = 0 := by
  change P.all.oneCochainCoordinates
      ((h1Representative x).1.1 -
        (P.structuralD0 hE
          (primitiveFor (entry :: tail) (h1Representative x).1)).1)
        entry.edge = 0
  rw [map_sub, Pi.sub_apply, structuralD0_primitiveFor_head_coordinate
    entry tail (h1Representative x).1 hedge]
  exact sub_self _

/-- Prefix corrections preserve the selected suffix correction's incidence coordinate. -/
private theorem structuralD0_primitiveFor_prefix_coordinate
    (before : List (StructuralForestPruningEntry P))
    (entry : StructuralForestPruningEntry P)
    (tail : List (StructuralForestPruningEntry P))
    (horder : (before ++ entry :: tail).Pairwise
      StructuralForestPruningEntry.Fresh)
    (y : P.structural1) :
    P.all.oneCochainCoordinates
        (P.structuralD0 hE (primitiveFor (before ++ entry :: tail) y)).1
        entry.edge =
      P.all.oneCochainCoordinates
        (P.structuralD0 hE (primitiveFor (entry :: tail) y)).1 entry.edge := by
  change P.all.oneCochainCoordinates
      (P.all.d0 (primitiveFor (before ++ entry :: tail) y).1) entry.edge =
    P.all.oneCochainCoordinates
      (P.all.d0 (primitiveFor (entry :: tail) y).1) entry.edge
  rw [P.d0_coordinate, P.d0_coordinate]
  simpa [primitiveFor, incidenceCoordinate] using
    solveCoordinates_prefix_preserves before entry tail
      (P.all.oneCochainCoordinates y.1)
      (pairwise_prefix_fresh before entry tail horder)

/-- Prefix corrections preserve the selected suffix representative's pivot coordinate. -/
private theorem normalizedFor_prefix_coordinate
    (before : List (StructuralForestPruningEntry P))
    (entry : StructuralForestPruningEntry P)
    (tail : List (StructuralForestPruningEntry P))
    (horder : (before ++ entry :: tail).Pairwise
      StructuralForestPruningEntry.Fresh)
    (x : (P.structuralComplex hE).H1) :
    P.all.oneCochainCoordinates
        (normalizedFor (before ++ entry :: tail) x).1.1 entry.edge =
      P.all.oneCochainCoordinates
        (normalizedFor (entry :: tail) x).1.1 entry.edge := by
  change P.all.oneCochainCoordinates
      ((h1Representative x).1.1 -
        (P.structuralD0 hE
          (primitiveFor (before ++ entry :: tail) (h1Representative x).1)).1)
        entry.edge =
    P.all.oneCochainCoordinates
      ((h1Representative x).1.1 -
        (P.structuralD0 hE
          (primitiveFor (entry :: tail) (h1Representative x).1)).1)
        entry.edge
  rw [map_sub, map_sub, Pi.sub_apply, Pi.sub_apply,
    structuralD0_primitiveFor_prefix_coordinate before entry tail horder]

/-- Every private suffix representative differs from the chosen cycle by an actual boundary. -/
private theorem normalizedFor_class
    (entries : List (StructuralForestPruningEntry P))
    (x : (P.structuralComplex hE).H1) :
    (LinearMap.range (P.structuralComplex hE).boundaryToCycles).mkQ
        (normalizedFor entries x) = x := by
  calc
    (LinearMap.range (P.structuralComplex hE).boundaryToCycles).mkQ
          (normalizedFor entries x) =
        (LinearMap.range (P.structuralComplex hE).boundaryToCycles).mkQ
          (h1Representative x) := by
      apply (Submodule.Quotient.eq _).2
      refine ⟨-primitiveFor entries (h1Representative x).1, ?_⟩
      apply Subtype.ext
      simp [normalizedFor, ThreeCochainComplex.boundaryToCycles]
    _ = x := h1Representative_class x

/--
The reviewed edge-absorption certificate generated internally from the actual
forest normalization.  Its support predicate is the natural nonzero-coordinate
support on actual edges that occur in no face, measured on one common full
normalized representative.  Each local absorption transports a suffix-head zero
to that common representative; the predecessor theorem alone aggregates those
edgewise facts before the no-support criterion concludes vanishing.
-/
def toReviewedCertificate (F : StructuralForestPruning P hE) :
    FiniteForestEdgeAbsorptionData
      (liftCoverNerve.{w, max n u} P.indexing.expandedNerve) := by
  letI : Fintype P.indexing.expandedNerve.EdgeComponent :=
    P.indexing.edgeFintype
  let edgeOrder := Fintype.equivFin P.indexing.expandedNerve.EdgeComponent
  exact
    { H1 := P.LiftedStructuralH1 hE
      steps := Fintype.card P.indexing.expandedNerve.EdgeComponent
      prunedEdge := fun i => ULift.up (edgeOrder.symm i)
      noTripleFaces := ⟨fun face => F.noTripleFaces.false face.down⟩
      edgeSupport := fun x edge =>
        FaceFreeEdge P.indexing.expandedNerve edge.down ∧
          family.Structural (P.indexing.edgePairAt edge.down) ∧
            P.all.oneCochainCoordinates
              (normalizedFor F.entries x.down).1.1 edge.down ≠ 0
      classAt := fun x _m => x
      start_class := fun _x => rfl
      edge_absorption_preserves := by intros; rfl
      edge_absorbed := by
        intro x i
        rintro ⟨hfree, hedge, hnonzero⟩
        rcases List.mem_map.mp
            (F.all_faceFree_structural_edges (edgeOrder.symm i) hfree hedge) with
          ⟨entry, hmem, hedge_eq⟩
        rcases exists_split_of_mem hmem with ⟨before, tail, hsplit⟩
        have hentry : family.Structural (P.indexing.edgePairAt entry.edge) := by
          simpa [hedge_eq] using hedge
        have horder :
            (before ++ entry :: tail).Pairwise
              StructuralForestPruningEntry.Fresh := by
          simpa [← hsplit] using F.leafOrder
        have hfull :
            P.all.oneCochainCoordinates
                (normalizedFor F.entries x.down).1.1 entry.edge = 0 := by
          rw [hsplit]
          exact (normalizedFor_prefix_coordinate
            before entry tail horder x.down).trans
              (normalizedFor_head_coordinate_zero entry tail x.down hentry)
        exact hnonzero (by simpa [hedge_eq] using hfull)
      all_edges_pruned := by
        intro edge
        refine ⟨edgeOrder edge.down, ?_⟩
        apply ULift.ext
        simp [edgeOrder]
      zero_of_no_edgeSupport := by
        intro hfaces x hx
        apply ULift.ext
        change x.down = 0
        have hnormalized_underlying :
            (normalizedFor F.entries x.down).1.1 = 0 := by
          apply P.all.oneCochainCoordinates.injective
          funext edge
          simp only [map_zero, Pi.zero_apply]
          by_cases hedge : family.Structural (P.indexing.edgePairAt edge)
          · have hfree : FaceFreeEdge P.indexing.expandedNerve edge := by
              intro face
              exact (hfaces.false (ULift.up face)).elim
            by_contra hnonzero
            exact (hx (ULift.up edge)) ⟨hfree, hedge, hnonzero⟩
          · exact (P.mem_structural1_iff
                (normalizedFor F.entries x.down).1.1).1
              (normalizedFor F.entries x.down).1.2 edge hedge
        have hnormalized : normalizedFor F.entries x.down = 0 := by
          apply Subtype.ext
          apply Subtype.ext
          exact hnormalized_underlying
        have hclass := normalizedFor_class F.entries x.down
        rw [hnormalized] at hclass
        exact hclass.symm }

/-- The reviewed certificate is definitionally tied to the actual structural `H^1` lift. -/
theorem reviewedCertificate_H1_eq (F : StructuralForestPruning P hE) :
    F.toReviewedCertificate.H1 = P.LiftedStructuralH1 hE :=
  rfl

/-- Reviewed forest absorption forces the actual structural `H^1` to vanish. -/
theorem structuralForestH1Zero (F : StructuralForestPruning P hE) :
    (P.structuralComplex hE).H1Zero := by
  intro x
  have hlift : (ULift.up x : P.LiftedStructuralH1 hE) = 0 :=
    F.toReviewedCertificate.forestVanishing (ULift.up x)
  have hdown := congrArg ULift.down hlift
  simpa using hdown

/-- The canonical semantic quotient map is injective in the reviewed forest regime. -/
theorem forestStandardSemanticH1Map_injective
    (F : StructuralForestPruning P hE) :
    Function.Injective (P.standardSemanticH1Map hE) :=
  P.standardSemanticH1Map_injective hE F.structuralForestH1Zero

/-- Every nonzero all-phase obstruction class has nonzero semantic image in this regime. -/
theorem forestNonzeroClass_mapsNonzero
    (F : StructuralForestPruning P hE)
    (x : P.allComplex.H1) (hx : x ≠ 0) :
    P.standardSemanticH1Map hE x ≠ 0 := by
  intro hmap
  apply hx
  apply F.forestStandardSemanticH1Map_injective
  simpa using hmap

end StructuralForestPruning

end AtomIndexedCoefficientComplex

end AAT.AG.TwoPhase

#assert_standard_axioms_only AAT.AG.TwoPhase
