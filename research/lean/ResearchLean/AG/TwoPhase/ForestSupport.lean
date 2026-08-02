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

`entries` is a leaf-removal order for structural support: each earlier leaf is
absent from every later listed edge, and every structural expanded edge occurs
in the list.  Semantic edges need not occur, so semantic cycles remain possible.
The local structural endpoint condition is part of each entry; no all-phase
`d0` surjectivity is supplied.
-/
structure StructuralForestPruning
    (P : AtomIndexedCoefficientComplex.{u, n, v, w} D family N k)
    (hE : P.ConditionE) where
  entries : List (StructuralForestPruningEntry P)
  all_structural_edges :
    ∀ edge : P.indexing.expandedNerve.EdgeComponent,
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
    (entry : StructuralForestPruningEntry P)
    (_hedge : family.Structural (P.indexing.edgePairAt entry.edge)) :
    P.structural0 →ₗ[k] k where
  toFun c := P.all.zeroCochainCoordinates c.1 entry.leaf
  map_add' x y := by simp
  map_smul' scalar x := by simp

/-- The chosen structural endpoint makes the actual scalar restriction surjective. -/
theorem leafRestriction_surjective
    (entry : StructuralForestPruningEntry P)
    (hedge : family.Structural (P.indexing.edgePairAt entry.edge)) :
    Function.Surjective (leafRestriction entry hedge) := by
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

/--
Recursive chart-coordinate normalization along a leaf-pruning list.

The tail is solved first.  The head leaf is absent from the tail, so its single
coordinate correction fixes the head edge without changing any later edge.
-/
noncomputable def solveCoordinates :
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

/-- The recursive normalization uses only structural chart coordinates. -/
theorem solveCoordinates_supported
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

/-- Every structural edge in the list is solved to its requested value. -/
theorem solveCoordinates_matches
    (entries : List (StructuralForestPruningEntry P))
    (horder : entries.Pairwise StructuralForestPruningEntry.Fresh)
    (values : P.indexing.expandedNerve.EdgeComponent → k)
    {entry : StructuralForestPruningEntry P}
    (hmem : entry ∈ entries)
    (hedge : family.Structural (P.indexing.edgePairAt entry.edge)) :
    incidenceCoordinate (solveCoordinates entries values) entry.edge =
      values entry.edge := by
  classical
  induction entries generalizing entry with
  | nil => simp at hmem
  | cons head tail ih =>
      have hpair := List.pairwise_cons.mp horder
      rcases hpair with ⟨hfresh, htail⟩
      rcases List.mem_cons.mp hmem with rfl | hmem
      · cases hside : entry.leafOnRight
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
      · have hmatch := ih htail hmem hedge
        have hf := hfresh entry hmem
        by_cases hhead : family.Structural (P.indexing.edgePairAt head.edge)
        · cases hside : head.leafOnRight <;>
            simpa [solveCoordinates, hhead, hside, incidenceCoordinate,
              coordinateVector, hf.1, hf.2] using hmatch
        · simpa [solveCoordinates, hhead] using hmatch

/-- Chart coordinates produced for a structural degree-one cochain. -/
def primitiveCoordinates (F : StructuralForestPruning P hE)
    (y : P.structural1) : P.indexing.expandedNerve.Chart → k :=
  solveCoordinates F.entries (P.all.oneCochainCoordinates y.1)

/-- The actual structural degree-zero cochain generated by forest normalization. -/
def primitive (F : StructuralForestPruning P hE)
    (y : P.structural1) : P.structural0 :=
  ⟨P.all.zeroCochainCoordinates.symm (F.primitiveCoordinates y), by
    rw [P.mem_structural0_iff]
    intro chart hchart
    simpa [primitiveCoordinates] using
      solveCoordinates_supported F.entries
        (P.all.oneCochainCoordinates y.1) chart hchart⟩

/-- Forest normalization is a derived right inverse of the actual structural `d0`. -/
theorem structuralD0_primitive (F : StructuralForestPruning P hE)
    (y : P.structural1) :
    P.structuralD0 hE (F.primitive y) = y := by
  apply Subtype.ext
  apply P.all.oneCochainCoordinates.injective
  funext edge
  by_cases hedge : family.Structural (P.indexing.edgePairAt edge)
  · rcases List.mem_map.mp (F.all_structural_edges edge hedge) with
      ⟨entry, hmem, rfl⟩
    change P.all.oneCochainCoordinates
        (P.all.d0 (F.primitive y).1) entry.edge =
      P.all.oneCochainCoordinates y.1 entry.edge
    rw [P.d0_coordinate]
    simpa [primitive, primitiveCoordinates, incidenceCoordinate] using
      solveCoordinates_matches F.entries F.leafOrder
        (P.all.oneCochainCoordinates y.1) hmem hedge
  · have hd0mem : P.all.d0 (F.primitive y).1 ∈ P.structural1 :=
      hE.1 (F.primitive y).2
    have hleft := (P.mem_structural1_iff (P.all.d0 (F.primitive y).1)).1
      hd0mem edge hedge
    have hright := (P.mem_structural1_iff y.1).1 y.2 edge hedge
    exact hleft.trans hright.symm

/-- A canonical representative chosen only for building the reviewed support trace. -/
def h1Representative (_F : StructuralForestPruning P hE)
    (x : (P.structuralComplex hE).H1) :
    LinearMap.ker (P.structuralComplex hE).d1 :=
  Classical.choose
    ((LinearMap.range (P.structuralComplex hE).boundaryToCycles).mkQ_surjective x)

/-- The chosen representative represents the original structural cohomology class. -/
theorem h1Representative_class (F : StructuralForestPruning P hE)
    (x : (P.structuralComplex hE).H1) :
    (LinearMap.range (P.structuralComplex hE).boundaryToCycles).mkQ
        (F.h1Representative x) = x :=
  Classical.choose_spec
    ((LinearMap.range (P.structuralComplex hE).boundaryToCycles).mkQ_surjective x)

/-- The representative after subtracting its forest-generated boundary primitive. -/
def normalizedCycle (F : StructuralForestPruning P hE)
    (x : (P.structuralComplex hE).H1) :
    LinearMap.ker (P.structuralComplex hE).d1 :=
  ⟨(F.h1Representative x).1 -
      (P.structuralComplex hE).d0 (F.primitive (F.h1Representative x).1), by
    simp [(P.structuralComplex hE).d1_comp_d0]⟩

/-- Forest normalization removes every structural edge coordinate. -/
theorem normalizedCycle_zero (F : StructuralForestPruning P hE)
    (x : (P.structuralComplex hE).H1) :
    F.normalizedCycle x = 0 := by
  apply Subtype.ext
  change (F.h1Representative x).1 -
      (P.structuralComplex hE).d0
        (F.primitive (F.h1Representative x).1) =
    (0 : (P.structuralComplex hE).C1)
  have hprimitive :
      (P.structuralComplex hE).d0
          (F.primitive (F.h1Representative x).1) =
        (F.h1Representative x).1 :=
    F.structuralD0_primitive (F.h1Representative x).1
  exact sub_eq_zero.mpr hprimitive.symm

/-- Forest normalization changes a representative only by an actual boundary. -/
theorem normalizedCycle_class (F : StructuralForestPruning P hE)
    (x : (P.structuralComplex hE).H1) :
    (LinearMap.range (P.structuralComplex hE).boundaryToCycles).mkQ
        (F.normalizedCycle x) = x := by
  calc
    (LinearMap.range (P.structuralComplex hE).boundaryToCycles).mkQ
          (F.normalizedCycle x) =
        (LinearMap.range (P.structuralComplex hE).boundaryToCycles).mkQ
          (F.h1Representative x) := by
      apply (Submodule.Quotient.eq _).2
      refine ⟨-F.primitive (F.h1Representative x).1, ?_⟩
      apply Subtype.ext
      simp [normalizedCycle, ThreeCochainComplex.boundaryToCycles]
    _ = x := F.h1Representative_class x

/--
The reviewed edge-absorption certificate generated internally from the actual
forest normalization.  Its support predicate is the normalized representative's
actual structural edge coordinate, not a freely supplied predicate.
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
        family.Structural (P.indexing.edgePairAt edge.down) ∧
          P.all.oneCochainCoordinates (F.normalizedCycle x.down).1.1 edge.down ≠ 0
      classAt := fun x _m => x
      start_class := fun _x => rfl
      edge_absorption_preserves := by intros; rfl
      edge_absorbed := by
        intro x i
        rintro ⟨_hedge, hnonzero⟩
        apply hnonzero
        rw [F.normalizedCycle_zero x.down]
        simp
      all_edges_pruned := by
        intro edge
        refine ⟨edgeOrder edge.down, ?_⟩
        apply ULift.ext
        simp [edgeOrder]
      zero_of_no_edgeSupport := by
        intro _hfaces x hx
        apply ULift.ext
        change x.down = 0
        have hnormalized_underlying : (F.normalizedCycle x.down).1.1 = 0 := by
          apply P.all.oneCochainCoordinates.injective
          funext edge
          simp only [map_zero, Pi.zero_apply]
          by_cases hedge : family.Structural (P.indexing.edgePairAt edge)
          · by_contra hnonzero
            exact (hx (ULift.up edge)) ⟨hedge, hnonzero⟩
          · exact (P.mem_structural1_iff (F.normalizedCycle x.down).1.1).1
              (F.normalizedCycle x.down).1.2 edge hedge
        have hnormalized : F.normalizedCycle x.down = 0 := by
          apply Subtype.ext
          apply Subtype.ext
          exact hnormalized_underlying
        have hclass := F.normalizedCycle_class x.down
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
