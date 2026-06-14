import Formal.AG.RepresentationAnalysis.PreservationReflection
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Matrix.Mul

noncomputable section

namespace AAT.AG
namespace RepresentationAnalysis

universe u v w x y z

/--
VII.定義3.3: finite directed graph target for selected relation readings.

The vertex, edge, and label carriers are fixed by the representation profile.
This keeps the graph target a first-order analytic target while still recording
finite graph data, source / target maps, and selected relation labels.
-/
structure FiniteDirectedGraphTarget
    (Vertex Edge RelationLabel : Type z) where
  vertexFintype : Fintype Vertex
  vertexDecidableEq : DecidableEq Vertex
  edgeFintype : Fintype Edge
  edgeDecidableEq : DecidableEq Edge
  source : Edge -> Vertex
  target : Edge -> Vertex
  relationLabel : Edge -> RelationLabel

attribute [instance] FiniteDirectedGraphTarget.vertexFintype
attribute [instance] FiniteDirectedGraphTarget.vertexDecidableEq
attribute [instance] FiniteDirectedGraphTarget.edgeFintype
attribute [instance] FiniteDirectedGraphTarget.edgeDecidableEq

namespace FiniteDirectedGraphTarget

/-- VII.定義3.3: selected edge relation between vertices. -/
def HasEdge {Vertex Edge RelationLabel : Type z}
    (G : FiniteDirectedGraphTarget Vertex Edge RelationLabel)
    (i j : Vertex) : Prop :=
  ∃ e : Edge, G.source e = i ∧ G.target e = j

/-- VII.命題3.4 precursor: selected directed walk following graph source/target maps. -/
inductive DirectedWalk {Vertex Edge RelationLabel : Type z}
    (G : FiniteDirectedGraphTarget Vertex Edge RelationLabel) :
    Vertex -> Vertex -> List Edge -> Prop where
  | nil (v : Vertex) : DirectedWalk G v v []
  | cons {start finish : Vertex} (e : Edge) (tail : List Edge)
      (hsource : G.source e = start)
      (hrest : DirectedWalk G (G.target e) finish tail) :
      DirectedWalk G start finish (e :: tail)

/-- VII.命題3.6 precursor: directed walk indexed by its selected edge length. -/
inductive CountedDirectedWalk {Vertex Edge RelationLabel : Type z}
    (G : FiniteDirectedGraphTarget Vertex Edge RelationLabel) :
    Vertex -> Vertex -> Nat -> Type z where
  | nil (v : Vertex) : CountedDirectedWalk G v v 0
  | cons {start finish : Vertex} (e : Edge) (n : Nat)
      (hsource : G.source e = start)
      (tail : CountedDirectedWalk G (G.target e) finish n) :
      CountedDirectedWalk G start finish (n + 1)

namespace CountedDirectedWalk

/-- The edge list underlying a counted directed walk. -/
def edges {Vertex Edge RelationLabel : Type z}
    {G : FiniteDirectedGraphTarget Vertex Edge RelationLabel}
    {start finish : Vertex} {n : Nat} :
    CountedDirectedWalk G start finish n -> List Edge
  | nil _ => []
  | cons e _ _ tail => e :: edges tail

/-- The vertex trace underlying a counted directed walk. -/
def vertices {Vertex Edge RelationLabel : Type z}
    {G : FiniteDirectedGraphTarget Vertex Edge RelationLabel}
    {start finish : Vertex} {n : Nat} :
    CountedDirectedWalk G start finish n -> List Vertex
  | nil v => [v]
  | cons e _ _ tail => G.source e :: vertices tail

/-- A counted directed walk forgets to the list-indexed directed walk. -/
def toDirectedWalk {Vertex Edge RelationLabel : Type z}
    {G : FiniteDirectedGraphTarget Vertex Edge RelationLabel}
    {start finish : Vertex} {n : Nat}
    (w : CountedDirectedWalk G start finish n) :
    DirectedWalk G start finish (edges w) :=
  match w with
  | nil v => DirectedWalk.nil v
  | cons e _ hsource tail => DirectedWalk.cons e (edges tail) hsource tail.toDirectedWalk

/-- The counted walk edge list has the counted length. -/
theorem edges_length {Vertex Edge RelationLabel : Type z}
    {G : FiniteDirectedGraphTarget Vertex Edge RelationLabel}
    {start finish : Vertex} {n : Nat}
    (w : CountedDirectedWalk G start finish n) :
    (edges w).length = n := by
  induction w with
  | nil v => rfl
  | cons e n hsource tail ih =>
      simp [edges, ih]

/-- The counted walk vertex trace has one more vertex than the edge length. -/
theorem vertices_length {Vertex Edge RelationLabel : Type z}
    {G : FiniteDirectedGraphTarget Vertex Edge RelationLabel}
    {start finish : Vertex} {n : Nat}
    (w : CountedDirectedWalk G start finish n) :
    (vertices w).length = n + 1 := by
  induction w with
  | nil v => simp [vertices]
  | cons e n hsource tail ih =>
      simp [vertices, ih]

end CountedDirectedWalk

/-- VII.命題3.4 precursor: selected directed cycle witness. -/
structure DirectedCycle {Vertex Edge RelationLabel : Type z}
    (G : FiniteDirectedGraphTarget Vertex Edge RelationLabel) where
  start : Vertex
  edges : List Edge
  nonempty : edges ≠ []
  closedWalk : DirectedWalk G start start edges

/-- VII.命題3.4 precursor: acyclicity is absence of selected cycle witnesses. -/
def Acyclic {Vertex Edge RelationLabel : Type z}
    (G : FiniteDirectedGraphTarget Vertex Edge RelationLabel) : Prop :=
  IsEmpty (DirectedCycle G)

namespace CountedDirectedWalk

/-- A counted closed walk of positive length gives a selected directed cycle. -/
def toDirectedCycle {Vertex Edge RelationLabel : Type z}
    {G : FiniteDirectedGraphTarget Vertex Edge RelationLabel}
    {v : Vertex} {n : Nat}
    (w : CountedDirectedWalk G v v (n + 1)) :
    DirectedCycle G where
  start := v
  edges := edges w
  nonempty := by
    cases w with
    | cons e n hsource tail =>
        simp [edges]
  closedWalk := w.toDirectedWalk

/-- A vertex appearing in the trace of a counted walk is reached by a prefix. -/
theorem exists_prefix_of_mem_vertices {Vertex Edge RelationLabel : Type z}
    {G : FiniteDirectedGraphTarget Vertex Edge RelationLabel}
    {start finish x : Vertex} {n : Nat}
    (w : CountedDirectedWalk G start finish n)
    (hmem : x ∈ vertices w) :
    ∃ m : Nat, Nonempty (CountedDirectedWalk G start x m) := by
  induction w with
  | nil v =>
      have hx : x = v := by
        simpa [vertices] using hmem
      subst x
      exact ⟨0, ⟨CountedDirectedWalk.nil v⟩⟩
  | cons e n hsource tail ih =>
      have hx : x = G.source e ∨ x ∈ vertices tail := by
        simpa [vertices] using hmem
      cases hx with
      | inl hxHead =>
          subst x
          exact ⟨0, ⟨by simpa [hsource] using CountedDirectedWalk.nil (G.source e)⟩⟩
      | inr hxTail =>
          rcases ih hxTail with ⟨m, ⟨pref⟩⟩
          exact ⟨m + 1, ⟨CountedDirectedWalk.cons e m hsource pref⟩⟩

/-- In an acyclic selected graph, counted directed walks have no repeated vertices. -/
theorem vertices_nodup_of_acyclic {Vertex Edge RelationLabel : Type z}
    {G : FiniteDirectedGraphTarget Vertex Edge RelationLabel}
    (hacyclic : Acyclic G) :
    ∀ {start finish : Vertex} {n : Nat}
      (w : CountedDirectedWalk G start finish n), (vertices w).Nodup
  | _, _, _, CountedDirectedWalk.nil v => by
      simp [vertices]
  | _, _, _, CountedDirectedWalk.cons e n hsource tail => by
      have hTail : (vertices tail).Nodup :=
        vertices_nodup_of_acyclic hacyclic tail
      have hFresh : G.source e ∉ vertices tail := by
        intro hmem
        rcases exists_prefix_of_mem_vertices tail hmem with ⟨m, ⟨pref⟩⟩
        have closed :
            CountedDirectedWalk G (G.source e) (G.source e) (m + 1) :=
          CountedDirectedWalk.cons e m rfl pref
        exact hacyclic.false closed.toDirectedCycle
      show (G.source e :: vertices tail).Nodup
      exact List.nodup_cons.mpr ⟨hFresh, hTail⟩

/-- In an acyclic finite selected graph, a counted walk is shorter than the vertex count. -/
theorem length_lt_card_of_acyclic {Vertex Edge RelationLabel : Type z}
    [Fintype Vertex]
    {G : FiniteDirectedGraphTarget Vertex Edge RelationLabel}
    (hacyclic : Acyclic G)
    {start finish : Vertex} {n : Nat}
    (w : CountedDirectedWalk G start finish n) :
    n < Fintype.card Vertex := by
  classical
  have hlen :
      (vertices w).length ≤ Fintype.card Vertex :=
    List.Nodup.length_le_card (vertices_nodup_of_acyclic hacyclic w)
  rw [vertices_length] at hlen
  omega

end CountedDirectedWalk

end FiniteDirectedGraphTarget

/--
VII.定義3.3: morphism of finite graph targets.

Compatibility of selected relation labels is kept as an explicit predicate so
later concrete graph readings can choose the exact label discipline.
-/
structure FiniteDirectedGraphHom {Vertex Edge RelationLabel : Type z}
    (G H : FiniteDirectedGraphTarget Vertex Edge RelationLabel) where
  vertexMap : Vertex -> Vertex
  edgeMap : Edge -> Edge
  source_comm :
    ∀ e : Edge, H.source (edgeMap e) = vertexMap (G.source e)
  target_comm :
    ∀ e : Edge, H.target (edgeMap e) = vertexMap (G.target e)
  relationLabelCompatible : Prop
  relationLabelCompatible_cert : relationLabelCompatible

namespace FiniteDirectedGraphHom

/-- VII.定義3.3: identity graph morphism. -/
def id {Vertex Edge RelationLabel : Type z}
    (G : FiniteDirectedGraphTarget Vertex Edge RelationLabel) :
    FiniteDirectedGraphHom G G where
  vertexMap := fun v => v
  edgeMap := fun e => e
  source_comm := by intro e; rfl
  target_comm := by intro e; rfl
  relationLabelCompatible := True
  relationLabelCompatible_cert := trivial

/-- VII.定義3.3: composition of selected graph morphisms. -/
def comp {Vertex Edge RelationLabel : Type z}
    {G H K : FiniteDirectedGraphTarget Vertex Edge RelationLabel}
    (f : FiniteDirectedGraphHom G H) (g : FiniteDirectedGraphHom H K) :
    FiniteDirectedGraphHom G K where
  vertexMap := fun v => g.vertexMap (f.vertexMap v)
  edgeMap := fun e => g.edgeMap (f.edgeMap e)
  source_comm := by
    intro e
    rw [g.source_comm, f.source_comm]
  target_comm := by
    intro e
    rw [g.target_comm, f.target_comm]
  relationLabelCompatible := f.relationLabelCompatible ∧ g.relationLabelCompatible
  relationLabelCompatible_cert :=
    ⟨f.relationLabelCompatible_cert, g.relationLabelCompatible_cert⟩

/-- VII.定義3.3: expose selected label compatibility. -/
theorem relationLabelCompatible_holds {Vertex Edge RelationLabel : Type z}
    {G H : FiniteDirectedGraphTarget Vertex Edge RelationLabel}
    (f : FiniteDirectedGraphHom G H) :
    f.relationLabelCompatible :=
  f.relationLabelCompatible_cert

end FiniteDirectedGraphHom

/-- VII.定義3.3: target-category interface for finite graph readings. -/
def finiteDirectedGraphTargetCategory (Vertex Edge RelationLabel : Type z) :
    AnalyticTargetCategory (FiniteDirectedGraphTarget Vertex Edge RelationLabel) where
  Hom := FiniteDirectedGraphHom
  id := FiniteDirectedGraphHom.id
  comp := FiniteDirectedGraphHom.comp

/--
VII.定義3.3: selected relation profile used to build a graph reading.

The profile records how selected relation data for each decorated architecture
scheme is sent into the graph edges.  Exact cycle witness properties are left
to AC5.
-/
structure GraphRepresentationProfile {U : AtomCarrier.{u}} {A : ArchitectureObject U}
    {S : Site.AATSite A} {k : Type v} [CommRing k]
    (p : AATSchReadingParameter.{u, v, w, x, y} S k) where
  Vertex : Type z
  Edge : Type z
  RelationLabel : Type z
  SelectedRelation : AATSch p -> Type z
  graphOf : AATSch p -> FiniteDirectedGraphTarget Vertex Edge RelationLabel
  relationEdge : ∀ X : AATSch p, SelectedRelation X -> Edge
  selectedEdge : AATSch p -> Edge -> Prop
  relationEdge_selected :
    ∀ (X : AATSch p) (r : SelectedRelation X), selectedEdge X (relationEdge X r)
  mapGraph :
    ∀ {X Y : AATSch p}, AATSchMorphism X Y ->
      FiniteDirectedGraphHom (graphOf X) (graphOf Y)
  map_id :
    ∀ {X : AATSch p} (I : AATSchIdentityData X),
      mapGraph I.morphism = FiniteDirectedGraphHom.id (graphOf X)
  map_comp :
    ∀ {X Y Z : AATSch p} {f : AATSchMorphism X Y} {g : AATSchMorphism Y Z}
      (C : AATSchCompositionData f g),
      mapGraph C.morphism = FiniteDirectedGraphHom.comp (mapGraph f) (mapGraph g)

namespace GraphRepresentationProfile

variable {U : AtomCarrier.{u}} {A : ArchitectureObject U}
variable {S : Site.AATSite A} {k : Type v} [CommRing k]
variable {p : AATSchReadingParameter.{u, v, w, x, y} S k}

/-- VII.定義3.3: graph profile as an analytic representation. -/
def toAnalyticRepresentation (P : GraphRepresentationProfile p) :
    AnalyticRepresentation p (FiniteDirectedGraphTarget P.Vertex P.Edge P.RelationLabel) where
  targetCategory := finiteDirectedGraphTargetCategory P.Vertex P.Edge P.RelationLabel
  obj := P.graphOf
  map := P.mapGraph
  map_id := P.map_id
  map_comp := P.map_comp

/-- VII.定義3.3: relation data maps to selected graph edges. -/
theorem relationEdge_selected_holds (P : GraphRepresentationProfile p)
    (X : AATSch p) (r : P.SelectedRelation X) :
    P.selectedEdge X (P.relationEdge X r) :=
  P.relationEdge_selected X r

end GraphRepresentationProfile

/--
VII.命題3.4: assumptions needed for acyclicity preservation.

This package records exactly the direction used by Proposition 3.4: when the
dependency-axis graph reading is selected, every graph cycle yields a selected
cycle-obstruction witness, and structural dependency-obstruction zero excludes
such witnesses.
-/
structure DependencyAcyclicityProfile {U : AtomCarrier.{u}} {A : ArchitectureObject U}
    {S : Site.AATSite A} {k : Type v} [CommRing k]
    {p : AATSchReadingParameter.{u, v, w, x, y} S k}
    (P : GraphRepresentationProfile p) where
  dependencyAxisSelected : AATSch p -> Prop
  structuralDependencyObstructionZero : AATSch p -> Prop
  selectedCycleObstructionWitness :
    ∀ X : AATSch p, FiniteDirectedGraphTarget.DirectedCycle (P.graphOf X) -> Prop
  graphCycle_yields_obstructionWitness :
    ∀ X : AATSch p, dependencyAxisSelected X ->
      ∀ c : FiniteDirectedGraphTarget.DirectedCycle (P.graphOf X),
        selectedCycleObstructionWitness X c
  obstructionZero_excludes_cycleWitness :
    ∀ X : AATSch p, structuralDependencyObstructionZero X ->
      ∀ c : FiniteDirectedGraphTarget.DirectedCycle (P.graphOf X),
        ¬ selectedCycleObstructionWitness X c

namespace DependencyAcyclicityProfile

variable {U : AtomCarrier.{u}} {A : ArchitectureObject U}
variable {S : Site.AATSite A} {k : Type v} [CommRing k]
variable {p : AATSchReadingParameter.{u, v, w, x, y} S k}
variable {P : GraphRepresentationProfile p}

/-- VII.命題3.4: graph cycles yield selected obstruction witnesses. -/
theorem selectedCycleObstructionWitness_of_graphCycle
    (D : DependencyAcyclicityProfile P) {X : AATSch p}
    (haxis : D.dependencyAxisSelected X)
    (c : FiniteDirectedGraphTarget.DirectedCycle (P.graphOf X)) :
    D.selectedCycleObstructionWitness X c :=
  D.graphCycle_yields_obstructionWitness X haxis c

/-- VII.命題3.4: structural dependency-obstruction zero excludes cycle witnesses. -/
theorem no_selectedCycleObstructionWitness_of_obstructionZero
    (D : DependencyAcyclicityProfile P) {X : AATSch p}
    (hzero : D.structuralDependencyObstructionZero X)
    (c : FiniteDirectedGraphTarget.DirectedCycle (P.graphOf X)) :
    ¬ D.selectedCycleObstructionWitness X c :=
  D.obstructionZero_excludes_cycleWitness X hzero c

/--
VII.命題3.4: Acyclicity Preservation.

If the dependency-axis graph reading is selected, graph cycles are exact enough
to produce selected cycle-obstruction witnesses, and structural dependency
obstruction is zero, then the selected graph reading is acyclic.
-/
theorem acyclicityPreservation
    (D : DependencyAcyclicityProfile P) {X : AATSch p}
    (haxis : D.dependencyAxisSelected X)
    (hzero : D.structuralDependencyObstructionZero X) :
    FiniteDirectedGraphTarget.Acyclic (P.graphOf X) := by
  refine ⟨?_⟩
  intro c
  exact D.no_selectedCycleObstructionWitness_of_obstructionZero hzero c
    (D.selectedCycleObstructionWitness_of_graphCycle haxis c)

end DependencyAcyclicityProfile

/-- VII.定義3.5: adjacency matrix over natural edge multiplicities. -/
def adjacencyMatrix {Vertex Edge RelationLabel : Type z}
    (G : FiniteDirectedGraphTarget Vertex Edge RelationLabel) :
    Matrix Vertex Vertex Nat :=
  by
    classical
    letI := G.edgeFintype
    letI := G.edgeDecidableEq
    exact fun i j => Fintype.card { e : Edge // G.source e = i ∧ G.target e = j }

/-- VII.定義3.5: signed incidence matrix of selected edges. -/
def incidenceMatrix {Vertex Edge RelationLabel : Type z}
    (G : FiniteDirectedGraphTarget Vertex Edge RelationLabel) :
    Matrix Vertex Edge Int :=
  by
    classical
    letI := G.vertexDecidableEq
    exact fun v e =>
      if G.source e = v then (1 : Int)
      else if G.target e = v then (-1 : Int)
      else 0

/-- VII.定義3.5: transition relation matrix. -/
def transitionMatrix {Vertex Edge RelationLabel : Type z}
    (G : FiniteDirectedGraphTarget Vertex Edge RelationLabel) :
    Matrix Vertex Vertex Prop :=
  fun i j => G.HasEdge i j

/-- VII.定義3.5: bundled matrix representation target attached to a graph. -/
structure MatrixRepresentationTarget (Vertex Edge RelationLabel : Type z) where
  graph : FiniteDirectedGraphTarget Vertex Edge RelationLabel
  adjacency : Matrix Vertex Vertex Nat
  incidence : Matrix Vertex Edge Int
  transition : Matrix Vertex Vertex Prop

namespace MatrixRepresentationTarget

/-- VII.定義3.5: the canonical matrix package computed from a finite graph. -/
def ofGraph {Vertex Edge RelationLabel : Type z}
    (G : FiniteDirectedGraphTarget Vertex Edge RelationLabel) :
    MatrixRepresentationTarget Vertex Edge RelationLabel where
  graph := G
  adjacency := adjacencyMatrix G
  incidence := incidenceMatrix G
  transition := transitionMatrix G

/-- VII.定義3.5: canonical adjacency accessor. -/
theorem ofGraph_adjacency {Vertex Edge RelationLabel : Type z}
    (G : FiniteDirectedGraphTarget Vertex Edge RelationLabel) :
    (ofGraph G).adjacency = adjacencyMatrix G :=
  rfl

/-- VII.定義3.5: canonical incidence accessor. -/
theorem ofGraph_incidence {Vertex Edge RelationLabel : Type z}
    (G : FiniteDirectedGraphTarget Vertex Edge RelationLabel) :
    (ofGraph G).incidence = incidenceMatrix G :=
  rfl

/-- VII.定義3.5: canonical transition accessor. -/
theorem ofGraph_transition {Vertex Edge RelationLabel : Type z}
    (G : FiniteDirectedGraphTarget Vertex Edge RelationLabel) :
    (ofGraph G).transition = transitionMatrix G :=
  rfl

end MatrixRepresentationTarget

/-- VII.命題3.6 precursor: selected `n`th adjacency-matrix power. -/
def adjacencyMatrixPower {Vertex Edge RelationLabel : Type z}
    (G : FiniteDirectedGraphTarget Vertex Edge RelationLabel) (n : Nat) :
    Matrix Vertex Vertex Nat :=
  by
    classical
    letI := G.vertexFintype
    letI := G.vertexDecidableEq
    exact adjacencyMatrix G ^ n

/--
VII.命題3.6 precursor: selected length-`n` walk count read by matrix powers.

The recursion is the usual adjacency-matrix walk recursion: length zero is the
identity walk, and a length `n + 1` walk is a length `n` walk followed by one
selected edge relation.
-/
def matrixWalkCount {Vertex Edge RelationLabel : Type z}
    (G : FiniteDirectedGraphTarget Vertex Edge RelationLabel) :
    Nat -> Vertex -> Vertex -> Nat := by
  classical
  letI := G.vertexFintype
  letI := G.vertexDecidableEq
  exact
    Nat.rec
      (motive := fun _ => Vertex -> Vertex -> Nat)
      (fun i j => if i = j then 1 else 0)
      (fun _ previous i j =>
        ∑ k : Vertex, adjacencyMatrix G i k * previous k j)

/--
VII.命題3.6: matrix powers read the selected recursive length-`n` walk count.
-/
theorem adjacencyMatrixPower_apply_eq_matrixWalkCount
    {Vertex Edge RelationLabel : Type z}
    (G : FiniteDirectedGraphTarget Vertex Edge RelationLabel)
    (n : Nat) (i j : Vertex) :
    (adjacencyMatrixPower G n) i j = matrixWalkCount G n i j := by
  classical
  letI := G.vertexFintype
  letI := G.vertexDecidableEq
  induction n generalizing i j with
  | zero =>
      simp [adjacencyMatrixPower, matrixWalkCount, Matrix.one_apply]
  | succ n ih =>
      calc
        (adjacencyMatrixPower G (n + 1)) i j =
            ∑ k : Vertex, adjacencyMatrix G i k * (adjacencyMatrixPower G n) k j := by
          simp [adjacencyMatrixPower, pow_succ', Matrix.mul_apply]
        _ = ∑ k : Vertex, adjacencyMatrix G i k * matrixWalkCount G n k j := by
          simp [ih]
        _ = matrixWalkCount G (n + 1) i j := by
          simp [matrixWalkCount]

/-- VII.命題3.6 precursor: positive adjacency entry is exactly a selected edge. -/
theorem adjacencyMatrix_pos_iff_hasEdge {Vertex Edge RelationLabel : Type z}
    (G : FiniteDirectedGraphTarget Vertex Edge RelationLabel) (i j : Vertex) :
    0 < adjacencyMatrix G i j ↔ G.HasEdge i j := by
  classical
  letI := G.edgeFintype
  letI := G.edgeDecidableEq
  constructor
  · intro hpos
    rcases Fintype.card_pos_iff.mp (by simpa [adjacencyMatrix] using hpos) with
      ⟨⟨e, hsource, htarget⟩⟩
    exact ⟨e, hsource, htarget⟩
  · rintro ⟨e, hsource, htarget⟩
    exact by
      simpa [adjacencyMatrix] using
        (Fintype.card_pos_iff.mpr
          (show Nonempty { e : Edge // G.source e = i ∧ G.target e = j } from
            ⟨⟨e, hsource, htarget⟩⟩))

/--
VII.命題3.6 precursor: positive recursive walk count has a concrete counted
directed-walk witness, and conversely.
-/
theorem matrixWalkCount_pos_iff_countedDirectedWalk
    {Vertex Edge RelationLabel : Type z}
    (G : FiniteDirectedGraphTarget Vertex Edge RelationLabel) :
    ∀ (n : Nat) (i j : Vertex),
      0 < matrixWalkCount G n i j ↔
        Nonempty (FiniteDirectedGraphTarget.CountedDirectedWalk G i j n) := by
  classical
  letI := G.vertexFintype
  letI := G.vertexDecidableEq
  intro n
  induction n with
  | zero =>
      intro i j
      constructor
      · intro hpos
        by_cases hij : i = j
        · subst j
          exact ⟨FiniteDirectedGraphTarget.CountedDirectedWalk.nil i⟩
        · simp [matrixWalkCount, hij] at hpos
      · rintro ⟨w⟩
        cases w with
        | nil v =>
            simp [matrixWalkCount]
  | succ n ih =>
      intro i j
      constructor
      · intro hpos
        have hExists :
            ∃ k : Vertex,
              adjacencyMatrix G i k * matrixWalkCount G n k j ≠ 0 := by
          by_contra hno
          have hAll :
              ∀ k : Vertex,
                adjacencyMatrix G i k * matrixWalkCount G n k j = 0 := by
            intro k
            by_contra hk
            exact hno ⟨k, hk⟩
          have hsum :
              (∑ k : Vertex,
                adjacencyMatrix G i k * matrixWalkCount G n k j) = 0 := by
            simp [hAll]
          have hcount : matrixWalkCount G (n + 1) i j = 0 := by
            simpa [matrixWalkCount] using hsum
          omega
        rcases hExists with ⟨k, hprodNe⟩
        have hadjPos : 0 < adjacencyMatrix G i k := by
          apply Nat.pos_of_ne_zero
          intro hzero
          exact hprodNe (by simp [hzero])
        have hcountPos : 0 < matrixWalkCount G n k j := by
          apply Nat.pos_of_ne_zero
          intro hzero
          exact hprodNe (by simp [hzero])
        rcases (adjacencyMatrix_pos_iff_hasEdge G i k).mp hadjPos with
          ⟨e, hsource, htarget⟩
        rcases (ih k j).mp hcountPos with ⟨tail⟩
        have tail' :
            FiniteDirectedGraphTarget.CountedDirectedWalk G (G.target e) j n := by
          simpa [htarget] using tail
        exact ⟨FiniteDirectedGraphTarget.CountedDirectedWalk.cons e n hsource tail'⟩
      · rintro ⟨w⟩
        cases w with
        | cons e n hsource tail =>
            have hadjPos : 0 < adjacencyMatrix G i (G.target e) := by
              apply (adjacencyMatrix_pos_iff_hasEdge G i (G.target e)).mpr
              exact ⟨e, hsource, rfl⟩
            have htailPos : 0 < matrixWalkCount G n (G.target e) j :=
              (ih (G.target e) j).mpr ⟨tail⟩
            have hterm :
                0 <
                  adjacencyMatrix G i (G.target e) *
                    matrixWalkCount G n (G.target e) j :=
              Nat.mul_pos hadjPos htailPos
            have hle :
                adjacencyMatrix G i (G.target e) *
                    matrixWalkCount G n (G.target e) j ≤
                  ∑ k : Vertex,
                    adjacencyMatrix G i k * matrixWalkCount G n k j :=
              Finset.single_le_sum
                (fun k _ => Nat.zero_le
                  (adjacencyMatrix G i k * matrixWalkCount G n k j))
                (Finset.mem_univ (G.target e))
            exact Nat.lt_of_lt_of_le hterm (by
              simpa [matrixWalkCount] using hle)

/-- VII.命題3.6: acyclic finite selected graphs have no walks at the vertex-card cutoff. -/
theorem matrixWalkCount_eq_zero_at_card_of_acyclic
    {Vertex Edge RelationLabel : Type z} [Fintype Vertex]
    {G : FiniteDirectedGraphTarget Vertex Edge RelationLabel}
    (hacyclic : FiniteDirectedGraphTarget.Acyclic G) (i j : Vertex) :
    matrixWalkCount G (Fintype.card Vertex) i j = 0 := by
  classical
  by_contra hne
  have hpos : 0 < matrixWalkCount G (Fintype.card Vertex) i j :=
    Nat.pos_of_ne_zero hne
  rcases (matrixWalkCount_pos_iff_countedDirectedWalk G
    (Fintype.card Vertex) i j).mp hpos with ⟨w⟩
  have hlt :
      Fintype.card Vertex < Fintype.card Vertex :=
    FiniteDirectedGraphTarget.CountedDirectedWalk.length_lt_card_of_acyclic
      hacyclic w
  omega

/-- VII.命題3.6: at the vertex-card cutoff, an acyclic finite graph has zero matrix power. -/
theorem adjacencyMatrixPower_eq_zero_at_card_of_acyclic
    {Vertex Edge RelationLabel : Type z} [Fintype Vertex]
    {G : FiniteDirectedGraphTarget Vertex Edge RelationLabel}
    (hacyclic : FiniteDirectedGraphTarget.Acyclic G) :
    adjacencyMatrixPower G (Fintype.card Vertex) = 0 := by
  ext i j
  rw [adjacencyMatrixPower_apply_eq_matrixWalkCount]
  exact matrixWalkCount_eq_zero_at_card_of_acyclic hacyclic i j

/-- VII.命題3.6: finite DAG readings have some zero adjacency-matrix power. -/
theorem exists_adjacencyMatrixPower_eq_zero_of_acyclic
    {Vertex Edge RelationLabel : Type z}
    {G : FiniteDirectedGraphTarget Vertex Edge RelationLabel}
    (hacyclic : FiniteDirectedGraphTarget.Acyclic G) :
    ∃ N : Nat, adjacencyMatrixPower G N = 0 := by
  classical
  letI := G.vertexFintype
  exact ⟨Fintype.card Vertex, adjacencyMatrixPower_eq_zero_at_card_of_acyclic hacyclic⟩

/-- VII.命題3.6: selected walk-count profile for adjacency matrix powers. -/
structure MatrixWalkReadingProfile {Vertex Edge RelationLabel : Type z}
    (G : FiniteDirectedGraphTarget Vertex Edge RelationLabel) where
  lengthNWalkCount : Nat -> Vertex -> Vertex -> Nat
  lengthNWalkCount_eq_matrixWalkCount :
    ∀ (n : Nat) (i j : Vertex), lengthNWalkCount n i j = matrixWalkCount G n i j

namespace MatrixWalkReadingProfile

/-- VII.命題3.6: matrix powers read selected length-`n` walk counts. -/
theorem matrixWalkReading {Vertex Edge RelationLabel : Type z}
    {G : FiniteDirectedGraphTarget Vertex Edge RelationLabel}
    (P : MatrixWalkReadingProfile G) (n : Nat) (i j : Vertex) :
    (adjacencyMatrixPower G n) i j = P.lengthNWalkCount n i j :=
  (adjacencyMatrixPower_apply_eq_matrixWalkCount G n i j).trans
    (P.lengthNWalkCount_eq_matrixWalkCount n i j).symm

end MatrixWalkReadingProfile

/-- VII.定義3.5: selected morphism between matrix representation targets. -/
structure MatrixRepresentationHom {Vertex Edge RelationLabel : Type z}
    (M N : MatrixRepresentationTarget Vertex Edge RelationLabel) where
  graphHom : FiniteDirectedGraphHom M.graph N.graph
  adjacencyCompatible : Prop
  adjacencyCompatible_cert : adjacencyCompatible
  incidenceCompatible : Prop
  incidenceCompatible_cert : incidenceCompatible
  transitionCompatible : Prop
  transitionCompatible_cert : transitionCompatible

namespace MatrixRepresentationHom

/-- VII.定義3.5: identity matrix-target morphism. -/
def id {Vertex Edge RelationLabel : Type z}
    (M : MatrixRepresentationTarget Vertex Edge RelationLabel) :
    MatrixRepresentationHom M M where
  graphHom := FiniteDirectedGraphHom.id M.graph
  adjacencyCompatible := True
  adjacencyCompatible_cert := trivial
  incidenceCompatible := True
  incidenceCompatible_cert := trivial
  transitionCompatible := True
  transitionCompatible_cert := trivial

/-- VII.定義3.5: composition of selected matrix-target morphisms. -/
def comp {Vertex Edge RelationLabel : Type z}
    {M N O : MatrixRepresentationTarget Vertex Edge RelationLabel}
    (f : MatrixRepresentationHom M N) (g : MatrixRepresentationHom N O) :
    MatrixRepresentationHom M O where
  graphHom := FiniteDirectedGraphHom.comp f.graphHom g.graphHom
  adjacencyCompatible := f.adjacencyCompatible ∧ g.adjacencyCompatible
  adjacencyCompatible_cert := ⟨f.adjacencyCompatible_cert, g.adjacencyCompatible_cert⟩
  incidenceCompatible := f.incidenceCompatible ∧ g.incidenceCompatible
  incidenceCompatible_cert := ⟨f.incidenceCompatible_cert, g.incidenceCompatible_cert⟩
  transitionCompatible := f.transitionCompatible ∧ g.transitionCompatible
  transitionCompatible_cert := ⟨f.transitionCompatible_cert, g.transitionCompatible_cert⟩

/-- VII.定義3.5: expose selected adjacency compatibility. -/
theorem adjacencyCompatible_holds {Vertex Edge RelationLabel : Type z}
    {M N : MatrixRepresentationTarget Vertex Edge RelationLabel}
    (f : MatrixRepresentationHom M N) :
    f.adjacencyCompatible :=
  f.adjacencyCompatible_cert

/-- VII.定義3.5: expose selected incidence compatibility. -/
theorem incidenceCompatible_holds {Vertex Edge RelationLabel : Type z}
    {M N : MatrixRepresentationTarget Vertex Edge RelationLabel}
    (f : MatrixRepresentationHom M N) :
    f.incidenceCompatible :=
  f.incidenceCompatible_cert

/-- VII.定義3.5: expose selected transition compatibility. -/
theorem transitionCompatible_holds {Vertex Edge RelationLabel : Type z}
    {M N : MatrixRepresentationTarget Vertex Edge RelationLabel}
    (f : MatrixRepresentationHom M N) :
    f.transitionCompatible :=
  f.transitionCompatible_cert

end MatrixRepresentationHom

/-- VII.定義3.5: target-category interface for matrix readings. -/
def matrixRepresentationTargetCategory (Vertex Edge RelationLabel : Type z) :
    AnalyticTargetCategory (MatrixRepresentationTarget Vertex Edge RelationLabel) where
  Hom := MatrixRepresentationHom
  id := MatrixRepresentationHom.id
  comp := MatrixRepresentationHom.comp

/--
VII.定義3.5: matrix representation profile over decorated architecture schemes.

This is definition-only AC4 surface.  Walk-count and nilpotence claims are left
to AC6, where the required exactness assumptions can be stated explicitly.
-/
structure MatrixRepresentationProfile {U : AtomCarrier.{u}} {A : ArchitectureObject U}
    {S : Site.AATSite A} {k : Type v} [CommRing k]
    (p : AATSchReadingParameter.{u, v, w, x, y} S k) where
  Vertex : Type z
  Edge : Type z
  RelationLabel : Type z
  matrixOf : AATSch p -> MatrixRepresentationTarget Vertex Edge RelationLabel
  mapMatrix :
    ∀ {X Y : AATSch p}, AATSchMorphism X Y ->
      MatrixRepresentationHom (matrixOf X) (matrixOf Y)
  map_id :
    ∀ {X : AATSch p} (I : AATSchIdentityData X),
      mapMatrix I.morphism = MatrixRepresentationHom.id (matrixOf X)
  map_comp :
    ∀ {X Y Z : AATSch p} {f : AATSchMorphism X Y} {g : AATSchMorphism Y Z}
      (C : AATSchCompositionData f g),
      mapMatrix C.morphism = MatrixRepresentationHom.comp (mapMatrix f) (mapMatrix g)

namespace MatrixRepresentationProfile

variable {U : AtomCarrier.{u}} {A : ArchitectureObject U}
variable {S : Site.AATSite A} {k : Type v} [CommRing k]
variable {p : AATSchReadingParameter.{u, v, w, x, y} S k}

/-- VII.定義3.5: matrix profile as an analytic representation. -/
def toAnalyticRepresentation (P : MatrixRepresentationProfile p) :
    AnalyticRepresentation p
      (MatrixRepresentationTarget P.Vertex P.Edge P.RelationLabel) where
  targetCategory := matrixRepresentationTargetCategory P.Vertex P.Edge P.RelationLabel
  obj := P.matrixOf
  map := P.mapMatrix
  map_id := P.map_id
  map_comp := P.map_comp

end MatrixRepresentationProfile

end RepresentationAnalysis
end AAT.AG
