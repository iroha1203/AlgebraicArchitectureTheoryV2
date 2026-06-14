import Formal.AG.RepresentationAnalysis.PreservationReflection
import Mathlib.Data.Matrix.Basic

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
