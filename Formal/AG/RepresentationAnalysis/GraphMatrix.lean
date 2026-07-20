import Formal.AG.RepresentationAnalysis.PreservationReflection
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Matrix.Mul

noncomputable section

namespace AAT.AG
namespace RepresentationAnalysis

open CategoryTheory

universe u v w x z

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

/-- VII.定義3.3: graph hom equality is determined by vertex / edge maps and
the selected label-compatibility proposition. -/
@[ext]
theorem ext {Vertex Edge RelationLabel : Type z}
    {G H : FiniteDirectedGraphTarget Vertex Edge RelationLabel}
    {f g : FiniteDirectedGraphHom G H}
    (hV : f.vertexMap = g.vertexMap) (hE : f.edgeMap = g.edgeMap)
    (hRel : f.relationLabelCompatible ↔ g.relationLabelCompatible) :
    f = g := by
  cases f
  cases g
  cases hV
  cases hE
  cases propext hRel
  simp

/-- VII.定義3.3: identity is a left unit for selected graph morphisms. -/
theorem id_comp {Vertex Edge RelationLabel : Type z}
    {G H : FiniteDirectedGraphTarget Vertex Edge RelationLabel}
    (f : FiniteDirectedGraphHom G H) :
    comp (id G) f = f := by
  apply ext
  · rfl
  · rfl
  · constructor
    · intro h
      exact h.2
    · intro h
      exact ⟨trivial, h⟩

/-- VII.定義3.3: identity is a right unit for selected graph morphisms. -/
theorem comp_id {Vertex Edge RelationLabel : Type z}
    {G H : FiniteDirectedGraphTarget Vertex Edge RelationLabel}
    (f : FiniteDirectedGraphHom G H) :
    comp f (id H) = f := by
  apply ext
  · rfl
  · rfl
  · constructor
    · intro h
      exact h.1
    · intro h
      exact ⟨h, trivial⟩

/-- VII.定義3.3: selected graph morphism composition is associative. -/
theorem assoc {Vertex Edge RelationLabel : Type z}
    {G H K L : FiniteDirectedGraphTarget Vertex Edge RelationLabel}
    (f : FiniteDirectedGraphHom G H) (g : FiniteDirectedGraphHom H K)
    (h : FiniteDirectedGraphHom K L) :
    comp (comp f g) h = comp f (comp g h) := by
  apply ext
  · rfl
  · rfl
  · constructor
    · intro hcomp
      exact ⟨hcomp.1.1, ⟨hcomp.1.2, hcomp.2⟩⟩
    · intro hcomp
      exact ⟨⟨hcomp.1, hcomp.2.1⟩, hcomp.2.2⟩

end FiniteDirectedGraphHom

/-- VII.定義3.3: finite graph readings form a Mathlib category. -/
instance FiniteDirectedGraphTarget.category
    (Vertex Edge RelationLabel : Type z) :
    Category (FiniteDirectedGraphTarget Vertex Edge RelationLabel) where
  Hom := FiniteDirectedGraphHom
  id := FiniteDirectedGraphHom.id
  comp := FiniteDirectedGraphHom.comp
  id_comp := FiniteDirectedGraphHom.id_comp
  comp_id := FiniteDirectedGraphHom.comp_id
  assoc := FiniteDirectedGraphHom.assoc

/--
VII.定義3.3: selected relation profile used to build a graph reading.

The profile records how selected relation data for each decorated architecture
scheme is sent into the graph edges.  Exact cycle witness properties are left
to AC5.
-/
structure GraphRepresentationProfile {U : AtomCarrier.{u}} {A : ArchitectureObject U}
    {S : Site.AATSite A} {k : Type v} [CommRing k]
    {raw : LawAlgebra.RawAmbientRestrictionSystem S k}
    [HasSheafify S.topology (LawAlgebra.AATCommAlgCat k)]
    (p : AATSchReadingParameter raw) where
  Vertex : Type z
  Edge : Type z
  RelationLabel : Type z
  representation : AnalyticRepresentation p
    (FiniteDirectedGraphTarget Vertex Edge RelationLabel)
  SelectedRelation : AATSch p -> Type z
  relationEdge : ∀ X : AATSch p, SelectedRelation X -> Edge
  selectedEdge : AATSch p -> Edge -> Prop
  relationEdge_selected :
    ∀ (X : AATSch p) (r : SelectedRelation X), selectedEdge X (relationEdge X r)

namespace GraphRepresentationProfile

variable {U : AtomCarrier.{u}} {A : ArchitectureObject U}
variable {S : Site.AATSite A} {k : Type v} [CommRing k]
variable {raw : LawAlgebra.RawAmbientRestrictionSystem S k}
variable [HasSheafify S.topology (LawAlgebra.AATCommAlgCat k)]
variable {p : AATSchReadingParameter raw}

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
    {raw : LawAlgebra.RawAmbientRestrictionSystem S k}
    [HasSheafify S.topology (LawAlgebra.AATCommAlgCat k)]
    {p : AATSchReadingParameter raw}
    (P : GraphRepresentationProfile p) where
  dependencyAxisSelected : AATSch p -> Prop
  structuralDependencyObstructionZero : AATSch p -> Prop
  selectedCycleObstructionWitness :
    ∀ X : AATSch p, FiniteDirectedGraphTarget.DirectedCycle (P.representation.obj X) -> Prop
  graphCycle_yields_obstructionWitness :
    ∀ X : AATSch p, dependencyAxisSelected X ->
      ∀ c : FiniteDirectedGraphTarget.DirectedCycle (P.representation.obj X),
        selectedCycleObstructionWitness X c
  obstructionZero_excludes_cycleWitness :
    ∀ X : AATSch p, structuralDependencyObstructionZero X ->
      ∀ c : FiniteDirectedGraphTarget.DirectedCycle (P.representation.obj X),
        ¬ selectedCycleObstructionWitness X c

namespace DependencyAcyclicityProfile

variable {U : AtomCarrier.{u}} {A : ArchitectureObject U}
variable {S : Site.AATSite A} {k : Type v} [CommRing k]
variable {raw : LawAlgebra.RawAmbientRestrictionSystem S k}
variable [HasSheafify S.topology (LawAlgebra.AATCommAlgCat k)]
variable {p : AATSchReadingParameter raw}
variable {P : GraphRepresentationProfile p}

/-- VII.命題3.4: graph cycles yield selected obstruction witnesses. -/
theorem selectedCycleObstructionWitness_of_graphCycle
    (D : DependencyAcyclicityProfile P) {X : AATSch p}
    (haxis : D.dependencyAxisSelected X)
    (c : FiniteDirectedGraphTarget.DirectedCycle (P.representation.obj X)) :
    D.selectedCycleObstructionWitness X c :=
  D.graphCycle_yields_obstructionWitness X haxis c

/-- VII.命題3.4: structural dependency-obstruction zero excludes cycle witnesses. -/
theorem no_selectedCycleObstructionWitness_of_obstructionZero
    (D : DependencyAcyclicityProfile P) {X : AATSch p}
    (hzero : D.structuralDependencyObstructionZero X)
    (c : FiniteDirectedGraphTarget.DirectedCycle (P.representation.obj X)) :
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
    FiniteDirectedGraphTarget.Acyclic (P.representation.obj X) := by
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

/-- VII.定義3.5: cardinality of the selected edge fiber from `i` to `j`. -/
def edgeFiberCard {Vertex Edge RelationLabel : Type z}
    (G : FiniteDirectedGraphTarget Vertex Edge RelationLabel) (i j : Vertex) : Nat :=
  by
    classical
    letI := G.edgeFintype
    exact Fintype.card { e : Edge // G.source e = i ∧ G.target e = j }

namespace FiniteDirectedGraphTarget.CountedDirectedWalk

variable {Vertex Edge RelationLabel : Type z}
    {G : FiniteDirectedGraphTarget Vertex Edge RelationLabel}

/-- VII.命題3.6: a counted walk is determined by its ordered edge list. -/
theorem edges_injective {start finish : Vertex} {n : Nat} :
    Function.Injective
      (@edges Vertex Edge RelationLabel G start finish n) := by
  intro w
  induction w with
  | nil v =>
      intro w' h
      cases w'
      rfl
  | @cons start finish e n hsource tail ih =>
      intro w' h
      cases w' with
      | cons e' n' hsource' tail' =>
          simp only [edges, List.cons.injEq] at h
          rcases h with ⟨rfl, htail⟩
          have htails : tail = tail' := ih htail
          subst tail'
          rfl

/-- VII.命題3.6: fixed-length counted walks form a finite type. -/
noncomputable instance fintype
    (G : FiniteDirectedGraphTarget Vertex Edge RelationLabel)
    (start finish : Vertex) (n : Nat) :
    Fintype (CountedDirectedWalk G start finish n) := by
  classical
  letI := G.edgeFintype
  letI := G.edgeDecidableEq
  let vectorFinite : Finite (List.Vector Edge n) :=
    Finite.of_injective (fun v : List.Vector Edge n => fun i => v.get i) (by
      intro v w h
      apply List.Vector.ext
      intro i
      exact congrFun h i)
  let walkFinite : Finite (CountedDirectedWalk G start finish n) :=
    @Finite.of_injective _ _ vectorFinite
      (fun w => ⟨edges w, edges_length w⟩ :
        CountedDirectedWalk G start finish n -> List.Vector Edge n)
      (by
        intro w w' h
        apply edges_injective
        exact Subtype.ext_iff.mp h)
  letI := walkFinite
  exact Fintype.ofFinite _

/-- VII.命題3.6: length-zero walks are exactly endpoint equalities. -/
def zeroEquiv (G : FiniteDirectedGraphTarget Vertex Edge RelationLabel)
    (start finish : Vertex) :
    CountedDirectedWalk G start finish 0 ≃
      Subtype (fun _ : Unit => start = finish) where
  toFun w := by cases w; exact ⟨(), rfl⟩
  invFun h := by
    have hEq := h.property
    subst finish
    exact .nil start
  left_inv w := by cases w; rfl
  right_inv h := Subsingleton.elim _ _

/--
VII.命題3.6: a length-`n + 1` walk is exactly a middle vertex, a selected
first edge into that vertex, and a length-`n` tail.
-/
def succEquiv (G : FiniteDirectedGraphTarget Vertex Edge RelationLabel)
    (n : Nat) (start finish : Vertex) :
    CountedDirectedWalk G start finish (n + 1) ≃
      Σ middle : Vertex,
        { e : Edge // G.source e = start ∧ G.target e = middle } ×
          CountedDirectedWalk G middle finish n where
  toFun w := by
    cases w with
    | cons e n hsource tail =>
        exact ⟨G.target e, ⟨⟨e, hsource, rfl⟩, tail⟩⟩
  invFun data := by
    rcases data with ⟨middle, ⟨⟨e, hsource, htarget⟩, tail⟩⟩
    subst middle
    exact .cons e n hsource tail
  left_inv w := by cases w; rfl
  right_inv data := by
    rcases data with ⟨middle, ⟨⟨e, hsource, htarget⟩, tail⟩⟩
    subst middle
    rfl

/-- VII.命題3.6: cardinality of the length-zero walk type. -/
theorem card_zero (G : FiniteDirectedGraphTarget Vertex Edge RelationLabel)
    [DecidableEq Vertex]
    (start finish : Vertex) :
    Fintype.card (CountedDirectedWalk G start finish 0) =
      Fintype.card (Subtype (fun _ : Unit => start = finish)) := by
  classical
  exact Fintype.card_congr (zeroEquiv G start finish)

/--
VII.命題3.6: cardinality decomposition of length-`n + 1` walks through the
selected first-edge fiber and length-`n` tail.
-/
theorem card_succ (G : FiniteDirectedGraphTarget Vertex Edge RelationLabel)
    [Fintype Vertex]
    (n : Nat) (start finish : Vertex) :
    Fintype.card (CountedDirectedWalk G start finish (n + 1)) =
      ∑ middle : Vertex,
        edgeFiberCard G start middle *
          Fintype.card (CountedDirectedWalk G middle finish n) := by
  classical
  letI := G.edgeFintype
  letI := G.edgeDecidableEq
  rw [Fintype.card_congr (succEquiv G n start finish)]
  simp only [Fintype.card_sigma, Fintype.card_prod]
  rfl

end FiniteDirectedGraphTarget.CountedDirectedWalk

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
identity walk, and a length `n + 1` walk is one selected first edge followed by
a length `n` walk.
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

/-- VII.命題3.6: the selected adjacency entry is the cardinality of its edge fiber. -/
theorem adjacencyMatrix_apply_eq_edgeFiber_card
    {Vertex Edge RelationLabel : Type z}
    (G : FiniteDirectedGraphTarget Vertex Edge RelationLabel) (i j : Vertex) :
    adjacencyMatrix G i j = edgeFiberCard G i j := by
  classical
  unfold adjacencyMatrix edgeFiberCard
  rfl

/--
VII.命題3.6: length-one matrix walk count is the cardinality of the selected
edge fiber.
-/
theorem matrixWalkCount_one_eq_edgeFiber_card
    {Vertex Edge RelationLabel : Type z}
    (G : FiniteDirectedGraphTarget Vertex Edge RelationLabel) (i j : Vertex) :
    matrixWalkCount G 1 i j = edgeFiberCard G i j := by
  classical
  letI := G.vertexFintype
  letI := G.vertexDecidableEq
  rw [← adjacencyMatrix_apply_eq_edgeFiber_card G i j]
  calc
    matrixWalkCount G 1 i j =
        ∑ k : Vertex, adjacencyMatrix G i k * (if k = j then 1 else 0) := by
      simp [matrixWalkCount]
    _ = adjacencyMatrix G i j := by
      rw [Finset.sum_eq_single j]
      · simp
      · intro b _ hb
        simp [hb]
      · intro hnot
        exact False.elim (hnot (Finset.mem_univ j))

/--
VII.命題3.6: the recursive matrix walk count is the actual cardinality of the
length-indexed counted-walk type, for every natural length.
-/
theorem matrixWalkCount_eq_countedDirectedWalk_card
    {Vertex Edge RelationLabel : Type z}
    (G : FiniteDirectedGraphTarget Vertex Edge RelationLabel) :
    ∀ (n : Nat) (start finish : Vertex),
      matrixWalkCount G n start finish =
        Fintype.card (FiniteDirectedGraphTarget.CountedDirectedWalk
          G start finish n) := by
  classical
  letI := G.vertexFintype
  letI := G.vertexDecidableEq
  letI := G.edgeFintype
  letI := G.edgeDecidableEq
  intro n
  induction n with
  | zero =>
      intro start finish
      rw [FiniteDirectedGraphTarget.CountedDirectedWalk.card_zero]
      by_cases h : start = finish <;> simp [matrixWalkCount, h]
  | succ n ih =>
      intro start finish
      rw [FiniteDirectedGraphTarget.CountedDirectedWalk.card_succ]
      change
        (∑ middle : Vertex,
          adjacencyMatrix G start middle * matrixWalkCount G n middle finish) =
        ∑ middle : Vertex,
          edgeFiberCard G start middle *
            Fintype.card (FiniteDirectedGraphTarget.CountedDirectedWalk
              G middle finish n)
      apply Finset.sum_congr rfl
      intro middle _
      rw [adjacencyMatrix_apply_eq_edgeFiber_card, ih]

/--
VII.命題3.6 Matrix Walk Reading: every adjacency-matrix power entry is the
cardinality of the selected length-`n` counted-walk type.
-/
theorem adjacencyMatrixPower_apply_eq_countedDirectedWalk_card
    {Vertex Edge RelationLabel : Type z}
    (G : FiniteDirectedGraphTarget Vertex Edge RelationLabel)
    (n : Nat) (start finish : Vertex) :
    (adjacencyMatrixPower G n) start finish =
      Fintype.card (FiniteDirectedGraphTarget.CountedDirectedWalk
        G start finish n) :=
  (adjacencyMatrixPower_apply_eq_matrixWalkCount G n start finish).trans
    (matrixWalkCount_eq_countedDirectedWalk_card G n start finish)

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

/-- VII.定義3.5: matrix hom equality is determined by the selected graph hom
and the matrix-compatibility propositions. -/
@[ext]
theorem ext {Vertex Edge RelationLabel : Type z}
    {M N : MatrixRepresentationTarget Vertex Edge RelationLabel}
    {f g : MatrixRepresentationHom M N}
    (hGraph : f.graphHom = g.graphHom)
    (hAdj : f.adjacencyCompatible ↔ g.adjacencyCompatible)
    (hInc : f.incidenceCompatible ↔ g.incidenceCompatible)
    (hTrans : f.transitionCompatible ↔ g.transitionCompatible) :
    f = g := by
  cases f
  cases g
  cases hGraph
  cases propext hAdj
  cases propext hInc
  cases propext hTrans
  simp

/-- VII.定義3.5: identity is a left unit for selected matrix morphisms. -/
theorem id_comp {Vertex Edge RelationLabel : Type z}
    {M N : MatrixRepresentationTarget Vertex Edge RelationLabel}
    (f : MatrixRepresentationHom M N) :
    comp (id M) f = f := by
  apply ext
  · exact FiniteDirectedGraphHom.id_comp f.graphHom
  · constructor
    · intro h
      exact h.2
    · intro h
      exact ⟨trivial, h⟩
  · constructor
    · intro h
      exact h.2
    · intro h
      exact ⟨trivial, h⟩
  · constructor
    · intro h
      exact h.2
    · intro h
      exact ⟨trivial, h⟩

/-- VII.定義3.5: identity is a right unit for selected matrix morphisms. -/
theorem comp_id {Vertex Edge RelationLabel : Type z}
    {M N : MatrixRepresentationTarget Vertex Edge RelationLabel}
    (f : MatrixRepresentationHom M N) :
    comp f (id N) = f := by
  apply ext
  · exact FiniteDirectedGraphHom.comp_id f.graphHom
  · constructor
    · intro h
      exact h.1
    · intro h
      exact ⟨h, trivial⟩
  · constructor
    · intro h
      exact h.1
    · intro h
      exact ⟨h, trivial⟩
  · constructor
    · intro h
      exact h.1
    · intro h
      exact ⟨h, trivial⟩

/-- VII.定義3.5: selected matrix morphism composition is associative. -/
theorem assoc {Vertex Edge RelationLabel : Type z}
    {M N O P : MatrixRepresentationTarget Vertex Edge RelationLabel}
    (f : MatrixRepresentationHom M N) (g : MatrixRepresentationHom N O)
    (h : MatrixRepresentationHom O P) :
    comp (comp f g) h = comp f (comp g h) := by
  apply ext
  · exact FiniteDirectedGraphHom.assoc f.graphHom g.graphHom h.graphHom
  · constructor
    · intro hcomp
      exact ⟨hcomp.1.1, ⟨hcomp.1.2, hcomp.2⟩⟩
    · intro hcomp
      exact ⟨⟨hcomp.1, hcomp.2.1⟩, hcomp.2.2⟩
  · constructor
    · intro hcomp
      exact ⟨hcomp.1.1, ⟨hcomp.1.2, hcomp.2⟩⟩
    · intro hcomp
      exact ⟨⟨hcomp.1, hcomp.2.1⟩, hcomp.2.2⟩
  · constructor
    · intro hcomp
      exact ⟨hcomp.1.1, ⟨hcomp.1.2, hcomp.2⟩⟩
    · intro hcomp
      exact ⟨⟨hcomp.1, hcomp.2.1⟩, hcomp.2.2⟩

end MatrixRepresentationHom

/-- VII.定義3.5: matrix readings form a Mathlib category. -/
instance MatrixRepresentationTarget.category
    (Vertex Edge RelationLabel : Type z) :
    Category (MatrixRepresentationTarget Vertex Edge RelationLabel) where
  Hom := MatrixRepresentationHom
  id := MatrixRepresentationHom.id
  comp := MatrixRepresentationHom.comp
  id_comp := MatrixRepresentationHom.id_comp
  comp_id := MatrixRepresentationHom.comp_id
  assoc := MatrixRepresentationHom.assoc

/--
VII.定義3.5: matrix representation profile over decorated architecture schemes.

This is definition-only AC4 surface.  Walk-count and nilpotence claims are left
to AC6, where the required exactness assumptions can be stated explicitly.
-/
structure MatrixRepresentationProfile {U : AtomCarrier.{u}} {A : ArchitectureObject U}
    {S : Site.AATSite A} {k : Type v} [CommRing k]
    {raw : LawAlgebra.RawAmbientRestrictionSystem S k}
    [HasSheafify S.topology (LawAlgebra.AATCommAlgCat k)]
    (p : AATSchReadingParameter raw) where
  Vertex : Type z
  Edge : Type z
  RelationLabel : Type z
  representation : AnalyticRepresentation p
    (MatrixRepresentationTarget Vertex Edge RelationLabel)

namespace MatrixRepresentationProfile

variable {U : AtomCarrier.{u}} {A : ArchitectureObject U}
variable {S : Site.AATSite A} {k : Type v} [CommRing k]
variable {raw : LawAlgebra.RawAmbientRestrictionSystem S k}
variable [HasSheafify S.topology (LawAlgebra.AATCommAlgCat k)]
variable {p : AATSchReadingParameter raw}

end MatrixRepresentationProfile

end RepresentationAnalysis
end AAT.AG
