import ResearchLean.AG.VisibleCycleReflection.ActualSearchCounterinput
import Mathlib.Topology.Order.UpperLowerSetTopology
import Formal.Util.AssertStandardAxioms

/-!
# Finite incidence points and their actual Alexandrov topology

## Implementation notes

Point codes contain vertices followed by edge points. The only strict order
relations put a vertex below an incident edge point. The finite open table lists
all upward closed point sets. Charts are precisely the principal upper sets of
vertices. The geometric proof is derived from these columns, separately from
primitive Law and target data.
-/

namespace AAT.AG.VisibleCycleReflection
open FiniteInputTable

/-- Pure finite geometry data: vertices, edge points, and each edge's two endpoint codes. -/
structure FiniteIncidenceGeometry where
  vertexCount : ℕ
  edgeCount : ℕ
  endpoints : Fin edgeCount → Fin vertexCount × Fin vertexCount

namespace FiniteIncidenceGeometry
variable (D : FiniteIncidenceGeometry)
/-- Geometric vertex codes. -/
abbrev Vertex := Fin D.vertexCount
/-- Geometric edge-point codes. -/
abbrev EdgePoint := Fin D.edgeCount
/-- All geometric point codes, with vertices before edge points. -/
abbrev Point := Fin (D.vertexCount + D.edgeCount)
/-- The geometric point representing a vertex. -/
def vertexPoint (i : D.Vertex) : D.Point := i.castAdd D.edgeCount
/-- The geometric point representing an edge. -/
def edgePoint (e : D.EdgePoint) : D.Point := e.natAdd D.vertexCount
/-- A vertex is incident precisely when it is one of the two endpoints of that edge point. -/
def Incident (i : D.Vertex) (e : D.EdgePoint) : Prop :=
  i = (D.endpoints e).1 ∨ i = (D.endpoints e).2
/-- Endpoint incidence is computed by finite code equality. -/
instance incidentDecidable (i : D.Vertex) (e : D.EdgePoint) : Decidable (D.Incident i e) :=
  inferInstanceAs (Decidable (i = (D.endpoints e).1 ∨ i = (D.endpoints e).2))

/-- Vertex point coding is injective. -/
theorem vertexPoint_injective : Function.Injective D.vertexPoint := by
  intro i j h
  apply Fin.ext
  have hv := congrArg Fin.val h
  exact hv
/-- Edge point coding is injective. -/
theorem edgePoint_injective : Function.Injective D.edgePoint := by
  intro i j h
  apply Fin.ext
  have hv := congrArg Fin.val h
  change D.vertexCount + i.val = D.vertexCount + j.val at hv
  omega
/-- A vertex point and an edge point are distinct geometric points. -/
theorem vertexPoint_ne_edgePoint (i : D.Vertex) (e : D.EdgePoint) :
    D.vertexPoint i ≠ D.edgePoint e := by
  intro h
  have hv := congrArg Fin.val h
  change i.val = D.vertexCount + e.val at hv
  have hi := i.isLt
  omega

/-- The incidence order has only reflexive pairs and vertex-to-incident-edge pairs. -/
def Below (x y : D.Point) : Prop :=
  x = y ∨ ∃ i e, x = D.vertexPoint i ∧ y = D.edgePoint e ∧ D.Incident i e

/-- The vertex-below-edge relation is an actual partial order on geometric points. -/
def order : PartialOrder D.Point where
  lt x y := D.Below x y ∧ ¬D.Below y x
  le := D.Below
  le_refl x := Or.inl rfl
  le_trans x y z hxy hyz := by
    rcases hxy with rfl | ⟨i,e,rfl,rfl,hie⟩
    · exact hyz
    · rcases hyz with rfl | ⟨j,f,hj,rfl,hjf⟩
      · exact Or.inr ⟨i,e,rfl,rfl,hie⟩
      · exact False.elim (D.vertexPoint_ne_edgePoint j e hj.symm)
  le_antisymm x y hxy hyx := by
    rcases hxy with h | ⟨i,e,rfl,rfl,hie⟩
    · exact h
    · rcases hyx with h | ⟨j,f,hj,hf,hjf⟩
      · exact h.symm
      · exact False.elim (D.vertexPoint_ne_edgePoint j e hj.symm)

/-- Upward closure is tested directly on every incident vertex/edge-point pair. -/
def UpClosed (U : Finset D.Point) : Prop :=
  ∀ i e, D.Incident i e → D.vertexPoint i ∈ U → D.edgePoint e ∈ U
/-- Finite upward closure is a finite universal test on incidence and membership. -/
instance upClosedDecidable (U : Finset D.Point) : Decidable (D.UpClosed U) :=
  inferInstanceAs (Decidable (∀ i e, D.Incident i e → D.vertexPoint i ∈ U → D.edgePoint e ∈ U))
/-- Enumerate all and only upward closed subsets of the finite geometric point set. -/
def opens : Finset (Finset D.Point) := Finset.univ.powerset.filter D.UpClosed
/-- Membership in the open table is exactly upward closure along incidence pairs. -/
@[simp] theorem mem_opens (U : Finset D.Point) : U ∈ D.opens ↔ D.UpClosed U := by
  simp [opens]

/-- The actual topology is the standard upper-set topology of the incidence partial order. -/
def upperTopology : TopologicalSpace D.Point := @Topology.upperSet D.Point D.order.toPreorder

/-- The finite closure predicate is exactly the standard upper-set predicate. -/
theorem upClosed_iff_upper (U : Finset D.Point) :
    D.UpClosed U ↔ @IsUpperSet D.Point D.order.toLE (U : Set D.Point) := by
  constructor
  · intro h x y hxy hx
    rcases hxy with rfl | ⟨i,e,rfl,rfl,hie⟩
    · exact hx
    · exact h i e hie hx
  · intro h i e hie hi
    exact h (Or.inr ⟨i,e,rfl,rfl,hie⟩) hi

/-- A chart is exactly its vertex together with every incident edge point. -/
def chart (i : D.Vertex) : Finset D.Point :=
  Finset.univ.filter fun x => x = D.vertexPoint i ∨ ∃ e, x = D.edgePoint e ∧ D.Incident i e
/-- The chart's finite point membership is its principal incidence upper-set formula. -/
@[simp] theorem mem_chart (i : D.Vertex) (x : D.Point) :
    x ∈ D.chart i ↔ x = D.vertexPoint i ∨ ∃ e, x = D.edgePoint e ∧ D.Incident i e := by
  simp [chart]
/-- Each chart contains its own geometric vertex point. -/
theorem vertex_mem_chart (i : D.Vertex) : D.vertexPoint i ∈ D.chart i :=
  (D.mem_chart i _).mpr (Or.inl rfl)
/-- Vertex membership in a chart determines that chart's index uniquely. -/
@[simp] theorem vertex_mem_chart_iff (i j : D.Vertex) : D.vertexPoint j ∈ D.chart i ↔ j = i := by
  rw [D.mem_chart]
  constructor
  · rintro (h | ⟨e,he,_⟩)
    · exact D.vertexPoint_injective h
    · exact False.elim (D.vertexPoint_ne_edgePoint j e he)
  · rintro rfl; exact Or.inl rfl
/-- An edge point lies in a chart exactly when that chart's vertex is an endpoint. -/
@[simp] theorem edge_mem_chart_iff (i : D.Vertex) (e : D.EdgePoint) :
    D.edgePoint e ∈ D.chart i ↔ D.Incident i e := by
  rw [D.mem_chart]
  constructor
  · rintro (h | ⟨f,hf,hi⟩)
    · exact False.elim (D.vertexPoint_ne_edgePoint i e h.symm)
    · exact D.edgePoint_injective hf ▸ hi
  · intro h; exact Or.inr ⟨e,rfl,h⟩
/-- Every chart is upward closed under the actual incidence order. -/
theorem chart_upClosed (i : D.Vertex) : D.UpClosed (D.chart i) := by
  intro j e hje hj
  have hji := (D.vertex_mem_chart_iff i j).mp hj
  subst j
  exact (D.edge_mem_chart_iff i e).mpr hje

/-- Attach independent geometry and target columns to an unchanged primitive finite table. -/
abbrev table (B : FiniteInputTable) (target : D.Vertex → Finset (Fin B.targetCount))
    (edgeOrder : List (D.Vertex × D.Vertex) := []) : FiniteInputTable :=
  {B with
    pointCount := D.vertexCount + D.edgeCount
    chartCount := D.vertexCount
    opens := D.opens
    chart := D.chart
    target := target
    edgeOrder := edgeOrder}

/-- The incidence open table is closed under all finite topology operations. -/
theorem table_topology_valid (B : FiniteInputTable)
    (target : D.Vertex → Finset (Fin B.targetCount)) (edgeOrder : List (D.Vertex × D.Vertex)) :
    (D.table B target edgeOrder).TopologyValid := by
  change ∅ ∈ D.opens ∧ Finset.univ ∈ D.opens ∧ _ ∧ _
  refine ⟨D.mem_opens _ |>.mpr (by simp [UpClosed]),
    D.mem_opens _ |>.mpr (by simp [UpClosed]),?_,?_⟩
  · intro U V
    apply (D.mem_opens _).mpr
    intro i e hie hi
    rcases Finset.mem_union.mp hi with hi | hi
    · exact Finset.mem_union.mpr (Or.inl ((D.mem_opens _).mp U.2 i e hie hi))
    · exact Finset.mem_union.mpr (Or.inr ((D.mem_opens _).mp V.2 i e hie hi))
  · intro U V
    apply (D.mem_opens _).mpr
    intro i e hie hi
    exact Finset.mem_inter.mpr ⟨(D.mem_opens _).mp U.2 i e hie (Finset.mem_inter.mp hi).1,
      (D.mem_opens _).mp V.2 i e hie (Finset.mem_inter.mp hi).2⟩

/-- An open set containing a chart's minimal vertex contains that entire chart. -/
theorem chart_subset_of_vertex (U : Finset D.Point) (hU : D.UpClosed U) (i : D.Vertex)
    (hi : D.vertexPoint i ∈ U) : D.chart i ⊆ U := by
  intro x hx
  rcases (D.mem_chart i x).mp hx with rfl | ⟨e,rfl,hie⟩
  · exact hi
  · exact hU i e hie hi

/-- Connectedness of each actual chart is generated by its minimal vertex. -/
theorem table_chart_preconnected (B : FiniteInputTable)
    (target : D.Vertex → Finset (Fin B.targetCount)) (edgeOrder : List (D.Vertex × D.Vertex))
    (i : D.Vertex) : (D.table B target edgeOrder).Preconnected (D.chart i) := by
  intro U V hsub hU hV
  have hi := Finset.mem_union.mp (hsub (D.vertex_mem_chart i))
  rcases hi with hi | hi
  · have hwhole := D.chart_subset_of_vertex U.1 ((D.mem_opens _).mp U.2) i hi
    obtain ⟨x,hx⟩ := hV
    exact ⟨x,Finset.mem_inter.mpr ⟨(Finset.mem_inter.mp hx).1,
      Finset.mem_inter.mpr ⟨hwhole (Finset.mem_inter.mp hx).1,(Finset.mem_inter.mp hx).2⟩⟩⟩
  · have hwhole := D.chart_subset_of_vertex V.1 ((D.mem_opens _).mp V.2) i hi
    obtain ⟨x,hx⟩ := hU
    exact ⟨x,Finset.mem_inter.mpr ⟨(Finset.mem_inter.mp hx).1,
      Finset.mem_inter.mpr ⟨(Finset.mem_inter.mp hx).2,hwhole (Finset.mem_inter.mp hx).1⟩⟩⟩

/-- Every point belongs to a chart: its vertex chart or a chart of one of its edge endpoints. -/
theorem charts_cover (x : D.Point) : ∃ i, x ∈ D.chart i := by
  refine Fin.addCases (fun i => ?_) (fun e => ?_) x
  · exact ⟨i,D.vertex_mem_chart i⟩
  · exact ⟨(D.endpoints e).1,(D.edge_mem_chart_iff _ e).mpr (Or.inl rfl)⟩

/-- Ordered chart overlaps consist exactly of edge points with that endpoint pair. -/
theorem mem_overlap_iff (ho : ∀ e, (D.endpoints e).1 < (D.endpoints e).2)
    (i j : D.Vertex) (hij : i < j) (x : D.Point) :
    x ∈ D.chart i ∩ D.chart j ↔ ∃ e, x = D.edgePoint e ∧ D.endpoints e = (i,j) := by
  constructor
  · intro hx
    have hi := (D.mem_chart i x).mp (Finset.mem_inter.mp hx).1
    have hj := (D.mem_chart j x).mp (Finset.mem_inter.mp hx).2
    rcases hi with rfl | ⟨e,rfl,hi⟩
    · have he := (D.vertex_mem_chart_iff j i).mp (Finset.mem_inter.mp hx).2
      exact False.elim ((ne_of_lt hij) he)
    · have hj := (D.edge_mem_chart_iff j e).mp (Finset.mem_inter.mp hx).2
      refine ⟨e,rfl,?_⟩
      rcases hi with hi | hi <;> rcases hj with hj | hj
      · exact False.elim ((ne_of_lt hij) (hi.trans hj.symm))
      · exact Prod.ext hi.symm hj.symm
      · have he := ho e
        rw [← hj,← hi] at he
        exact False.elim (not_lt_of_ge (le_of_lt hij) he)
      · exact False.elim ((ne_of_lt hij) (hi.trans hj.symm))
  · rintro ⟨e,rfl,he⟩
    apply Finset.mem_inter.mpr
    constructor
    · apply (D.edge_mem_chart_iff i e).mpr
      exact Or.inl (congrArg Prod.fst he).symm
    · apply (D.edge_mem_chart_iff j e).mpr
      exact Or.inr (congrArg Prod.snd he).symm

/-- Simplicity of endpoint pairs makes every nonempty ordered overlap a singleton edge point. -/
theorem overlap_eq_singleton (ho : ∀ e, (D.endpoints e).1 < (D.endpoints e).2)
    (hu : Function.Injective D.endpoints) (i j : D.Vertex) (hij : i < j)
    (hne : (D.chart i ∩ D.chart j).Nonempty) :
    ∃ e, D.chart i ∩ D.chart j = {D.edgePoint e} := by
  obtain ⟨x,hx⟩ := hne
  obtain ⟨e,rfl,he⟩ := (D.mem_overlap_iff ho i j hij x).mp hx
  refine ⟨e,?_⟩
  ext y
  rw [D.mem_overlap_iff ho i j hij,Finset.mem_singleton]
  constructor
  · rintro ⟨f,rfl,hf⟩
    exact congrArg D.edgePoint (hu (hf.trans he.symm))
  · rintro rfl
    exact ⟨e,rfl,he⟩

/-- A singleton point passes the actual finite open-pair connectedness check. -/
theorem singleton_preconnected (T : FiniteInputTable) (x : T.Point) :
    T.Preconnected {x} := by
  intro U V _ hU hV
  obtain ⟨y,hy⟩ := hU
  obtain ⟨z,hz⟩ := hV
  have hyx := Finset.mem_singleton.mp (Finset.mem_inter.mp hy).1
  have hzx := Finset.mem_singleton.mp (Finset.mem_inter.mp hz).1
  have hu : x ∈ U.1 := hyx ▸ (Finset.mem_inter.mp hy).2
  have hv : x ∈ V.1 := hzx ▸ (Finset.mem_inter.mp hz).2
  exact ⟨x,by simp [hu,hv]⟩

/-- Distinct three charts have no common point in incidence geometry. -/
theorem triple_empty (i j k : D.Vertex) (hij : i < j) (hjk : j < k) :
    D.chart i ∩ D.chart j ∩ D.chart k = ∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro x hx
  have hi := (D.mem_chart i x).mp (Finset.mem_inter.mp (Finset.mem_inter.mp hx).1).1
  rcases hi with rfl | ⟨e,rfl,hi⟩
  · have he := (D.vertex_mem_chart_iff j i).mp
      (Finset.mem_inter.mp (Finset.mem_inter.mp hx).1).2
    exact (ne_of_lt hij) he
  · have hj := (D.edge_mem_chart_iff j e).mp
      (Finset.mem_inter.mp (Finset.mem_inter.mp hx).1).2
    have hk := (D.edge_mem_chart_iff k e).mp (Finset.mem_inter.mp hx).2
    rcases hi with hi | hi <;> rcases hj with hj | hj <;> rcases hk with hk | hk
    all_goals first
      | exact (ne_of_lt hij) (hi.trans hj.symm)
      | exact (ne_of_lt hjk) (hj.trans hk.symm)
      | exact (ne_of_lt (lt_trans hij hjk)) (hi.trans hk.symm)

/-- All geometric T0 conditions follow from a nonempty finite simple incidence graph. -/
theorem table_geometry_valid (B : FiniteInputTable)
    (target : D.Vertex → Finset (Fin B.targetCount)) (edgeOrder : List (D.Vertex × D.Vertex))
    (hv : 0 < D.vertexCount) (ho : ∀ e, (D.endpoints e).1 < (D.endpoints e).2)
    (hu : Function.Injective D.endpoints) : (D.table B target edgeOrder).GeometryValid := by
  refine ⟨hv,fun i => (D.mem_opens _).mpr (D.chart_upClosed i),
    fun i => ⟨D.vertexPoint i,D.vertex_mem_chart i⟩,D.charts_cover,
    D.table_chart_preconnected B target edgeOrder,?_,D.triple_empty⟩
  intro i j hij hne
  obtain ⟨e,he⟩ := D.overlap_eq_singleton ho hu i j hij hne
  change (D.table B target edgeOrder).Preconnected (D.chart i ∩ D.chart j)
  rw [he]
  exact singleton_preconnected (D.table B target edgeOrder) (D.edgePoint e)

/-- The decoded topology equals the actual upper-set topology of the incidence order. -/
theorem table_topology_eq_upper (B : FiniteInputTable)
    (target : D.Vertex → Finset (Fin B.targetCount)) (edgeOrder : List (D.Vertex × D.Vertex))
    (h : (D.table B target edgeOrder).Valid) :
    (D.table B target edgeOrder).actualTopology h = D.upperTopology := by
  classical
  apply TopologicalSpace.ext
  funext s
  apply propext
  change (∃ U ∈ D.opens, (U : Set D.Point) = s) ↔ @IsOpen D.Point D.upperTopology s
  change (∃ U ∈ D.opens, (U : Set D.Point) = s) ↔ @IsUpperSet D.Point D.order.toLE s
  constructor
  · rintro ⟨U,hU,rfl⟩
    exact (D.upClosed_iff_upper U).mp ((D.mem_opens U).mp hU)
  · intro hs
    refine ⟨s.toFinite.toFinset,?_,by ext x; simp; rfl⟩
    apply (D.mem_opens _).mpr
    apply (D.upClosed_iff_upper _).mpr
    simpa using hs

/-- The incidence topology is Alexandrov: arbitrary intersections of its opens are open. -/
theorem upperTopology_alexandrov : @AlexandrovDiscrete D.Point D.upperTopology := by
  letI : Preorder D.Point := D.order.toPreorder
  letI : TopologicalSpace D.Point := D.upperTopology
  exact Finite.toAlexandrovDiscrete

end FiniteIncidenceGeometry
end AAT.AG.VisibleCycleReflection
#assert_standard_axioms_only AAT.AG.VisibleCycleReflection.FiniteIncidenceGeometry
