import ResearchLean.AG.VisibleCycleReflection.AATStateSheaf
import Mathlib.Combinatorics.SimpleGraph.Connectivity.WalkCounting
import Mathlib.Data.List.Dedup
import Formal.Util.AssertStandardAxioms

/-!
# Finite primitive and geometric input tables

## Implementation notes

All runtime fields use finite indices, Boolean primitive relations, and finite
sets. Geometry and target support are separate tables. Law values have their
own finite bound for each declared Law. No adequacy, relation reflection,
connectedness, sheaf condition, or repair certificate is a raw input field.
-/

namespace AAT.AG.VisibleCycleReflection
open CanonicalResolution ResolutionInvariance ObstructionDiagnosticBridge

/-- Raw finite data for C, before any validity or reflection decision. -/
structure FiniteInputTable where
  sourceCount : ℕ
  lawCount : ℕ
  targetCount : ℕ
  pointCount : ℕ
  chartCount : ℕ
  valueCount : Fin lawCount → ℕ
  eval : (law : Fin lawCount) → Fin sourceCount → Fin (valueCount law)
  read : Fin sourceCount → Fin targetCount
  relation : (Fin lawCount × Fin sourceCount) → (Fin lawCount × Fin sourceCount) → Bool
  opens : Finset (Finset (Fin pointCount))
  chart : Fin chartCount → Finset (Fin pointCount)
  target : Fin chartCount → Finset (Fin targetCount)
  edgeOrder : List (Fin chartCount × Fin chartCount) := []

namespace FiniteInputTable
variable (T : FiniteInputTable)

/-- Enumerated primitive subjects. -/
abbrev Source := Fin T.sourceCount
/-- Enumerated geometric points. -/
abbrev Point := Fin T.pointCount
/-- Ordered actual chart indices. -/
abbrev Chart := Fin T.chartCount
/-- Enumerated raw primitive generators. -/
abbrev Generator := Fin T.lawCount × T.Source
/-- Law-dependent finite value codes, retaining the Law tag. -/
abbrev RawLabel := Σ law : Fin T.lawCount, Fin (T.valueCount law)

/-- Decode exactly the declared finite Law evaluation table. -/
def laws : FiniteLawFamily T.Source where
  Law := Fin T.lawCount
  lawFintype := inferInstance
  Value law := Fin (T.valueCount law)
  valueDecidableEq _ := inferInstance
  eval := T.eval

/-- Raw generator labels used by the finite input validator. -/
def rawLabel (g : T.Generator) : T.RawLabel := ⟨g.1,T.eval g.1 g.2⟩

/-- Public raw label evaluation, retaining the declared Law and value. -/
@[simp] theorem rawLabel_apply (g : T.Generator) : T.rawLabel g = ⟨g.1,T.eval g.1 g.2⟩ := rfl

/-- Symmetric finite primitive-relation graph; loops contribute only reflexivity. -/
def relationGraph : SimpleGraph T.Generator where
  Adj g h := g ≠ h ∧ (T.relation g h = true ∨ T.relation h g = true)
  symm := by
    intro g h hg
    exact ⟨Ne.symm hg.1,hg.2.symm⟩
  loopless := ⟨fun g hg => hg.1 rfl⟩

/-- Public adjacency predicate of the finite primitive-relation graph. -/
theorem relationGraph_adj (g h : T.Generator) :
    T.relationGraph.Adj g h ↔ g ≠ h ∧ (T.relation g h = true ∨ T.relation h g = true) := Iff.rfl

/-- Primitive relation adjacency has a computable decision from the Boolean table. -/
instance relationGraphDecidable : DecidableRel T.relationGraph.Adj :=
  fun _ _ => inferInstanceAs (Decidable (_ ≠ _ ∧ (_ = true ∨ _ = true)))

/-- The complete raw graph comes from actual point-table intersections, independently of target support. -/
def rawGraph : SimpleGraph T.Chart where
  Adj i j := i ≠ j ∧ (T.chart i ∩ T.chart j).Nonempty
  symm := by intro i j h; exact ⟨h.1.symm,by simpa only [Finset.inter_comm] using h.2⟩
  loopless := ⟨fun i h => h.1 rfl⟩

/-- Public adjacency formula for the complete raw geometric graph. -/
theorem rawGraph_adj (i j : T.Chart) :
    T.rawGraph.Adj i j ↔ i ≠ j ∧ (T.chart i ∩ T.chart j).Nonempty := Iff.rfl

instance rawGraphDecidable : DecidableRel T.rawGraph.Adj :=
  fun i j => inferInstanceAs (Decidable (i ≠ j ∧ (T.chart i ∩ T.chart j).Nonempty))

/-- Ordered complete raw intersection cells, with witness multiplicity erased by proof irrelevance. -/
abbrev RawEdge := {ij : T.Chart × T.Chart // ij.1 < ij.2 ∧ (T.chart ij.1 ∩ T.chart ij.2).Nonempty}

/-- Remove repeated columns while retaining their first occurrence. -/
def firstOccurrences {α : Type*} [DecidableEq α] (xs : List α) : List α :=
  xs.reverse.dedup.reverse

/-- Removing repeated columns preserves exactly their membership. -/
@[simp] theorem mem_firstOccurrences {α : Type*} [DecidableEq α] (a : α) (xs : List α) :
    a ∈ firstOccurrences xs ↔ a ∈ xs := by simp [firstOccurrences]

/-- No column is repeated in the resulting finite enumeration. -/
theorem firstOccurrences_nodup {α : Type*} [DecidableEq α] (xs : List α) :
    (firstOccurrences xs).Nodup := by
  simpa only [firstOccurrences, List.nodup_reverse] using List.nodup_dedup xs.reverse

/-- Enumerate every primitive Law/source occurrence in the order of the finite input indices. -/
def rawGenerators : List T.Generator :=
  (List.finRange T.lawCount).flatMap fun law => (List.finRange T.sourceCount).map fun s => (law,s)

/-- Every original primitive generator occurs in the explicit bounded enumeration. -/
theorem mem_rawGenerators (g : T.Generator) : g ∈ T.rawGenerators := by
  simp only [rawGenerators,List.mem_flatMap,List.mem_map]
  exact ⟨g.1,by simp, g.2,by simp,rfl⟩

/-- Enumerate exactly source-generated raw Law/value labels, with duplicate occurrences removed. -/
def rawLabels : List T.RawLabel := firstOccurrences (T.rawGenerators.map T.rawLabel)

/-- Label table membership is exactly generation by an original primitive occurrence. -/
theorem mem_rawLabels_iff (r : T.RawLabel) : r ∈ T.rawLabels ↔ ∃ g, T.rawLabel g = r := by
  simp only [rawLabels,mem_firstOccurrences,List.mem_map]
  exact ⟨fun ⟨g,_,hg⟩ => ⟨g,hg⟩,fun ⟨g,hg⟩ => ⟨g,T.mem_rawGenerators g,hg⟩⟩

/-- Input edge-column order followed by all chart pairs; missing columns cannot omit actual intersections. -/
def rawEdgePairs : List (T.Chart × T.Chart) :=
  firstOccurrences (T.edgeOrder ++ (List.finRange T.chartCount).flatMap
    (fun i => (List.finRange T.chartCount).map fun j => (i,j)))

/-- All chart pairs remain in the finite search table, independently of a supplied display order. -/
theorem mem_rawEdgePairs (ij : T.Chart × T.Chart) : ij ∈ T.rawEdgePairs := by
  simp only [rawEdgePairs,mem_firstOccurrences,List.mem_append,List.mem_flatMap,List.mem_map]
  exact Or.inr ⟨ij.1,by simp,ij.2,by simp,rfl⟩

/-- Enumerate every nonempty actual ordered chart intersection from the same point table. -/
def rawEdges : List T.RawEdge :=
  firstOccurrences (T.rawEdgePairs.filterMap fun ij =>
    if h : ij.1 < ij.2 ∧ (T.chart ij.1 ∩ T.chart ij.2).Nonempty then some ⟨ij,h⟩ else none)

/-- Every actual raw edge occurs in the finite enumeration. -/
theorem mem_rawEdges (e : T.RawEdge) : e ∈ T.rawEdges := by
  rw [rawEdges,mem_firstOccurrences]
  apply List.mem_filterMap.mpr
  exact ⟨e.1,T.mem_rawEdgePairs e.1,by rw [dif_pos e.2]⟩

/-- The enumeration cannot duplicate an actual chart-pair edge. -/
theorem rawEdges_nodup : T.rawEdges.Nodup := firstOccurrences_nodup _

/-- The raw visible vertex test searches the same target column and its original reading preimages. -/
def VertexVisible (r : T.RawLabel) (i : T.Chart) : Prop :=
  ∃ t ∈ T.target i, ∃ s : T.Source, T.read s = t ∧ T.eval r.1 s = r.2

/-- A raw visible edge requires one target in both columns, rather than separate matching labels. -/
def EdgeVisible (r : T.RawLabel) (ij : T.Chart × T.Chart) : Prop :=
  ∃ t ∈ T.target ij.1 ∩ T.target ij.2, ∃ s : T.Source, T.read s = t ∧ T.eval r.1 s = r.2

instance decidableVertexVisible (r : T.RawLabel) (i : T.Chart) : Decidable (T.VertexVisible r i) :=
  inferInstanceAs (Decidable (∃ t ∈ T.target i, ∃ s : T.Source, T.read s = t ∧ T.eval r.1 s = r.2))
instance decidableEdgeVisible (r : T.RawLabel) (ij : T.Chart × T.Chart) : Decidable (T.EdgeVisible r ij) :=
  inferInstanceAs (Decidable (∃ t ∈ T.target ij.1 ∩ T.target ij.2, ∃ s : T.Source,
    T.read s = t ∧ T.eval r.1 s = r.2))

/-- Raw reading surjectivity is a finite source search for every target. -/
def SurjectiveReading : Prop := ∀ t : Fin T.targetCount, ∃ s : T.Source, T.read s = t

/-- Raw adequacy checks every reading fiber against every declared Law. -/
def AdequateReading : Prop :=
  ∀ (a b : T.Source), T.read a = T.read b → ∀ law, T.eval law a = T.eval law b

/-- Every Boolean primitive relation must preserve its actual Law/value code. -/
def LabelPreserving : Prop :=
  ∀ g h : T.Generator, T.relation g h = true → T.rawLabel g = T.rawLabel h

/-- Equal raw Law/value labels must be connected in the generated primitive graph. -/
def RelationReflecting : Prop :=
  ∀ g h : T.Generator, T.rawLabel g = T.rawLabel h → T.relationGraph.Reachable g h

/-- Enumerated open sets are closed under empty, whole space, union, and intersection. -/
def TopologyValid : Prop :=
  ∅ ∈ T.opens ∧ Finset.univ ∈ T.opens ∧
    (∀ U : T.opens, ∀ V : T.opens, U.1 ∪ V.1 ∈ T.opens) ∧
    (∀ U : T.opens, ∀ V : T.opens, U.1 ∩ V.1 ∈ T.opens)

/-- Finite open separation test for a geometric subset, including the empty set. -/
def Preconnected (S : Finset T.Point) : Prop :=
  ∀ U : T.opens, ∀ V : T.opens, S ⊆ U.1 ∪ V.1 →
    (S ∩ U.1).Nonempty → (S ∩ V.1).Nonempty → (S ∩ (U.1 ∩ V.1)).Nonempty

/-- The raw chart table satisfies exactly the finite geometric T0 requirements. -/
def GeometryValid : Prop :=
  0 < T.chartCount ∧
    (∀ i, T.chart i ∈ T.opens) ∧
    (∀ i, (T.chart i).Nonempty) ∧
    (∀ x : T.Point, ∃ i, x ∈ T.chart i) ∧
    (∀ i, T.Preconnected (T.chart i)) ∧
    (∀ i j, i < j → (T.chart i ∩ T.chart j).Nonempty →
      T.Preconnected (T.chart i ∩ T.chart j)) ∧
    (∀ i j k, i < j → j < k → T.chart i ∩ T.chart j ∩ T.chart k = ∅)

/-- Target supports are separately supplied nonempty finite sets. -/
def TargetValid : Prop := ∀ i, (T.target i).Nonempty

/-- All finite T0 checks, before the later B1 reflection test. -/
def Valid : Prop :=
  T.SurjectiveReading ∧ T.AdequateReading ∧ T.LabelPreserving ∧ T.RelationReflecting ∧
    T.TopologyValid ∧ T.GeometryValid ∧ T.TargetValid

instance decidableSurjectiveReading : Decidable T.SurjectiveReading :=
  inferInstanceAs (Decidable (∀ t : Fin T.targetCount, ∃ s : T.Source, T.read s = t))
instance decidableAdequateReading : Decidable T.AdequateReading :=
  inferInstanceAs (Decidable (∀ (a b : T.Source), T.read a = T.read b →
    ∀ law, T.eval law a = T.eval law b))
instance decidableLabelPreserving : Decidable T.LabelPreserving :=
  inferInstanceAs (Decidable (∀ g h : T.Generator, T.relation g h = true → T.rawLabel g = T.rawLabel h))
instance decidableRelationReflecting : Decidable T.RelationReflecting :=
  inferInstanceAs (Decidable (∀ g h : T.Generator, T.rawLabel g = T.rawLabel h →
    T.relationGraph.Reachable g h))
instance decidableTopologyValid : Decidable T.TopologyValid :=
  inferInstanceAs (Decidable (∅ ∈ T.opens ∧ Finset.univ ∈ T.opens ∧
    (∀ U : T.opens, ∀ V : T.opens, U.1 ∪ V.1 ∈ T.opens) ∧
    (∀ U : T.opens, ∀ V : T.opens, U.1 ∩ V.1 ∈ T.opens)))
instance decidablePreconnected (S : Finset T.Point) : Decidable (T.Preconnected S) :=
  inferInstanceAs (Decidable (∀ U : T.opens, ∀ V : T.opens, S ⊆ U.1 ∪ V.1 →
    (S ∩ U.1).Nonempty → (S ∩ V.1).Nonempty → (S ∩ (U.1 ∩ V.1)).Nonempty))
instance decidableGeometryValid : Decidable T.GeometryValid :=
  inferInstanceAs (Decidable (0 < T.chartCount ∧
    (∀ i, T.chart i ∈ T.opens) ∧ (∀ i, (T.chart i).Nonempty) ∧
    (∀ x : T.Point, ∃ i, x ∈ T.chart i) ∧ (∀ i, T.Preconnected (T.chart i)) ∧
    (∀ i j, i < j → (T.chart i ∩ T.chart j).Nonempty → T.Preconnected (T.chart i ∩ T.chart j)) ∧
    (∀ i j k, i < j → j < k → T.chart i ∩ T.chart j ∩ T.chart k = ∅)))
instance decidableTargetValid : Decidable T.TargetValid :=
  inferInstanceAs (Decidable (∀ i, (T.target i).Nonempty))
instance decidableValid : Decidable T.Valid :=
  inferInstanceAs (Decidable (T.SurjectiveReading ∧ T.AdequateReading ∧ T.LabelPreserving ∧
    T.RelationReflecting ∧ T.TopologyValid ∧ T.GeometryValid ∧ T.TargetValid))

/-- A terminating finite-table validity decision with no supplied T0 certificate. -/
def validate : Bool := decide T.Valid

/-- Validator success is equivalent to the complete finite T0 checks. -/
theorem validate_true_iff : T.validate = true ↔ T.Valid := by
  exact decide_eq_true_iff

/-- Validator failure denotes an invalid T0 table, rather than failure of zero reflection. -/
theorem validate_false_iff : T.validate = false ↔ ¬ T.Valid := by
  exact decide_eq_false_iff_not

/-- Checked output retains the original table and obtains all proofs from the finite decision. -/
def validated : Option {S : FiniteInputTable // S.Valid} :=
  if h : T.Valid then some ⟨T,h⟩ else none

/-- Invalid raw tables produce no checked input. -/
theorem validated_none_iff : T.validated = none ↔ ¬ T.Valid := by
  simp only [validated]
  split_ifs with h <;> simp [h]

/-- Every returned checked table is exactly the original raw input. -/
theorem validated_retains_input (S : {S : FiniteInputTable // S.Valid})
    (h : T.validated = some S) : S.1 = T := by
  unfold validated at h
  split_ifs at h with hv
  · exact congrArg Subtype.val (Option.some.inj h).symm

/-- Validity is equivalent to an actual output of the terminating checker. -/
theorem validated_some_iff : (∃ S, T.validated = some S) ↔ T.Valid := by
  constructor
  · rintro ⟨S,hS⟩
    exact T.validated_retains_input S hS ▸ S.2
  · intro h
    exact ⟨⟨T,h⟩,by rw [validated,dif_pos h]⟩

end FiniteInputTable
end AAT.AG.VisibleCycleReflection
#assert_standard_axioms_only AAT.AG.VisibleCycleReflection
