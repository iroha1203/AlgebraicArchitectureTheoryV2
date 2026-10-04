import ResearchLean.AG.VisibleCycleReflection.FiniteInputTable
import Formal.Util.AssertStandardAxioms

/-!
# Finite topology checks and the actual connected cover

## Implementation notes

The enumerated open family defines the actual topology. Finite binary union
closure gives arbitrary union closure because the point set, hence its power
set, is finite. The runtime separation check quantifies over every enumerated
open pair and is equivalent to actual IsPreconnected. Geometry is decoded
only after its finite checks succeed; no geometric proof fields occur in the
raw table.
-/

noncomputable section
open Set TopologicalSpace
namespace AAT.AG.VisibleCycleReflection.FiniteInputTable
variable (T : FiniteInputTable)

/-- Finite union closure proves actual arbitrary union closure of the enumerated opens. -/
theorem opens_sUnion (h : T.TopologyValid) (S : Set (Set T.Point))
    (hS : ∀ s ∈ S, ∃ U ∈ T.opens, (U : Set T.Point) = s) :
    ∃ U ∈ T.opens, (U : Set T.Point) = ⋃₀ S := by
  classical
  have hf : S.Finite := Set.toFinite S
  revert hS
  induction S,hf using Set.Finite.induction_on with
  | empty =>
    intro _
    exact ⟨∅,h.1,by simp⟩
  | @insert a S ha hf ih =>
    intro hS
    obtain ⟨U,hU,rfl⟩ := hS a (Set.mem_insert _ _)
    obtain ⟨V,hV,hVeq⟩ := ih (fun s hs => hS s (Set.mem_insert_of_mem _ hs))
    refine ⟨U ∪ V,h.2.2.1 ⟨U,hU⟩ ⟨V,hV⟩,?_⟩
    rw [Finset.coe_union,hVeq,Set.sUnion_insert]

/-- The actual topological space decoded from the entire finite open table. -/
def topology (h : T.TopologyValid) : TopologicalSpace T.Point where
  IsOpen s := ∃ U ∈ T.opens, (U : Set T.Point) = s
  isOpen_univ := ⟨Finset.univ,h.2.1,Finset.coe_univ⟩
  isOpen_inter := by
    rintro a b ⟨U,hU,rfl⟩ ⟨V,hV,rfl⟩
    exact ⟨U ∩ V,h.2.2.2 ⟨U,hU⟩ ⟨V,hV⟩,Finset.coe_inter U V⟩
  isOpen_sUnion := T.opens_sUnion h

/-- Public characterization of every actual decoded open. -/
theorem topology_isOpen_iff (h : T.TopologyValid) (s : Set T.Point) :
    @IsOpen T.Point (T.topology h) s ↔ ∃ U ∈ T.opens, (U : Set T.Point) = s := Iff.rfl

/-- Enumerated finite sets are open exactly when they occur in the raw open table. -/
theorem topology_finset_isOpen_iff (h : T.TopologyValid) (U : Finset T.Point) :
    @IsOpen T.Point (T.topology h) (U : Set T.Point) ↔ U ∈ T.opens := by
  rw [T.topology_isOpen_iff]
  constructor
  · rintro ⟨V,hV,he⟩
    exact Finset.coe_injective he ▸ hV
  · intro hU
    exact ⟨U,hU,rfl⟩

/-- Topology validation is equivalent to a real topology with exactly the enumerated finite opens. -/
theorem topologyValid_iff_exists : T.TopologyValid ↔
    ∃ t : TopologicalSpace T.Point, ∀ U : Finset T.Point,
      @IsOpen T.Point t (U : Set T.Point) ↔ U ∈ T.opens := by
  constructor
  · intro h
    exact ⟨T.topology h,T.topology_finset_isOpen_iff h⟩
  · rintro ⟨t,ho⟩
    letI : TopologicalSpace T.Point := t
    refine ⟨(ho ∅).mp (by simp),
      (ho Finset.univ).mp (by simp),?_,?_⟩
    · intro U V
      apply (ho (U.1 ∪ V.1)).mp
      simpa only [Finset.coe_union] using ((ho U.1).mpr U.2).union ((ho V.1).mpr V.2)
    · intro U V
      apply (ho (U.1 ∩ V.1)).mp
      simpa only [Finset.coe_inter] using ((ho U.1).mpr U.2).inter ((ho V.1).mpr V.2)

/-- The finite open-pair test is equivalent to actual preconnectedness, in both directions. -/
theorem preconnected_iff (h : T.TopologyValid) (S : Finset T.Point) :
    T.Preconnected S ↔ @IsPreconnected T.Point (T.topology h) (S : Set T.Point) := by
  constructor
  · intro hc U V hU hV hsub hSU hSV
    obtain ⟨A,hA,rfl⟩ := (T.topology_isOpen_iff h U).mp hU
    obtain ⟨B,hB,rfl⟩ := (T.topology_isOpen_iff h V).mp hV
    have hs : S ⊆ A ∪ B := by simpa only [← Finset.coe_subset,Finset.coe_union] using hsub
    have hsa : (S ∩ A).Nonempty := by simpa only [← Finset.coe_nonempty,Finset.coe_inter] using hSU
    have hsb : (S ∩ B).Nonempty := by simpa only [← Finset.coe_nonempty,Finset.coe_inter] using hSV
    simpa only [← Finset.coe_nonempty,Finset.coe_inter] using hc ⟨A,hA⟩ ⟨B,hB⟩ hs hsa hsb
  · intro hc A B hs hsa hsb
    have hA := (T.topology_finset_isOpen_iff h A.1).mpr A.2
    have hB := (T.topology_finset_isOpen_iff h B.1).mpr B.2
    have hsub : (S : Set T.Point) ⊆ (A.1 : Set T.Point) ∪ (B.1 : Set T.Point) := by
      simpa only [← Finset.coe_subset,Finset.coe_union] using hs
    have hSU : ((S : Set T.Point) ∩ (A.1 : Set T.Point)).Nonempty := by
      simpa only [← Finset.coe_nonempty,Finset.coe_inter] using hsa
    have hSV : ((S : Set T.Point) ∩ (B.1 : Set T.Point)).Nonempty := by
      simpa only [← Finset.coe_nonempty,Finset.coe_inter] using hsb
    simpa only [← Finset.coe_nonempty,Finset.coe_inter] using hc _ _ hA hB hsub hSU hSV

/-- Each decoded chart is the same finite subset, with its checked actual openness. -/
def patch (h : T.TopologyValid) (hg : T.GeometryValid) (i : T.Chart) :
    @Opens T.Point (T.topology h) := by
  letI : TopologicalSpace T.Point := T.topology h
  exact ⟨(T.chart i : Set T.Point),(T.topology_finset_isOpen_iff h (T.chart i)).mpr (hg.2.1 i)⟩

/-- Public membership in decoded geometric chart support. -/
@[simp] theorem mem_patch (h : T.TopologyValid) (hg : T.GeometryValid) (i : T.Chart) (x : T.Point) :
    letI : TopologicalSpace T.Point := T.topology h
    x ∈ T.patch h hg i ↔ x ∈ T.chart i := Iff.rfl

/-- Decoded chart support is exactly the raw finite point subset. -/
theorem patch_coe (h : T.TopologyValid) (hg : T.GeometryValid) (i : T.Chart) :
    letI : TopologicalSpace T.Point := T.topology h
    (T.patch h hg i : Set T.Point) = (T.chart i : Set T.Point) := rfl

/-- All checked raw geometric T0 conditions generate the complete actual cover. -/
def geometricCover (h : T.TopologyValid) (hg : T.GeometryValid) :
    @GeometricCover T.Point T.Chart (T.topology h) inferInstance := by
  letI : TopologicalSpace T.Point := T.topology h
  exact {
    patch := T.patch h hg
    covers := hg.2.2.2.1
    chartNonempty i := Finset.coe_nonempty.mpr (hg.2.2.1 i)
    chartPreconnected i := (T.preconnected_iff h (T.chart i)).mp (hg.2.2.2.2.1 i)
    overlapPreconnected := by
      intro i j hij hne
      have hn : (T.chart i ∩ T.chart j).Nonempty := by
        apply Finset.coe_nonempty.mp
        simpa only [Opens.coe_inf,T.patch_coe,Finset.coe_inter] using hne
      have hc := (T.preconnected_iff h (T.chart i ∩ T.chart j)).mp
        (hg.2.2.2.2.2.1 i j hij hn)
      simpa only [Opens.coe_inf,T.patch_coe,Finset.coe_inter] using hc
    tripleEmpty := by
      intro i j k hij hjk hn
      have he := hg.2.2.2.2.2.2 i j k hij hjk
      have hset : (((T.patch h hg i ⊓ T.patch h hg j ⊓ T.patch h hg k) : Opens T.Point) : Set T.Point) = ∅ := by
        change ((T.chart i : Set T.Point) ∩ (T.chart j : Set T.Point) ∩ (T.chart k : Set T.Point)) = ∅
        rw [← Finset.coe_inter,← Finset.coe_inter,he,Finset.coe_empty]
      rw [hset] at hn
      exact Set.not_nonempty_empty hn
  }

/-- The complete actual cover retains every supplied raw chart. -/
theorem geometricCover_patch (h : T.TopologyValid) (hg : T.GeometryValid) (i : T.Chart) :
    letI : TopologicalSpace T.Point := T.topology h
    (T.geometricCover h hg).patch i = T.patch h hg i := rfl

/-- Actual ordered nerve edges are exactly all nonempty raw chart intersections. -/
theorem geometricCover_edge_iff (h : T.TopologyValid) (hg : T.GeometryValid) (i j : T.Chart) :
    letI : TopologicalSpace T.Point := T.topology h
    i < j ∧ (((T.geometricCover h hg).patch i ⊓ (T.geometricCover h hg).patch j) : Set T.Point).Nonempty ↔
      i < j ∧ (T.chart i ∩ T.chart j).Nonempty := by
  letI : TopologicalSpace T.Point := T.topology h
  change i < j ∧ ((T.chart i : Set T.Point) ∩ (T.chart j : Set T.Point)).Nonempty ↔ _
  rw [← Finset.coe_inter,Finset.coe_nonempty]

/-- Geometric validation is equivalent to a genuine nonempty T0 cover with exactly the raw charts. -/
theorem geometryValid_iff_exists (h : T.TopologyValid) :
    T.GeometryValid ↔
      letI : TopologicalSpace T.Point := T.topology h
      ∃ K : GeometricCover T.Point T.Chart, Nonempty T.Chart ∧
        ∀ i, (K.patch i : Set T.Point) = (T.chart i : Set T.Point) := by
  letI : TopologicalSpace T.Point := T.topology h
  constructor
  · intro hg
    exact ⟨T.geometricCover h hg,⟨⟨0,hg.1⟩⟩,T.patch_coe h hg⟩
  · rintro ⟨K,hI,hp⟩
    obtain ⟨i⟩ := hI
    refine ⟨lt_of_le_of_lt (Nat.zero_le i.1) i.2,?_,?_,?_,?_,?_,?_⟩
    · intro j
      apply (T.topology_finset_isOpen_iff h (T.chart j)).mp
      rw [← hp j]
      exact (K.patch j).isOpen
    · intro j
      apply Finset.coe_nonempty.mp
      rw [← hp j]
      exact K.chartNonempty j
    · intro x
      obtain ⟨j,hj⟩ := K.covers x
      refine ⟨j,?_⟩
      change x ∈ (T.chart j : Set T.Point)
      rw [← hp j]
      exact hj
    · intro j
      apply (T.preconnected_iff h (T.chart j)).mpr
      rw [← hp j]
      exact K.chartPreconnected j
    · intro j k hjk hn
      apply (T.preconnected_iff h (T.chart j ∩ T.chart k)).mpr
      have hnk : ((K.patch j ⊓ K.patch k : Opens T.Point) : Set T.Point).Nonempty := by
        simpa only [Opens.coe_inf,hp j,hp k,← Finset.coe_inter] using Finset.coe_nonempty.mpr hn
      simpa only [Opens.coe_inf,hp j,hp k,Finset.coe_inter] using K.overlapPreconnected j k hjk hnk
    · intro j k l hjk hkl
      by_contra hn
      have hraw := Finset.coe_nonempty.mpr (Finset.nonempty_iff_ne_empty.mpr hn)
      apply K.tripleEmpty j k l hjk hkl
      simpa only [Opens.coe_inf,hp j,hp k,hp l,← Finset.coe_inter] using hraw

end AAT.AG.VisibleCycleReflection.FiniteInputTable
#assert_standard_axioms_only AAT.AG.VisibleCycleReflection
