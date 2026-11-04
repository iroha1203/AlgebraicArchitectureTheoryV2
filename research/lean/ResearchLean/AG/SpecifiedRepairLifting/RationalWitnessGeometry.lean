import ResearchLean.AG.SpecifiedRepairLifting.ActualCechLifting
import Mathlib.Topology.Order.UpperLowerSetTopology

/-! # 固定W1の三点incidence空間

Implementation notes: 二頂点と一辺の上集合位相を原始有限順序から生成する。
chartを抽象indexだけで与える代わりに、実開集合と交差・被覆・連結性を証明する。
-/
namespace AAT.AG.SpecifiedRepairLifting.RationalWitnessGeometry
open TopologicalSpace Set
/-- 固定W1の三つの幾何点。 -/
inductive Point where
  | v0 | v1 | edge
  deriving DecidableEq, Fintype
/-- 辺点が二頂点の上にあるincidence順序。 -/
def pointLE (x y : Point) : Prop := x = y ∨ y = .edge
instance pointLEDecidable : DecidableRel pointLE := fun _ _ => inferInstanceAs (Decidable (_ ∨ _))
instance pointPartialOrder : PartialOrder Point where
  le := pointLE
  le_refl := by decide
  le_trans := by decide
  le_antisymm := by decide
instance pointDecidableLE : DecidableLE Point := pointLEDecidable
/-- 同じ三点の上集合位相。 -/
abbrev Space := Topology.WithUpperSet Point
/-- 順序点を実位相空間へ入れる。 -/
def point (x : Point) : Space := Topology.WithUpperSet.toUpperSet x
/-- 原始点の最小開近傍。 -/
def neighborhood (x : Point) : Opens Space where
  carrier := Ici (point x)
  is_open' := by
    rw [Topology.IsUpperSet.isOpen_iff_isUpperSet]
    intro a b hab hxa
    exact le_trans hxa hab
/-- 開近傍の点membershipは原始incidenceに一致。 -/
theorem mem_neighborhood (x y : Point) : point y ∈ neighborhood x ↔ pointLE x y := Iff.rfl
/-- 原始近傍は自身の基点を含む。 -/
def neighborhoodNonempty (x : Point) : Nonempty (neighborhood x) := ⟨⟨point x,show point x ≤ point x from le_rfl⟩⟩
/-- 最小開近傍は上集合位相で前連結。 -/
theorem neighborhood_preconnected (v : Point) : IsPreconnected (neighborhood v : Set Space) := by
  intro left right hleft hright hcover
  rintro ⟨x,hx,hxl⟩ ⟨y,hy,hyr⟩
  have hv : point v ∈ (neighborhood v : Set Space) := show point v ≤ point v from le_rfl
  rcases hcover hv with hl | hr
  · exact ⟨y,hy,(Topology.IsUpperSet.isOpen_iff_isUpperSet.mp hleft) hy hl,hyr⟩
  · exact ⟨x,hx,hxl,(Topology.IsUpperSet.isOpen_iff_isUpperSet.mp hright) hx hr⟩
/-- 係数層で使用する前連結性の証拠。 -/
def neighborhoodPreconnected (x : Point) : PreconnectedSpace (neighborhood x) :=
  Subtype.preconnectedSpace (neighborhood_preconnected x)
/-- 二つのchartの頂点。 -/
def chartVertex : Bool → Point | false => .v0 | true => .v1
/-- W1のU0とU1は各頂点の最小開近傍。 -/
def patch (i : Bool) : Opens Space := neighborhood (chartVertex i)
/-- U0の点はv0とe。 -/
theorem mem_patch_false (x : Point) : point x ∈ patch false ↔ x = .v0 ∨ x = .edge := by
  change pointLE .v0 x ↔ _
  cases x <;> decide
/-- U1の点はv1とe。 -/
theorem mem_patch_true (x : Point) : point x ∈ patch true ↔ x = .v1 ∨ x = .edge := by
  change pointLE .v1 x ↔ _
  cases x <;> decide
/-- 辺の開近傍は一つの点だけ。 -/
theorem mem_edge_neighborhood (x : Point) : point x ∈ neighborhood .edge ↔ x = .edge := by
  rw [mem_neighborhood]
  cases x <;> decide
/-- 二つのchartの交差は辺点の最小近傍。 -/
theorem patch_intersection : patch false ⊓ patch true = neighborhood .edge := by
  ext x
  change (point x ∈ patch false ∧ point x ∈ patch true) ↔ point x ∈ neighborhood .edge
  rw [mem_patch_false,mem_patch_true,mem_edge_neighborhood]
  cases x <;> simp
/-- 二つのchartは同じ三点空間を被覆する。 -/
theorem patches_cover (x : Space) : ∃ i : Bool, x ∈ patch i := by
  cases x with
  | v0 => exact ⟨false,(mem_patch_false _).mpr (Or.inl rfl)⟩
  | v1 => exact ⟨true,(mem_patch_true _).mpr (Or.inl rfl)⟩
  | edge => exact ⟨false,(mem_patch_false _).mpr (Or.inr rfl)⟩
/-- 実patchの非空性。 -/
def patchNonempty (i : Bool) : Nonempty (patch i) := neighborhoodNonempty _
/-- 実patchの前連結性。 -/
def patchPreconnected (i : Bool) : PreconnectedSpace (patch i) := neighborhoodPreconnected _
/-- 二chartには相異なる三chartの組が存在しない。 -/
theorem no_three_distinct_charts : ¬ ∃ f : Fin 3 → Bool, Function.Injective f := by decide
end AAT.AG.SpecifiedRepairLifting.RationalWitnessGeometry

#print axioms AAT.AG.SpecifiedRepairLifting.RationalWitnessGeometry.Point
#print axioms AAT.AG.SpecifiedRepairLifting.RationalWitnessGeometry.pointLE
#print axioms AAT.AG.SpecifiedRepairLifting.RationalWitnessGeometry.pointLEDecidable
#print axioms AAT.AG.SpecifiedRepairLifting.RationalWitnessGeometry.pointPartialOrder
#print axioms AAT.AG.SpecifiedRepairLifting.RationalWitnessGeometry.pointDecidableLE
#print axioms AAT.AG.SpecifiedRepairLifting.RationalWitnessGeometry.Space
#print axioms AAT.AG.SpecifiedRepairLifting.RationalWitnessGeometry.point
#print axioms AAT.AG.SpecifiedRepairLifting.RationalWitnessGeometry.neighborhood
#print axioms AAT.AG.SpecifiedRepairLifting.RationalWitnessGeometry.mem_neighborhood
#print axioms AAT.AG.SpecifiedRepairLifting.RationalWitnessGeometry.neighborhoodNonempty
#print axioms AAT.AG.SpecifiedRepairLifting.RationalWitnessGeometry.neighborhood_preconnected
#print axioms AAT.AG.SpecifiedRepairLifting.RationalWitnessGeometry.neighborhoodPreconnected
#print axioms AAT.AG.SpecifiedRepairLifting.RationalWitnessGeometry.chartVertex
#print axioms AAT.AG.SpecifiedRepairLifting.RationalWitnessGeometry.patch
#print axioms AAT.AG.SpecifiedRepairLifting.RationalWitnessGeometry.mem_patch_false
#print axioms AAT.AG.SpecifiedRepairLifting.RationalWitnessGeometry.mem_patch_true
#print axioms AAT.AG.SpecifiedRepairLifting.RationalWitnessGeometry.mem_edge_neighborhood
#print axioms AAT.AG.SpecifiedRepairLifting.RationalWitnessGeometry.patch_intersection
#print axioms AAT.AG.SpecifiedRepairLifting.RationalWitnessGeometry.patches_cover
#print axioms AAT.AG.SpecifiedRepairLifting.RationalWitnessGeometry.patchNonempty
#print axioms AAT.AG.SpecifiedRepairLifting.RationalWitnessGeometry.patchPreconnected
#print axioms AAT.AG.SpecifiedRepairLifting.RationalWitnessGeometry.no_three_distinct_charts
#assert_standard_axioms_only AAT.AG.SpecifiedRepairLifting.RationalWitnessGeometry
