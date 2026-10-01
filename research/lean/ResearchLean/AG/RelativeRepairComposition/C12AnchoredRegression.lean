import ResearchLean.AG.RelativeRepairComposition.AnchoredFiniteCover
import ResearchLean.AG.AbelianLiftingObstruction.GroupExtension
import Mathlib.Data.ZMod.Basic

/-!
# Nonzero actual reference-change predicate inputs

The original single-object tower has the full F₂ translation kernel, two
separately named loops, and no faces or triples. One loop is physically fixed.
The alternative actual lift translates by one on both loops. Independent raw
equations accept -a and reject zero on the fixed loop; two individually valid
local raw equations can disagree on the other shared original loop.
-/
namespace AAT.AG.RelativeRepairComposition.C12AnchoredRegression
open CategoryTheory TransportCoherence TransportCoherence.Arbitrary AbelianLiftingObstruction

/-- One vertex, two original named loops, and empty higher-cell input. -/
def geometry : FiniteTransportPresentation where
  Vertex := Unit
  vertexFintype := inferInstance
  Edge := fun _ _ => Bool
  edgeFintype := fun _ _ => inferInstance
  TwoCell := Empty
  twoCellFintype := inferInstance
  twoSource := fun f => nomatch f
  twoTarget := fun f => nomatch f
  twoLeft := fun f => nomatch f
  twoRight := fun f => nomatch f
  ThreeCell := Empty
  threeCellFintype := inferInstance
  threeSource := fun f => nomatch f
  threeTarget := fun f => nomatch f
  threeStart := fun f => nomatch f
  threeFinish := fun f => nomatch f
  threeLeft := fun f => nomatch f
  threeRight := fun f => nomatch f

/-- Equality on original loop names is the concrete Bool equality. -/
instance edgeEquality {i j : geometry.Vertex} : DecidableEq (geometry.Edge i j) :=
  inferInstanceAs (DecidableEq Bool)

/-- Original group elements are the two translations of F₂. -/
abbrev E := Multiplicative (ZMod 2)
/-- The projection forgets translation while retaining the original arrows. -/
def projection : E →* PUnit.{1} := 1
/-- The full actual kernel is abelian since all original translations commute. -/
theorem kernel_comm (a b : projection.ker) : a * b = b * a := mul_comm a b
/-- The fixed original core is the unique lower arrow. -/
def core : ∀ {i j : geometry.Vertex}, geometry.Edge i j → PUnit.{1} := fun _ => 1
/-- The supplied actual lift has translation zero at every original edge. -/
def reference : ∀ {i j : geometry.Vertex}, geometry.Edge i j → E := fun _ => 1
/-- Both original lifts project to the same fixed core. -/
theorem projects {i j : geometry.Vertex} (e : geometry.Edge i j) :
    projection (reference e) = core e := rfl
/-- Empty original faces impose no extra relation assumptions. -/
theorem relations (f : geometry.TwoCell) :
    GroupExtension.pathValue geometry core (geometry.twoLeft f) =
      GroupExtension.pathValue geometry core (geometry.twoRight f) := Empty.elim f
/-- Strongness, transport and full kernel conditions are generated from actual inputs. -/
noncomputable abbrev tower :=
  GroupExtension.input geometry projection kernel_comm core reference projects relations
/-- A different actual lift translates by one on the unchanged original edges. -/
noncomputable def other : ∀ {i j : geometry.Vertex} (_ : geometry.Edge i j),
    FiberAut (GroupExtension.projection projection ⋙ GroupExtension.terminal PUnit.{1})
      (tower.original.object j) :=
  fun _ => GroupExtension.upperEquiv projection (Multiplicative.ofAdd 1)
/-- The alternative actual lift preserves the fixed original core. -/
theorem other_projects {i j : geometry.Vertex} (e : geometry.Edge i j) :
    fiberPushforward _ _ (tower.original.object j) (other e) = tower.core e := by
  change fiberPushforward (GroupExtension.projection projection) (GroupExtension.terminal PUnit.{1})
    (SingleObj.star E) (GroupExtension.upperEquiv projection (Multiplicative.ofAdd 1)) = _
  rw [GroupExtension.pushforward_eq]

/-- The closed physical fixed part contains exactly the first original loop. -/
def fixed : ClosedRegion geometry where
  vertices := Set.univ
  edges := {e | e.2.2 = false}
  faces := ∅
  triples := ∅
  edge_closed _ _ := ⟨trivial,trivial⟩
  face_closed f _ := Empty.elim f
  triple_closed t _ := Empty.elim t
/-- Each local region is the entire unchanged original geometry. -/
def region : ClosedRegion geometry := ClosedRegion.all
/-- The two regions share both original named loops. -/
def regions : Bool → ClosedRegion geometry := fun _ => region
/-- The physical fixed original edge. -/
def fixedEdge : region.edges := ⟨⟨(),(),false⟩,trivial⟩
/-- The other shared original edge remains free. -/
def freeEdge : region.edges := ⟨⟨(),(),true⟩,trivial⟩
/-- The actual lift difference on unchanged original edge names. -/
noncomputable abbrev shift := AnchoredLocal.shift tower other other_projects region

/-- The actual reference difference is nonzero on the physically fixed original edge. -/
theorem shift_fixed_nonzero : shift fixedEdge ≠ 0 := by
  intro hz
  have hh := congrArg (fun a => FiberAut.hom (kernelInclusion _ _ _ (Additive.toMul a))) hz
  change (Multiplicative.ofAdd (1 : ZMod 2)) * (1 : E)⁻¹ = 1 at hh
  simp only [inv_one,mul_one] at hh
  have he : (1 : ZMod 2) = 0 := congrArg Multiplicative.toAdd hh
  exact (by decide : (1 : ZMod 2) ≠ 0) he

/-- Raw values are -a on the fixed loop; the free original loop varies independently. -/
noncomputable def raw (vary : Bool) : ClosedRegion.C1 tower.toTower.localCoefficients region :=
  fun e => -shift e + if e.1.2.2 = false then 0 else if vary then shift e else 0

/-- Each raw input directly satisfies its fixed and actual face conditions. -/
theorem raw_valid (vary : Bool) :
    (∀ e : region.edges, e.1 ∈ fixedEdgesForRange fixed.edges ∅ ∅ → raw vary e = -shift e) ∧
    ClosedRegion.d1Hom tower.toTower.localCoefficients region (raw vary) =
      -AnchoredLocal.defect tower other other_projects region := by
  constructor
  · intro e he
    have hf : e.1.2.2 = false := by
      rcases he with hp | hc
      · exact hp
      · exact False.elim hc.1
    simp only [raw,hf,ite_true,add_zero]
  · funext f
    exact Empty.elim f.1

/-- A local raw object is constructed from the concrete actual tower. -/
noncomputable def rawLocal (vary : Bool) :
    AnchoredLocal.Objects tower other other_projects fixed region ∅ ∅ := ⟨raw vary,raw_valid vary⟩

/-- The raw -a fixed input is accepted with its nonzero physical anchor. -/
theorem raw_fixed_accept :
    ∃ h : AnchoredLocal.Objects tower other other_projects fixed region ∅ ∅,
      h.1 fixedEdge = -shift fixedEdge ∧ h.1 fixedEdge ≠ 0 := by
  refine ⟨rawLocal false,?_,?_⟩
  · exact (raw_valid false).1 fixedEdge (Or.inl rfl)
  · change raw false fixedEdge ≠ 0
    rw [(raw_valid false).1 fixedEdge (Or.inl rfl)]
    exact neg_ne_zero.mpr shift_fixed_nonzero

/-- Zero on that same physically fixed original edge is rejected. -/
theorem raw_fixed_reject :
    ¬ ∃ h : AnchoredLocal.Objects tower other other_projects fixed region ∅ ∅,
      h.1 fixedEdge = 0 := by
  rintro ⟨h,hz⟩
  have ha := AnchoredLocal.fixed_value tower other other_projects fixed region ∅ ∅ h
    fixedEdge (Or.inl rfl)
  rw [hz] at ha
  exact shift_fixed_nonzero (neg_eq_zero.mp ha.symm)

/-- Equal individually valid raw equations agree on every shared original edge. -/
theorem raw_shared_accept :
    ∃ h : AnchoredFinite.Objects tower other other_projects fixed regions ∅ ∅,
      ∀ i, h.1 i = rawLocal false := by
  refine ⟨⟨fun _ => rawLocal false,?_⟩,fun _ => rfl⟩
  intro i j e hi hj
  rfl

/-- Individually valid local raw equations with different free shared values are rejected. -/
theorem raw_shared_reject :
    ¬ (∀ i j e (hi : e ∈ (regions i).edges) (hj : e ∈ (regions j).edges),
      (rawLocal i).1 ⟨e,hi⟩ = (rawLocal j).1 ⟨e,hj⟩) := by
  intro h
  have he := h false true freeEdge.1 freeEdge.2 freeEdge.2
  change -shift freeEdge + 0 = -shift freeEdge + shift freeEdge at he
  have hz : shift freeEdge = 0 := add_left_cancel he.symm
  exact shift_fixed_nonzero hz

end AAT.AG.RelativeRepairComposition.C12AnchoredRegression
#assert_standard_axioms_only AAT.AG.RelativeRepairComposition.C12AnchoredRegression
