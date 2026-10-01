import ResearchLean.AG.RelativeRepairComposition.OriginalFiniteDual

/-! # Finite supported correction search on all original edge coordinates -/
namespace AAT.AG.RelativeRepairComposition
open TransportCoherence AbelianLiftingObstruction FiniteCoefficients
universe uk uG uA
namespace OriginalFiniteCorrection
set_option autoImplicit false
variable {k : Type uk} [Field k] [Fintype k] [DecidableEq k]
variable {K : FiniteTransportPresentation.{uG}} (M : LocalCoefficients.{uG,uA} K)
variable [∀ v, Module k (M.A v)]
variable (B : FiniteFamily.Bases (k := k) M.A) (P : ClosedRegion K)
variable [DecidablePred (· ∈ P.edges)] [DecidablePred (· ∈ P.faces)]
variable (candidates : Set (EdgeName (K := K))) [DecidablePred (· ∈ candidates)]
variable (houtside : ∀ e ∈ candidates, e ∉ P.edges)
variable (hlinear : ∀ {i j : K.Vertex} (e : K.Edge i j) (t : k) (x : M.A i),
  M.edge e (t • x) = t • M.edge e x)
variable [Fintype (EdgeName (K := K))] [DecidableEq (EdgeName (K := K))]
variable [Fintype K.TwoCell] [DecidableEq K.TwoCell]
/-- Decide membership in the full original edge region by its universal predicate. -/
local instance allEdgesDecidable : DecidablePred (· ∈ (ClosedRegion.all (K := K)).edges) :=
  fun _ => isTrue trivial
/-- Decide membership in the full original vertex region by its universal predicate. -/
local instance allVerticesDecidable : DecidablePred (· ∈ (ClosedRegion.all (K := K)).vertices) :=
  fun _ => isTrue trivial
/-- Decide membership in the full original face region by its universal predicate. -/
local instance allFacesDecidable : DecidablePred (· ∈ (ClosedRegion.all (K := K)).faces) :=
  fun _ => isTrue trivial
local notation "D0" => OriginalColumns.D (k := k) M P candidates hlinear
local notation "Ecol" => OriginalColumns.column (k := k) M P candidates houtside hlinear
local notation "coord1" => FiniteNative.coordinate1 M B ClosedRegion.all P
local notation "coord2" => FiniteNative.coordinate2 M B ClosedRegion.all P

variable (delta : RelativeCover.C2 M ClosedRegion.all P)
variable (S : Set candidates) [DecidablePred (· ∈ S)]
variable (enumK : FiniteElimination.Enumeration k)
variable (enumEdges : FiniteElimination.Enumeration (EdgeName (K := K)))

/-- Independent tests retain the same original equation and every forbidden whole kernel value. -/
def Valid (x : FiniteNative.Index1 M B ClosedRegion.all P → k) : Prop :=
  coord2 (differential1 M hlinear ClosedRegion.all P ((coord1).symm x)) = coord2 (-delta) ∧
    ∀ e : candidates, e ∉ S →
      B.coordinate e.1.2.1 (((coord1).symm x).1 ⟨e.1,Set.mem_univ e.1⟩) = 0

/-- Tests use finite full coordinate equality, rather than a chosen solution certificate. -/
instance validDecidable (x : FiniteNative.Index1 M B ClosedRegion.all P → k) :
    Decidable (Valid M B P candidates hlinear delta S x) :=
  inferInstanceAs (Decidable (_ ∧ _))

/-- The original whole-edge coordinate list is generated independently of rhs and allowed range. -/
def coordinates : FiniteElimination.Enumeration (FiniteNative.Index1 M B ClosedRegion.all P → k) :=
  (FiniteNative.enum1 M B ClosedRegion.all P enumEdges).pi (fun _ => enumK)

/-- Finite search returns an actual original full correction coordinate vector. -/
def find : Option (FiniteNative.Index1 M B ClosedRegion.all P → k) :=
  (coordinates M B P enumK enumEdges).values.find?
    (fun x => decide (Valid M B P candidates hlinear delta S x))

omit [Fintype k] [DecidableEq k] [DecidablePred (· ∈ candidates)]
  [Fintype (EdgeName (K := K))] [DecidableEq (EdgeName (K := K))]
  [Fintype K.TwoCell] [DecidableEq K.TwoCell] [DecidablePred (· ∈ S)] in
/-- Every independently valid supported equation passes the full finite coordinate test. -/
theorem valid_of_object (h : SupportedEquation.Objects M P ClosedRegion.all candidates
    (OriginalRanges.allowed candidates S) delta) :
    Valid M B P candidates hlinear delta S (coord1 h.1.1) := by
  constructor
  · rw [LinearEquiv.symm_apply_apply,differential1_eq]
    have hh := h.1.2
    have hface := hh.trans (congrArg Neg.neg (CoverEquation.defect_all M P delta))
    exact congrArg coord2 hface
  · intro e he
    rw [LinearEquiv.symm_apply_apply]
    have hz := h.2 ⟨e.1,Set.mem_univ e.1⟩
      ⟨e.2,fun ha => he ((OriginalRanges.allowed_iff candidates S e).mp ha)⟩
    rw [hz,map_zero]

/-- Restore a checked finite vector to the independently defined original supported equation. -/
def restore (x : FiniteNative.Index1 M B ClosedRegion.all P → k)
    (hx : Valid M B P candidates hlinear delta S x) :
    SupportedEquation.Objects M P ClosedRegion.all candidates
      (OriginalRanges.allowed candidates S) delta :=
  ⟨⟨(coord1).symm x,by
    rw [CoverEquation.defect_all]
    rw [← differential1_eq M hlinear ClosedRegion.all P]
    exact (coord2).injective hx.1⟩,by
    intro e he
    have hs : (⟨e.1,he.1⟩ : candidates) ∉ S :=
      fun hs => he.2 ((OriginalRanges.allowed_iff candidates S ⟨e.1,he.1⟩).mpr hs)
    have hz := hx.2 ⟨e.1,he.1⟩ hs
    exact (B.coordinate e.1.2.1).injective (hz.trans (map_zero _).symm)⟩

omit [Fintype k] [DecidableEq K.TwoCell] in
/-- Every successful original range makes the finite search succeed. -/
theorem find_isSome
    (h : Nonempty (SupportedEquation.Objects M P ClosedRegion.all candidates
      (OriginalRanges.allowed candidates S) delta)) :
    (find M B P candidates hlinear delta S enumK enumEdges).isSome = true := by
  rw [find,List.find?_isSome]
  obtain ⟨h⟩ := h
  exact ⟨coord1 h.1.1,(coordinates M B P enumK enumEdges).complete _,
    decide_eq_true (valid_of_object M B P candidates hlinear delta S h)⟩

/-- A successful raw finite find result itself supplies every restoration premise. -/
def restoreFound (x : FiniteNative.Index1 M B ClosedRegion.all P → k)
    (hx : find M B P candidates hlinear delta S enumK enumEdges = some x) :
    SupportedEquation.Objects M P ClosedRegion.all candidates
      (OriginalRanges.allowed candidates S) delta := by
  have ht := List.find?_some hx
  exact restore M B P candidates hlinear delta S x (of_decide_eq_true ht)

omit [Fintype k] [DecidableEq K.TwoCell] in
/-- The finite success decision is equivalent to the independent original supported equation. -/
theorem find_isSome_iff :
    (find M B P candidates hlinear delta S enumK enumEdges).isSome = true ↔
      Nonempty (SupportedEquation.Objects M P ClosedRegion.all candidates
        (OriginalRanges.allowed candidates S) delta) := by
  constructor
  · intro hf
    exact ⟨restoreFound M B P candidates hlinear delta S enumK enumEdges
      ((find M B P candidates hlinear delta S enumK enumEdges).get hf)
      (Option.some_get hf).symm⟩
  · exact find_isSome M B P candidates hlinear delta S enumK enumEdges

/-- The returned full original correction is the actual finite find output. -/
def computedObject
    (h : Nonempty (SupportedEquation.Objects M P ClosedRegion.all candidates
      (OriginalRanges.allowed candidates S) delta)) :
    SupportedEquation.Objects M P ClosedRegion.all candidates
      (OriginalRanges.allowed candidates S) delta := by
  have hf := find_isSome M B P candidates hlinear delta S enumK enumEdges h
  let x := (find M B P candidates hlinear delta S enumK enumEdges).get hf
  have ht := List.find?_some (Option.some_get hf).symm
  exact restore M B P candidates hlinear delta S x (of_decide_eq_true ht)

omit [Fintype k] [DecidableEq k] [DecidablePred (· ∈ candidates)]
  [Fintype (EdgeName (K := K))] [DecidableEq (EdgeName (K := K))]
  [Fintype K.TwoCell] [DecidableEq K.TwoCell] [DecidablePred (· ∈ S)] in
/-- Restoration keeps each original full kernel value of the computed coordinates. -/
theorem restore_value (x : FiniteNative.Index1 M B ClosedRegion.all P → k)
    (hx : Valid M B P candidates hlinear delta S x) (e : EdgeName (K := K)) :
    (restore M B P candidates hlinear delta S x hx).1.1.1 ⟨e,Set.mem_univ e⟩ =
      ((coord1).symm x).1 ⟨e,Set.mem_univ e⟩ := rfl

end OriginalFiniteCorrection
end AAT.AG.RelativeRepairComposition
#assert_standard_axioms_only AAT.AG.RelativeRepairComposition
