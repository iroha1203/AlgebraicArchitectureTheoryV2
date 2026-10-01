import Formal.Util.AssertStandardAxioms
import Mathlib.Data.ZMod.Basic
import ResearchLean.AG.RelativeRepairComposition.StrictCoverZeroCases

/-!
# Concrete forbidden and nonmatching original values

## Implementation notes

Two original vertices and four named directed edges carry the full one-dimensional
F₂ coefficient space. There are no face or three-cell constraints. Two copies of
the complete closed region share every original cell. The examples supply the
nonzero corrections and labels themselves before applying the exclusion APIs.
They are predicate witnesses, separate from the specified affine W1–W5 examples.
-/
namespace AAT.AG.RelativeRepairComposition
open TransportCoherence AbelianLiftingObstruction
namespace StrictCoverNegativeCases
/-- A finite original geometry with nontrivial vertex and edge families. -/
def geometry : FiniteTransportPresentation where
  Vertex := Bool
  vertexFintype := inferInstance
  Edge _ _ := Unit
  edgeFintype _ _ := inferInstance
  TwoCell := Empty
  twoCellFintype := inferInstance
  twoSource := Empty.elim
  twoTarget := Empty.elim
  twoLeft := fun cell => cell.elim
  twoRight := fun cell => cell.elim
  ThreeCell := Empty
  threeCellFintype := inferInstance
  threeSource := Empty.elim
  threeTarget := Empty.elim
  threeStart := fun cell => cell.elim
  threeFinish := fun cell => cell.elim
  threeLeft := fun cell => cell.elim
  threeRight := fun cell => cell.elim
/-- The full nonzero finite vector space with identity transport on every edge. -/
def coefficients : LocalCoefficients geometry where
  A _ := Fin 1 → ZMod 2
  commGroup _ := inferInstance
  edge _ := AddEquiv.refl _
  face_transport := fun f => f.elim
/-- The canonical F₂ module on the full original coefficient space at each vertex. -/
instance coefficientModule (v : geometry.Vertex) : Module (ZMod 2) (coefficients.A v) :=
  inferInstanceAs (Module (ZMod 2) (Fin 1 → ZMod 2))
/-- Full original one-dimensional bases. -/
def bases : FiniteFamily.Bases (k := ZMod 2) coefficients.A where
  dimension _ := 1
  coordinate _ := LinearEquiv.refl _ _
/-- The same closed region at each of the two cover indices. -/
def regions (_ : Bool) : ClosedRegion geometry := ClosedRegion.all
/-- A specified original edge joining the two distinct vertices. -/
def edge : EdgeName (K := geometry) := ⟨false,true,()⟩
/-- Equality of the two original Boolean vertices is decidable. -/
instance vertexDecidable : DecidableEq geometry.Vertex := inferInstanceAs (DecidableEq Bool)
/-- Equality retains both original endpoints and the named Unit edge. -/
instance edgeDecidable : DecidableEq (EdgeName (K := geometry)) := inferInstanceAs
  (DecidableEq (Sigma fun _ : Bool => Sigma fun _ : Bool => Unit))
/-- The empty fixed region contains no original edges. -/
instance pEdgesDecidable : DecidablePred (· ∈ (ClosedRegion.empty (K := geometry)).edges) := fun _ => isFalse id
/-- The empty fixed region contains no original faces. -/
instance pFacesDecidable : DecidablePred (· ∈ (ClosedRegion.empty (K := geometry)).faces) := fun _ => isFalse id
/-- Each complete local region contains every original vertex. -/
instance regionVerticesDecidable : ∀ i, DecidablePred (· ∈ (regions i).vertices) := fun _ _ => isTrue trivial
/-- Each complete local region contains every original edge. -/
instance regionEdgesDecidable : ∀ i, DecidablePred (· ∈ (regions i).edges) := fun _ _ => isTrue trivial
/-- Each complete local region contains every original face. -/
instance regionFacesDecidable : ∀ i, DecidablePred (· ∈ (regions i).faces) := fun _ _ => isTrue trivial
/-- Equality on the empty original face type is decidable. -/
instance faceDecidable : DecidableEq geometry.TwoCell := inferInstanceAs (DecidableEq Empty)
/-- The original transport is linear on the complete coefficient space. -/
theorem linear {i j : geometry.Vertex} (e : geometry.Edge i j) (t : ZMod 2) (x : coefficients.A i) :
    coefficients.edge e (t • x) = t • coefficients.edge e x := rfl
/-- Complete field enumeration for the same generated local relation. -/
def fieldEnum : FiniteElimination.Enumeration (ZMod 2) :=
  ⟨[0,1],by intro i; fin_cases i <;> simp⟩
/-- Complete enumeration of all original named edges. -/
def edgeEnum : FiniteElimination.Enumeration (EdgeName (K := geometry)) :=
  ⟨[⟨false,false,()⟩,⟨false,true,()⟩,⟨true,false,()⟩,⟨true,true,()⟩],by
    rintro ⟨i,j,⟨⟩⟩
    cases i <;> cases j <;> simp⟩
/-- The original face enumeration is empty. -/
def faceEnum : FiniteElimination.Enumeration geometry.TwoCell := ⟨[],fun f => f.elim⟩
/-- A constant original edge correction is a full local solution. -/
def solution (t : ZMod 2) (i : Bool) :
    CoverEquation.Solution coefficients ClosedRegion.empty 0 (regions i) :=
  ⟨⟨fun _ _ => t,by intro e he; exact he.elim⟩,by
    apply Subtype.ext
    funext f
    exact f.1.elim⟩
/-- A vertex label with nonzero original coboundary on false→true. -/
def label : RelativeCover.C0 coefficients (regions false) ClosedRegion.empty :=
  ⟨fun v _ => if v.1 = true then 1 else 0,by intro v hv; exact hv.elim⟩
/-- The supplied label has the nonzero full coefficient value one on the named edge. -/
theorem label_d0 : (RelativeCover.d0 coefficients (regions false) ClosedRegion.empty label).1
    ⟨edge,trivial⟩ = (fun _ => (1 : ZMod 2)) := by
  rw [RelativeCover.d0_edge_value]
  funext j
  change (1 : ZMod 2) - 0 = 1
  exact sub_zero _
/-- The nonzero original correction actually violates a forbidden candidate condition. -/
theorem forbidden_correction :
    ¬ (∀ e : (regions false).edges, e.1 ∈ (Set.univ : Set (EdgeName (K := geometry))) \ ∅ →
      (solution 1 false).1.1 e = 0) := by
  apply SupportedEquation.not_supported_of_ne coefficients ClosedRegion.empty (regions false)
    Set.univ ∅ 0 (solution 1 false) ⟨edge,trivial⟩ ⟨trivial,by intro h; exact h⟩
  intro h
  have hh := congrFun h (0 : Fin 1)
  exact one_ne_zero hh
/-- The concrete endpoint label violates the forbidden-candidate gauge condition. -/
theorem forbidden_label :
    label ∉ SupportedEquation.Labels coefficients ClosedRegion.empty (regions false) Set.univ ∅ := by
  apply SupportedEquation.not_mem_labels_of_ne coefficients ClosedRegion.empty (regions false)
    Set.univ ∅ label ⟨edge,trivial⟩ ⟨trivial,by intro h; exact h⟩
  rw [label_d0]
  intro h
  exact one_ne_zero (congrFun h (0 : Fin 1))
/-- Individually supported solutions with distinct original values on their shared edge. -/
def localObjects (i : Bool) : SupportedEquation.Objects coefficients ClosedRegion.empty (regions i) ∅ ∅ 0 :=
  ⟨solution (if i then 1 else 0) i,by intro e he; exact he.1.elim⟩
/-- The explicit two solutions cannot satisfy strict shared-edge gluing. -/
theorem shared_edge :
    ¬ (∀ i j e (hi : e ∈ (regions i).edges) (hj : e ∈ (regions j).edges),
      (localObjects i).1.1.1 ⟨e,hi⟩ = (localObjects j).1.1.1 ⟨e,hj⟩) := by
  apply StrictSupportedCover.not_strict_of_ne coefficients ClosedRegion.empty regions ∅ ∅ 0
    localObjects false true edge trivial trivial
  intro h
  exact zero_ne_one (congrFun h (0 : Fin 1))
/-- Distinct constant original vertex labels, each locally permitted. -/
def localLabels (i : Bool) : SupportedEquation.Labels coefficients ClosedRegion.empty (regions i) ∅ ∅ :=
  ⟨⟨fun _ _ => if i then 1 else 0,by intro v hv; exact hv.elim⟩,
    by intro e he; exact he.1.elim⟩
/-- The actual labels disagree on a shared original vertex even with identical local effects. -/
theorem shared_label :
    localLabels ∉ StrictSupportedCover.Labels coefficients ClosedRegion.empty regions ∅ ∅ := by
  apply StrictSupportedCover.not_mem_labels_of_ne coefficients ClosedRegion.empty regions ∅ ∅
    localLabels false true false trivial trivial
  intro h
  exact zero_ne_one (congrFun h (0 : Fin 1))
section Generated
variable (candidates : Set (EdgeName (K := geometry))) [DecidablePred (· ∈ candidates)]
local notation "private" i => ClosedRegion.privateAlwaysEdges regions ClosedRegion.empty candidates i
local notation "E" i => FiniteNative.generatedSolutionEquiv coefficients bases (regions i) ClosedRegion.empty
  (private i) linear 0 fieldEnum edgeEnum faceEnum
/-- The actual local solutions are sent to the same once-generated full interfaces. -/
def generated (i : Bool) := (E i) (solution (if i then 1 else 0) i)
/-- Every local generated public value has the explicitly supplied original correction. -/
theorem generated_value (i : Bool) :
    GeneratedStrictCover.publicValue coefficients bases ClosedRegion.empty regions candidates i
      (generated candidates i).1.1 ⟨edge,trivial⟩ = (fun _ => (if i then 1 else 0 : ZMod 2)) := by
  have hv := GeneratedStrictCover.restored_value_public coefficients bases ClosedRegion.empty regions candidates
    linear 0 fieldEnum edgeEnum faceEnum i (generated candidates i) ⟨edge,trivial⟩
    (ClosedRegion.overlap_not_private regions ClosedRegion.empty candidates i (!i) (by cases i <;> decide)
      edge ⟨trivial,trivial⟩)
  change ((E i).symm ((E i) (solution (if i then 1 else 0) i))).1.1 ⟨edge,trivial⟩ = _ at hv
  rw [Equiv.symm_apply_apply] at hv
  exact hv.symm
end Generated
/-- The generated public coordinates actually violate both complete and public feasibility. -/
theorem generated_forbidden_public :
    (¬ GeneratedStrictCover.PublicCompatible coefficients bases ClosedRegion.empty regions Set.univ
      linear 0 fieldEnum edgeEnum faceEnum ∅ (generated Set.univ)) ∧
    ¬ (∃ z : GeneratedPublicRelations.Objects coefficients bases ClosedRegion.empty regions Set.univ
      linear 0 fieldEnum edgeEnum faceEnum ∅, z.1 = fun i => (generated Set.univ i).1) := by
  have hn : GeneratedStrictCover.publicValue coefficients bases ClosedRegion.empty regions Set.univ true
      (generated Set.univ true).1.1 ⟨edge,trivial⟩ ≠ 0 := by
    rw [generated_value]
    intro h
    exact one_ne_zero (congrFun h (0 : Fin 1))
  constructor
  · intro h
    exact hn (h.1 true ⟨edge,trivial⟩ ⟨trivial,by intro h; exact h⟩)
  · rintro ⟨z,hz⟩
    have hp := GeneratedPublicRelations.not_supported_of_ne coefficients bases ClosedRegion.empty regions Set.univ
      linear 0 fieldEnum edgeEnum faceEnum ∅ (fun i => (generated Set.univ i).1) true
      ⟨edge,trivial⟩ ⟨trivial,by intro h; exact h⟩ hn
    apply hp
    rw [← hz]
    exact z.2
/-- Distinct original solutions violate both whole and public shared-edge feasibility. -/
theorem generated_shared_public :
    (¬ GeneratedStrictCover.PublicCompatible coefficients bases ClosedRegion.empty regions ∅
      linear 0 fieldEnum edgeEnum faceEnum ∅ (generated ∅)) ∧
    ¬ (∃ z : GeneratedPublicRelations.Objects coefficients bases ClosedRegion.empty regions ∅
      linear 0 fieldEnum edgeEnum faceEnum ∅, z.1 = fun i => (generated ∅ i).1) := by
  have hn : GeneratedStrictCover.publicValue coefficients bases ClosedRegion.empty regions ∅ false
      (generated ∅ false).1.1 ⟨edge,trivial⟩ ≠
      GeneratedStrictCover.publicValue coefficients bases ClosedRegion.empty regions ∅ true
      (generated ∅ true).1.1 ⟨edge,trivial⟩ := by
    rw [generated_value,generated_value]
    intro h
    exact zero_ne_one (congrFun h (0 : Fin 1))
  constructor
  · intro h
    exact hn (h.2 false true edge trivial trivial (by decide))
  · rintro ⟨z,hz⟩
    have hp := GeneratedPublicRelations.not_shared_of_ne coefficients bases ClosedRegion.empty regions ∅
      linear 0 fieldEnum edgeEnum faceEnum ∅ (fun i => (generated ∅ i).1) false true
      edge trivial trivial (by decide) hn
    apply hp
    rw [← hz]
    exact z.2
/-- The same nontrivial original geometry supplies an actual positive input for all new predicates. -/
theorem zero_accepted :
    Nonempty (SupportedEquation.Objects coefficients ClosedRegion.empty (regions false) Set.univ ∅ 0) ∧
    Nonempty (StrictSupportedCover.Objects coefficients ClosedRegion.empty regions Set.univ ∅ 0) ∧
    Nonempty (GeneratedPublicRelations.Objects coefficients bases ClosedRegion.empty regions Set.univ
      linear 0 fieldEnum edgeEnum faceEnum ∅) :=
  ⟨⟨SupportedEquation.zeroObject coefficients ClosedRegion.empty (regions false) Set.univ ∅⟩,
    ⟨StrictCoverZeroCases.originalZero coefficients ClosedRegion.empty regions Set.univ ∅⟩,
    ⟨StrictCoverZeroCases.publicZero coefficients bases ClosedRegion.empty regions Set.univ
      linear fieldEnum edgeEnum faceEnum ∅⟩⟩
end StrictCoverNegativeCases
end AAT.AG.RelativeRepairComposition
#assert_standard_axioms_only AAT.AG.RelativeRepairComposition
