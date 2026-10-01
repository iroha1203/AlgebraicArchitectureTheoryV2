import ResearchLean.AG.RelativeRepairComposition.AffineContextFamilies
import Mathlib.Data.ZMod.Basic

/-! # Original finite regions with one shared loop and one internal candidate -/
namespace AAT.AG.RelativeRepairComposition.C16CandidateGeometry
open TransportCoherence AbelianLiftingObstruction NativeAffine

/-- The common original vertex and shared loop have no authored face or triple. -/
def boundaryGeometry : FiniteTransportPresentation where
  Vertex := Unit
  vertexFintype := inferInstance
  Edge := fun _ _ => Unit
  edgeFintype := fun _ _ => inferInstance
  TwoCell := Empty
  twoCellFintype := inferInstance
  twoSource f := nomatch f
  twoTarget f := nomatch f
  twoLeft f := nomatch f
  twoRight f := nomatch f
  ThreeCell := Empty
  threeCellFintype := inferInstance
  threeSource f := nomatch f
  threeTarget f := nomatch f
  threeStart f := nomatch f
  threeFinish f := nomatch f
  threeLeft f := nomatch f
  threeRight f := nomatch f

/-- The full original region retains the candidate word once or twice before its shared edge. -/
def geometry (double : Bool) : FiniteTransportPresentation where
  Vertex := Unit
  vertexFintype := inferInstance
  Edge := fun _ _ => Bool
  edgeFintype := fun _ _ => inferInstance
  TwoCell := Unit
  twoCellFintype := inferInstance
  twoSource _ := ()
  twoTarget _ := ()
  twoLeft _ := if double then .cons (j := ()) true (.cons true (.nil ())) else .cons true (.nil ())
  twoRight _ := .cons false (.nil ())
  ThreeCell := Empty
  threeCellFintype := inferInstance
  threeSource f := nomatch f
  threeTarget f := nomatch f
  threeStart f := nomatch f
  threeFinish f := nomatch f
  threeLeft f := nomatch f
  threeRight f := nomatch f

/-- Original loop equality is decided using the concrete Bool names. -/
instance edgeEquality (double : Bool) {i j : (geometry double).Vertex} :
    DecidableEq ((geometry double).Edge i j) := inferInstanceAs (DecidableEq Bool)

/-- All original shared word occurrences map to the false loop in their original order. -/
def includePath (double : Bool) {i j : boundaryGeometry.Vertex} :
    boundaryGeometry.Path i j → (geometry double).Path i j
  | .nil i => .nil i
  | .cons _ w => .cons false (includePath double w)

/-- The full original shared empty-face routes map at their same complete bookends. -/
def includeRoute (double : Bool) {i j : boundaryGeometry.Vertex} {w z : boundaryGeometry.Path i j} :
    RewritePasting boundaryGeometry.toFiniteTransportTwoPresentation w z →
      RewritePasting (geometry double).toFiniteTransportTwoPresentation
        (includePath double w) (includePath double z)
  | .nil _ => .nil _
  | .cons s _ => Empty.elim s.face.cell

/-- Exact full typed sharing is generated directly by the named loop inclusion. -/
def embedding (double : Bool) : FinitePresentationEmbedding boundaryGeometry (geometry double) where
  vertex := id
  vertex_injective := Function.injective_id
  edge := fun _ => false
  edge_injective _ _ := fun e f _ => by
    exact @Subsingleton.elim Unit inferInstance e f
  path := includePath double
  path_nil _ := rfl
  path_cons _ _ := rfl
  face := Empty.elim
  face_injective := fun f => Empty.elim f
  face_source f := Empty.elim f
  face_target f := Empty.elim f
  face_left f := Empty.elim f
  face_right f := Empty.elim f
  step := fun s => Empty.elim s.face.cell
  step_face s := Empty.elim s.face.cell
  step_incoming s := Empty.elim s.face.cell
  step_outgoing s := Empty.elim s.face.cell
  step_orientation s := Empty.elim s.face.cell
  route := includeRoute double
  route_nil _ := rfl
  route_cons s _ := Empty.elim s.face.cell
  triple := Empty.elim
  triple_injective := fun f => Empty.elim f
  triple_source f := Empty.elim f
  triple_target f := Empty.elim f
  triple_start f := Empty.elim f
  triple_finish f := Empty.elim f
  triple_left f := Empty.elim f
  triple_right f := Empty.elim f

/-- The actual shared original subregion contains precisely the vertex and false loop. -/
def shared (double : Bool) : ClosedRegion (geometry double) where
  vertices := Set.univ
  edges := {e | e.2.2 = false}
  faces := ∅
  triples := ∅
  edge_closed _ _ := ⟨trivial,trivial⟩
  face_closed _ h := h.elim
  triple_closed f _ := Empty.elim f

/-- The true loop is an internal original candidate and is outside the shared subregion. -/
def candidates (double : Bool) : Set (EdgeName (K := geometry double)) := {e | e.2.2 = true}

/-- The full affine translations use the one original F3 coordinate. -/
abbrev V := Fin 1 → ZMod 3

/-- The shared original and reference operation is the identity real affine map. -/
def boundaryReference : ∀ {i j : boundaryGeometry.Vertex}, boundaryGeometry.Edge i j →
    Operations (ZMod 3) V := fun _ => 1

/-- Every original region reference is the actual identity affine operation. -/
def reference (double : Bool) : ∀ {i j : (geometry double).Vertex},
    (geometry double).Edge i j → Operations (ZMod 3) V := fun _ => 1

/-- Both complete original reference words evaluate to identity, regardless of the candidate multiplicity. -/
theorem aligned (double : Bool) (f : (geometry double).TwoCell) :
    (GroupExtension.pathValue (geometry double) (reference double) ((geometry double).twoLeft f)).linear =
      (GroupExtension.pathValue (geometry double) (reference double) ((geometry double).twoRight f)).linear := by
  cases double <;> simp [geometry,reference,GroupExtension.pathValue]

/-- Both original whole inputs have primitive affine data with the same exact W and no physical anchors. -/
def input (double : Bool) : AffineContextInput boundaryGeometry boundaryReference boundaryReference
    (fun f => Empty.elim f) ClosedRegion.empty ∅ where
  geometry := geometry double
  embedding := embedding double
  shared := shared double
  shared_vertices := by change Set.univ = Set.range id; exact Set.range_id.symm
  shared_edges := by
    ext ⟨i,j,e⟩
    cases i; cases j
    constructor
    · intro h; exact ⟨⟨(),(),()⟩,by cases h; rfl⟩
    · rintro ⟨⟨a,b,c⟩,h⟩; cases a; cases b; cases c; cases h; rfl
  shared_faces := by
    ext f
    change False ↔ ∃ e : Empty, Empty.elim e = f
    constructor
    · intro h; exact h.elim
    · rintro ⟨e,_⟩; exact Empty.elim e
  shared_triples := by ext f; exact Empty.elim f
  originals := reference double
  references := reference double
  comparisons := fun _ => 0
  aligned := aligned double
  three_law f := Empty.elim f
  fixed := ClosedRegion.empty
  fixed_faces _ h := h.elim
  candidates := candidates double
  shared_reference _ := rfl
  shared_core _ := rfl
  shared_comparison f := Empty.elim f
  shared_fixed_vertices _ := Iff.rfl
  shared_fixed_edges _ := Iff.rfl
  shared_fixed_faces f := Empty.elim f
  shared_fixed_triples f := Empty.elim f
  shared_candidates _ := by
    change false = true ↔ False
    simp

/-- Internal permissions are quantified independently of the empty shared candidate set. -/
def permissions (double permit : Bool) (S : Set (EdgeName (K := boundaryGeometry))) :
    (input double).Range S where
  allowed := if permit then Set.univ else ∅
  shared_allowed _ h := h.elim

end AAT.AG.RelativeRepairComposition.C16CandidateGeometry
#assert_standard_axioms_only AAT.AG.RelativeRepairComposition.C16CandidateGeometry
