import ResearchLean.AG.RelativeRepairComposition.ClosedRegions

/-!
# Complete closed presentations and their original cochain restriction

G-130 A / n1017 §2.1–2.2: retain original cell names, every typed path,
all contextual rewrite steps and both complete three-cell routes. The selected
coefficient families reindex to the accepted original-index restriction in all
degrees, and the differentials agree with that restriction.

## Implementation notes

Membership proofs choose the same finite cells; they add no coherence field.
Full route equality uses its ordered typed face contexts and bookend paths.
Degreewise zero extension compares the native differential to the earlier
original-index construction; it is never asserted to be a chain map.
-/
namespace AAT.AG.RelativeRepairComposition
open CategoryTheory TransportCoherence AbelianLiftingObstruction
universe uG
variable {K : FiniteTransportPresentation.{uG}}
namespace ClosedRegion
variable (U : ClosedRegion K)
/-- G-130 A: selected vertices retain their original names. -/
abbrev Vertex := U.vertices
/-- G-130 A: selected typed edges retain their endpoints and original edge values. -/
abbrev Edge (i j : Vertex U) := {e : K.Edge i.1 j.1 // (⟨i.1,j.1,e⟩ : EdgeName) ∈ U.edges}
/-- G-130 A: finite typed paths on the selected original edges. -/
abbrev Path (i j : Vertex U) := PresentedPath (Edge U) i j

/-- Forget membership proofs while keeping each ordered original edge occurrence. -/
def forgetPath : {i j : Vertex U} → Path U i j → K.Path i.1 j.1
  | _, _, .nil i => .nil i.1
  | _, _, .cons e w => .cons e.1 (forgetPath w)

/-- Restrict a complete original path using closure of every edge occurrence. -/
def restrictPath : {i j : K.Vertex} → (w : K.Path i j) →
    (hi : i ∈ U.vertices) → (hj : j ∈ U.vertices) →
    (hw : pathEdges w ⊆ U.edges) → Path U ⟨i,hi⟩ ⟨j,hj⟩
  | _, _, .nil v, hi, _, _ => PresentedPath.nil (⟨v,hi⟩ : Vertex U)
  | _, _, .cons e tail, _, hj, hw =>
    let he := hw (Or.inl rfl)
    .cons ⟨e,he⟩ (restrictPath tail (U.edge_closed _ he).2 hj (fun _ ha => hw (Or.inr ha)))

/-- Path restriction followed by forgetting is the same complete original path. -/
theorem forget_restrict {i j : K.Vertex} (w : K.Path i j) (hi : i ∈ U.vertices) (hj : j ∈ U.vertices)
    (hw : pathEdges w ⊆ U.edges) : forgetPath U (restrictPath U w hi hj hw) = w := by
  induction w with
  | nil i => rfl
  | cons e w ih =>
    change PresentedPath.cons e (forgetPath U (restrictPath U w _ _ _)) = PresentedPath.cons e w
    rw [ih]

/-- Every original edge occurring in a selected path belongs to the closed region. -/
theorem forget_path_edges {i j : Vertex U} (w : Path U i j) : pathEdges (forgetPath U w) ⊆ U.edges := by
  induction w with
  | nil i => exact Set.empty_subset _
  | cons e w ih =>
    rintro a (rfl | ha)
    · exact e.2
    · exact ih ha

/-- Forgetting and restricting restores the selected typed path. -/
theorem restrict_forget {i j : Vertex U} (w : Path U i j) :
    restrictPath U (forgetPath U w) i.2 j.2 (forget_path_edges U w) = w := by
  induction w with
  | nil i => rfl
  | cons e w ih =>
    change PresentedPath.cons ⟨e.1, _⟩ (restrictPath U (forgetPath U w) _ _ _) = PresentedPath.cons e w
    rw [ih]

/-- Original path values distinguish all selected typed paths. -/
theorem forget_path_injective {i j : Vertex U} : Function.Injective (@forgetPath _ U i j) := by
  intro w z h
  have he := congrArg (fun a : {w : K.Path i.1 j.1 // pathEdges w ⊆ U.edges} =>
    restrictPath U a.1 i.2 j.2 a.2)
    (show (⟨forgetPath U w, forget_path_edges U w⟩ : {w : K.Path i.1 j.1 // pathEdges w ⊆ U.edges}) =
      ⟨forgetPath U z, forget_path_edges U z⟩ from Subtype.ext h)
  simpa only [restrict_forget] using he

/-- Forgetting preserves ordered path concatenation. -/
theorem forget_path_append {i j k : Vertex U} (w : Path U i j) (z : Path U j k) :
    forgetPath U (w.append z) = (forgetPath U w).append (forgetPath U z) := by
  induction w with
  | nil i => rfl
  | cons e w ih =>
    change PresentedPath.cons e.1 (forgetPath U (w.append z)) =
      PresentedPath.cons e.1 ((forgetPath U w).append (forgetPath U z))
    rw [ih]

/-- G-130 A: the closed original 0/1/2-cell skeleton with both complete face paths. -/
noncomputable def twoPresentation : FiniteTransportTwoPresentation.{uG} := by
  classical
  letI := K.vertexFintype
  letI := K.twoCellFintype
  exact {
    Vertex := Vertex U
    vertexFintype := Fintype.ofFinite _
    Edge := Edge U
    edgeFintype := fun i j => by
      letI := K.edgeFintype i.1 j.1
      exact Fintype.ofFinite _
    TwoCell := U.faces
    twoCellFintype := Fintype.ofFinite _
    twoSource := fun f => ⟨K.twoSource f.1, (U.face_closed f.1 f.2).1⟩
    twoTarget := fun f => ⟨K.twoTarget f.1, (U.face_closed f.1 f.2).2.1⟩
    twoLeft := fun f => restrictPath U (K.twoLeft f.1) _ _ (U.face_closed f.1 f.2).2.2.1
    twoRight := fun f => restrictPath U (K.twoRight f.1) _ _ (U.face_closed f.1 f.2).2.2.2 }

/-- The selected left face path is the same original left path. -/
theorem forget_two_left (f : (twoPresentation U).TwoCell) :
    forgetPath U ((twoPresentation U).twoLeft f) = K.twoLeft f.1 :=
  forget_restrict U _ _ _ _

/-- The selected right face path is the same original right path. -/
theorem forget_two_right (f : (twoPresentation U).TwoCell) :
    forgetPath U ((twoPresentation U).twoRight f) = K.twoRight f.1 :=
  forget_restrict U _ _ _ _

/-- Restrict the face name, orientation, incoming prefix and outgoing suffix together. -/
noncomputable def restrictWhiskeredFace {i j : K.Vertex}
    (face : WhiskeredFace K.toFiniteTransportTwoPresentation i j)
    (hi : i ∈ U.vertices) (hj : j ∈ U.vertices)
    (hf : face.cell ∈ U.faces)
    (hpre : pathEdges face.incoming ⊆ U.edges) (hpost : pathEdges face.outgoing ⊆ U.edges) :
    WhiskeredFace (twoPresentation U) ⟨i,hi⟩ ⟨j,hj⟩ where
  cell := ⟨face.cell,hf⟩
  incoming := restrictPath U face.incoming hi (U.face_closed _ hf).1 hpre
  outgoing := restrictPath U face.outgoing (U.face_closed _ hf).2.1 hj hpost
  orientation := face.orientation

/-- The restricted contextual face retains its complete original input path. -/
theorem forget_face_before {i j : K.Vertex}
    (face : WhiskeredFace K.toFiniteTransportTwoPresentation i j)
    (hi : i ∈ U.vertices) (hj : j ∈ U.vertices)
    (hf : face.cell ∈ U.faces)
    (hpre : pathEdges face.incoming ⊆ U.edges) (hpost : pathEdges face.outgoing ⊆ U.edges) :
    forgetPath U (restrictWhiskeredFace U face hi hj hf hpre hpost).before = face.before := by
  cases face with
  | mk cell pre post orientation =>
    cases orientation <;>
      simp only [WhiskeredFace.before, WhiskeredFace.localBefore,
        restrictWhiskeredFace, twoPresentation, forget_path_append, forget_restrict]

/-- The restricted contextual face retains its complete original output path. -/
theorem forget_face_after {i j : K.Vertex}
    (face : WhiskeredFace K.toFiniteTransportTwoPresentation i j)
    (hi : i ∈ U.vertices) (hj : j ∈ U.vertices)
    (hf : face.cell ∈ U.faces)
    (hpre : pathEdges face.incoming ⊆ U.edges) (hpost : pathEdges face.outgoing ⊆ U.edges) :
    forgetPath U (restrictWhiskeredFace U face hi hj hf hpre hpost).after = face.after := by
  cases face with
  | mk cell pre post orientation =>
    cases orientation <;>
      simp only [WhiskeredFace.after, WhiskeredFace.localAfter,
        restrictWhiskeredFace, twoPresentation, forget_path_append, forget_restrict]

/-- Restrict an original rewrite with both indexed paths and its complete geometric context. -/
noncomputable def restrictStep {i j : K.Vertex} {before after : K.Path i j}
    (step : RewriteStep K.toFiniteTransportTwoPresentation before after)
    (hi : i ∈ U.vertices) (hj : j ∈ U.vertices)
    (hb : pathEdges before ⊆ U.edges) (ha : pathEdges after ⊆ U.edges)
    (hf : step.face.cell ∈ U.faces)
    (hpre : pathEdges step.face.incoming ⊆ U.edges) (hpost : pathEdges step.face.outgoing ⊆ U.edges) :
    RewriteStep (twoPresentation U) (restrictPath U before hi hj hb) (restrictPath U after hi hj ha) where
  face := restrictWhiskeredFace U step.face hi hj hf hpre hpost
  before_eq := forget_path_injective U ((forget_restrict U before hi hj hb).trans
    (step.before_eq.trans (forget_face_before U step.face hi hj hf hpre hpost).symm))
  after_eq := forget_path_injective U ((forget_restrict U after hi hj ha).trans
    (step.after_eq.trans (forget_face_after U step.face hi hj hf hpre hpost).symm))

/-- The output of a selected contextual face is a closed original path for the next step. -/
theorem middle_closed {i j : K.Vertex} {before middle : K.Path i j}
    (step : RewriteStep K.toFiniteTransportTwoPresentation before middle)
    (hi : i ∈ U.vertices) (hj : j ∈ U.vertices)
    (hf : step.face.cell ∈ U.faces)
    (hpre : pathEdges step.face.incoming ⊆ U.edges) (hpost : pathEdges step.face.outgoing ⊆ U.edges) :
    pathEdges middle ⊆ U.edges := by
  rw [step.after_eq, ← forget_face_after U step.face hi hj hf hpre hpost]
  exact forget_path_edges U _

/-- Restrict every ordered rewrite step with its typed shared middle path. -/
noncomputable def restrictPasting : {i j : K.Vertex} → {before finish : K.Path i j} →
    (pasting : RewritePasting K.toFiniteTransportTwoPresentation before finish) →
    (hi : i ∈ U.vertices) → (hj : j ∈ U.vertices) →
    (hb : pathEdges before ⊆ U.edges) → (hz : pathEdges finish ⊆ U.edges) →
    (hf : pastingFaces pasting ⊆ U.faces) → (hc : pastingContextEdges pasting ⊆ U.edges) →
    RewritePasting (twoPresentation U) (restrictPath U before hi hj hb) (restrictPath U finish hi hj hz)
  | _, _, _, _, .nil w, hi, hj, hb, _, _, _ => @RewritePasting.nil (twoPresentation U) _ _ (restrictPath U w hi hj hb)
  | _, _, _, _, .cons step tail, hi, hj, hb, hz, hf, hc =>
    let hface := hf (Or.inl rfl)
    let hpre := fun e he => hc (Or.inl (Or.inl he))
    let hpost := fun e he => hc (Or.inl (Or.inr he))
    let hm := middle_closed U step hi hj hface hpre hpost
    .cons (restrictStep U step hi hj hb hm hface hpre hpost)
      (restrictPasting tail hi hj hm hz (fun _ h => hf (Or.inr h)) (fun _ h => hc (Or.inr h)))

/-- G-130 A: the full closed 0/1/2/3-cell presentation, preserving both typed three-cell routes. -/
noncomputable def presentation : FiniteTransportPresentation.{uG} := by
  classical
  letI := K.threeCellFintype
  exact {
    toFiniteTransportTwoPresentation := twoPresentation U
    ThreeCell := U.triples
    threeCellFintype := Fintype.ofFinite _
    threeSource := fun s => ⟨K.threeSource s.1, (U.triple_closed s.1 s.2).1⟩
    threeTarget := fun s => ⟨K.threeTarget s.1, (U.triple_closed s.1 s.2).2.1⟩
    threeStart := fun s => restrictPath U (K.threeStart s.1) _ _ (U.triple_closed s.1 s.2).2.2.1
    threeFinish := fun s => restrictPath U (K.threeFinish s.1) _ _ (U.triple_closed s.1 s.2).2.2.2.1
    threeLeft := fun s => restrictPasting U (K.threeLeft s.1) _ _ _ _
      (U.triple_closed s.1 s.2).2.2.2.2.1 (U.triple_closed s.1 s.2).2.2.2.2.2.2.1
    threeRight := fun s => restrictPasting U (K.threeRight s.1) _ _ _ _
      (U.triple_closed s.1 s.2).2.2.2.2.2.1 (U.triple_closed s.1 s.2).2.2.2.2.2.2.2 }

/-- G-130 A: forget subtype proofs, retaining the complete oriented face. -/
noncomputable def forgetWhiskeredFace {i j : Vertex U}
    (face : WhiskeredFace (twoPresentation U) i j) :
    WhiskeredFace K.toFiniteTransportTwoPresentation i.1 j.1 where
  cell := face.cell.1
  incoming := forgetPath U face.incoming
  outgoing := forgetPath U face.outgoing
  orientation := face.orientation

/-- Forgetting a face preserves its complete incoming path. -/
theorem forget_whiskered_before {i j : Vertex U}
    (face : WhiskeredFace (twoPresentation U) i j) :
    (forgetWhiskeredFace U face).before = forgetPath U face.before := by
  cases face with
  | mk cell pre post orientation =>
    cases orientation <;>
      simp only [forgetWhiskeredFace, WhiskeredFace.before, WhiskeredFace.localBefore,
        twoPresentation, forget_path_append, forget_restrict]

/-- Forgetting a face preserves its complete outgoing path. -/
theorem forget_whiskered_after {i j : Vertex U}
    (face : WhiskeredFace (twoPresentation U) i j) :
    (forgetWhiskeredFace U face).after = forgetPath U face.after := by
  cases face with
  | mk cell pre post orientation =>
    cases orientation <;>
      simp only [forgetWhiskeredFace, WhiskeredFace.after, WhiskeredFace.localAfter,
        twoPresentation, forget_path_append, forget_restrict]

/-- Forgetting a step preserves both path indices and the whole face context. -/
noncomputable def forgetStep {i j : Vertex U} {w z : Path U i j}
    (step : RewriteStep (twoPresentation U) w z) :
    RewriteStep K.toFiniteTransportTwoPresentation (forgetPath U w) (forgetPath U z) where
  face := forgetWhiskeredFace U step.face
  before_eq := (congrArg (forgetPath U) step.before_eq).trans
    (forget_whiskered_before U step.face).symm
  after_eq := (congrArg (forgetPath U) step.after_eq).trans
    (forget_whiskered_after U step.face).symm

/-- Forgetting a typed pasting keeps every step and adjacent middle path. -/
noncomputable def forgetPasting : {i j : Vertex U} → {w z : Path U i j} →
    RewritePasting (twoPresentation U) w z →
    RewritePasting K.toFiniteTransportTwoPresentation (forgetPath U w) (forgetPath U z)
  | _, _, _, _, .nil w => .nil (forgetPath U w)
  | _, _, _, _, .cons step tail => .cons (forgetStep U step) (forgetPasting tail)

/-- Restricting and forgetting a face returns all original geometric fields. -/
theorem forget_restrict_whiskered_face {i j : K.Vertex}
    (face : WhiskeredFace K.toFiniteTransportTwoPresentation i j)
    (hi : i ∈ U.vertices) (hj : j ∈ U.vertices) (hf : face.cell ∈ U.faces)
    (hpre : pathEdges face.incoming ⊆ U.edges) (hpost : pathEdges face.outgoing ⊆ U.edges) :
    forgetWhiskeredFace U (restrictWhiskeredFace U face hi hj hf hpre hpost) = face := by
  cases face
  simp only [forgetWhiskeredFace, restrictWhiskeredFace, forget_restrict]

/-- The typed list stores every original face, prefix, suffix and orientation of a route. -/
def pastingTrace {i j : K.Vertex} {w z : K.Path i j} :
    RewritePasting K.toFiniteTransportTwoPresentation w z →
    List (Σ i : K.Vertex, Σ j : K.Vertex, WhiskeredFace K.toFiniteTransportTwoPresentation i j)
  | .nil _ => []
  | .cons step tail => ⟨_,_,step.face⟩ :: pastingTrace tail

/-- With the same bookend paths, the full geometric trace determines the typed pasting. -/
theorem pasting_trace_injective {i j : K.Vertex} {w z : K.Path i j} :
    Function.Injective (@pastingTrace K i j w z) := by
  intro a
  induction a with
  | nil w =>
    intro b hb
    cases b with
    | nil _ => rfl
    | cons step tail => simp only [pastingTrace] at hb; cases hb
  | @cons w middle z step tail ih =>
    intro b hb
    cases b with
    | nil _ => simp only [pastingTrace] at hb; cases hb
    | @cons _ middle' _ step' tail' =>
      have hhead := List.cons.inj hb
      have hf : step.face = step'.face := by
        simpa only [Sigma.mk.inj_iff, heq_iff_eq, true_and] using hhead.1
      have hm : middle = middle' := step.after_eq.trans
        ((congrArg WhiskeredFace.after hf).trans step'.after_eq.symm)
      cases hm
      have hs : step = step' := by
        cases step
        cases step'
        cases hf
        rfl
      cases hs
      exact congrArg (RewritePasting.cons step) (ih hhead.2)

/-- Transport only the two bookend path indices of a typed route. -/
def castPasting {i j : K.Vertex} {w w' z z' : K.Path i j}
    (hw : w = w') (hz : z = z')
    (pasting : RewritePasting K.toFiniteTransportTwoPresentation w z) :
    RewritePasting K.toFiniteTransportTwoPresentation w' z' := hw ▸ hz ▸ pasting

/-- Bookend transport keeps the complete geometric route unchanged. -/
theorem cast_pasting_trace {i j : K.Vertex} {w w' z z' : K.Path i j}
    (hw : w = w') (hz : z = z')
    (pasting : RewritePasting K.toFiniteTransportTwoPresentation w z) :
    pastingTrace (castPasting hw hz pasting) = pastingTrace pasting := by
  cases hw
  cases hz
  rfl

/-- Restriction preserves the entire ordered geometric trace of every rewrite sequence. -/
theorem forget_restrict_pasting_trace {i j : K.Vertex} {w z : K.Path i j}
    (pasting : RewritePasting K.toFiniteTransportTwoPresentation w z)
    (hi : i ∈ U.vertices) (hj : j ∈ U.vertices)
    (hb : pathEdges w ⊆ U.edges) (hz : pathEdges z ⊆ U.edges)
    (hf : pastingFaces pasting ⊆ U.faces) (hc : pastingContextEdges pasting ⊆ U.edges) :
    pastingTrace (forgetPasting U (restrictPasting U pasting hi hj hb hz hf hc)) =
      pastingTrace pasting := by
  induction pasting with
  | nil w => simp only [restrictPasting, forgetPasting, pastingTrace]
  | cons step tail ih =>
    simp only [restrictPasting, forgetPasting, pastingTrace, forgetStep, restrictStep,
      forget_restrict_whiskered_face, ih]

/-- Full typed restriction followed by forgetting is the original route, including indices. -/
theorem forget_restrict_pasting {i j : K.Vertex} {w z : K.Path i j}
    (pasting : RewritePasting K.toFiniteTransportTwoPresentation w z)
    (hi : i ∈ U.vertices) (hj : j ∈ U.vertices)
    (hb : pathEdges w ⊆ U.edges) (hz : pathEdges z ⊆ U.edges)
    (hf : pastingFaces pasting ⊆ U.faces) (hc : pastingContextEdges pasting ⊆ U.edges) :
    castPasting (forget_restrict U w hi hj hb) (forget_restrict U z hi hj hz)
      (forgetPasting U (restrictPasting U pasting hi hj hb hz hf hc)) = pasting := by
  apply pasting_trace_injective
  rw [cast_pasting_trace, forget_restrict_pasting_trace]

/-- The restricted three-cell starts at exactly the original path. -/
theorem forget_three_start (t : (presentation U).ThreeCell) :
    forgetPath U ((presentation U).threeStart t) = K.threeStart t.1 :=
  forget_restrict U _ _ _ _

/-- The restricted three-cell finishes at exactly the original path. -/
theorem forget_three_finish (t : (presentation U).ThreeCell) :
    forgetPath U ((presentation U).threeFinish t) = K.threeFinish t.1 :=
  forget_restrict U _ _ _ _

/-- The left three-cell route retains every face and full geometric context in order. -/
theorem forget_three_left_trace (t : (presentation U).ThreeCell) :
    pastingTrace (forgetPasting U ((presentation U).threeLeft t)) = pastingTrace (K.threeLeft t.1) :=
  forget_restrict_pasting_trace U _ _ _ _ _ _ _

/-- The right three-cell route retains every face and full geometric context in order. -/
theorem forget_three_right_trace (t : (presentation U).ThreeCell) :
    pastingTrace (forgetPasting U ((presentation U).threeRight t)) = pastingTrace (K.threeRight t.1) :=
  forget_restrict_pasting_trace U _ _ _ _ _ _ _

/-- The left restricted three-cell route is the complete original typed route after bookend transport. -/
theorem forget_three_left (t : (presentation U).ThreeCell) :
    castPasting (forget_three_start U t) (forget_three_finish U t)
      (forgetPasting U ((presentation U).threeLeft t)) = K.threeLeft t.1 :=
  forget_restrict_pasting U _ _ _ _ _ _ _

/-- The right restricted three-cell route is the complete original typed route after bookend transport. -/
theorem forget_three_right (t : (presentation U).ThreeCell) :
    castPasting (forget_three_start U t) (forget_three_finish U t)
      (forgetPasting U ((presentation U).threeRight t)) = K.threeRight t.1 :=
  forget_restrict_pasting U _ _ _ _ _ _ _

universe uA
/-- The restricted edge coefficients retain the original groups and transports. -/
def restrictEdgeCoefficients (M : EdgeCoefficients.{uG,uA} K) :
    EdgeCoefficients (presentation U) where
  A v := M.A v.1
  commGroup v := M.commGroup v.1
  edge e := M.edge e.1

/-- Every path uses exactly the original ordered edge transports. -/
theorem restrict_path_transport (M : EdgeCoefficients.{uG,uA} K)
    {i j : Vertex U} (w : Path U i j) :
    (restrictEdgeCoefficients U M).pathTransport w = M.pathTransport (forgetPath U w) := by
  induction w with
  | nil i => rfl
  | cons e w ih =>
    change (M.edge e.1).trans ((restrictEdgeCoefficients U M).pathTransport w) =
      (M.edge e.1).trans (M.pathTransport (forgetPath U w))
    rw [ih]

/-- Restriction discharges the face relation using the original two actual paths. -/
noncomputable def restrictCoefficients (M : LocalCoefficients.{uG,uA} K) :
    LocalCoefficients (presentation U) where
  toEdgeCoefficients := restrictEdgeCoefficients U M.toEdgeCoefficients
  face_transport f := by
    change (restrictEdgeCoefficients U M.toEdgeCoefficients).pathTransport
      ((twoPresentation U).twoLeft f) =
      (restrictEdgeCoefficients U M.toEdgeCoefficients).pathTransport
        ((twoPresentation U).twoRight f)
    rw [restrict_path_transport, restrict_path_transport, forget_two_left, forget_two_right]
    exact M.face_transport f.1

/-- Local coefficient restriction retains original path transport. -/
theorem restrict_local_path_transport (M : LocalCoefficients.{uG,uA} K)
    {i j : Vertex U} (w : Path U i j) :
    (restrictCoefficients U M).pathTransport w = M.pathTransport (forgetPath U w) :=
  restrict_path_transport U M.toEdgeCoefficients w

/-- Reindex the selected original edge names, preserving both endpoints and each edge. -/
def edgeNameEquiv : EdgeName (K := presentation U) ≃ U.edges where
  toFun e := ⟨⟨e.1.1,e.2.1.1,e.2.2.1⟩,e.2.2.2⟩
  invFun e := ⟨⟨e.1.1,(U.edge_closed e.1 e.2).1⟩,
    ⟨e.1.2.1,(U.edge_closed e.1 e.2).2⟩,⟨e.1.2.2,e.2⟩⟩
  left_inv e := by rcases e with ⟨⟨i,hi⟩,⟨j,hj⟩,⟨e,he⟩⟩; rfl
  right_inv e := by rcases e with ⟨⟨i,j,e⟩,he⟩; rfl

/-- Restriction in native degree zero agrees with the earlier original-index restriction. -/
def nativeR0 (M : LocalCoefficients.{uG,uA} K) :
    AbelianLiftingObstruction.C0 M →+ AbelianLiftingObstruction.C0 (restrictCoefficients U M) where
  toFun b v := b v.1
  map_zero' := rfl
  map_add' _ _ := rfl

/-- Restriction in native degree one retains each original named edge value. -/
def nativeR1 (M : LocalCoefficients.{uG,uA} K) :
    AbelianLiftingObstruction.C1 M →+ AbelianLiftingObstruction.C1 (restrictCoefficients U M) where
  toFun h e := h (edgeNameEquiv U e).1
  map_zero' := rfl
  map_add' _ _ := rfl

/-- Restriction in native degree two retains each original face value. -/
def nativeR2 (M : LocalCoefficients.{uG,uA} K) :
    AbelianLiftingObstruction.C2 M →+ AbelianLiftingObstruction.C2 (restrictCoefficients U M) where
  toFun h f := h f.1
  map_zero' := rfl
  map_add' _ _ := rfl

/-- Restriction in native degree three retains each original triple value. -/
def nativeR3 (M : LocalCoefficients.{uG,uA} K) :
    AbelianLiftingObstruction.C3 M →+ AbelianLiftingObstruction.C3 (restrictCoefficients U M) where
  toFun h t := h t.1
  map_zero' := rfl
  map_add' _ _ := rfl

/-- Native correction restriction retains the original correction on every selected path. -/
theorem native_path_correction (M : LocalCoefficients.{uG,uA} K)
    (h : AbelianLiftingObstruction.C1 M) {i j : Vertex U} (w : Path U i j) :
    pathCorrection (restrictCoefficients U M) (nativeR1 U M h) w =
      pathCorrection M h (forgetPath U w) := by
  induction w with
  | nil i => rfl
  | cons e w ih =>
    change (restrictCoefficients U M).pathTransport w (h ⟨_,_,e.1⟩) +
      pathCorrection (restrictCoefficients U M) (nativeR1 U M h) w =
      M.pathTransport (forgetPath U w) (h ⟨_,_,e.1⟩) + pathCorrection M h (forgetPath U w)
    rw [restrict_local_path_transport, ih]
    rfl

/-- The same signed face value survives restriction of its complete context. -/
theorem native_face_correction (M : LocalCoefficients.{uG,uA} K)
    (c : AbelianLiftingObstruction.C2 M) {i j : K.Vertex}
    (face : WhiskeredFace K.toFiniteTransportTwoPresentation i j)
    (hi : i ∈ U.vertices) (hj : j ∈ U.vertices) (hf : face.cell ∈ U.faces)
    (hpre : pathEdges face.incoming ⊆ U.edges) (hpost : pathEdges face.outgoing ⊆ U.edges) :
    faceCorrection (restrictCoefficients U M) (nativeR2 U M c)
      (restrictWhiskeredFace U face hi hj hf hpre hpost) = faceCorrection M c face := by
  cases face with
  | mk cell pre post orientation =>
    cases orientation <;>
      simp only [faceCorrection, restrictWhiskeredFace, nativeR2, AddMonoidHom.coe_mk,
        ZeroHom.coe_mk, restrict_local_path_transport, forget_restrict] <;> rfl

/-- Restriction retains the value of every typed rewrite sequence, step by step. -/
theorem native_pasting_correction (M : LocalCoefficients.{uG,uA} K)
    (c : AbelianLiftingObstruction.C2 M) {i j : K.Vertex} {w z : K.Path i j}
    (pasting : RewritePasting K.toFiniteTransportTwoPresentation w z)
    (hi : i ∈ U.vertices) (hj : j ∈ U.vertices)
    (hb : pathEdges w ⊆ U.edges) (hz : pathEdges z ⊆ U.edges)
    (hf : pastingFaces pasting ⊆ U.faces) (hc : pastingContextEdges pasting ⊆ U.edges) :
    pastingCorrection (restrictCoefficients U M) (nativeR2 U M c)
      (restrictPasting U pasting hi hj hb hz hf hc) = pastingCorrection M c pasting := by
  induction pasting with
  | nil w => simp only [restrictPasting, pastingCorrection]
  | cons step tail ih =>
    simp only [restrictPasting, pastingCorrection, restrictStep,
      native_face_correction, ih]

/-- Native restriction commutes with the same original typed three-cell differential. -/
theorem native_r_d2 (M : LocalCoefficients.{uG,uA} K) (c : AbelianLiftingObstruction.C2 M) :
    nativeR3 U M (d2 M c) = d2 (restrictCoefficients U M) (nativeR2 U M c) := by
  funext t
  change pastingCorrection M c (K.threeLeft t.1) - pastingCorrection M c (K.threeRight t.1) =
    pastingCorrection (restrictCoefficients U M) (nativeR2 U M c)
      (restrictPasting U (K.threeLeft t.1) _ _ _ _ _ _) -
    pastingCorrection (restrictCoefficients U M) (nativeR2 U M c)
      (restrictPasting U (K.threeRight t.1) _ _ _ _ _ _)
  rw [native_pasting_correction, native_pasting_correction]

/-- Native restriction commutes with the same original vertex gauge differential. -/
theorem native_r_d0 (M : LocalCoefficients.{uG,uA} K) (b : AbelianLiftingObstruction.C0 M) :
    nativeR1 U M (d0 M b) = d0 (restrictCoefficients U M) (nativeR0 U M b) := rfl

/-- Native restriction commutes with the same original face differential. -/
theorem native_r_d1 (M : LocalCoefficients.{uG,uA} K) (h : AbelianLiftingObstruction.C1 M) :
    nativeR2 U M (d1 M h) = d1 (restrictCoefficients U M) (nativeR1 U M h) := by
  funext f
  change pathCorrection M h (K.twoLeft f.1) - pathCorrection M h (K.twoRight f.1) =
    pathCorrection (restrictCoefficients U M) (nativeR1 U M h) ((twoPresentation U).twoLeft f) -
      pathCorrection (restrictCoefficients U M) (nativeR1 U M h) ((twoPresentation U).twoRight f)
  rw [native_path_correction, native_path_correction, forget_two_left, forget_two_right]


/-- Reindex native edge cochains to the same original terminal coefficient families. -/
def nativeC1Equiv (M : LocalCoefficients.{uG,uA} K) :
    AbelianLiftingObstruction.C1 (restrictCoefficients U M) ≃+ ClosedRegion.C1 M U where
  toFun h e := h ((edgeNameEquiv U).symm e)
  invFun h e := h (edgeNameEquiv U e)
  left_inv h := by funext e; rcases e with ⟨⟨i,hi⟩,⟨j,hj⟩,⟨e,he⟩⟩; rfl
  right_inv h := by funext e; rcases e with ⟨⟨i,j,e⟩,he⟩; rfl
  map_add' _ _ := rfl

/-- Original-index and native degree-one restrictions are the same map under reindexing. -/
theorem native_c1_restrict (M : LocalCoefficients.{uG,uA} K) (h : AbelianLiftingObstruction.C1 M) :
    nativeC1Equiv U M (nativeR1 U M h) = r1 M U h := by
  funext e
  rcases e with ⟨⟨i,j,e⟩,he⟩
  rfl

/-- Zero extension restricts back to every native edge cochain under the same reindexing. -/
theorem native_r1_extend (M : LocalCoefficients.{uG,uA} K) (h : ClosedRegion.C1 M U) :
    nativeR1 U M (e1 M U h) = (nativeC1Equiv U M).symm h := by
  funext e
  exact Family.extend_on (fun e : EdgeName (K := K) => M.A e.2.1)
    U.edges h (edgeNameEquiv U e).1 (edgeNameEquiv U e).2

/-- The native vertex differential is exactly the accepted original-index differential. -/
theorem native_d0_eq (M : LocalCoefficients.{uG,uA} K) (b : ClosedRegion.C0 M U) :
    nativeC1Equiv U M (d0 (restrictCoefficients U M) b) = d0Hom M U b := by
  have hr := native_r_d0 U M (e0 M U b)
  have he : nativeR0 U M (e0 M U b) = b := Family.restrict_extend _ _ _
  rw [he] at hr
  rw [← hr, native_c1_restrict]
  rfl

/-- The native face differential is exactly the accepted original-index differential. -/
theorem native_d1_eq (M : LocalCoefficients.{uG,uA} K) (h : ClosedRegion.C1 M U) :
    d1 (restrictCoefficients U M) ((nativeC1Equiv U M).symm h) = d1Hom M U h := by
  rw [← native_r1_extend, ← native_r_d1]
  rfl

/-- The native triple differential is exactly the accepted original-index differential. -/
theorem native_d2_eq (M : LocalCoefficients.{uG,uA} K) (c : ClosedRegion.C2 M U) :
    d2 (restrictCoefficients U M) c = d2Hom M U c := by
  have hr := native_r_d2 U M (e2 M U c)
  have he : nativeR2 U M (e2 M U c) = c := Family.restrict_extend _ _ _
  rw [he] at hr
  rw [← hr]
  rfl

universe uE uB uD vE vB vD
variable {E : Type uE} {B : Type uB} {D : Type uD}
variable [Category.{vE} E] [Category.{vB} B] [Category.{vD} D]
open TransportCoherence.Arbitrary

/-- G-130 A: original objects and actual strong arrows on the closed skeleton. -/
def restrictLiftData {r : E ⥤ B}
    (L : LiftData K.toFiniteTransportTwoPresentation r) : LiftData (twoPresentation U) r where
  object v := L.object v.1
  edgeBase e := L.edgeBase e.1
  edgeLift e := L.edgeLift e.1
  edgeStrong e := L.edgeStrong e.1

/-- Original base evaluation is retained on every selected path. -/
theorem restrict_path_base {r : E ⥤ B}
    (L : LiftData K.toFiniteTransportTwoPresentation r) {i j : Vertex U} (w : Path U i j) :
    (restrictLiftData U L).pathBase w = L.pathBase (forgetPath U w) := by
  induction w with
  | nil i => rfl
  | cons e w ih =>
    change L.edgeBase e.1 ≫ (restrictLiftData U L).pathBase w =
      L.edgeBase e.1 ≫ L.pathBase (forgetPath U w)
    rw [ih]

/-- Original upper evaluation is retained on every selected path. -/
theorem restrict_path_lift {r : E ⥤ B}
    (L : LiftData K.toFiniteTransportTwoPresentation r) {i j : Vertex U} (w : Path U i j) :
    (restrictLiftData U L).pathLift w = L.pathLift (forgetPath U w) := by
  induction w with
  | nil i => rfl
  | cons e w ih =>
    change L.edgeLift e.1 ≫ (restrictLiftData U L).pathLift w =
      L.edgeLift e.1 ≫ L.pathLift (forgetPath U w)
    rw [ih]

/-- Selected actual arrows commute with restriction of original lift choices. -/
theorem restrict_selected_upper {p : E ⥤ B} {q : B ⥤ D}
    (L : LiftData K.toFiniteTransportTwoPresentation (p ⋙ q))
    (choice : ∀ {i j : K.Vertex} (_ : K.Edge i j), FiberAut (p ⋙ q) (L.object j)) :
    selectedUpper (presentation U) p q (restrictLiftData U L) (fun e => choice e.1) =
      restrictLiftData U (selectedUpper K p q L choice) := rfl

end ClosedRegion
end AAT.AG.RelativeRepairComposition

#assert_standard_axioms_only AAT.AG.RelativeRepairComposition
