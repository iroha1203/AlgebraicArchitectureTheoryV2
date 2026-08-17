import ResearchLean.AG.CrossStageCoherence.PastingObstruction

/-!
# Cell-chain affine transport

This module builds the comparison graph required by the revised G-109 target.
For each fixed endpoint pair, nodes are exactly presented paths occurring on a
declared two-cell face, together with the empty path.  Oriented graph steps
carry the endpoint equalities explicitly, so distinct cell labels sharing one
semantic path meet at the same node.

The coordinate carrier is the composite-fiber group `C_G`.  A forward cell
acts by the twisted affine equivalence
`x ↦ u_c * x * φ₀(c)⁻¹`; a backward cell acts by its inverse.  Route transport
is composition of these equivalences, while `CellChainCoherent` is defined
independently by universal identity of every closed route.

## Implementation notes

The endpoint-indexed node type was chosen instead of a literal strong-lift
groupoid: strong-lift uniqueness would make every self-comparator trivial and
authored comparators do not carry lift-factorization certificates.  An
untwisted left action was also rejected because it drops the canonical right
factor outside the identity/central special cases.  Coherence is deliberately
not defined by existence of a section, potential, orbit witness, or gauge;
those are downstream comparison theorems with proof content.
-/

namespace AAT.AG.CrossStageCoherence

universe u v

open CategoryTheory
open AtomFoundation
open GeometryTransport
open TransportCoherence

set_option maxHeartbeats 3000000

/-! ## Typed nodes and oriented steps -/

/--
Transport one presented path along explicit equalities of both endpoints.
The equality direction is fixed from the cell endpoints to the graph indices.
-/
def castPresentedPath {P : FiniteTransportPresentation.{u}}
    {source target source' target' : P.Vertex}
    (source_eq : source = source') (target_eq : target = target')
    (path : P.Path source target) : P.Path source' target' := by
  subst source'
  subst target'
  exact path

/-- A path is admitted as a graph node only when it is empty or occurs on a cell. -/
inductive CellChainNodeSupported (P : FiniteTransportPresentation.{u}) :
    {source target : P.Vertex} → P.Path source target → Prop
  | nil (vertex : P.Vertex) :
      CellChainNodeSupported P (.nil vertex)
  | left (cell : P.TwoCell) :
      CellChainNodeSupported P (P.twoLeft cell)
  | right (cell : P.TwoCell) :
      CellChainNodeSupported P (P.twoRight cell)

/-- One semantic path node in the cell graph at a fixed endpoint pair. -/
structure CellChainNode (P : FiniteTransportPresentation.{u})
    (source target : P.Vertex) where
  /-- The represented typed path. -/
  path : P.Path source target
  /-- Provenance as an empty path or a declared two-cell side. -/
  supported : CellChainNodeSupported P path

namespace CellChainNode

/-- The empty-path node at one vertex. -/
def nil (P : FiniteTransportPresentation.{u}) (vertex : P.Vertex) :
    CellChainNode P vertex vertex :=
  ⟨.nil vertex, .nil vertex⟩

/-- The left-path node of one declared two-cell. -/
def left (P : FiniteTransportPresentation.{u}) (cell : P.TwoCell) :
    CellChainNode P (P.twoSource cell) (P.twoTarget cell) :=
  ⟨P.twoLeft cell, .left cell⟩

/-- The right-path node of one declared two-cell. -/
def right (P : FiniteTransportPresentation.{u}) (cell : P.TwoCell) :
    CellChainNode P (P.twoSource cell) (P.twoTarget cell) :=
  ⟨P.twoRight cell, .right cell⟩

/-- Node equality is equality of the semantic typed path; support proofs carry no data. -/
@[ext]
theorem ext {P : FiniteTransportPresentation.{u}} {source target : P.Vertex}
    {first second : CellChainNode P source target}
    (path_eq : first.path = second.path) : first = second := by
  cases first
  cases second
  cases path_eq
  rfl

end CellChainNode

/-- The Sigma-typed global node carrier, retaining both path endpoints. -/
abbrev CellChainSigmaNode (P : FiniteTransportPresentation.{u}) :=
  Σ source : P.Vertex, Σ target : P.Vertex, CellChainNode P source target

/-- Finite labels that generate every semantic cell-graph node. -/
abbrev CellChainNodeGenerator (P : FiniteTransportPresentation.{u}) :=
  P.Vertex ⊕ (P.TwoCell ⊕ P.TwoCell)

/-- Send a vertex/left-face/right-face label to its semantic graph node. -/
def cellChainNodeOfGenerator (P : FiniteTransportPresentation.{u}) :
    CellChainNodeGenerator P → CellChainSigmaNode P
  | .inl vertex => ⟨vertex, vertex, CellChainNode.nil P vertex⟩
  | .inr (.inl cell) =>
      ⟨P.twoSource cell, P.twoTarget cell, CellChainNode.left P cell⟩
  | .inr (.inr cell) =>
      ⟨P.twoSource cell, P.twoTarget cell, CellChainNode.right P cell⟩

/-- The finite generator family covers every supported semantic node. -/
theorem cellChainNodeOfGenerator_surjective
    (P : FiniteTransportPresentation.{u}) :
    Function.Surjective (cellChainNodeOfGenerator P) := by
  rintro ⟨source, target, ⟨path, supported⟩⟩
  cases supported with
  | nil => exact ⟨.inl source, rfl⟩
  | left cell => exact ⟨.inr (.inl cell), rfl⟩
  | right cell => exact ⟨.inr (.inr cell), rfl⟩

/-- The global Sigma carrier of cell-graph nodes is finite. -/
noncomputable instance cellChainSigmaNodeFintype
    (P : FiniteTransportPresentation.{u}) : Fintype (CellChainSigmaNode P) := by
  classical
  exact Fintype.ofSurjective (cellChainNodeOfGenerator P)
    (cellChainNodeOfGenerator_surjective P)

namespace CellChainNode

/-- Include one fixed-endpoint node into the global finite Sigma carrier. -/
def toSigma {P : FiniteTransportPresentation.{u}}
    {source target : P.Vertex} (node : CellChainNode P source target) :
    CellChainSigmaNode P :=
  ⟨source, target, node⟩

/-- The fixed-endpoint inclusion loses no semantic node data. -/
theorem toSigma_injective {P : FiniteTransportPresentation.{u}}
    {source target : P.Vertex} :
    Function.Injective
      (@toSigma P source target) := by
  intro first second equality
  cases equality
  rfl

/-- Every fixed-endpoint node carrier is finite. -/
noncomputable instance fintype {P : FiniteTransportPresentation.{u}}
    {source target : P.Vertex} : Fintype (CellChainNode P source target) := by
  classical
  exact Fintype.ofInjective toSigma toSigma_injective

end CellChainNode

/-- The path before traversing a cell in the selected orientation and endpoint cast. -/
def orientedCellBeforePath {P : FiniteTransportPresentation.{u}}
    {source target : P.Vertex} (cell : P.TwoCell)
    (source_eq : P.twoSource cell = source)
    (target_eq : P.twoTarget cell = target)
    (orientation : FaceOrientation) : P.Path source target :=
  castPresentedPath source_eq target_eq <|
    match orientation with
    | .forward => P.twoLeft cell
    | .backward => P.twoRight cell

/-- The path after traversing a cell in the selected orientation and endpoint cast. -/
def orientedCellAfterPath {P : FiniteTransportPresentation.{u}}
    {source target : P.Vertex} (cell : P.TwoCell)
    (source_eq : P.twoSource cell = source)
    (target_eq : P.twoTarget cell = target)
    (orientation : FaceOrientation) : P.Path source target :=
  castPresentedPath source_eq target_eq <|
    match orientation with
    | .forward => P.twoRight cell
    | .backward => P.twoLeft cell

/--
One typed oriented arrow between semantic path nodes.  Endpoint and path
equalities are geometry only; no comparison equation is stored.
-/
structure CellChainStep (P : FiniteTransportPresentation.{u})
    {source target : P.Vertex}
    (before after : CellChainNode P source target) where
  /-- The declared two-cell traversed by this arrow. -/
  cell : P.TwoCell
  /-- Identification of the cell source with the graph source index. -/
  source_eq : P.twoSource cell = source
  /-- Identification of the cell target with the graph target index. -/
  target_eq : P.twoTarget cell = target
  /-- Whether the cell is traversed left-to-right or right-to-left. -/
  orientation : FaceOrientation
  /-- The incoming node is the oriented cell's semantic input path. -/
  before_eq : before.path =
    orientedCellBeforePath cell source_eq target_eq orientation
  /-- The outgoing node is the oriented cell's semantic output path. -/
  after_eq : after.path =
    orientedCellAfterPath cell source_eq target_eq orientation

namespace CellChainStep

/-- A typed step is determined by its declared cell and reviewed orientation. -/
@[ext]
theorem ext {P : FiniteTransportPresentation.{u}}
    {source target : P.Vertex}
    {before after : CellChainNode P source target}
    {first second : CellChainStep P before after}
    (cell_eq : first.cell = second.cell)
    (orientation_eq : first.orientation = second.orientation) :
    first = second := by
  cases first
  cases second
  cases cell_eq
  cases orientation_eq
  rfl

/-- Encode the two reviewed face orientations by a finite Boolean label. -/
def orientationCode : FaceOrientation → Bool
  | .forward => false
  | .backward => true

/-- The Boolean orientation code is injective. -/
theorem orientationCode_injective : Function.Injective orientationCode := by
  intro first second equality
  cases first <;> cases second <;> simp_all [orientationCode]

/-- Finite code of one step; all remaining fields are propositions. -/
def code {P : FiniteTransportPresentation.{u}}
    {source target : P.Vertex}
    {before after : CellChainNode P source target}
    (step : CellChainStep P before after) : P.TwoCell × Bool :=
  (step.cell, orientationCode step.orientation)

/-- The finite code retains the whole typed step. -/
theorem code_injective {P : FiniteTransportPresentation.{u}}
    {source target : P.Vertex}
    {before after : CellChainNode P source target} :
    Function.Injective (@code P source target before after) := by
  intro first second equality
  apply ext
  · exact congrArg Prod.fst equality
  · apply orientationCode_injective
    exact congrArg Prod.snd equality

/-- Every arrow family between two fixed semantic nodes is finite. -/
noncomputable instance fintype {P : FiniteTransportPresentation.{u}}
    {source target : P.Vertex}
    {before after : CellChainNode P source target} :
    Fintype (CellChainStep P before after) := by
  classical
  exact Fintype.ofInjective code code_injective

/-- The canonical forward arrow of a declared two-cell. -/
def forward {P : FiniteTransportPresentation.{u}} (cell : P.TwoCell) :
    CellChainStep P (CellChainNode.left P cell) (CellChainNode.right P cell) where
  cell := cell
  source_eq := rfl
  target_eq := rfl
  orientation := .forward
  before_eq := rfl
  after_eq := rfl

/-- The canonical backward arrow of a declared two-cell. -/
def backward {P : FiniteTransportPresentation.{u}} (cell : P.TwoCell) :
    CellChainStep P (CellChainNode.right P cell) (CellChainNode.left P cell) where
  cell := cell
  source_eq := rfl
  target_eq := rfl
  orientation := .backward
  before_eq := rfl
  after_eq := rfl

/-- Reverse one typed arrow without changing its underlying semantic cell. -/
def reverse {P : FiniteTransportPresentation.{u}}
    {source target : P.Vertex}
    {before after : CellChainNode P source target}
    (step : CellChainStep P before after) : CellChainStep P after before := by
  rcases step with
    ⟨cell, source_eq, target_eq, orientation, before_eq, after_eq⟩
  cases orientation with
  | forward =>
      exact
        { cell := cell
          source_eq := source_eq
          target_eq := target_eq
          orientation := .backward
          before_eq := after_eq
          after_eq := before_eq }
  | backward =>
      exact
        { cell := cell
          source_eq := source_eq
          target_eq := target_eq
          orientation := .forward
          before_eq := after_eq
          after_eq := before_eq }

/--
Regard one unwhiskered cell-graph arrow as the existing typed upper rewrite
step with empty incoming and outgoing paths.  This is the route-integrity bridge
to the reviewed pasting evaluator; no second orientation convention is used.
-/
def toRewriteStep {P : FiniteTransportPresentation.{u}}
    {source target : P.Vertex}
    {before after : CellChainNode P source target}
    (step : CellChainStep P before after) :
    RewriteStep P.toFiniteTransportTwoPresentation before.path after.path := by
  rcases step with
    ⟨cell, source_eq, target_eq, orientation, before_eq, after_eq⟩
  subst source
  subst target
  let face : WhiskeredFace P.toFiniteTransportTwoPresentation
      (P.twoSource cell) (P.twoTarget cell) :=
    { cell := cell
      incoming := .nil (P.twoSource cell)
      outgoing := .nil (P.twoTarget cell)
      orientation := orientation }
  refine
    { face := face
      before_eq := ?_
      after_eq := ?_ }
  · simpa only [face, WhiskeredFace.before, WhiskeredFace.localBefore,
      PresentedPath.append, PresentedPath.append_nil,
      orientedCellBeforePath, castPresentedPath] using before_eq
  · simpa only [face, WhiskeredFace.after, WhiskeredFace.localAfter,
      PresentedPath.append, PresentedPath.append_nil,
      orientedCellAfterPath, castPresentedPath] using after_eq

end CellChainStep

/-- The global Sigma carrier of all cell-graph arrows. -/
abbrev CellChainSigmaStep (P : FiniteTransportPresentation.{u}) :=
  Σ source : P.Vertex,
    Σ target : P.Vertex,
      Σ before : CellChainNode P source target,
        Σ after : CellChainNode P source target,
          CellChainStep P before after

/-- The global arrow carrier of the cell graph is finite. -/
noncomputable instance cellChainSigmaStepFintype
    (P : FiniteTransportPresentation.{u}) : Fintype (CellChainSigmaStep P) := by
  classical
  exact inferInstance

/-- A typed zigzag of oriented two-cell arrows between path nodes. -/
inductive CellChain (P : FiniteTransportPresentation.{u})
    {source target : P.Vertex} :
    CellChainNode P source target → CellChainNode P source target → Type u
  | nil (node : CellChainNode P source target) : CellChain P node node
  | cons {first middle last : CellChainNode P source target}
      (step : CellChainStep P first middle)
      (tail : CellChain P middle last) : CellChain P first last

namespace CellChain

/-- Concatenate two typed cell chains with a shared semantic middle node. -/
def append {P : FiniteTransportPresentation.{u}}
    {source target : P.Vertex}
    {first middle last : CellChainNode P source target}
    (head : CellChain P first middle) (tail : CellChain P middle last) :
    CellChain P first last :=
  match head with
  | .nil _ => tail
  | .cons step rest => .cons step (append rest tail)

/-- Reuse the reviewed upper pasting carrier for every typed cell chain. -/
def toRewritePasting {P : FiniteTransportPresentation.{u}}
    {source target : P.Vertex}
    {first last : CellChainNode P source target}
    (chain : CellChain P first last) :
    RewritePasting P.toFiniteTransportTwoPresentation first.path last.path :=
  match chain with
  | .nil node => .nil node.path
  | .cons step tail => .cons step.toRewriteStep (toRewritePasting tail)

end CellChain

/-! ## Affine coordinate transport -/

/-- Transport a composite-fiber coordinate along equality of target vertices. -/
noncomputable def castCompositeFiberAut
    {P : FiniteTransportPresentation.{u}} {U : AtomCarrier.{u}}
    (lift : TwoLayerLiftData.{u, v} P U) {first second : P.Vertex}
    (target_eq : first = second)
    (coordinate : CompositeFiberAut (lift.geometry first)) :
    CompositeFiberAut (lift.geometry second) := by
  subst second
  exact coordinate

/-- Endpoint transport preserves the identity coordinate. -/
@[simp]
theorem castCompositeFiberAut_one
    {P : FiniteTransportPresentation.{u}} {U : AtomCarrier.{u}}
    (lift : TwoLayerLiftData.{u, v} P U) {first second : P.Vertex}
    (target_eq : first = second) :
    castCompositeFiberAut lift target_eq 1 = 1 := by
  subst second
  rfl

/-- Endpoint transport preserves coordinate multiplication. -/
@[simp]
theorem castCompositeFiberAut_mul
    {P : FiniteTransportPresentation.{u}} {U : AtomCarrier.{u}}
    (lift : TwoLayerLiftData.{u, v} P U) {first second : P.Vertex}
    (target_eq : first = second)
    (left right : CompositeFiberAut (lift.geometry first)) :
    castCompositeFiberAut lift target_eq (left * right) =
      castCompositeFiberAut lift target_eq left *
        castCompositeFiberAut lift target_eq right := by
  subst second
  rfl

/-- Endpoint transport preserves coordinate inversion. -/
@[simp]
theorem castCompositeFiberAut_inv
    {P : FiniteTransportPresentation.{u}} {U : AtomCarrier.{u}}
    (lift : TwoLayerLiftData.{u, v} P U) {first second : P.Vertex}
    (target_eq : first = second)
    (coordinate : CompositeFiberAut (lift.geometry first)) :
    castCompositeFiberAut lift target_eq coordinate⁻¹ =
      (castCompositeFiberAut lift target_eq coordinate)⁻¹ := by
  subst second
  rfl

/-- Upper whiskering along an empty suffix leaves the coordinate unchanged. -/
@[simp]
theorem upperWhiskerCompositeFiberAut_nil
    {P : FiniteTransportPresentation.{u}} {U : AtomCarrier.{u}}
    (data : TwoLayerLiftData.{u, v} P U)
    (reselection : UpperEdgeReselection data) {vertex : P.Vertex}
    (automorphism : CompositeFiberAut (data.geometry vertex)) :
    upperWhiskerCompositeFiberAut data reselection automorphism (.nil vertex) =
      automorphism := by
  letI : (crossStageProjection.{u, v} U).IsStronglyCocartesian
      (upperReselectedPathLift data reselection (.nil vertex)).base.base
      (upperReselectedPathLift data reselection (.nil vertex)) :=
    (upperReselectLiftData data reselection).pathLift_compositeStrong
      (.nil vertex)
  apply CompositeFiberAut.ext_of_strong_fac
    (upperReselectedPathLift data reselection (.nil vertex))
  calc
    _ = upperFiberAutThenPath data reselection automorphism (.nil vertex) :=
      upperWhiskerCompositeFiberAut_fac data reselection automorphism
        (.nil vertex)
    _ = CompositeFiberAut.hom automorphism := by
      change (CompositeFiberAut.hom automorphism).comp
          (GeometryTotalHom.id (data.geometry vertex)) = _
      exact (@Category.comp_id
        (GeomReadCategory.{u, v} U) (geometryTotalCategory U)
        _ _ (CompositeFiberAut.hom automorphism))
    _ = _ := by
      change _ = (GeometryTotalHom.id (data.geometry vertex)).comp
        (CompositeFiberAut.hom automorphism)
      exact (@Category.id_comp
        (GeomReadCategory.{u, v} U) (geometryTotalCategory U)
        _ _ (CompositeFiberAut.hom automorphism)).symm

/-- The invertible two-sided affine action `x ↦ left * x * right⁻¹`. -/
def cellGaugeAffineEquiv {G : Type*} [Group G] (left right : G) : G ≃ G where
  toFun coordinate := left * coordinate * right⁻¹
  invFun coordinate := left⁻¹ * coordinate * right
  left_inv coordinate := by simp [mul_assoc]
  right_inv coordinate := by simp [mul_assoc]

/-- The authored factor of one oriented graph step, transported to its endpoint. -/
noncomputable def cellAuthoredFactor
    {P : FiniteTransportPresentation.{u}} {U : AtomCarrier.{u}}
    (data : TwoLayerTransportData.{u, v} P U)
    {source target : P.Vertex}
    {before after : CellChainNode P source target}
    (step : CellChainStep P before after) :
    CompositeFiberAut (data.lift.geometry target) :=
  let authored := castCompositeFiberAut data.lift step.target_eq
    (data.comparator step.cell)
  match step.orientation with
  | .forward => authored
  | .backward => authored⁻¹

/--
The canonical factor of one oriented graph step at an arbitrary edge
reselection.  Closed products of these factors telescope by strong uniqueness.
-/
noncomputable def cellCanonicalFactor
    {P : FiniteTransportPresentation.{u}} {U : AtomCarrier.{u}}
    (data : TwoLayerTransportData.{u, v} P U)
    (reselection : UpperEdgeReselection data.lift)
    {source target : P.Vertex}
    {before after : CellChainNode P source target}
    (step : CellChainStep P before after) :
    CompositeFiberAut (data.lift.geometry target) :=
  let canonical := castCompositeFiberAut data.lift step.target_eq
    (upperCanonicalTwoCellComparator data reselection step.cell)
  match step.orientation with
  | .forward => canonical
  | .backward => canonical⁻¹

/-- The required twisted affine equivalence carried by one oriented cell. -/
noncomputable def CellAffineStep
    {P : FiniteTransportPresentation.{u}} {U : AtomCarrier.{u}}
    (data : TwoLayerTransportData.{u, v} P U)
    {source target : P.Vertex}
    {before after : CellChainNode P source target}
    (step : CellChainStep P before after) :
    CompositeFiberAut (data.lift.geometry target) ≃
      CompositeFiberAut (data.lift.geometry target) :=
  cellGaugeAffineEquiv (cellAuthoredFactor data step)
    (cellCanonicalFactor data 1 step)

/-- The affine-step formula is exposed without unfolding the equivalence record. -/
theorem cellAffineStep_apply
    {P : FiniteTransportPresentation.{u}} {U : AtomCarrier.{u}}
    (data : TwoLayerTransportData.{u, v} P U)
    {source target : P.Vertex}
    {before after : CellChainNode P source target}
    (step : CellChainStep P before after)
    (coordinate : CompositeFiberAut (data.lift.geometry target)) :
    CellAffineStep data step coordinate =
      cellAuthoredFactor data step * coordinate *
        (cellCanonicalFactor data 1 step)⁻¹ :=
  rfl

/-- At the identity coordinate, a canonical forward arrow is the raw defect. -/
theorem cellAffineStep_forward_one_eq_upperRaw
    {P : FiniteTransportPresentation.{u}} {U : AtomCarrier.{u}}
    (data : TwoLayerTransportData.{u, v} P U) (cell : P.TwoCell) :
    CellAffineStep data (CellChainStep.forward cell) 1 =
      upperRawTwoCellDefect data 1 cell := by
  simp only [cellAffineStep_apply, cellAuthoredFactor,
    cellCanonicalFactor, CellChainStep.forward, castCompositeFiberAut,
    mul_one, upperRawTwoCellDefect]

/-- Compose the affine steps along one typed cell chain. -/
noncomputable def CellRouteTransport
    {P : FiniteTransportPresentation.{u}} {U : AtomCarrier.{u}}
    (data : TwoLayerTransportData.{u, v} P U)
    {source target : P.Vertex}
    {first last : CellChainNode P source target}
    (chain : CellChain P first last) :
    CompositeFiberAut (data.lift.geometry target) ≃
      CompositeFiberAut (data.lift.geometry target) :=
  match chain with
  | .nil _ => Equiv.refl _
  | .cons step tail =>
      (CellAffineStep data step).trans (CellRouteTransport data tail)

/-- Authored word accumulated by a chain in route-composition order. -/
noncomputable def cellAuthoredWord
    {P : FiniteTransportPresentation.{u}} {U : AtomCarrier.{u}}
    (data : TwoLayerTransportData.{u, v} P U)
    {source target : P.Vertex}
    {first last : CellChainNode P source target}
    (chain : CellChain P first last) :
    CompositeFiberAut (data.lift.geometry target) :=
  match chain with
  | .nil _ => 1
  | .cons step tail =>
      cellAuthoredWord data tail * cellAuthoredFactor data step

/-- Canonical word accumulated by a chain at one edge reselection. -/
noncomputable def cellCanonicalWord
    {P : FiniteTransportPresentation.{u}} {U : AtomCarrier.{u}}
    (data : TwoLayerTransportData.{u, v} P U)
    (reselection : UpperEdgeReselection data.lift)
    {source target : P.Vertex}
    {first last : CellChainNode P source target}
    (chain : CellChain P first last) :
    CompositeFiberAut (data.lift.geometry target) :=
  match chain with
  | .nil _ => 1
  | .cons step tail =>
      cellCanonicalWord data reselection tail *
        cellCanonicalFactor data reselection step

/-- One authored cell factor is exactly the existing upper oriented-face evaluator. -/
theorem cellAuthoredFactor_eq_upperOrientedFaceAuthoredComparator
    {P : FiniteTransportPresentation.{u}} {U : AtomCarrier.{u}}
    (data : TwoLayerTransportData.{u, v} P U)
    {source target : P.Vertex}
    {before after : CellChainNode P source target}
    (step : CellChainStep P before after) :
    cellAuthoredFactor data step =
      upperOrientedFaceAuthoredComparator data 1
        step.toRewriteStep.face := by
  rcases step with
    ⟨cell, source_eq, target_eq, orientation, before_eq, after_eq⟩
  subst source
  subst target
  cases orientation <;>
    simp [cellAuthoredFactor, CellChainStep.toRewriteStep,
      upperOrientedFaceAuthoredComparator, upperOrientedFaceComparator,
      upperAuthoredComparatorFamily, castCompositeFiberAut]

/-- One canonical cell factor is exactly the existing upper oriented-face evaluator. -/
theorem cellCanonicalFactor_eq_upperOrientedFaceCanonicalComparator
    {P : FiniteTransportPresentation.{u}} {U : AtomCarrier.{u}}
    (data : TwoLayerTransportData.{u, v} P U)
    (reselection : UpperEdgeReselection data.lift)
    {source target : P.Vertex}
    {before after : CellChainNode P source target}
    (step : CellChainStep P before after) :
    cellCanonicalFactor data reselection step =
      upperOrientedFaceCanonicalComparator data reselection
        step.toRewriteStep.face := by
  rcases step with
    ⟨cell, source_eq, target_eq, orientation, before_eq, after_eq⟩
  subst source
  subst target
  cases orientation <;>
    simp [cellCanonicalFactor, CellChainStep.toRewriteStep,
      upperOrientedFaceCanonicalComparator, upperOrientedFaceComparator,
      upperCanonicalComparatorFamily, castCompositeFiberAut]

/-- The authored cell-chain word uses the reviewed upper pasting convention. -/
theorem cellAuthoredWord_eq_upperAuthoredPastingComparator
    {P : FiniteTransportPresentation.{u}} {U : AtomCarrier.{u}}
    (data : TwoLayerTransportData.{u, v} P U)
    {source target : P.Vertex}
    {first last : CellChainNode P source target}
    (chain : CellChain P first last) :
    cellAuthoredWord data chain =
      upperAuthoredPastingComparator data 1 chain.toRewritePasting := by
  induction chain with
  | nil node => rfl
  | cons step tail inductionHypothesis =>
      simp only [cellAuthoredWord, CellChain.toRewritePasting,
        upperAuthoredPastingComparator, upperPastingComparator]
      rw [inductionHypothesis,
        cellAuthoredFactor_eq_upperOrientedFaceAuthoredComparator]
      rfl

/-- The canonical cell-chain word uses the reviewed upper pasting convention. -/
theorem cellCanonicalWord_eq_upperCanonicalPastingComparator
    {P : FiniteTransportPresentation.{u}} {U : AtomCarrier.{u}}
    (data : TwoLayerTransportData.{u, v} P U)
    (reselection : UpperEdgeReselection data.lift)
    {source target : P.Vertex}
    {first last : CellChainNode P source target}
    (chain : CellChain P first last) :
    cellCanonicalWord data reselection chain =
      upperCanonicalPastingComparator data reselection
        chain.toRewritePasting := by
  induction chain with
  | nil node => rfl
  | cons step tail inductionHypothesis =>
      simp only [cellCanonicalWord, CellChain.toRewritePasting,
        upperCanonicalPastingComparator, upperPastingComparator]
      rw [inductionHypothesis,
        cellCanonicalFactor_eq_upperOrientedFaceCanonicalComparator]
      rfl

/-- Reversing a step inverts its authored affine factor. -/
theorem cellAuthoredFactor_reverse
    {P : FiniteTransportPresentation.{u}} {U : AtomCarrier.{u}}
    (data : TwoLayerTransportData.{u, v} P U)
    {source target : P.Vertex}
    {before after : CellChainNode P source target}
    (step : CellChainStep P before after) :
    cellAuthoredFactor data step.reverse =
      (cellAuthoredFactor data step)⁻¹ := by
  rcases step with
    ⟨cell, source_eq, target_eq, orientation, before_eq, after_eq⟩
  cases orientation <;>
    simp [CellChainStep.reverse, cellAuthoredFactor]

/-- Reversing a step inverts its canonical affine factor. -/
theorem cellCanonicalFactor_reverse
    {P : FiniteTransportPresentation.{u}} {U : AtomCarrier.{u}}
    (data : TwoLayerTransportData.{u, v} P U)
    (reselection : UpperEdgeReselection data.lift)
    {source target : P.Vertex}
    {before after : CellChainNode P source target}
    (step : CellChainStep P before after) :
    cellCanonicalFactor data reselection step.reverse =
      (cellCanonicalFactor data reselection step)⁻¹ := by
  rcases step with
    ⟨cell, source_eq, target_eq, orientation, before_eq, after_eq⟩
  cases orientation <;>
    simp [CellChainStep.reverse, cellCanonicalFactor]

/-- Authored words turn chain concatenation into reversed-order multiplication. -/
theorem cellAuthoredWord_append
    {P : FiniteTransportPresentation.{u}} {U : AtomCarrier.{u}}
    (data : TwoLayerTransportData.{u, v} P U)
    {source target : P.Vertex}
    {first middle last : CellChainNode P source target}
    (head : CellChain P first middle) (tail : CellChain P middle last) :
    cellAuthoredWord data (head.append tail) =
      cellAuthoredWord data tail * cellAuthoredWord data head := by
  induction head with
  | nil node => simp [CellChain.append, cellAuthoredWord]
  | cons step rest inductionHypothesis =>
      simp only [CellChain.append, cellAuthoredWord]
      rw [inductionHypothesis]
      exact mul_assoc _ _ _

/-- Canonical words obey the same concatenation order at every reselection. -/
theorem cellCanonicalWord_append
    {P : FiniteTransportPresentation.{u}} {U : AtomCarrier.{u}}
    (data : TwoLayerTransportData.{u, v} P U)
    (reselection : UpperEdgeReselection data.lift)
    {source target : P.Vertex}
    {first middle last : CellChainNode P source target}
    (head : CellChain P first middle) (tail : CellChain P middle last) :
    cellCanonicalWord data reselection (head.append tail) =
      cellCanonicalWord data reselection tail *
        cellCanonicalWord data reselection head := by
  induction head with
  | nil node => simp [CellChain.append, cellCanonicalWord]
  | cons step rest inductionHypothesis =>
      simp only [CellChain.append, cellCanonicalWord]
      rw [inductionHypothesis]
      exact mul_assoc _ _ _

/-- Route transport has the two-sided word normal form before using closedness. -/
theorem cellRouteTransport_apply
    {P : FiniteTransportPresentation.{u}} {U : AtomCarrier.{u}}
    (data : TwoLayerTransportData.{u, v} P U)
    {source target : P.Vertex}
    {first last : CellChainNode P source target}
    (chain : CellChain P first last)
    (coordinate : CompositeFiberAut (data.lift.geometry target)) :
    CellRouteTransport data chain coordinate =
      cellAuthoredWord data chain * coordinate *
        (cellCanonicalWord data 1 chain)⁻¹ := by
  induction chain generalizing coordinate with
  | nil node => simp [CellRouteTransport, cellAuthoredWord, cellCanonicalWord]
  | cons step tail inductionHypothesis =>
      simp only [CellRouteTransport, Equiv.trans_apply, CellAffineStep,
        cellGaugeAffineEquiv, cellAuthoredWord, cellCanonicalWord]
      change CellRouteTransport data tail
          (cellAuthoredFactor data step * coordinate *
            (cellCanonicalFactor data 1 step)⁻¹) = _
      rw [inductionHypothesis]
      group

/-! ## Canonical thinness and telescoping -/

/-- The hom represented by a product uses the categorical composition order. -/
@[simp]
theorem compositeFiberAut_hom_mul
    {U : AtomCarrier.{u}} {G : GeometryPackage.{u, v} U}
    (left right : CompositeFiberAut G) :
    CompositeFiberAut.hom (left * right) =
      (CompositeFiberAut.hom right).comp (CompositeFiberAut.hom left) :=
  rfl

/-- The hom represented by the identity coordinate is the identity morphism. -/
@[simp]
theorem compositeFiberAut_hom_one
    {U : AtomCarrier.{u}} {G : GeometryPackage.{u, v} U} :
    CompositeFiberAut.hom (1 : CompositeFiberAut G) = 𝟙 G :=
  rfl

/--
One oriented canonical factor identifies the step's semantic input and output
path lifts.  The endpoint equalities are consumed here, not stored in a
factorization certificate.
-/
theorem cellCanonicalFactor_fac
    {P : FiniteTransportPresentation.{u}} {U : AtomCarrier.{u}}
    (data : TwoLayerTransportData.{u, v} P U)
    (reselection : UpperEdgeReselection data.lift)
    {source target : P.Vertex}
    {before after : CellChainNode P source target}
    (step : CellChainStep P before after) :
    (upperReselectedPathLift data.lift reselection before.path).comp
        (CompositeFiberAut.hom
          (cellCanonicalFactor data reselection step)) =
      upperReselectedPathLift data.lift reselection after.path := by
  rcases step with
    ⟨cell, source_eq, target_eq, orientation, before_eq, after_eq⟩
  subst source
  subst target
  cases orientation with
  | forward =>
      simp only [orientedCellBeforePath, orientedCellAfterPath,
        castPresentedPath] at before_eq after_eq
      rw [before_eq, after_eq]
      simpa only [cellCanonicalFactor, castCompositeFiberAut] using
        upperCanonicalTwoCellComparator_fac data reselection cell
  | backward =>
      simp only [orientedCellBeforePath, orientedCellAfterPath,
        castPresentedPath] at before_eq after_eq
      rw [before_eq, after_eq]
      simpa only [cellCanonicalFactor, castCompositeFiberAut] using
        upperCanonicalTwoCellComparator_inv_fac data reselection cell

/--
The canonical word of an arbitrary typed route identifies its endpoint path
lifts.  This is the telescoping statement before specializing to a loop.
-/
theorem cellCanonicalWord_fac
    {P : FiniteTransportPresentation.{u}} {U : AtomCarrier.{u}}
    (data : TwoLayerTransportData.{u, v} P U)
    (reselection : UpperEdgeReselection data.lift)
    {source target : P.Vertex}
    {first last : CellChainNode P source target}
    (chain : CellChain P first last) :
    (upperReselectedPathLift data.lift reselection first.path).comp
        (CompositeFiberAut.hom
          (cellCanonicalWord data reselection chain)) =
      upperReselectedPathLift data.lift reselection last.path := by
  induction chain with
  | nil node =>
      simp only [cellCanonicalWord, compositeFiberAut_hom_one]
      exact @Category.comp_id
        (GeomReadCategory.{u, v} U) (geometryTotalCategory U)
        _ _ (upperReselectedPathLift data.lift reselection node.path)
  | cons step tail inductionHypothesis =>
      simp only [cellCanonicalWord, compositeFiberAut_hom_mul]
      calc
        (upperReselectedPathLift data.lift reselection _).comp
            ((CompositeFiberAut.hom
              (cellCanonicalFactor data reselection step)).comp
              (CompositeFiberAut.hom
                (cellCanonicalWord data reselection tail))) =
          ((upperReselectedPathLift data.lift reselection _).comp
            (CompositeFiberAut.hom
              (cellCanonicalFactor data reselection step))).comp
              (CompositeFiberAut.hom
                (cellCanonicalWord data reselection tail)) :=
            (@Category.assoc
              (GeomReadCategory.{u, v} U) (geometryTotalCategory U)
              _ _ _ _
              (upperReselectedPathLift data.lift reselection _)
              (CompositeFiberAut.hom
                (cellCanonicalFactor data reselection step))
              (CompositeFiberAut.hom
                (cellCanonicalWord data reselection tail))).symm
        _ = (upperReselectedPathLift data.lift reselection _).comp
              (CompositeFiberAut.hom
                (cellCanonicalWord data reselection tail)) := by
          rw [cellCanonicalFactor_fac data reselection step]
        _ = upperReselectedPathLift data.lift reselection _ :=
          inductionHypothesis

/-- Every closed canonical word is identity, at every edge reselection. -/
theorem cellCanonicalWord_closed_eq_one
    {P : FiniteTransportPresentation.{u}} {U : AtomCarrier.{u}}
    (data : TwoLayerTransportData.{u, v} P U)
    (reselection : UpperEdgeReselection data.lift)
    {source target : P.Vertex}
    {node : CellChainNode P source target}
    (chain : CellChain P node node) :
    cellCanonicalWord data reselection chain = 1 := by
  let lift := upperReselectedPathLift data.lift reselection node.path
  letI : (crossStageProjection.{u, v} U).IsStronglyCocartesian
      lift.base.base lift :=
    (upperReselectLiftData data.lift reselection).pathLift_compositeStrong
      node.path
  apply CompositeFiberAut.ext_of_strong_fac lift
  calc
    lift.comp (CompositeFiberAut.hom
        (cellCanonicalWord data reselection chain)) = lift :=
      cellCanonicalWord_fac data reselection chain
    _ = lift.comp (CompositeFiberAut.hom
        (1 : CompositeFiberAut (data.lift.geometry target))) := by
      rw [compositeFiberAut_hom_one]
      exact (@Category.comp_id
        (GeomReadCategory.{u, v} U) (geometryTotalCategory U)
        _ _ lift).symm

/-! ## Closed-chain coherence -/

/-- Holonomy is route transport evaluated at the identity coordinate. -/
noncomputable def CellChainHolonomy
    {P : FiniteTransportPresentation.{u}} {U : AtomCarrier.{u}}
    (data : TwoLayerTransportData.{u, v} P U)
    {source target : P.Vertex}
    {node : CellChainNode P source target}
    (chain : CellChain P node node) :
    CompositeFiberAut (data.lift.geometry target) :=
  CellRouteTransport data chain 1

/--
Cell-chain coherence is universal identity of closed affine route transport.
No section, potential, orbit membership, or gauge existence occurs here.
-/
def CellChainCoherent
    {P : FiniteTransportPresentation.{u}} {U : AtomCarrier.{u}}
    (data : TwoLayerTransportData.{u, v} P U) : Prop :=
  ∀ (source target : P.Vertex) (node : CellChainNode P source target)
    (chain : CellChain P node node),
    CellRouteTransport data chain = Equiv.refl _

/-- Closed route transport is left multiplication by its holonomy. -/
theorem cellRouteTransport_closed_apply
    {P : FiniteTransportPresentation.{u}} {U : AtomCarrier.{u}}
    (data : TwoLayerTransportData.{u, v} P U)
    {source target : P.Vertex}
    {node : CellChainNode P source target}
    (chain : CellChain P node node)
    (coordinate : CompositeFiberAut (data.lift.geometry target)) :
    CellRouteTransport data chain coordinate =
      CellChainHolonomy data chain * coordinate := by
  rw [cellRouteTransport_apply,
    cellCanonicalWord_closed_eq_one data 1 chain]
  simp only [inv_one, mul_one]
  unfold CellChainHolonomy
  rw [cellRouteTransport_apply,
    cellCanonicalWord_closed_eq_one data 1 chain]
  simp

/-- Canonical thinness identifies holonomy with the authored closed word. -/
theorem cellChainHolonomy_eq_authoredWord
    {P : FiniteTransportPresentation.{u}} {U : AtomCarrier.{u}}
    (data : TwoLayerTransportData.{u, v} P U)
    {source target : P.Vertex}
    {node : CellChainNode P source target}
    (chain : CellChain P node node) :
    CellChainHolonomy data chain = cellAuthoredWord data chain := by
  unfold CellChainHolonomy
  rw [cellRouteTransport_apply,
    cellCanonicalWord_closed_eq_one data 1 chain]
  simp

/--
Changing the base node of a closed route conjugates holonomy by the authored
word along the connecting half-route.
-/
theorem cellChainHolonomy_rotate
    {P : FiniteTransportPresentation.{u}} {U : AtomCarrier.{u}}
    (data : TwoLayerTransportData.{u, v} P U)
    {source target : P.Vertex}
    {first second : CellChainNode P source target}
    (outbound : CellChain P first second)
    (inbound : CellChain P second first) :
    CellChainHolonomy data (inbound.append outbound) =
      cellAuthoredWord data outbound *
        CellChainHolonomy data (outbound.append inbound) *
          (cellAuthoredWord data outbound)⁻¹ := by
  rw [cellChainHolonomy_eq_authoredWord,
    cellChainHolonomy_eq_authoredWord,
    cellAuthoredWord_append, cellAuthoredWord_append]
  group

/-- Holonomy vanishing is invariant under changing the base node of a loop. -/
theorem cellChainHolonomy_rotate_eq_one_iff
    {P : FiniteTransportPresentation.{u}} {U : AtomCarrier.{u}}
    (data : TwoLayerTransportData.{u, v} P U)
    {source target : P.Vertex}
    {first second : CellChainNode P source target}
    (outbound : CellChain P first second)
    (inbound : CellChain P second first) :
    CellChainHolonomy data (inbound.append outbound) = 1 ↔
      CellChainHolonomy data (outbound.append inbound) = 1 := by
  constructor
  · intro rotatedIdentity
    let conjugator := cellAuthoredWord data outbound
    have conjugacy := cellChainHolonomy_rotate data outbound inbound
    calc
      CellChainHolonomy data (outbound.append inbound) =
          conjugator⁻¹ *
            CellChainHolonomy data (inbound.append outbound) *
              conjugator := by
        dsimp only [conjugator]
        rw [conjugacy]
        group
      _ = 1 := by rw [rotatedIdentity]; simp
  · intro baseIdentity
    rw [cellChainHolonomy_rotate data outbound inbound, baseIdentity]
    simp

/-- Raw defect carried by one oriented cell-graph arrow. -/
noncomputable def cellRawDefectFactor
    {P : FiniteTransportPresentation.{u}} {U : AtomCarrier.{u}}
    (data : TwoLayerTransportData.{u, v} P U)
    {source target : P.Vertex}
    {before after : CellChainNode P source target}
    (step : CellChainStep P before after) :
    CompositeFiberAut (data.lift.geometry target) :=
  cellAuthoredFactor data step * (cellCanonicalFactor data 1 step)⁻¹

/-- On a declared forward cell, the oriented defect is the reviewed upper raw defect. -/
theorem cellRawDefectFactor_forward_eq_upperRaw
    {P : FiniteTransportPresentation.{u}} {U : AtomCarrier.{u}}
    (data : TwoLayerTransportData.{u, v} P U) (cell : P.TwoCell) :
    cellRawDefectFactor data (CellChainStep.forward cell) =
      upperRawTwoCellDefect data 1 cell := by
  simp only [cellRawDefectFactor, cellAuthoredFactor,
    cellCanonicalFactor, CellChainStep.forward, castCompositeFiberAut,
    upperRawTwoCellDefect]

/-- Parallel arrows have the same canonical factor by strong cancellation. -/
theorem cellCanonicalFactor_eq_of_parallel
    {P : FiniteTransportPresentation.{u}} {U : AtomCarrier.{u}}
    (data : TwoLayerTransportData.{u, v} P U)
    (reselection : UpperEdgeReselection data.lift)
    {source target : P.Vertex}
    {left right : CellChainNode P source target}
    (first second : CellChainStep P left right) :
    cellCanonicalFactor data reselection first =
      cellCanonicalFactor data reselection second := by
  let lift := upperReselectedPathLift data.lift reselection left.path
  letI : (crossStageProjection.{u, v} U).IsStronglyCocartesian
      lift.base.base lift :=
    (upperReselectLiftData data.lift reselection).pathLift_compositeStrong
      left.path
  apply CompositeFiberAut.ext_of_strong_fac lift
  exact (cellCanonicalFactor_fac data reselection first).trans
    (cellCanonicalFactor_fac data reselection second).symm

/-- The two-step loop comparing parallel arrows starts at their common right node. -/
def parallelCellTwoChain
    {P : FiniteTransportPresentation.{u}}
    {source target : P.Vertex}
    {left right : CellChainNode P source target}
    (first second : CellChainStep P left right) : CellChain P right right :=
  .cons second.reverse (.cons first (.nil right))

/-- Parallel two-chain holonomy is the authored comparator ratio. -/
theorem parallelCellTwoChain_holonomy
    {P : FiniteTransportPresentation.{u}} {U : AtomCarrier.{u}}
    (data : TwoLayerTransportData.{u, v} P U)
    {source target : P.Vertex}
    {left right : CellChainNode P source target}
    (first second : CellChainStep P left right) :
    CellChainHolonomy data (parallelCellTwoChain first second) =
      cellAuthoredFactor data first * (cellAuthoredFactor data second)⁻¹ := by
  rw [cellChainHolonomy_eq_authoredWord]
  simp only [parallelCellTwoChain, cellAuthoredWord,
    cellAuthoredFactor_reverse, one_mul]

/-- Parallel two-chain holonomy is also the ratio of its oriented raw defects. -/
theorem parallelCellTwoChain_holonomy_eq_rawDefectRatio
    {P : FiniteTransportPresentation.{u}} {U : AtomCarrier.{u}}
    (data : TwoLayerTransportData.{u, v} P U)
    {source target : P.Vertex}
    {left right : CellChainNode P source target}
    (first second : CellChainStep P left right) :
    CellChainHolonomy data (parallelCellTwoChain first second) =
      cellRawDefectFactor data first *
        (cellRawDefectFactor data second)⁻¹ := by
  rw [parallelCellTwoChain_holonomy]
  unfold cellRawDefectFactor
  rw [cellCanonicalFactor_eq_of_parallel data 1 first second]
  group

/-- Universal route identity is equivalent to identity of every holonomy. -/
theorem cellChainCoherent_iff_holonomy_eq_one
    {P : FiniteTransportPresentation.{u}} {U : AtomCarrier.{u}}
    (data : TwoLayerTransportData.{u, v} P U) :
    CellChainCoherent data ↔
      ∀ (source target : P.Vertex)
        (node : CellChainNode P source target)
        (chain : CellChain P node node),
        CellChainHolonomy data chain = 1 := by
  constructor
  · intro coherent source target node chain
    have identityAtOne := congrArg
      (fun equivalence :
        CompositeFiberAut (data.lift.geometry target) ≃
          CompositeFiberAut (data.lift.geometry target) => equivalence 1)
      (coherent source target node chain)
    simpa only [CellChainHolonomy, Equiv.refl_apply] using identityAtOne
  · intro holonomyIdentity source target node chain
    apply Equiv.ext
    intro coordinate
    rw [cellRouteTransport_closed_apply,
      holonomyIdentity source target node chain]
    exact one_mul coordinate

/-! ## General necessity of chain coherence -/

/-- Actual total coherence identifies each authored and canonical comparator. -/
theorem authoredComparator_eq_canonical_of_crossStageCoherentAt
    {P : FiniteTransportPresentation.{u}} {U : AtomCarrier.{u}}
    (data : TwoLayerTransportData.{u, v} P U)
    (reselection : UpperEdgeReselection data.lift)
    (coherent : CrossStageCoherentAt data reselection)
    (cell : P.TwoCell) :
    data.comparator cell =
      upperCanonicalTwoCellComparator data reselection cell := by
  have rawIdentity := congrFun
    ((crossStageCoherentAt_iff_rawCochain_identity data reselection).1 coherent)
    cell
  exact (upperRawTwoCellDefect_eq_one_iff data reselection cell).1 rawIdentity

/-- Under actual total coherence, every authored step factor is canonical. -/
theorem cellAuthoredFactor_eq_canonical_of_crossStageCoherentAt
    {P : FiniteTransportPresentation.{u}} {U : AtomCarrier.{u}}
    (data : TwoLayerTransportData.{u, v} P U)
    (reselection : UpperEdgeReselection data.lift)
    (coherent : CrossStageCoherentAt data reselection)
    {source target : P.Vertex}
    {before after : CellChainNode P source target}
    (step : CellChainStep P before after) :
    cellAuthoredFactor data step =
      cellCanonicalFactor data reselection step := by
  rcases step with
    ⟨cell, source_eq, target_eq, orientation, before_eq, after_eq⟩
  have comparator_eq :=
    authoredComparator_eq_canonical_of_crossStageCoherentAt
      data reselection coherent cell
  cases orientation <;>
    simp only [cellAuthoredFactor, cellCanonicalFactor] <;>
    rw [comparator_eq]

/-- Under actual total coherence, authored and canonical words agree on all routes. -/
theorem cellAuthoredWord_eq_canonical_of_crossStageCoherentAt
    {P : FiniteTransportPresentation.{u}} {U : AtomCarrier.{u}}
    (data : TwoLayerTransportData.{u, v} P U)
    (reselection : UpperEdgeReselection data.lift)
    (coherent : CrossStageCoherentAt data reselection)
    {source target : P.Vertex}
    {first last : CellChainNode P source target}
    (chain : CellChain P first last) :
    cellAuthoredWord data chain =
      cellCanonicalWord data reselection chain := by
  induction chain with
  | nil node => rfl
  | cons step tail inductionHypothesis =>
      simp only [cellAuthoredWord, cellCanonicalWord]
      rw [inductionHypothesis,
        cellAuthoredFactor_eq_canonical_of_crossStageCoherentAt
          data reselection coherent step]

/-- Any actual total coherent gauge forces universal closed-chain coherence. -/
theorem crossStageCoherentAt_cellChainCoherent
    {P : FiniteTransportPresentation.{u}} {U : AtomCarrier.{u}}
    (data : TwoLayerTransportData.{u, v} P U)
    (reselection : UpperEdgeReselection data.lift)
    (coherent : CrossStageCoherentAt data reselection) :
    CellChainCoherent data := by
  apply (cellChainCoherent_iff_holonomy_eq_one data).2
  intro source target node chain
  rw [cellChainHolonomy_eq_authoredWord,
    cellAuthoredWord_eq_canonical_of_crossStageCoherentAt
      data reselection coherent chain,
    cellCanonicalWord_closed_eq_one data reselection chain]

/-- T2: joint vanishing implies cell-chain coherence on every presentation. -/
theorem jointVanishes_cellChainCoherent
    {P : FiniteTransportPresentation.{u}} {U : AtomCarrier.{u}}
    (data : TwoLayerTransportData.{u, v} P U) :
    JointVanishes data → CellChainCoherent data := by
  intro joint
  obtain ⟨reselection, coherent⟩ :=
    (jointVanishes_iff_crossStageCoherentizable data).1 joint
  exact crossStageCoherentAt_cellChainCoherent data reselection coherent

end AAT.AG.CrossStageCoherence

#assert_standard_axioms_only AAT.AG.CrossStageCoherence
