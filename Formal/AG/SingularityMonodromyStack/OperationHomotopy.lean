import Mathlib.GroupTheory.PresentedGroup
import Formal.AG.SingularityMonodromyStack.OperationCategory

noncomputable section

namespace AAT.AG
namespace SingularityMonodromyStack

universe u v w x y z q

/--
VI.定義9.3: selected operation homotopy generator family.

Each generator is a finite selected path-pair relation with common endpoints.
Finite loop relators are recorded separately at selected base states. The family
is chosen data, so different choices of `H` give different `pi_1^AAT`
readings.
-/
structure HomotopyGeneratorFamily {U : AtomCarrier.{u}} {A : ArchitectureObject U}
    {S : Site.AATSite A} {P : StratumReadingParameter S}
    {k : Type v} [CommRing k]
    {X : ArchitectureStratum.{u, v, w, x, y} P k}
    {G : OperationCategoryData.{u, v, w, x, y, z} X}
    (R : RefactorEndpointReading.{u, v, w, x, y, z} G) where
  PathCell : Type z
  [pathCellFintype : Fintype PathCell]
  cellSource : PathCell -> G.State
  cellTarget : PathCell -> G.State
  leftPath : (h : PathCell) -> OperationPath G (cellSource h) (cellTarget h)
  rightPath : (h : PathCell) -> OperationPath G (cellSource h) (cellTarget h)
  LoopRelator : Type z
  [loopRelatorFintype : Fintype LoopRelator]
  relatorBase : LoopRelator -> G.State
  relatorLoop : (r : LoopRelator) -> OperationLoop R
  relator_based :
    ∀ r : LoopRelator, (relatorLoop r).base = relatorBase r

attribute [instance] HomotopyGeneratorFamily.pathCellFintype
attribute [instance] HomotopyGeneratorFamily.loopRelatorFintype

namespace HomotopyGeneratorFamily

variable {U : AtomCarrier.{u}} {A : ArchitectureObject U}
variable {S : Site.AATSite A} {P : StratumReadingParameter S}
variable {k : Type v} [CommRing k]
variable {X : ArchitectureStratum.{u, v, w, x, y} P k}
variable {G : OperationCategoryData.{u, v, w, x, y, z} X}
variable {R : RefactorEndpointReading.{u, v, w, x, y, z} G}

/-- VI.定義9.3: a homotopy generator carries two paths with common endpoints. -/
theorem pathCell_commonEndpoints
    (H : HomotopyGeneratorFamily.{u, v, w, x, y, z} R)
    (h : H.PathCell) :
    (H.leftPath h : OperationPath G (H.cellSource h) (H.cellTarget h)) =
      H.leftPath h ∧
    (H.rightPath h : OperationPath G (H.cellSource h) (H.cellTarget h)) =
      H.rightPath h :=
  ⟨rfl, rfl⟩

/-- VI.定義9.3: expose the selected relator base certificate. -/
theorem relator_based_holds
    (H : HomotopyGeneratorFamily.{u, v, w, x, y, z} R)
    (r : H.LoopRelator) :
    (H.relatorLoop r).base = H.relatorBase r :=
  H.relator_based r

end HomotopyGeneratorFamily

/--
VI.定義9.4: presentation two-complex.

Vertices are selected architecture states, edges index selected operation edges,
and 2-cells are selected homotopy generators. This is a presentation surface,
not an unselected homotopy or infinity-groupoid.
-/
structure PresentationTwoComplex {U : AtomCarrier.{u}} {A : ArchitectureObject U}
    {S : Site.AATSite A} {P : StratumReadingParameter S}
    {k : Type v} [CommRing k]
    {X : ArchitectureStratum.{u, v, w, x, y} P k}
    {G : OperationCategoryData.{u, v, w, x, y, z} X}
    {R : RefactorEndpointReading.{u, v, w, x, y, z} G}
    (H : HomotopyGeneratorFamily.{u, v, w, x, y, z} R) where
  Vertex : Type z
  vertexEquivState : Vertex ≃ G.State
  Edge : Type z
  edgeBoundary : Edge ≃ Σ a : G.State, Σ b : G.State, SelectedOperation G a b
  TwoCell : Type z
  twoCellEquivGenerator : TwoCell ≃ H.PathCell

namespace PresentationTwoComplex

variable {U : AtomCarrier.{u}} {A : ArchitectureObject U}
variable {S : Site.AATSite A} {P : StratumReadingParameter S}
variable {k : Type v} [CommRing k]
variable {X : ArchitectureStratum.{u, v, w, x, y} P k}
variable {G : OperationCategoryData.{u, v, w, x, y, z} X}
variable {R : RefactorEndpointReading.{u, v, w, x, y, z} G}
variable {H : HomotopyGeneratorFamily.{u, v, w, x, y, z} R}

/-- VI.定義9.4: selected vertices are equivalent to selected operation states. -/
def vertices_read_states
    (K : PresentationTwoComplex.{u, v, w, x, y, z} H) :
    K.Vertex ≃ G.State :=
  K.vertexEquivState

/-- VI.定義9.4: selected 2-cells are equivalent to selected homotopy generators. -/
def twoCells_read_generators
    (K : PresentationTwoComplex.{u, v, w, x, y, z} H) :
    K.TwoCell ≃ H.PathCell :=
  K.twoCellEquivGenerator

end PresentationTwoComplex

/-- VI.定義9.5: an oriented edge or selected refactor identification with typed endpoints. -/
inductive FormalEdgeStep {U : AtomCarrier.{u}} {A : ArchitectureObject U}
    {S : Site.AATSite A} {P : StratumReadingParameter S}
    {k : Type v} [CommRing k]
    {X : ArchitectureStratum.{u, v, w, x, y} P k}
    {G : OperationCategoryData.{u, v, w, x, y, z} X}
    {R : RefactorEndpointReading.{u, v, w, x, y, z} G}
    {H : HomotopyGeneratorFamily.{u, v, w, x, y, z} R}
    (K : PresentationTwoComplex.{u, v, w, x, y, z} H) :
    G.State -> G.State -> Type z where
  | forward (edge : K.Edge) :
      FormalEdgeStep K (K.edgeBoundary edge).1 (K.edgeBoundary edge).2.1
  | backward (edge : K.Edge) :
      FormalEdgeStep K (K.edgeBoundary edge).2.1 (K.edgeBoundary edge).1
  | refactor {a b : G.State} (h : R.RefactorEquivalent a b) :
      FormalEdgeStep K a b

namespace FormalEdgeStep

variable {U : AtomCarrier.{u}} {A : ArchitectureObject U}
variable {S : Site.AATSite A} {P : StratumReadingParameter S}
variable {k : Type v} [CommRing k]
variable {X : ArchitectureStratum.{u, v, w, x, y} P k}
variable {G : OperationCategoryData.{u, v, w, x, y, z} X}
variable {R : RefactorEndpointReading.{u, v, w, x, y, z} G}
variable {H : HomotopyGeneratorFamily.{u, v, w, x, y, z} R}
variable {K : PresentationTwoComplex.{u, v, w, x, y, z} H}

/-- VI.定義9.5: reverse the orientation of one formal edge step. -/
def reverse {a b : G.State} :
    FormalEdgeStep.{u, v, w, x, y, z} K a b -> FormalEdgeStep K b a
  | .forward edge => .backward edge
  | .backward edge => .forward edge
  | .refactor h => .refactor (R.symm h)

/-- VI.定義9.5: read an oriented step in the free group on presentation edges. -/
def toFreeGroup {a b : G.State}
    (step : FormalEdgeStep.{u, v, w, x, y, z} K a b) : FreeGroup K.Edge :=
  match step with
  | .forward edge => FreeGroup.of edge
  | .backward edge => (FreeGroup.of edge)⁻¹
  | .refactor _ => 1

@[simp] theorem toFreeGroup_refactor {a b : G.State}
    (h : R.RefactorEquivalent a b) :
    (FormalEdgeStep.refactor (K := K) h).toFreeGroup = 1 :=
  rfl

@[simp] theorem toFreeGroup_reverse {a b : G.State}
    (step : FormalEdgeStep.{u, v, w, x, y, z} K a b) :
    step.reverse.toFreeGroup = step.toFreeGroup⁻¹ := by
  cases step <;> simp [reverse, toFreeGroup]

/-- VI.定義9.5: selected operation edge with endpoints transported through the edge equivalence. -/
def ofSelectedOperation {a b : G.State} (op : SelectedOperation G a b) :
    FormalEdgeStep.{u, v, w, x, y, z} K a b := by
  let edge := K.edgeBoundary.symm ⟨a, b, op⟩
  have hedge : K.edgeBoundary edge = ⟨a, b, op⟩ :=
    K.edgeBoundary.apply_symm_apply ⟨a, b, op⟩
  have hsource : (K.edgeBoundary edge).1 = a := congrArg Sigma.fst hedge
  have htarget : (K.edgeBoundary edge).2.1 = b :=
    congrArg (fun boundary => boundary.2.1) hedge
  rw [← hsource, ← htarget]
  exact .forward edge

end FormalEdgeStep

/-- VI.定義9.5: finite formal edge paths with composability enforced by indices. -/
inductive FormalEdgePath {U : AtomCarrier.{u}} {A : ArchitectureObject U}
    {S : Site.AATSite A} {P : StratumReadingParameter S}
    {k : Type v} [CommRing k]
    {X : ArchitectureStratum.{u, v, w, x, y} P k}
    {G : OperationCategoryData.{u, v, w, x, y, z} X}
    {R : RefactorEndpointReading.{u, v, w, x, y, z} G}
    {H : HomotopyGeneratorFamily.{u, v, w, x, y, z} R}
    (K : PresentationTwoComplex.{u, v, w, x, y, z} H) :
    G.State -> G.State -> Type z where
  | nil (a : G.State) : FormalEdgePath K a a
  | cons {a b c : G.State} :
      FormalEdgeStep K a b -> FormalEdgePath K b c -> FormalEdgePath K a c

namespace FormalEdgePath

variable {U : AtomCarrier.{u}} {A : ArchitectureObject U}
variable {S : Site.AATSite A} {P : StratumReadingParameter S}
variable {k : Type v} [CommRing k]
variable {X : ArchitectureStratum.{u, v, w, x, y} P k}
variable {G : OperationCategoryData.{u, v, w, x, y, z} X}
variable {R : RefactorEndpointReading.{u, v, w, x, y, z} G}
variable {H : HomotopyGeneratorFamily.{u, v, w, x, y, z} R}
variable {K : PresentationTwoComplex.{u, v, w, x, y, z} H}

/-- VI.定義9.5: concatenate two endpoint-compatible formal paths. -/
def concat {a b c : G.State} :
    FormalEdgePath K a b -> FormalEdgePath K b c -> FormalEdgePath K a c
  | .nil _, q => q
  | .cons step rest, q => .cons step (concat rest q)

/-- VI.定義9.5: reverse a formal path and every oriented step in it. -/
def reverse {a b : G.State} : FormalEdgePath K a b -> FormalEdgePath K b a
  | .nil a => .nil a
  | .cons step rest =>
      concat (reverse rest) (.cons step.reverse (.nil _))

/-- VI.定義9.5: read a typed formal path as a free-group word. -/
def toFreeGroup {a b : G.State} : FormalEdgePath K a b -> FreeGroup K.Edge
  | .nil _ => 1
  | .cons step rest => step.toFreeGroup * toFreeGroup rest

@[simp] theorem toFreeGroup_single_refactor {a b : G.State}
    (h : R.RefactorEquivalent a b) :
    (FormalEdgePath.cons (FormalEdgeStep.refactor (K := K) h)
      (FormalEdgePath.nil b)).toFreeGroup = 1 := by
  simp [toFreeGroup]

@[simp] theorem toFreeGroup_concat {a b c : G.State}
    (p : FormalEdgePath K a b) (q : FormalEdgePath K b c) :
    (p.concat q).toFreeGroup = p.toFreeGroup * q.toFreeGroup := by
  induction p with
  | nil => simp [concat, toFreeGroup]
  | cons step rest ih => simp [concat, toFreeGroup, ih, mul_assoc]

@[simp] theorem toFreeGroup_reverse {a b : G.State}
    (p : FormalEdgePath K a b) :
    p.reverse.toFreeGroup = p.toFreeGroup⁻¹ := by
  induction p with
  | nil => simp [reverse, toFreeGroup]
  | cons step rest ih =>
      simp [reverse, toFreeGroup, ih]

/-- VI.定義9.5: number of formal steps in a typed path. -/
def length {a b : G.State} : FormalEdgePath K a b -> Nat
  | .nil _ => 0
  | .cons _ rest => rest.length + 1

end FormalEdgePath

namespace OperationPath

variable {U : AtomCarrier.{u}} {A : ArchitectureObject U}
variable {S : Site.AATSite A} {P : StratumReadingParameter S}
variable {k : Type v} [CommRing k]
variable {X : ArchitectureStratum.{u, v, w, x, y} P k}
variable {G : OperationCategoryData.{u, v, w, x, y, z} X}
variable {R : RefactorEndpointReading.{u, v, w, x, y, z} G}
variable {H : HomotopyGeneratorFamily.{u, v, w, x, y, z} R}

/-- VI.定義9.5: read a selected operation path inside the presentation one-skeleton. -/
def toFormalEdgePath
    (K : PresentationTwoComplex.{u, v, w, x, y, z} H)
    {a b : G.State} : OperationPath G a b -> FormalEdgePath K a b
  | .nil a => .nil a
  | .cons op rest =>
      .cons (.ofSelectedOperation op) (toFormalEdgePath K rest)

end OperationPath

/-- VI.定義9.5: a selected free edge word is a typed loop at the selected base. -/
abbrev FreeEdgeWord {U : AtomCarrier.{u}} {A : ArchitectureObject U}
    {S : Site.AATSite A} {P : StratumReadingParameter S}
    {k : Type v} [CommRing k]
    {X : ArchitectureStratum.{u, v, w, x, y} P k}
    {G : OperationCategoryData.{u, v, w, x, y, z} X}
    {R : RefactorEndpointReading.{u, v, w, x, y, z} G}
    {H : HomotopyGeneratorFamily.{u, v, w, x, y, z} R}
    (K : PresentationTwoComplex.{u, v, w, x, y, z} H)
    (base : G.State) :=
  FormalEdgePath K base base

/-- VI.定義9.5: the based path-cell attaching loop computed from actual selected paths. -/
def pathCellRelatorPath {U : AtomCarrier.{u}} {A : ArchitectureObject U}
    {S : Site.AATSite A} {P : StratumReadingParameter S}
    {k : Type v} [CommRing k]
    {X : ArchitectureStratum.{u, v, w, x, y} P k}
    {G : OperationCategoryData.{u, v, w, x, y, z} X}
    {R : RefactorEndpointReading.{u, v, w, x, y, z} G}
    {H : HomotopyGeneratorFamily.{u, v, w, x, y, z} R}
    (K : PresentationTwoComplex.{u, v, w, x, y, z} H)
    {base : G.State} (h : H.PathCell)
    (connector : OperationPath G base (H.cellSource h)) : FreeEdgeWord K base :=
  let c := connector.toFormalEdgePath K
  let left := (H.leftPath h).toFormalEdgePath K
  let right := (H.rightPath h).toFormalEdgePath K
  c.concat (left.concat (right.reverse.concat c.reverse))

/-- VI.定義9.5: the based loop-relator path computed from its actual operation loop. -/
def loopRelatorPath {U : AtomCarrier.{u}} {A : ArchitectureObject U}
    {S : Site.AATSite A} {P : StratumReadingParameter S}
    {k : Type v} [CommRing k]
    {X : ArchitectureStratum.{u, v, w, x, y} P k}
    {G : OperationCategoryData.{u, v, w, x, y, z} X}
    {R : RefactorEndpointReading.{u, v, w, x, y, z} G}
    {H : HomotopyGeneratorFamily.{u, v, w, x, y, z} R}
    (K : PresentationTwoComplex.{u, v, w, x, y, z} H)
    {base : G.State} (r : H.LoopRelator)
    (connector : OperationPath G base (H.relatorLoop r).base) : FreeEdgeWord K base :=
  let c := connector.toFormalEdgePath K
  let gamma := (H.relatorLoop r).gamma.toFormalEdgePath K
  let close : FormalEdgePath K (H.relatorLoop r).endpoint (H.relatorLoop r).base :=
    .cons (.refactor (H.relatorLoop r).endpoint_equivalent) (.nil _)
  c.concat (gamma.concat (close.concat c.reverse))

/-- VI.定義9.5: a path-cell together with a selected path from the global base. -/
abbrev BasedPathCell {U : AtomCarrier.{u}} {A : ArchitectureObject U}
    {S : Site.AATSite A} {P : StratumReadingParameter S}
    {k : Type v} [CommRing k]
    {X : ArchitectureStratum.{u, v, w, x, y} P k}
    {G : OperationCategoryData.{u, v, w, x, y, z} X}
    {R : RefactorEndpointReading.{u, v, w, x, y, z} G}
    (H : HomotopyGeneratorFamily.{u, v, w, x, y, z} R)
    (base : G.State) :=
  Σ h : H.PathCell, OperationPath G base (H.cellSource h)

/-- VI.定義9.5: an operation-loop relator together with a path from the global base. -/
abbrev BasedLoopRelator {U : AtomCarrier.{u}} {A : ArchitectureObject U}
    {S : Site.AATSite A} {P : StratumReadingParameter S}
    {k : Type v} [CommRing k]
    {X : ArchitectureStratum.{u, v, w, x, y} P k}
    {G : OperationCategoryData.{u, v, w, x, y, z} X}
    {R : RefactorEndpointReading.{u, v, w, x, y, z} G}
    (H : HomotopyGeneratorFamily.{u, v, w, x, y, z} R)
    (base : G.State) :=
  Σ r : H.LoopRelator, OperationPath G base (H.relatorLoop r).base

/--
VI.定義9.5: presented architecture fundamental group package.

The quotient carrier and universal property are explicit selected data. This
keeps `pi_1^AAT(X,U,H,A)` relative to the chosen operation graph and generator
family.
-/
structure PresentedArchitectureFundamentalGroup {U : AtomCarrier.{u}}
    {A : ArchitectureObject U}
    {S : Site.AATSite A} {P : StratumReadingParameter S}
    {k : Type v} [CommRing k]
    {X : ArchitectureStratum.{u, v, w, x, y} P k}
    {G : OperationCategoryData.{u, v, w, x, y, z} X}
    {R : RefactorEndpointReading.{u, v, w, x, y, z} G}
    (H : HomotopyGeneratorFamily.{u, v, w, x, y, z} R)
    (base : G.State) where
  /-- Selected two-complex whose edges enumerate the selected operations. -/
  presentation : PresentationTwoComplex H
  FreeWord : Type z
  freeWordEquivSelected : FreeWord ≃ FreeEdgeWord presentation base
  Relator : FreeWord -> Prop
  pathCellRelatorWord : BasedPathCell H base -> FreeWord
  /-- The path-cell word is the actual connector-conjugated attaching path. -/
  pathCellRelator_path : ∀ h : BasedPathCell H base,
    freeWordEquivSelected (pathCellRelatorWord h) =
      pathCellRelatorPath presentation h.1 h.2
  pathCellRelator_selected : ∀ h : BasedPathCell H base, Relator (pathCellRelatorWord h)
  loopRelatorWord : BasedLoopRelator H base -> FreeWord
  /-- The loop-relator word is the actual connector-conjugated operation loop. -/
  loopRelator_path : ∀ r : BasedLoopRelator H base,
    freeWordEquivSelected (loopRelatorWord r) =
      loopRelatorPath presentation r.1 r.2
  loopRelator_selected : ∀ r : BasedLoopRelator H base, Relator (loopRelatorWord r)
  relator_generated_by_selected_generator :
    ∀ {w : FreeWord}, Relator w ->
      (∃ h : BasedPathCell H base, pathCellRelatorWord h = w) ∨
      (∃ r : BasedLoopRelator H base, loopRelatorWord r = w)
  Pi1 : Type z
  [pi1Group : Group Pi1]
  quotientMap : FreeWord -> Pi1
  relator_maps_to_identity : ∀ w : FreeWord, Relator w -> quotientMap w = 1
  FreeTransport : Type z
  QuotientTransport : Type z
  SendsRelatorsToIdentity : FreeTransport -> Prop
  FactorsThroughQuotient : FreeTransport -> QuotientTransport -> Prop
  quotientUniversalProperty :
    ∀ T : FreeTransport,
      SendsRelatorsToIdentity T ↔ ∃ Q : QuotientTransport, FactorsThroughQuotient T Q

attribute [instance] PresentedArchitectureFundamentalGroup.pi1Group

namespace PresentedArchitectureFundamentalGroup

variable {U : AtomCarrier.{u}} {A : ArchitectureObject U}
variable {S : Site.AATSite A} {P : StratumReadingParameter S}
variable {k : Type v} [CommRing k]
variable {X : ArchitectureStratum.{u, v, w, x, y} P k}
variable {G : OperationCategoryData.{u, v, w, x, y, z} X}
variable {R : RefactorEndpointReading.{u, v, w, x, y, z} G}
variable {H : HomotopyGeneratorFamily.{u, v, w, x, y, z} R}
variable {base : G.State}

/-- VI.R8/VI-2: interpret a selected free word as a Mathlib free-group word. -/
def selectedFreeGroupWord
    (P : PresentedArchitectureFundamentalGroup.{u, v, w, x, y, z} H base)
    (w : P.FreeWord) :
    FreeGroup P.presentation.Edge :=
  (P.freeWordEquivSelected w).toFreeGroup

/-- VI.R8/VI-2: selected homotopy-generator relators. -/
def selectedRelators
    (P : PresentedArchitectureFundamentalGroup.{u, v, w, x, y, z} H base) :
    Set (FreeGroup P.presentation.Edge) :=
  { r | ∃ w : P.FreeWord, P.Relator w ∧ P.selectedFreeGroupWord w = r }

/-- VI.R8/VI-2: actual selected homotopy attaching words. -/
def presentedRelators
    (P : PresentedArchitectureFundamentalGroup.{u, v, w, x, y, z} H base) :
    Set (FreeGroup P.presentation.Edge) :=
  P.selectedRelators

/--
VI.R8/VI-2: ambient Mathlib group presented by the selected one-skeleton and
actual attaching-loop relators.
-/
abbrev rawPresentedGroup
    (P : PresentedArchitectureFundamentalGroup.{u, v, w, x, y, z} H base) :
    Type z :=
  PresentedGroup P.presentedRelators

/-- VI.R8/VI-2: canonical ambient quotient map for a typed based loop. -/
def rawPresentedQuotientMap
    (P : PresentedArchitectureFundamentalGroup.{u, v, w, x, y, z} H base) :
    P.FreeWord -> P.rawPresentedGroup :=
  fun w => PresentedGroup.mk P.presentedRelators (P.selectedFreeGroupWord w)

/-- VI.定義9.5: ambient quotient elements represented by typed based loops. -/
def basedLoopElements
    (P : PresentedArchitectureFundamentalGroup.{u, v, w, x, y, z} H base) :
    Set P.rawPresentedGroup :=
  Set.range P.rawPresentedQuotientMap

/-- VI.定義9.5: subgroup generated by actual typed based loops. -/
def basedLoopSubgroup
    (P : PresentedArchitectureFundamentalGroup.{u, v, w, x, y, z} H base) :
    Subgroup P.rawPresentedGroup :=
  Subgroup.closure P.basedLoopElements

/-- VI.定義9.5: presented architecture fundamental group at the selected base. -/
abbrev pi1AAT
    (P : PresentedArchitectureFundamentalGroup.{u, v, w, x, y, z} H base) :
    Type z :=
  P.basedLoopSubgroup

/-- VI.定義9.5: every `pi1AAT` element lies in the closure generated by typed based loops. -/
theorem pi1AAT_mem_basedLoopClosure
    (P : PresentedArchitectureFundamentalGroup.{u, v, w, x, y, z} H base)
    (gamma : P.pi1AAT) :
    (gamma : P.rawPresentedGroup) ∈
      Subgroup.closure (Set.range P.rawPresentedQuotientMap) :=
  gamma.property

/-- VI.R8/VI-2: canonical element represented by a typed based loop. -/
def presentedQuotientMap
    (P : PresentedArchitectureFundamentalGroup.{u, v, w, x, y, z} H base)
    (w : P.FreeWord) : P.pi1AAT :=
  ⟨P.rawPresentedQuotientMap w, Subgroup.subset_closure ⟨w, rfl⟩⟩

/-- VI.R8/VI-2: selected relators become identity in the Mathlib presented group. -/
theorem presentedRelator_maps_to_identity
    (P : PresentedArchitectureFundamentalGroup.{u, v, w, x, y, z} H base)
    {w : P.FreeWord} (h : P.Relator w) :
    P.presentedQuotientMap w = 1 := by
  apply Subtype.ext
  exact PresentedGroup.one_of_mem ⟨w, h, rfl⟩

/--
VI.R8/VI-2: `PresentedGroup.toGroup` gives the universal map out of the
selected presented architecture fundamental group.
-/
def presentedGroupLift
    (P : PresentedArchitectureFundamentalGroup.{u, v, w, x, y, z} H base)
    {Y : Type q} [Group Y]
    (f : P.presentation.Edge -> Y)
    (hrels : ∀ r ∈ P.presentedRelators, FreeGroup.lift f r = 1) :
    (P.pi1AAT) →* Y :=
  (PresentedGroup.toGroup hrels).comp P.basedLoopSubgroup.subtype

/-- VI.R8/VI-2: the universal map evaluates a represented based loop word. -/
theorem presentedGroupLift_word
    (P : PresentedArchitectureFundamentalGroup.{u, v, w, x, y, z} H base)
    {Y : Type q} [Group Y]
    (f : P.presentation.Edge -> Y)
    (hrels : ∀ r ∈ P.presentedRelators, FreeGroup.lift f r = 1)
    (word : P.FreeWord) :
    P.presentedGroupLift f hrels (P.presentedQuotientMap word) =
      FreeGroup.lift f (P.selectedFreeGroupWord word) :=
  rfl

/-- VI.定義9.5: path-cell relator words are computed from their actual attaching paths. -/
theorem pathCellRelator_path_holds
    (P : PresentedArchitectureFundamentalGroup.{u, v, w, x, y, z} H base)
    (h : BasedPathCell H base) :
    P.freeWordEquivSelected (P.pathCellRelatorWord h) =
      pathCellRelatorPath P.presentation h.1 h.2 :=
  P.pathCellRelator_path h

/-- VI.定義9.5: loop-relator words are computed from their actual operation loops. -/
theorem loopRelator_path_holds
    (P : PresentedArchitectureFundamentalGroup.{u, v, w, x, y, z} H base)
    (r : BasedLoopRelator H base) :
    P.freeWordEquivSelected (P.loopRelatorWord r) =
      loopRelatorPath P.presentation r.1 r.2 :=
  P.loopRelator_path r

/-- VI.定義9.5: relators map to the identity in the selected quotient. -/
theorem relator_maps_to_identity_holds
    (P : PresentedArchitectureFundamentalGroup.{u, v, w, x, y, z} H base)
    {w : P.FreeWord} (h : P.Relator w) :
    P.quotientMap w = 1 :=
  P.relator_maps_to_identity w h

/-- VI.定義9.5: selected path-cell relators are relators of the quotient package. -/
theorem pathCellRelator_selected_holds
    (P : PresentedArchitectureFundamentalGroup.{u, v, w, x, y, z} H base)
    (h : BasedPathCell H base) :
    P.Relator (P.pathCellRelatorWord h) :=
  P.pathCellRelator_selected h

/-- VI.定義9.5: selected loop relators are relators of the quotient package. -/
theorem loopRelator_selected_holds
    (P : PresentedArchitectureFundamentalGroup.{u, v, w, x, y, z} H base)
    (r : BasedLoopRelator H base) :
    P.Relator (P.loopRelatorWord r) :=
  P.loopRelator_selected r

/--
VI.定義9.5: every selected relator in the package is generated by the chosen
path-cell or loop-relator family.
-/
theorem relator_generated_by_selected_generator_holds
    (P : PresentedArchitectureFundamentalGroup.{u, v, w, x, y, z} H base)
    {w : P.FreeWord} (h : P.Relator w) :
    (∃ c : BasedPathCell H base, P.pathCellRelatorWord c = w) ∨
      (∃ r : BasedLoopRelator H base, P.loopRelatorWord r = w) :=
  P.relator_generated_by_selected_generator h

/-- VI.定義9.5: the relator predicate is exactly the actual path-cell and loop-relator family. -/
theorem relator_iff_actual_attaching_loop
    (P : PresentedArchitectureFundamentalGroup.{u, v, w, x, y, z} H base)
    {w : P.FreeWord} :
    P.Relator w ↔
      (∃ c : BasedPathCell H base, P.pathCellRelatorWord c = w) ∨
      (∃ r : BasedLoopRelator H base, P.loopRelatorWord r = w) := by
  constructor
  · exact P.relator_generated_by_selected_generator
  · rintro (⟨c, rfl⟩ | ⟨r, rfl⟩)
    · exact P.pathCellRelator_selected c
    · exact P.loopRelator_selected r

/--
VI.定義9.5: quotient universal property.

A selected free transport descends to the presented architecture fundamental
group exactly when it kills the selected relators.
-/
theorem quotient_universal_property
    (P : PresentedArchitectureFundamentalGroup.{u, v, w, x, y, z} H base)
    (T : P.FreeTransport) :
    P.SendsRelatorsToIdentity T ↔
      ∃ Q : P.QuotientTransport, P.FactorsThroughQuotient T Q :=
  P.quotientUniversalProperty T

end PresentedArchitectureFundamentalGroup

end SingularityMonodromyStack
end AAT.AG
