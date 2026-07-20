import Mathlib.GroupTheory.PresentedGroup
import Formal.AG.SingularityMonodromyStack.OperationCategory

noncomputable section

namespace AAT.AG
namespace SingularityMonodromyStack

universe u v y z q

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
    {X : ArchitectureStratum.{u, v, y} P k}
    {G : OperationCategoryData.{u, v, y, z} X}
    (R : RefactorEndpointReading.{u, v, y, z} G) where
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
variable {X : ArchitectureStratum.{u, v, y} P k}
variable {G : OperationCategoryData.{u, v, y, z} X}
variable {R : RefactorEndpointReading.{u, v, y, z} G}

/-- VI.定義9.3: a homotopy generator carries two paths with common endpoints. -/
theorem pathCell_commonEndpoints
    (H : HomotopyGeneratorFamily.{u, v, y, z} R)
    (h : H.PathCell) :
    (H.leftPath h : OperationPath G (H.cellSource h) (H.cellTarget h)) =
      H.leftPath h ∧
    (H.rightPath h : OperationPath G (H.cellSource h) (H.cellTarget h)) =
      H.rightPath h :=
  ⟨rfl, rfl⟩

/-- VI.定義9.3: expose the selected relator base certificate. -/
theorem relator_based_holds
    (H : HomotopyGeneratorFamily.{u, v, y, z} R)
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
    {X : ArchitectureStratum.{u, v, y} P k}
    {G : OperationCategoryData.{u, v, y, z} X}
    {R : RefactorEndpointReading.{u, v, y, z} G}
    (H : HomotopyGeneratorFamily.{u, v, y, z} R) where
  Vertex : Type z
  vertexEquivState : Vertex ≃ G.State
  Edge : Type z
  edgeBoundary : Edge -> Σ a : G.State, Σ b : G.State, SelectedOperation G a b
  TwoCell : Type z
  twoCellEquivGenerator : TwoCell ≃ H.PathCell

namespace PresentationTwoComplex

variable {U : AtomCarrier.{u}} {A : ArchitectureObject U}
variable {S : Site.AATSite A} {P : StratumReadingParameter S}
variable {k : Type v} [CommRing k]
variable {X : ArchitectureStratum.{u, v, y} P k}
variable {G : OperationCategoryData.{u, v, y, z} X}
variable {R : RefactorEndpointReading.{u, v, y, z} G}
variable {H : HomotopyGeneratorFamily.{u, v, y, z} R}

/-- VI.定義9.4: selected vertices are equivalent to selected operation states. -/
def vertices_read_states
    (K : PresentationTwoComplex.{u, v, y, z} H) :
    K.Vertex ≃ G.State :=
  K.vertexEquivState

/-- VI.定義9.4: selected 2-cells are equivalent to selected homotopy generators. -/
def twoCells_read_generators
    (K : PresentationTwoComplex.{u, v, y, z} H) :
    K.TwoCell ≃ H.PathCell :=
  K.twoCellEquivGenerator

end PresentationTwoComplex

/--
VI.定義9.5: selected formal edge step.

`backward` is a formal inverse in the presentation. It does not assert that the
reverse direction is an executable architecture operation.
-/
inductive FormalEdgeStep {U : AtomCarrier.{u}} {A : ArchitectureObject U}
    {S : Site.AATSite A} {P : StratumReadingParameter S}
    {k : Type v} [CommRing k]
    {X : ArchitectureStratum.{u, v, y} P k}
    (G : OperationCategoryData.{u, v, y, z} X) : Type z where
  | forward {a b : G.State} : SelectedOperation G a b -> FormalEdgeStep G
  | backward {a b : G.State} : SelectedOperation G a b -> FormalEdgeStep G

/-- VI.定義9.5: selected free edge-word carrier at a base state. -/
structure FreeEdgeWord {U : AtomCarrier.{u}} {A : ArchitectureObject U}
    {S : Site.AATSite A} {P : StratumReadingParameter S}
    {k : Type v} [CommRing k]
    {X : ArchitectureStratum.{u, v, y} P k}
    (G : OperationCategoryData.{u, v, y, z} X)
    (base : G.State) where
  steps : List (FormalEdgeStep G)
  startsAtBase : Prop

namespace FreeEdgeWord

variable {U : AtomCarrier.{u}} {A : ArchitectureObject U}
variable {S : Site.AATSite A} {P : StratumReadingParameter S}
variable {k : Type v} [CommRing k]
variable {X : ArchitectureStratum.{u, v, y} P k}
variable {G : OperationCategoryData.{u, v, y, z} X}
variable {base : G.State}

/-- VI.定義9.5: read a selected edge word as a Mathlib free-group word. -/
def toFreeGroup (w : FreeEdgeWord.{u, v, y, z} G base) :
    FreeGroup (FormalEdgeStep.{u, v, y, z} G) :=
  (w.steps.map fun step => FreeGroup.of step).prod

end FreeEdgeWord

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
    {X : ArchitectureStratum.{u, v, y} P k}
    {G : OperationCategoryData.{u, v, y, z} X}
    {R : RefactorEndpointReading.{u, v, y, z} G}
    (H : HomotopyGeneratorFamily.{u, v, y, z} R)
    (base : G.State) where
  FreeWord : Type z
  freeWordEquivSelected : FreeWord ≃ FreeEdgeWord G base
  Relator : FreeWord -> Prop
  presentation : PresentationTwoComplex H
  pathCellRelatorWord : H.PathCell -> FreeWord
  pathCellRelator_selected : ∀ h : H.PathCell, Relator (pathCellRelatorWord h)
  loopRelatorWord : H.LoopRelator -> FreeWord
  loopRelator_selected : ∀ r : H.LoopRelator, Relator (loopRelatorWord r)
  relator_generated_by_selected_generator :
    ∀ {w : FreeWord}, Relator w ->
      (∃ h : H.PathCell, pathCellRelatorWord h = w) ∨
      (∃ r : H.LoopRelator, loopRelatorWord r = w)
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
variable {X : ArchitectureStratum.{u, v, y} P k}
variable {G : OperationCategoryData.{u, v, y, z} X}
variable {R : RefactorEndpointReading.{u, v, y, z} G}
variable {H : HomotopyGeneratorFamily.{u, v, y, z} R}
variable {base : G.State}

/-- VI.R8/VI-2: interpret a selected free word as a Mathlib free-group word. -/
def selectedFreeGroupWord
    (P : PresentedArchitectureFundamentalGroup.{u, v, y, z} H base)
    (w : P.FreeWord) :
    FreeGroup (FormalEdgeStep.{u, v, y, z} G) :=
  (P.freeWordEquivSelected w).toFreeGroup

/-- VI.R8/VI-2: selected relators as a Mathlib `PresentedGroup` relation set. -/
def presentedRelators
    (P : PresentedArchitectureFundamentalGroup.{u, v, y, z} H base) :
    Set (FreeGroup (FormalEdgeStep.{u, v, y, z} G)) :=
  { r | ∃ w : P.FreeWord, P.Relator w ∧ P.selectedFreeGroupWord w = r }

/--
VI.R8/VI-2: the Mathlib presented group generated by selected operation edge
steps and quotienting by the selected relators.
-/
abbrev pi1AAT
    (P : PresentedArchitectureFundamentalGroup.{u, v, y, z} H base) :
    Type z :=
  PresentedGroup P.presentedRelators

/-- VI.R8/VI-2: canonical map from a selected free word to the Mathlib presented group. -/
def presentedQuotientMap
    (P : PresentedArchitectureFundamentalGroup.{u, v, y, z} H base) :
    P.FreeWord -> P.pi1AAT :=
  fun w => PresentedGroup.mk P.presentedRelators (P.selectedFreeGroupWord w)

/-- VI.R8/VI-2: selected relators become identity in the Mathlib presented group. -/
theorem presentedRelator_maps_to_identity
    (P : PresentedArchitectureFundamentalGroup.{u, v, y, z} H base)
    {w : P.FreeWord} (h : P.Relator w) :
    P.presentedQuotientMap w = 1 :=
  PresentedGroup.one_of_mem ⟨w, h, rfl⟩

/--
VI.R8/VI-2: `PresentedGroup.toGroup` gives the universal map out of the
selected presented architecture fundamental group.
-/
def presentedGroupLift
    (P : PresentedArchitectureFundamentalGroup.{u, v, y, z} H base)
    {Y : Type q} [Group Y]
    (f : FormalEdgeStep.{u, v, y, z} G -> Y)
    (hrels : ∀ r ∈ P.presentedRelators, FreeGroup.lift f r = 1) :
    (P.pi1AAT) →* Y :=
  PresentedGroup.toGroup hrels

/-- VI.R8/VI-2: the universal map extends the selected generator map. -/
theorem presentedGroupLift_of
    (P : PresentedArchitectureFundamentalGroup.{u, v, y, z} H base)
    {Y : Type q} [Group Y]
    (f : FormalEdgeStep.{u, v, y, z} G -> Y)
    (hrels : ∀ r ∈ P.presentedRelators, FreeGroup.lift f r = 1)
    (step : FormalEdgeStep.{u, v, y, z} G) :
    P.presentedGroupLift f hrels (PresentedGroup.of step) = f step :=
  PresentedGroup.toGroup.of hrels

/-- VI.R8/VI-2: the `PresentedGroup` universal map is unique on generators. -/
theorem presentedGroupLift_unique
    (P : PresentedArchitectureFundamentalGroup.{u, v, y, z} H base)
    {Y : Type q} [Group Y]
    (f : FormalEdgeStep.{u, v, y, z} G -> Y)
    (hrels : ∀ r ∈ P.presentedRelators, FreeGroup.lift f r = 1)
    (g : (P.pi1AAT) →* Y)
    (hg : ∀ step : FormalEdgeStep.{u, v, y, z} G,
      g (PresentedGroup.of step) = f step)
    (x : P.pi1AAT) :
    g x = P.presentedGroupLift f hrels x :=
  PresentedGroup.toGroup.unique hrels g hg

/-- VI.定義9.5: relators map to the identity in the selected quotient. -/
theorem relator_maps_to_identity_holds
    (P : PresentedArchitectureFundamentalGroup.{u, v, y, z} H base)
    {w : P.FreeWord} (h : P.Relator w) :
    P.quotientMap w = 1 :=
  P.relator_maps_to_identity w h

/-- VI.定義9.5: selected path-cell relators are relators of the quotient package. -/
theorem pathCellRelator_selected_holds
    (P : PresentedArchitectureFundamentalGroup.{u, v, y, z} H base)
    (h : H.PathCell) :
    P.Relator (P.pathCellRelatorWord h) :=
  P.pathCellRelator_selected h

/-- VI.定義9.5: selected loop relators are relators of the quotient package. -/
theorem loopRelator_selected_holds
    (P : PresentedArchitectureFundamentalGroup.{u, v, y, z} H base)
    (r : H.LoopRelator) :
    P.Relator (P.loopRelatorWord r) :=
  P.loopRelator_selected r

/--
VI.定義9.5: every selected relator in the package is generated by the chosen
path-cell or loop-relator family.
-/
theorem relator_generated_by_selected_generator_holds
    (P : PresentedArchitectureFundamentalGroup.{u, v, y, z} H base)
    {w : P.FreeWord} (h : P.Relator w) :
    (∃ c : H.PathCell, P.pathCellRelatorWord c = w) ∨
      (∃ r : H.LoopRelator, P.loopRelatorWord r = w) :=
  P.relator_generated_by_selected_generator h

/--
VI.定義9.5: quotient universal property.

A selected free transport descends to the presented architecture fundamental
group exactly when it kills the selected relators.
-/
theorem quotient_universal_property
    (P : PresentedArchitectureFundamentalGroup.{u, v, y, z} H base)
    (T : P.FreeTransport) :
    P.SendsRelatorsToIdentity T ↔
      ∃ Q : P.QuotientTransport, P.FactorsThroughQuotient T Q :=
  P.quotientUniversalProperty T

end PresentedArchitectureFundamentalGroup

end SingularityMonodromyStack
end AAT.AG
