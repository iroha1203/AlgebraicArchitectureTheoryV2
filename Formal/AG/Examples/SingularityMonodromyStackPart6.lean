import Formal.AG.Examples.FiniteModel
import Formal.AG.Examples.RepresentationAnalysisPart7
import Formal.AG.SingularityMonodromyStack

noncomputable section

namespace AAT.AG

universe u v w x y z

namespace FiniteModel
namespace SingularityMonodromyStackPart6

open AAT.AG.SingularityMonodromyStack

/-!
R12 finite examples for Part VI.

Each package is deliberately selected and finite. It supplies the concrete
finite witness data needed by the corresponding Part VI theorem, then exposes
the theorem application as an example theorem.
-/

/-! ### Concrete nondegenerate finite carriers -/

abbrev ToyParameter :=
  RepresentationAnalysisPart7.finiteSynthesisStratumParameter

abbrev ToyStratum :=
  RepresentationAnalysisPart7.finiteSynthesisArchitectureStratum

def toyCotangentData : CotangentData.{0, 0, 0, 0, 0, 0} ToyStratum where
  Base := Bool
  CotangentComplex := Fin 2
  baseMap _ := false
  PullbackBase := Bool
  pullbackComplex b := if b then 1 else 0

def toyTangentData : TangentData.{0, 0, 0, 0, 0, 0} ToyStratum toyCotangentData where
  TangentComplex := Fin 2
  H0 := Bool
  H1 := Bool
  ObstructionTarget := Bool
  zeroObstruction := false
  rhomInterface_certificate := True
  h0ComputesInfinitesimalAutomorphisms_certificate := True
  h1ComputesObstructionTarget_certificate := True

def toyDeformationTheory :
    DeformationObstructionTheory.{0, 0, 0, 0, 0, 0} toyTangentData where
  DeformationTest := Bool
  LiftFill eta := eta = false
  ob eta := eta
  effective := by
    intro eta hzero
    simpa using hzero
  sound := by
    intro eta hfill
    simp [toyTangentData, hfill]

def toyBoundaryObstruction :
    BoundaryObstructionFamily.{0, 0, 0, 0, 0, 0} toyDeformationTheory where
  boundaryTest := true
  h1NonzeroClass :=
    toyDeformationTheory.ob true ≠ toyTangentData.zeroObstruction
  realizes_nonzero_obstruction := by
    intro h
    exact h

/--
VI.R12(a): finite singular-boundary toy model.

The finite witness consists of a finite family of deformation tests, a selected
boundary obstruction family, and a selected nonzero boundary class.
-/
structure SingularBoundaryToyModel {U : AtomCarrier.{u}} {A : ArchitectureObject U}
    {S : Site.AATSite A} {P : StratumReadingParameter S}
    {k : Type v} [CommRing k]
    {X : ArchitectureStratum.{u, v, w, x, y} P k}
    {L : CotangentData.{u, v, w, x, y, z} X}
    {T : TangentData.{u, v, w, x, y, z} X L}
    (D : DeformationObstructionTheory.{u, v, w, x, y, z} T) where
  finiteTests : Fintype D.DeformationTest
  boundary : BoundaryObstructionFamily.{u, v, w, x, y, z} D
  nonzeroBoundaryClass : boundary.h1NonzeroClass

namespace SingularBoundaryToyModel

variable {U : AtomCarrier.{u}} {A : ArchitectureObject U}
variable {S : Site.AATSite A} {P : StratumReadingParameter S}
variable {k : Type v} [CommRing k]
variable {X : ArchitectureStratum.{u, v, w, x, y} P k}
variable {L : CotangentData.{u, v, w, x, y, z} X}
variable {T : TangentData.{u, v, w, x, y, z} X L}
variable {D : DeformationObstructionTheory.{u, v, w, x, y, z} T}

/-- VI.R12(a): the finite singular-boundary toy model verifies 系6.5. -/
theorem verifies_singular_boundary
    (E : SingularBoundaryToyModel.{u, v, w, x, y, z} D) :
    USingularBoundary D :=
  E.boundary.singularBoundary E.nonzeroBoundaryClass

end SingularBoundaryToyModel

/--
VI.R12(b): finite operation-square toy model.

It selects a finite axis family, a measured square, and one nonzero
`mu_x`; theorem 10.7 then refutes the selected filling.
-/
structure OperationSquareToyModel {U : AtomCarrier.{u}} {A : ArchitectureObject U}
    {S : Site.AATSite A} {P : StratumReadingParameter S}
    {k : Type v} [CommRing k]
    {X : ArchitectureStratum.{u, v, w, x, y} P k}
    {G : OperationCategoryData.{u, v, w, x, y, z} X}
    {R : RefactorEndpointReading.{u, v, w, x, y, z} G}
    {H : HomotopyGeneratorFamily.{u, v, w, x, y, z} R}
    {base : G.State}
    {Pi : PresentedArchitectureFundamentalGroup.{u, v, w, x, y, z} H base}
    {M : MonodromyAction.{u, v, w, x, y, z} Pi}
    {K : PresentationTwoComplex.{u, v, w, x, y, z} H}
    (Q : MeasuredSquareMonodromy.{u, v, w, x, y, z} M K) where
  finiteAxis : Fintype Q.Axis
  filling : SquareMonodromyFillingProblem.{u, v, w, x, y, z} Q
  nonzeroMu : Q.mu filling.axis ≠ 0

namespace OperationSquareToyModel

variable {U : AtomCarrier.{u}} {A : ArchitectureObject U}
variable {S : Site.AATSite A} {P : StratumReadingParameter S}
variable {k : Type v} [CommRing k]
variable {X : ArchitectureStratum.{u, v, w, x, y} P k}
variable {G : OperationCategoryData.{u, v, w, x, y, z} X}
variable {R : RefactorEndpointReading.{u, v, w, x, y, z} G}
variable {H : HomotopyGeneratorFamily.{u, v, w, x, y, z} R}
variable {base : G.State}
variable {Pi : PresentedArchitectureFundamentalGroup.{u, v, w, x, y, z} H base}
variable {M : MonodromyAction.{u, v, w, x, y, z} Pi}
variable {K : PresentationTwoComplex.{u, v, w, x, y, z} H}
variable {Q : MeasuredSquareMonodromy.{u, v, w, x, y, z} M K}

/-- VI.R12(b): nonzero selected square monodromy refutes filling. -/
theorem verifies_square_nonfillability
    (E : OperationSquareToyModel.{u, v, w, x, y, z} Q) :
    ¬ E.filling.SelectedAxisFilling :=
  E.filling.squareMonodromy_nonfillability E.nonzeroMu

end OperationSquareToyModel

/--
VI.R12(c0): finite transport-descent zero toy model.

The zero case verifies quotient factorization. It is separated from the
nonzero case so the example package is not an empty `P ∧ ¬P` surface.
-/
structure TransportDescentZeroToyModel {U : AtomCarrier.{u}} {A : ArchitectureObject U}
    {S : Site.AATSite A} {P : StratumReadingParameter S}
    {k : Type v} [CommRing k]
    {X : ArchitectureStratum.{u, v, w, x, y} P k}
    {G : OperationCategoryData.{u, v, w, x, y, z} X}
    {R : RefactorEndpointReading.{u, v, w, x, y, z} G}
    {H : HomotopyGeneratorFamily.{u, v, w, x, y, z} R}
    {base : G.State}
    {Pi : PresentedArchitectureFundamentalGroup.{u, v, w, x, y, z} H base}
    {M : MonodromyAction.{u, v, w, x, y, z} Pi}
    {K : PresentationTwoComplex.{u, v, w, x, y, z} H}
    {Tfree : Pi.FreeTransport}
    (D : TransportDescentProblem.{u, v, w, x, y, z} (Pi := Pi) (M := M) (K := K) Tfree) where
  finiteSquares : Fintype D.Square
  zeroBoundaryCase : D.relationBoundaryZero

/--
VI.R12(c1): finite transport-descent nonzero toy model.

The selected nonzero case records failure of the zero-boundary predicate, so
the descent criterion refutes quotient factorization.
-/
structure TransportDescentNonzeroToyModel {U : AtomCarrier.{u}} {A : ArchitectureObject U}
    {S : Site.AATSite A} {P : StratumReadingParameter S}
    {k : Type v} [CommRing k]
    {X : ArchitectureStratum.{u, v, w, x, y} P k}
    {G : OperationCategoryData.{u, v, w, x, y, z} X}
    {R : RefactorEndpointReading.{u, v, w, x, y, z} G}
    {H : HomotopyGeneratorFamily.{u, v, w, x, y, z} R}
    {base : G.State}
    {Pi : PresentedArchitectureFundamentalGroup.{u, v, w, x, y, z} H base}
    {M : MonodromyAction.{u, v, w, x, y, z} Pi}
    {K : PresentationTwoComplex.{u, v, w, x, y, z} H}
    {Tfree : Pi.FreeTransport}
    (D : TransportDescentProblem.{u, v, w, x, y, z} (Pi := Pi) (M := M) (K := K) Tfree) where
  finiteSquares : Fintype D.Square
  nonzeroBoundaryCase : ¬ D.relationBoundaryZero

namespace TransportDescentZeroToyModel

variable {U : AtomCarrier.{u}} {A : ArchitectureObject U}
variable {S : Site.AATSite A} {P : StratumReadingParameter S}
variable {k : Type v} [CommRing k]
variable {X : ArchitectureStratum.{u, v, w, x, y} P k}
variable {G : OperationCategoryData.{u, v, w, x, y, z} X}
variable {R : RefactorEndpointReading.{u, v, w, x, y, z} G}
variable {H : HomotopyGeneratorFamily.{u, v, w, x, y, z} R}
variable {base : G.State}
variable {Pi : PresentedArchitectureFundamentalGroup.{u, v, w, x, y, z} H base}
variable {M : MonodromyAction.{u, v, w, x, y, z} Pi}
variable {K : PresentationTwoComplex.{u, v, w, x, y, z} H}
variable {Tfree : Pi.FreeTransport}
variable {D : TransportDescentProblem.{u, v, w, x, y, z} (Pi := Pi) (M := M) (K := K) Tfree}

/-- VI.R12(c0): selected finite zero-boundary data inhabits the zero toy-model package. -/
theorem nonempty_of_relationBoundaryZero
    [Fintype D.Square] (hzero : D.relationBoundaryZero) :
    Nonempty (TransportDescentZeroToyModel.{u, v, w, x, y, z} D) :=
  ⟨{ finiteSquares := inferInstance, zeroBoundaryCase := hzero }⟩

/-- VI.R12(c): zero selected boundary transport descends to the quotient. -/
theorem zero_case_descends
    (E : TransportDescentZeroToyModel.{u, v, w, x, y, z} D) :
    ∃ Q : Pi.QuotientTransport, Pi.FactorsThroughQuotient Tfree Q :=
  D.factorsThroughQuotient_of_relationBoundaryZero E.zeroBoundaryCase

end TransportDescentZeroToyModel

namespace TransportDescentNonzeroToyModel

variable {U : AtomCarrier.{u}} {A : ArchitectureObject U}
variable {S : Site.AATSite A} {P : StratumReadingParameter S}
variable {k : Type v} [CommRing k]
variable {X : ArchitectureStratum.{u, v, w, x, y} P k}
variable {G : OperationCategoryData.{u, v, w, x, y, z} X}
variable {R : RefactorEndpointReading.{u, v, w, x, y, z} G}
variable {H : HomotopyGeneratorFamily.{u, v, w, x, y, z} R}
variable {base : G.State}
variable {Pi : PresentedArchitectureFundamentalGroup.{u, v, w, x, y, z} H base}
variable {M : MonodromyAction.{u, v, w, x, y, z} Pi}
variable {K : PresentationTwoComplex.{u, v, w, x, y, z} H}
variable {Tfree : Pi.FreeTransport}
variable {D : TransportDescentProblem.{u, v, w, x, y, z} (Pi := Pi) (M := M) (K := K) Tfree}

/-- VI.R12(c1): selected finite nonzero-boundary data inhabits the nonzero toy-model package. -/
theorem nonempty_of_not_relationBoundaryZero
    [Fintype D.Square] (hnonzero : ¬ D.relationBoundaryZero) :
    Nonempty (TransportDescentNonzeroToyModel.{u, v, w, x, y, z} D) :=
  ⟨{ finiteSquares := inferInstance, nonzeroBoundaryCase := hnonzero }⟩

/-- VI.R12(c): selected nonzero boundary transport prevents quotient descent. -/
theorem nonzero_case_not_descend
    (E : TransportDescentNonzeroToyModel.{u, v, w, x, y, z} D) :
    ¬ ∃ Q : Pi.QuotientTransport, Pi.FactorsThroughQuotient Tfree Q := by
  intro hdescends
  exact E.nonzeroBoundaryCase (D.relationBoundaryZero_of_factorsThroughQuotient hdescends)

end TransportDescentNonzeroToyModel

/--
VI.R12(d): finite refactor-Galois toy model.

The package selects finite operation and invariant carriers and then evaluates
the already proved `Ops/Inv` Galois correspondence.
-/
structure RefactorGaloisToyModel {U : AtomCarrier.{u}} {A : ArchitectureObject U}
    {S : Site.AATSite A} {P : StratumReadingParameter S}
    {k : Type v} [CommRing k]
    {X : ArchitectureStratum.{u, v, w, x, y} P k}
    {G : OperationCategoryData.{u, v, w, x, y, z} X}
    {R : RefactorEndpointReading.{u, v, w, x, y, z} G}
    {RG : RefactorGroupoid.{u, v, w, x, y, z} R}
    (D : OperationInvariantGaloisData.{u, v, w, x, y, z} RG) where
  finiteInvariant : Fintype D.Invariant
  selectedOperations : RefactorMorphismFamily RG
  selectedInvariants : D.InvFam

namespace RefactorGaloisToyModel

variable {U : AtomCarrier.{u}} {A : ArchitectureObject U}
variable {S : Site.AATSite A} {P : StratumReadingParameter S}
variable {k : Type v} [CommRing k]
variable {X : ArchitectureStratum.{u, v, w, x, y} P k}
variable {G : OperationCategoryData.{u, v, w, x, y, z} X}
variable {R : RefactorEndpointReading.{u, v, w, x, y, z} G}
variable {RG : RefactorGroupoid.{u, v, w, x, y, z} R}
variable {D : OperationInvariantGaloisData.{u, v, w, x, y, z} RG}

/-- VI.R12(d): finite refactor-Galois toy model computes the Galois correspondence. -/
theorem verifies_galois_connection
    (E : RefactorGaloisToyModel.{u, v, w, x, y, z} D) :
    RefactorMorphismFamilySubset E.selectedOperations (D.Ops E.selectedInvariants) ↔
      D.InvFamSubset E.selectedInvariants (D.Inv E.selectedOperations) :=
  D.operationInvariantGaloisCorrespondence E.selectedOperations E.selectedInvariants

end RefactorGaloisToyModel

/--
VI.R12(e): finite decomposition-gerbe toy model.

It records finite local decompositions, a selected nonzero gerbe class, and the
soundness interface. The no-canonical-decomposition theorem is then applied.
-/
structure DecompositionGerbeToyModel {B : ArchitectureStackBase.{z}}
    {D : DecompositionStack.{z} B}
    (G : GerbeObstructionData.{z} D) where
  finiteLocalIndex : Fintype D.LocalIndex
  noCanonicalData : NoCanonicalDecompositionData.{z} G
  nonzeroGerbe : G.nonzero

namespace DecompositionGerbeToyModel

variable {B : ArchitectureStackBase.{z}}
variable {D : DecompositionStack.{z} B}
variable {G : GerbeObstructionData.{z} D}

/-- VI.R12(e): nonzero selected decomposition gerbe refutes global canonical decomposition. -/
theorem verifies_no_canonical_decomposition
    (E : DecompositionGerbeToyModel.{z} G) :
    ¬ E.noCanonicalData.globalCanonicalDecomposition :=
  E.noCanonicalData.noCanonicalDecomposition E.nonzeroGerbe

end DecompositionGerbeToyModel

/-! ### Concrete finite toy-model firings -/

def concreteSingularBoundaryToyModel :
    SingularBoundaryToyModel.{0, 0, 0, 0, 0, 0} toyDeformationTheory where
  finiteTests := by
    change Fintype Bool
    infer_instance
  boundary := toyBoundaryObstruction
  nonzeroBoundaryClass := by
    intro h
    cases h

theorem concreteSingularBoundaryToyModel_fires :
    USingularBoundary toyDeformationTheory :=
  SingularBoundaryToyModel.verifies_singular_boundary concreteSingularBoundaryToyModel

theorem toyBoundaryObstruction_nonzero :
    toyBoundaryObstruction.h1NonzeroClass :=
  concreteSingularBoundaryToyModel.nonzeroBoundaryClass

def toyOperationCategory :
    OperationCategoryData.{0, 0, 0, 0, 0, 0} ToyStratum where
  State := Bool
  Operation _ _ := Bool
  selectedState _ := false
  operationRespectsLawUniverse op := op = true

def toyEndpointReading :
    RefactorEndpointReading.{0, 0, 0, 0, 0, 0} toyOperationCategory where
  RefactorEquivalent a b := a = b
  refl _ := rfl
  symm h := h.symm
  trans h₁ h₂ := h₁.trans h₂
  preservesSelectedInvariants h := h = h
  preservesSelectedEssence h := h = h
  invariantCertificate _h := rfl
  essenceCertificate _h := rfl

def toySelectedOperation : SelectedOperation toyOperationCategory false true where
  op := true
  respectsLawUniverse := rfl

/-- Selected loop operation used by the presented monodromy fixture. -/
def toySelectedLoopOperation : SelectedOperation toyOperationCategory false false where
  op := true
  respectsLawUniverse := rfl

/-- Two composable selected loop operations at the fixture base state. -/
def toySelectedLoopPath : OperationPath toyOperationCategory false false :=
  OperationPath.cons toySelectedLoopOperation
    (OperationPath.cons toySelectedLoopOperation
      (OperationPath.nil (G := toyOperationCategory) false))

/-- One selected loop operation at the fixture base state. -/
def toySelectedLoopOncePath : OperationPath toyOperationCategory false false :=
  OperationPath.cons toySelectedLoopOperation
    (OperationPath.nil (G := toyOperationCategory) false)

theorem toyOperationCategory_operation_nontrivial :
    Nontrivial (toyOperationCategory.Operation false true) := by
  change Nontrivial Bool
  infer_instance

/-- Selected path-cell and concrete two-step loop-relator family. -/
def toyHomotopyGenerators :
    HomotopyGeneratorFamily.{0, 0, 0, 0, 0, 0} toyEndpointReading where
  PathCell := Bool
  cellSource _ := false
  cellTarget _ := true
  leftPath _ :=
    OperationPath.cons toySelectedOperation (OperationPath.nil (G := toyOperationCategory) true)
  rightPath _ :=
    OperationPath.cons toySelectedOperation (OperationPath.nil (G := toyOperationCategory) true)
  LoopRelator := Bool
  relatorBase _ := false
  relatorLoop _ :=
    { base := false
      endpoint := false
      gamma := toySelectedLoopPath
      endpoint_equivalent := rfl }
  relator_based _ := rfl

def toyPresentationTwoComplex :
    PresentationTwoComplex.{0, 0, 0, 0, 0, 0} toyHomotopyGenerators where
  Vertex := Bool
  vertexEquivState := Equiv.refl Bool
  Edge := Σ a : Bool, Σ b : Bool, SelectedOperation toyOperationCategory a b
  edgeBoundary := Equiv.refl _
  TwoCell := Bool
  twoCellEquivGenerator := by
    change Bool ≃ Bool
    exact Equiv.refl Bool

abbrev ToyFreeWord :=
  FreeEdgeWord toyPresentationTwoComplex false

/-- Empty composable loop word at the fixture base. -/
def toyEmptyFreeWord : ToyFreeWord :=
  FormalEdgePath.nil (K := toyPresentationTwoComplex) false

/-- Presentation edge corresponding to the selected loop operation. -/
def toyPresentedGenerator : toyPresentationTwoComplex.Edge :=
  ⟨false, false, toySelectedLoopOperation⟩

/-- One-step selected loop word at the fixture base. -/
def toyNonemptyFreeWord : ToyFreeWord :=
  toySelectedLoopOncePath.toFormalEdgePath toyPresentationTwoComplex

/-- The selected based path-cell index with its identity connector. -/
def toyBasedPathCell : BasedPathCell toyHomotopyGenerators false :=
  ⟨false, OperationPath.nil (G := toyOperationCategory) false⟩

/-- The selected based loop-relator index with its identity connector. -/
def toyBasedLoopRelator : BasedLoopRelator toyHomotopyGenerators false :=
  ⟨false, OperationPath.nil (G := toyOperationCategory) false⟩

/-- The identical path-cell pair read as a path followed by its formal inverse. -/
def toyPathCellFreeWord : ToyFreeWord :=
  pathCellRelatorPath toyPresentationTwoComplex toyBasedPathCell.1 toyBasedPathCell.2

/-- Two-step selected loop word used as the finite loop relator. -/
def toySquaredFreeWord : ToyFreeWord :=
  loopRelatorPath toyPresentationTwoComplex toyBasedLoopRelator.1 toyBasedLoopRelator.2

/-- The selected path-cell relator is computed from its two actual operation paths. -/
theorem toyPathCellFreeWord_has_selected_path_steps :
    toyPathCellFreeWord =
      pathCellRelatorPath toyPresentationTwoComplex
        toyBasedPathCell.1 toyBasedPathCell.2 :=
  rfl

/-- The selected loop relator word is computed from its actual composable loop path. -/
theorem toySquaredFreeWord_has_selected_loop_steps :
    toySquaredFreeWord =
      loopRelatorPath toyPresentationTwoComplex
        toyBasedLoopRelator.1 toyBasedLoopRelator.2 :=
  rfl

abbrev ToyLoopGroup :=
  Multiplicative (ZMod 2)

/-- The legacy supplied transport group remains nontrivial. -/
theorem toySuppliedPi1_nontrivial :
    Nontrivial ToyLoopGroup := by
  infer_instance

/-- The distinguished element of the legacy supplied transport group. -/
def toyLoopGenerator : ToyLoopGroup :=
  Multiplicative.ofAdd (1 : ZMod 2)

/-- The distinguished legacy transport element is not the identity. -/
theorem toyLoopGenerator_ne_one : toyLoopGenerator ≠ (1 : ToyLoopGroup) := by
  intro h
  have hAdd := congrArg Multiplicative.toAdd h
  norm_num [toyLoopGenerator] at hAdd

/-- The distinguished legacy transport element has order two. -/
theorem toyLoopGenerator_mul_self : toyLoopGenerator * toyLoopGenerator = 1 := by
  change Multiplicative.ofAdd ((1 : ZMod 2) + 1) = Multiplicative.ofAdd 0
  congr 1

/-- The legacy action evaluates the selected one-step based loop. -/
theorem toySelectedLoopOnce_legacy_evaluation :
    FreeGroup.lift (fun _ : toyPresentationTwoComplex.Edge => toyLoopGenerator)
        (toySelectedLoopOncePath.toFormalEdgePath toyPresentationTwoComplex).toFreeGroup =
      toyLoopGenerator := by
  simp [toySelectedLoopOncePath, OperationPath.toFormalEdgePath,
    FormalEdgePath.toFreeGroup, FormalEdgeStep.toFreeGroup,
    FormalEdgeStep.ofSelectedOperation, toyPresentationTwoComplex]

/-- The legacy action evaluates the selected two-step loop as a square. -/
theorem toySelectedLoopPath_legacy_evaluation :
    FreeGroup.lift (fun _ : toyPresentationTwoComplex.Edge => toyLoopGenerator)
        (toySelectedLoopPath.toFormalEdgePath toyPresentationTwoComplex).toFreeGroup =
      toyLoopGenerator * toyLoopGenerator := by
  simp [toySelectedLoopPath, OperationPath.toFormalEdgePath,
    FormalEdgePath.toFreeGroup, FormalEdgeStep.toFreeGroup,
    FormalEdgeStep.ofSelectedOperation, toyPresentationTwoComplex]

/-- Legacy finite transport quotient reading used by the descent fixture. -/
def toyQuotientMap (w : ToyFreeWord) : ToyLoopGroup :=
  FreeGroup.lift (fun _ : toyPresentationTwoComplex.Edge => toyLoopGenerator) w.toFreeGroup

/-- The empty word maps to the identity transport element. -/
theorem toyQuotientMap_empty : toyQuotientMap toyEmptyFreeWord = 1 := by
  simp [toyQuotientMap, toyEmptyFreeWord, FormalEdgePath.toFreeGroup]

/-- The one-step loop maps to the distinguished transport element. -/
theorem toyQuotientMap_nonempty : toyQuotientMap toyNonemptyFreeWord = toyLoopGenerator := by
  simpa [toyQuotientMap, toyNonemptyFreeWord] using
    toySelectedLoopOnce_legacy_evaluation

/-- The selected squared relator maps to the identity transport element. -/
theorem toyQuotientMap_squared : toyQuotientMap toySquaredFreeWord = 1 := by
  simp [toyQuotientMap, toySquaredFreeWord, loopRelatorPath,
    toyHomotopyGenerators, toyBasedLoopRelator,
    toySelectedLoopPath_legacy_evaluation, toyLoopGenerator_mul_self]

/-- Presented finite fixture with a path/inverse pair and a squared loop relator. -/
abbrev toyPresentedPi :
    PresentedArchitectureFundamentalGroup.{0, 0, 0, 0, 0, 0}
      toyHomotopyGenerators false where
  presentation := toyPresentationTwoComplex
  FreeWord := ToyFreeWord
  freeWordEquivSelected := Equiv.refl ToyFreeWord
  Relator w :=
    (∃ h : BasedPathCell toyHomotopyGenerators false,
      pathCellRelatorPath toyPresentationTwoComplex h.1 h.2 = w) ∨
    (∃ r : BasedLoopRelator toyHomotopyGenerators false,
      loopRelatorPath toyPresentationTwoComplex r.1 r.2 = w)
  pathCellRelatorWord h := pathCellRelatorPath toyPresentationTwoComplex h.1 h.2
  pathCellRelator_path _ := rfl
  pathCellRelator_selected h := Or.inl ⟨h, rfl⟩
  loopRelatorWord r := loopRelatorPath toyPresentationTwoComplex r.1 r.2
  loopRelator_path _ := rfl
  loopRelator_selected r := Or.inr ⟨r, rfl⟩
  relator_generated_by_selected_generator h := h
  Pi1 := ToyLoopGroup
  quotientMap := toyQuotientMap
  relator_maps_to_identity := by
    intro w h
    rcases h with ⟨h, rfl⟩ | ⟨r, rfl⟩
    · simp [toyQuotientMap, pathCellRelatorPath, toyHomotopyGenerators]
    · simp [toyQuotientMap, loopRelatorPath, toyHomotopyGenerators,
        toySelectedLoopPath_legacy_evaluation, toyLoopGenerator_mul_self]
  FreeTransport := Bool
  QuotientTransport := Bool
  SendsRelatorsToIdentity T :=
    toyQuotientMap (if T then toyEmptyFreeWord else toyNonemptyFreeWord) = 1
  FactorsThroughQuotient T Q :=
    Q = T ∧ toyQuotientMap (if T then toyEmptyFreeWord else toyNonemptyFreeWord) = 1
  quotientUniversalProperty := by
    intro T
    constructor
    · intro h
      exact ⟨T, rfl, h⟩
    · intro h
      rcases h with ⟨_Q, _hQT, hT⟩
      exact hT

def toyBoolFlipEquiv : Bool ≃ Bool where
  toFun b := !b
  invFun b := !b
  left_inv := by intro b; cases b <;> rfl
  right_inv := by intro b; cases b <;> rfl

def toyFlipCoefficientAutomorphism :
    CoefficientAutomorphism { Ob := Bool, Sem := Bool, Eff := Bool } where
  obAut := toyBoolFlipEquiv
  semAut := Equiv.refl Bool
  effAut := Equiv.refl Bool

/-- Every selected presentation edge acts by the Bool flip automorphism. -/
def toyPresentedGeneratorAction : toyPresentationTwoComplex.Edge ->
    CoefficientAutomorphism { Ob := Bool, Sem := Bool, Eff := Bool } :=
  fun ⟨_, _, _⟩ => toyFlipCoefficientAutomorphism

/-- The Bool flip automorphism has order two. -/
theorem toyFlipCoefficientAutomorphism_mul_self :
    toyFlipCoefficientAutomorphism * toyFlipCoefficientAutomorphism = 1 := by
  apply CoefficientAutomorphism.ext <;>
    apply Equiv.ext <;>
    intro b <;>
    cases b <;>
    rfl

/-- The coefficient action evaluates the selected two-step loop as a square. -/
theorem toySelectedLoopPath_coefficient_evaluation :
    FreeGroup.lift toyPresentedGeneratorAction
        (toySelectedLoopPath.toFormalEdgePath toyPresentationTwoComplex).toFreeGroup =
      toyFlipCoefficientAutomorphism * toyFlipCoefficientAutomorphism := by
  simp [toySelectedLoopPath, OperationPath.toFormalEdgePath,
    FormalEdgePath.toFreeGroup, FormalEdgeStep.toFreeGroup,
    FormalEdgeStep.ofSelectedOperation, toyPresentedGeneratorAction,
    toyPresentationTwoComplex]

/-- The selected path-cell and loop relators are killed by the fixture action. -/
theorem toySelectedRelator_lift_eq_one
    {r : FreeGroup toyPresentationTwoComplex.Edge}
    (hr : r ∈ toyPresentedPi.selectedRelators) :
    FreeGroup.lift toyPresentedGeneratorAction r = 1 := by
  rcases hr with ⟨word, hword, rfl⟩
  rcases hword with ⟨h, rfl⟩ | ⟨r, rfl⟩
  · simp [PresentedArchitectureFundamentalGroup.selectedFreeGroupWord,
      pathCellRelatorPath, toyHomotopyGenerators, toyPresentedPi]
  · simp [PresentedArchitectureFundamentalGroup.selectedFreeGroupWord,
      loopRelatorPath, toyHomotopyGenerators, toyPresentedPi,
      toySelectedLoopPath_coefficient_evaluation,
      toyFlipCoefficientAutomorphism_mul_self]

/-- All actual attaching-loop relators are killed by the fixture action. -/
theorem toyPresentedGeneratorAction_kills_relators :
    ∀ r ∈ toyPresentedPi.presentedRelators,
      FreeGroup.lift toyPresentedGeneratorAction r = 1 := by
  intro r hr
  exact toySelectedRelator_lift_eq_one hr

/-- Monodromy representation constructed from the presented generator action. -/
def toyMonodromyAction :
    MonodromyAction.{0, 0, 0, 0, 0, 0} toyPresentedPi :=
  MonodromyAction.ofPresentedGenerators
    toyPresentedPi
    { Ob := Bool, Sem := Bool, Eff := Bool }
    toyPresentedGeneratorAction
    toyPresentedGeneratorAction_kills_relators

/-- Distinguished element of the actual Mathlib presented group. -/
def toyPresentedLoopGenerator : toyPresentedPi.pi1AAT :=
  toyPresentedPi.presentedQuotientMap toyNonemptyFreeWord

/-- Presented monodromy evaluates to the selected generator action. -/
theorem toyMonodromyAction_generator_evaluation :
    toyMonodromyAction.Mon_gamma toyPresentedLoopGenerator =
      toyPresentedGeneratorAction toyPresentedGenerator := by
  unfold toyMonodromyAction
  simpa [PresentedArchitectureFundamentalGroup.selectedFreeGroupWord,
      FormalEdgePath.toFreeGroup, FormalEdgeStep.toFreeGroup,
      toyPresentedPi, toyNonemptyFreeWord] using
    (MonodromyAction.mon_gamma_presented_loop
      toyPresentedPi
      { Ob := Bool, Sem := Bool, Eff := Bool }
      toyPresentedGeneratorAction
      toyPresentedGeneratorAction_kills_relators
      toyNonemptyFreeWord)

/-- The selected squared loop relator has identity monodromy. -/
theorem toyMonodromyAction_relator_evaluation :
  toyMonodromyAction.Mon_gamma
      (toyPresentedPi.presentedQuotientMap toySquaredFreeWord) = 1 :=
  toyMonodromyAction.mon_gamma_presented_relator
    (Or.inr ⟨toyBasedLoopRelator, rfl⟩)

/-- The selected presented generator moves the obstruction coefficient. -/
theorem toyMonodromyAction_moves_false :
    (toyMonodromyAction.rho toyPresentedLoopGenerator).obAut false = true := by
  rw [show toyMonodromyAction.rho toyPresentedLoopGenerator =
      toyPresentedGeneratorAction toyPresentedGenerator from
    toyMonodromyAction_generator_evaluation]
  rfl

/-- The selected presented generator has nonidentity monodromy. -/
theorem toyMonodromyAction_nonidentity :
    toyMonodromyAction.rho toyPresentedLoopGenerator ≠ CoefficientAutomorphism.id _ := by
  intro h
  have hmoved := toyMonodromyAction_moves_false
  rw [h] at hmoved
  cases hmoved

/-- The selected generator is not the identity in the actual presented group. -/
theorem toyPresentedLoopGenerator_ne_one :
    toyPresentedLoopGenerator ≠ (1 : toyPresentedPi.pi1AAT) := by
  intro h
  apply toyMonodromyAction_nonidentity
  rw [h]
  exact toyMonodromyAction.rho.map_one

/-- The actual Mathlib presented group of the fixture is nontrivial. -/
theorem toyPresentedPi_pi1_nontrivial :
    Nontrivial toyPresentedPi.pi1AAT :=
  ⟨⟨toyPresentedLoopGenerator, 1, toyPresentedLoopGenerator_ne_one⟩⟩

/-- Read whether an automorphism moves the selected obstruction coefficient. -/
def toyObstructionCoefficientMoved
    (phi : CoefficientAutomorphism { Ob := Bool, Sem := Bool, Eff := Bool }) : Bool :=
  phi.obAut false

/-- Equality-defect value computed from the actual presented monodromy action. -/
def toyMonodromyDefectFromAction : Nat :=
  if toyObstructionCoefficientMoved
      (toyMonodromyAction.rho toyPresentedLoopGenerator) then 1 else 0

/-- Measured square whose selected boundary element is the identity. -/
def toyMeasuredSquareZero :
    MeasuredSquareMonodromy.{0, 0, 0, 0, 0, 0} toyMonodromyAction
      toyPresentationTwoComplex where
  Axis := Bool
  square := false
  boundaryElement := 1
  boundaryTransport := CoefficientAutomorphism.id _
  boundaryTransport_eq_monodromy := rfl
  equalityDefect _ := 0
  axisDetectsIdentity _ := (1 : ToyLoopGroup) = 1
  zero_defect_detects _ _ := rfl
  mu _ := 0
  mu_eq_defect _ := rfl

/-- Measured square detected by the nonidentity presented loop generator. -/
def toyMeasuredSquareNonzero :
    MeasuredSquareMonodromy.{0, 0, 0, 0, 0, 0} toyMonodromyAction
      toyPresentationTwoComplex where
  Axis := Bool
  square := true
  boundaryElement := toyPresentedLoopGenerator
  boundaryTransport := toyMonodromyAction.rho toyPresentedLoopGenerator
  boundaryTransport_eq_monodromy := rfl
  equalityDefect axis :=
    if axis then 0 else toyMonodromyDefectFromAction
  axisDetectsIdentity axis :=
    toyMonodromyAction.rho (if axis then 1 else toyPresentedLoopGenerator) =
      CoefficientAutomorphism.id _
  zero_defect_detects := by
    intro axis hzero
    cases axis
    · have hmoved := toyMonodromyAction_moves_false
      have hdefect : toyMonodromyDefectFromAction = 1 := by
        rfl
      rw [hdefect] at hzero
      cases hzero
    · exact toyMonodromyAction.rho.map_one
  mu axis := if axis then 0 else 1
  mu_eq_defect := by
    intro axis
    cases axis
    · have hmoved := toyMonodromyAction_moves_false
      rfl
    · rfl

/-- The nonzero square defect is computed from the moved coefficient. -/
theorem toyMeasuredSquareNonzero_defect_from_moved_coefficient :
    toyMeasuredSquareNonzero.equalityDefect false =
      toyMonodromyDefectFromAction ∧
    toyMonodromyDefectFromAction = 1 ∧
      (toyMonodromyAction.rho toyPresentedLoopGenerator).obAut false = true := by
  exact ⟨rfl, rfl, toyMonodromyAction_moves_false⟩

def toySquareFillingProblem :
    SquareMonodromyFillingProblem.{0, 0, 0, 0, 0, 0} toyMeasuredSquareNonzero where
  axis := false
  SelectedAxisFilling :=
    toyMeasuredSquareNonzero.axisDetectsIdentity false
  filling_implies_mu_zero := by
    intro h
    exact False.elim (toyMonodromyAction_nonidentity h)

def concreteOperationSquareToyModel :
    OperationSquareToyModel.{0, 0, 0, 0, 0, 0} toyMeasuredSquareNonzero where
  finiteAxis := by
    change Fintype Bool
    infer_instance
  filling := toySquareFillingProblem
  nonzeroMu := by
    intro h
    cases h

theorem concreteOperationSquareToyModel_fires :
    ¬ toySquareFillingProblem.SelectedAxisFilling :=
  OperationSquareToyModel.verifies_square_nonfillability concreteOperationSquareToyModel

def toySquareFillingPositiveProblem :
    SquareMonodromyFillingProblem.{0, 0, 0, 0, 0, 0} toyMeasuredSquareNonzero where
  axis := true
  SelectedAxisFilling :=
    toyMeasuredSquareNonzero.axisDetectsIdentity true
  filling_implies_mu_zero := by
    intro _h
    rfl

theorem toySquareFilling_positive :
    toySquareFillingPositiveProblem.SelectedAxisFilling := by
  exact toyMonodromyAction.rho.map_one

theorem toySquareFilling_negative :
    ¬ toySquareFillingProblem.SelectedAxisFilling :=
  concreteOperationSquareToyModel_fires

theorem toyPresentedPi_nontrivial_word_maps_to_generator :
    toyPresentedPi.quotientMap toyNonemptyFreeWord = toyLoopGenerator :=
  toyQuotientMap_nonempty

theorem toyPresentedPi_nontrivial_word_not_identity :
    toyPresentedPi.quotientMap toyNonemptyFreeWord ≠ 1 := by
  simpa [toyPresentedPi_nontrivial_word_maps_to_generator] using toyLoopGenerator_ne_one

theorem toyTransportNonzero_uses_second_pi1_element :
    toyPresentedPi.quotientMap toyNonemptyFreeWord =
      toyLoopGenerator ∧ toyLoopGenerator ≠ (1 : toyPresentedPi.Pi1) :=
  ⟨toyPresentedPi_nontrivial_word_maps_to_generator,
    by simpa using toyLoopGenerator_ne_one⟩

def toyTransportDescentZero :
    TransportDescentProblem.{0, 0, 0, 0, 0, 0}
      (Pi := toyPresentedPi) (M := toyMonodromyAction) (K := toyPresentationTwoComplex) true where
  Square := Bool
  measured _ := toyMeasuredSquareZero
  relationBoundaryZero_iff_sendsRelators := by
    constructor
    · intro _h
      simpa [toyPresentedPi] using toyQuotientMap_empty
    · intro _h square axis
      cases axis <;> rfl

def toyTransportDescentNonzero :
    TransportDescentProblem.{0, 0, 0, 0, 0, 0}
      (Pi := toyPresentedPi) (M := toyMonodromyAction) (K := toyPresentationTwoComplex) false where
  Square := Bool
  measured _ := toyMeasuredSquareNonzero
  relationBoundaryZero_iff_sendsRelators := by
    constructor
    · intro h
      have hfalse := h false false
      cases hfalse
    · intro hfalse
      exact False.elim (toyPresentedPi_nontrivial_word_not_identity hfalse)

theorem toyTransportDescent_square_nontrivial :
    Nontrivial toyTransportDescentNonzero.Square := by
  change Nontrivial Bool
  infer_instance

def concreteTransportDescentZeroToyModel :
    TransportDescentZeroToyModel.{0, 0, 0, 0, 0, 0} toyTransportDescentZero where
  finiteSquares := inferInstance
  zeroBoundaryCase := by
    intro square axis
    cases axis <;> rfl

def concreteTransportDescentNonzeroToyModel :
    TransportDescentNonzeroToyModel.{0, 0, 0, 0, 0, 0} toyTransportDescentNonzero where
  finiteSquares := inferInstance
  nonzeroBoundaryCase := by
    intro h
    have hfalse := h false false
    cases hfalse

theorem concreteTransportDescentZero_descends :
    ∃ Q : toyPresentedPi.QuotientTransport,
      toyPresentedPi.FactorsThroughQuotient true Q :=
  TransportDescentZeroToyModel.zero_case_descends concreteTransportDescentZeroToyModel

theorem concreteTransportDescentNonzero_not_descend :
    ¬ ∃ Q : toyPresentedPi.QuotientTransport,
      toyPresentedPi.FactorsThroughQuotient false Q :=
  by
    intro hdescends
    have hsends := (toyPresentedPi.quotientUniversalProperty false).mpr hdescends
    exact toyPresentedPi_nontrivial_word_not_identity hsends

theorem toyTransportDescent_relationBoundaryZero_positive :
    toyTransportDescentZero.relationBoundaryZero :=
  concreteTransportDescentZeroToyModel.zeroBoundaryCase

theorem toyTransportDescent_relationBoundaryZero_negative :
    ¬ toyTransportDescentNonzero.relationBoundaryZero :=
  concreteTransportDescentNonzeroToyModel.nonzeroBoundaryCase

def toyBoolComp (f g : Bool) : Bool :=
  if f then !g else g

structure ToyRefactorHom (a b : Bool) where
  state_eq : a = b
  tag : Bool

def toyRefactorGroupoid :
    RefactorGroupoid.{0, 0, 0, 0, 0, 0} toyEndpointReading where
  Object := Bool
  state := id
  Hom := ToyRefactorHom
  toRefactorEquivalent f := f.state_eq
  id _ := ⟨rfl, false⟩
  inv h := ⟨h.state_eq.symm, h.tag⟩
  comp h g := ⟨h.state_eq.trans g.state_eq, toyBoolComp h.tag g.tag⟩
  id_comp := by
    intro a b f
    cases f with
    | mk h tag =>
        cases h
        cases tag <;> rfl
  comp_id := by
    intro a b f
    cases f with
    | mk h tag =>
        cases h
        cases tag <;> rfl
  assoc := by
    intro a b c d f g h
    cases f with
    | mk hf tf =>
        cases g with
        | mk hg tg =>
            cases h with
            | mk hh th =>
                cases hf
                cases hg
                cases hh
                cases tf <;> cases tg <;> cases th <;> rfl
  inv_comp := by
    intro a b f
    cases f with
    | mk h tag =>
        cases h
        cases tag <;> rfl
  comp_inv := by
    intro a b f
    cases f with
    | mk h tag =>
        cases h
        cases tag <;> rfl

theorem toyRefactorGroupoid_hom_nontrivial :
    Nontrivial (toyRefactorGroupoid.Hom false false) := by
  refine ⟨⟨rfl, false⟩, ⟨rfl, true⟩, ?_⟩
  intro h
  cases h

theorem toyRefactorGroupoid_hom_carries_state_equality
    {a b : toyRefactorGroupoid.Object} (f : toyRefactorGroupoid.Hom a b) :
    toyRefactorGroupoid.state a = toyRefactorGroupoid.state b :=
  f.state_eq

def toyPreservesRelation {a b : toyRefactorGroupoid.Object}
    (g : toyRefactorGroupoid.Hom a b) (i : Bool) : Prop :=
  g.tag = false ∨ i = true

theorem toyPreservesRelation_positive :
    toyPreservesRelation (⟨rfl, false⟩ : toyRefactorGroupoid.Hom false false) false :=
  Or.inl rfl

theorem toyPreservesRelation_negative :
    ¬ toyPreservesRelation (⟨rfl, true⟩ : toyRefactorGroupoid.Hom false false) false := by
  intro h
  rcases h with h | h <;> cases h

def toyGaloisData :
    OperationInvariantGaloisData.{0, 0, 0, 0, 0, 0} toyRefactorGroupoid where
  Invariant := Bool
  Preserves g i := toyPreservesRelation g i
  id_preserves := by
    intro a i
    exact Or.inl rfl
  inv_preserves := by
    intro a b g i h
    exact h
  comp_preserves := by
    intro a b c g h i hg hh
    change toyPreservesRelation ⟨g.state_eq.trans h.state_eq, toyBoolComp g.tag h.tag⟩ i
    rcases hg with hg | hi
    · rcases hh with hh | hi
      · left
        simp [toyBoolComp, hg, hh]
      · exact Or.inr hi
    · exact Or.inr hi

def concreteRefactorGaloisToyModel :
    RefactorGaloisToyModel.{0, 0, 0, 0, 0, 0} toyGaloisData where
  finiteInvariant := by
    change Fintype Bool
    infer_instance
  selectedOperations := fun {_a _b} g => g.tag = false
  selectedInvariants := fun i => i = false

theorem concreteRefactorGaloisToyModel_fires :
    RefactorMorphismFamilySubset concreteRefactorGaloisToyModel.selectedOperations
        (toyGaloisData.Ops concreteRefactorGaloisToyModel.selectedInvariants) ↔
      toyGaloisData.InvFamSubset concreteRefactorGaloisToyModel.selectedInvariants
        (toyGaloisData.Inv concreteRefactorGaloisToyModel.selectedOperations) :=
  RefactorGaloisToyModel.verifies_galois_connection concreteRefactorGaloisToyModel

theorem toyGaloisData_preserves_positive :
    toyGaloisData.Preserves (a := false) (b := false) ⟨rfl, false⟩ false :=
  toyPreservesRelation_positive

theorem toyGaloisData_preserves_negative :
    ¬ toyGaloisData.Preserves (a := false) (b := false) ⟨rfl, true⟩ false :=
  toyPreservesRelation_negative

def toyArchitectureStackBase : ArchitectureStackBase.{0} where
  Context := Bool
  Overlap _ _ := Bool
  TripleOverlap _ _ _ := Bool
  restrict _ _ := Bool
  idRestrict _ := false
  compRestrict r s := toyBoolComp r s
  id_comp := by
    intro T U r
    cases r <;> rfl
  comp_id := by
    intro T U r
    cases r <;> rfl
  assoc := by
    intro T U V W r s t
    cases r <;> cases s <;> cases t <;> rfl
  overlapContext := fun {a} {_b} _o => a
  overlap_left _ := false
  overlap_right _ := false
  tripleContext := fun {a} {_b} {_c} _t => a
  triple_to_leftOverlap _ _ := false
  triple_to_rightOverlap _ _ := false
  triple_to_outerOverlap _ _ := false

def toyDecompositionGroupoid : DecompositionGroupoid.{0} where
  Object := Bool
  Hom _ _ := Bool
  equivalenceKind _ := DecompositionEquivalenceKind.refactor
  id _ := false
  inv h := h
  comp h g := toyBoolComp h g
  id_comp := by
    intro a b f
    cases f <;> rfl
  comp_id := by
    intro a b f
    cases f <;> rfl
  assoc := by
    intro a b c d f g h
    cases f <;> cases g <;> cases h <;> rfl
  inv_comp := by
    intro a b f
    cases f <;> rfl
  comp_inv := by
    intro a b f
    cases f <;> rfl

theorem toyDecompositionGroupoid_hom_nontrivial :
    Nontrivial (toyDecompositionGroupoid.Hom false false) := by
  change Nontrivial Bool
  infer_instance

theorem toyDecompositionGroupoid_hom_kind_refactor
    {a b : toyDecompositionGroupoid.Object} (f : toyDecompositionGroupoid.Hom a b) :
    toyDecompositionGroupoid.equivalenceKind f =
      DecompositionEquivalenceKind.refactor :=
  rfl

def toyLocalDecomposition : Bool -> Bool := id

def toyBadLocalDecomposition : Bool -> Bool := fun _ => false

def ToyOverlapCompatible (loc : Bool -> Bool) : Prop :=
  loc false = false ∧ loc true = true

def toyGerbeClassFromLocalData (loc : Bool -> Bool) : Bool :=
  if loc false = loc true then false else true

def toyBadGerbeClassFromLocalData (loc : Bool -> Bool) : Bool :=
  loc false

def ToyAutSheafDefined (Aut : Type) : Prop :=
  ∃ a b : Aut, a ≠ b

def ToyNonAbelianReading (cls zero : Bool) : Prop :=
  cls ≠ zero

def ToyLocalDecompositionsExist (loc : Bool -> Bool) : Prop :=
  (∃ i, loc i = false) ∧ ∃ j, loc j = true

def ToyGlobalCanonicalDecomposition (loc : Bool -> Bool) : Prop :=
  ∃ global : Bool, ∀ i : Bool, loc i = global

def ToyEffectiveDescent (classOf : (Bool -> Bool) -> Bool) : Prop :=
  ∀ loc : Bool -> Bool,
    classOf loc = false -> ToyGlobalCanonicalDecomposition loc

theorem toyOverlapCompatible_positive :
    ToyOverlapCompatible toyLocalDecomposition := ⟨rfl, rfl⟩

theorem toyOverlapCompatible_negative :
    ¬ ToyOverlapCompatible toyBadLocalDecomposition := by
  intro h
  cases h.2

theorem toyLocalDecompositionsExist_positive :
    ToyLocalDecompositionsExist toyLocalDecomposition :=
  ⟨⟨false, rfl⟩, ⟨true, rfl⟩⟩

theorem toyLocalDecompositionsExist_negative :
    ¬ ToyLocalDecompositionsExist toyBadLocalDecomposition := by
  intro h
  rcases h.2 with ⟨j, hj⟩
  cases j <;> cases hj

theorem toyGlobalCanonicalDecomposition_positive :
    ToyGlobalCanonicalDecomposition toyBadLocalDecomposition :=
  ⟨false, by intro i; cases i <;> rfl⟩

theorem toyGlobalCanonicalDecomposition_vanishes_class
    {loc : Bool -> Bool} :
    ToyGlobalCanonicalDecomposition loc ->
      toyGerbeClassFromLocalData loc = false := by
  intro h
  rcases h with ⟨global, hglobal⟩
  have hsame : loc false = loc true := (hglobal false).trans (hglobal true).symm
  simp [toyGerbeClassFromLocalData, hsame]

theorem toyGlobalCanonicalDecomposition_negative :
    ¬ ToyGlobalCanonicalDecomposition toyLocalDecomposition := by
  intro h
  have hclass := toyGlobalCanonicalDecomposition_vanishes_class h
  simp [toyGerbeClassFromLocalData, toyLocalDecomposition] at hclass

theorem toyEffectiveDescent_positive :
    ToyEffectiveDescent toyGerbeClassFromLocalData := by
  intro loc hzero
  by_cases hsame : loc false = loc true
  · refine ⟨loc false, ?_⟩
    intro i
    cases i
    · rfl
    · exact hsame.symm
  · simp [toyGerbeClassFromLocalData, hsame] at hzero

theorem toyEffectiveDescent_negative :
    ¬ ToyEffectiveDescent toyBadGerbeClassFromLocalData := by
  intro h
  exact toyGlobalCanonicalDecomposition_negative (h toyLocalDecomposition rfl)

theorem toyGlobalCanonicalDecomposition_localData_contradiction :
    ToyGlobalCanonicalDecomposition toyLocalDecomposition -> False :=
  toyGlobalCanonicalDecomposition_negative

theorem toyAutSheafDefined_positive :
    ToyAutSheafDefined Bool :=
  ⟨false, true, by decide⟩

theorem toyAutSheafDefined_negative :
    ¬ ToyAutSheafDefined Empty := by
  intro h
  rcases h with ⟨a, b, hab⟩
  cases a

theorem toyNonAbelianReading_positive :
    ToyNonAbelianReading true false := by
  intro h
  cases h

theorem toyNonAbelianReading_negative :
    ¬ ToyNonAbelianReading false false := by
  intro h
  exact h rfl

theorem toyGerbeClassFromLocalData_nonzero :
    toyGerbeClassFromLocalData toyLocalDecomposition ≠ false := by
  intro h
  simp [toyGerbeClassFromLocalData, toyLocalDecomposition] at h

def toyDecompositionPresheaf : DecompositionPresheaf.{0} toyArchitectureStackBase where
  fiber _ := toyDecompositionGroupoid
  restrictObject := fun {_T _W} _r a => a
  restrictHom := fun {_T _W} _r {_a _b} f => f
  restrict_id _ _ := rfl
  restrict_comp := by
    intro _T _W _r _a _b _c _f _g
    rfl

def toyDecompositionStack : DecompositionStack.{0} toyArchitectureStackBase where
  presheaf := toyDecompositionPresheaf
  LocalIndex := Bool
  localContext := fun i => i
  localDecomposition := toyLocalDecomposition
  overlapCompatible := ToyOverlapCompatible toyLocalDecomposition
  overlapCompatible_cert := toyOverlapCompatible_positive
  effectiveDescent := ToyEffectiveDescent toyGerbeClassFromLocalData
  effectiveDescent_cert := toyEffectiveDescent_positive

def toyGerbeObstructionData :
    GerbeObstructionData.{0} toyDecompositionStack where
  GerbeClass := Bool
  zero := false
  gerbeClass := true
  nonzero := true ≠ false
  nonzero_cert := by
    intro hnonzero hzero
    exact hnonzero hzero
  automorphismSheaf := Bool
  autSheafDefined := ToyAutSheafDefined Bool
  autSheafDefined_cert := toyAutSheafDefined_positive
  nonAbelianReading := ToyNonAbelianReading true false
  nonAbelianReading_cert := toyNonAbelianReading_positive

theorem toyGerbeClass_eq_computed_local_class :
    toyGerbeObstructionData.gerbeClass =
      toyGerbeClassFromLocalData toyLocalDecomposition := by
  rfl

theorem toyNoCanonicalDecomposition_soundness_from_local_data :
    ToyGlobalCanonicalDecomposition toyLocalDecomposition ->
      toyGerbeObstructionData.gerbeClass = toyGerbeObstructionData.zero := by
  intro hglobal
  have hclass := toyGlobalCanonicalDecomposition_vanishes_class hglobal
  exact hclass

def toyNoCanonicalDecompositionData :
    NoCanonicalDecompositionData.{0} toyGerbeObstructionData where
  localDecompositionsExist := ToyLocalDecompositionsExist toyLocalDecomposition
  localDecompositionsExist_cert := toyLocalDecompositionsExist_positive
  globalCanonicalDecomposition :=
    ToyGlobalCanonicalDecomposition toyLocalDecomposition
  soundness := toyNoCanonicalDecomposition_soundness_from_local_data

def concreteDecompositionGerbeToyModel :
    DecompositionGerbeToyModel.{0} toyGerbeObstructionData where
  finiteLocalIndex := by
    change Fintype Bool
    infer_instance
  noCanonicalData := toyNoCanonicalDecompositionData
  nonzeroGerbe := by
    intro h
    cases h

theorem concreteDecompositionGerbeToyModel_fires :
    toyDecompositionStack.overlapCompatible ∧
      toyDecompositionStack.effectiveDescent ∧
      toyNoCanonicalDecompositionData.localDecompositionsExist ∧
      toyGerbeObstructionData.autSheafDefined ∧
      toyGerbeObstructionData.nonAbelianReading ∧
      toyGerbeObstructionData.gerbeClass =
        toyGerbeClassFromLocalData toyLocalDecomposition ∧
      toyGerbeClassFromLocalData toyLocalDecomposition ≠
        toyGerbeObstructionData.zero ∧
      ¬ toyNoCanonicalDecompositionData.globalCanonicalDecomposition := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact toyDecompositionStack.overlapCompatible_cert
  · exact toyDecompositionStack.effectiveDescent_cert
  · exact toyNoCanonicalDecompositionData.localDecompositionsExist_cert
  · exact toyGerbeObstructionData.autSheafDefined_cert
  · exact toyGerbeObstructionData.nonAbelianReading_cert
  · exact toyGerbeClass_eq_computed_local_class
  · exact toyGerbeClassFromLocalData_nonzero
  · exact DecompositionGerbeToyModel.verifies_no_canonical_decomposition
      concreteDecompositionGerbeToyModel

theorem concreteDecompositionGerbeToyModel_no_global :
    ¬ toyNoCanonicalDecompositionData.globalCanonicalDecomposition :=
  concreteDecompositionGerbeToyModel_fires.2.2.2.2.2.2.2

end SingularityMonodromyStackPart6
end FiniteModel
end AAT.AG
