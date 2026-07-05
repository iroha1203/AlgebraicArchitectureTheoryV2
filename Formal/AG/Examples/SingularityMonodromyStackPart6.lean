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
  h1NonzeroClass := True
  realizes_nonzero_obstruction := by
    intro _h h
    cases h

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
  nonzeroBoundaryClass := trivial

theorem concreteSingularBoundaryToyModel_fires :
    USingularBoundary toyDeformationTheory :=
  SingularBoundaryToyModel.verifies_singular_boundary concreteSingularBoundaryToyModel

def toyOperationCategory :
    OperationCategoryData.{0, 0, 0, 0, 0, 0} ToyStratum where
  State := Bool
  Operation _ _ := PUnit
  selectedState _ := false
  operationRespectsLawUniverse _ := True

def toyEndpointReading :
    RefactorEndpointReading.{0, 0, 0, 0, 0, 0} toyOperationCategory where
  RefactorEquivalent _ _ := True
  refl _ := trivial
  symm _ := trivial
  trans _ _ := trivial
  preservesSelectedInvariants _ := True
  preservesSelectedEssence _ := True
  invariantCertificate _ := trivial
  essenceCertificate _ := trivial

def toySelectedOperation : SelectedOperation toyOperationCategory false true where
  op := PUnit.unit
  respectsLawUniverse := trivial

def toyHomotopyGenerators :
    HomotopyGeneratorFamily.{0, 0, 0, 0, 0, 0} toyEndpointReading where
  PathCell := Bool
  cellSource _ := false
  cellTarget _ := true
  leftPath _ :=
    OperationPath.cons toySelectedOperation (OperationPath.nil (G := toyOperationCategory) true)
  rightPath _ :=
    OperationPath.cons toySelectedOperation (OperationPath.nil (G := toyOperationCategory) true)
  LoopRelator := PUnit
  relatorBase _ := false
  relatorLoop _ := OperationLoop.identity false
  relator_based _ := rfl

def toyPresentationTwoComplex :
    PresentationTwoComplex.{0, 0, 0, 0, 0, 0} toyHomotopyGenerators where
  Vertex := Bool
  vertexEquivState := Equiv.refl Bool
  Edge := PUnit
  edgeBoundary _ := ⟨false, true, toySelectedOperation⟩
  TwoCell := Bool
  twoCellEquivGenerator := by
    change Bool ≃ Bool
    exact Equiv.refl Bool

abbrev ToyFreeWord :=
  FreeEdgeWord toyOperationCategory false

def toyEmptyFreeWord : ToyFreeWord where
  steps := []
  startsAtBase := True

def toyPresentedPi :
    PresentedArchitectureFundamentalGroup.{0, 0, 0, 0, 0, 0}
      toyHomotopyGenerators false where
  FreeWord := ToyFreeWord
  freeWordEquivSelected := Equiv.refl ToyFreeWord
  Relator w := w = toyEmptyFreeWord
  presentation := toyPresentationTwoComplex
  pathCellRelatorWord _ := toyEmptyFreeWord
  pathCellRelator_selected _ := rfl
  loopRelatorWord _ := toyEmptyFreeWord
  loopRelator_selected _ := rfl
  relator_generated_by_selected_generator := by
    intro w h
    exact Or.inl ⟨(show toyHomotopyGenerators.PathCell from false), h.symm⟩
  Pi1 := PUnit
  quotientMap _ := PUnit.unit
  relator_maps_to_identity _ _ := rfl
  FreeTransport := Bool
  QuotientTransport := PUnit
  SendsRelatorsToIdentity T := T = true
  FactorsThroughQuotient T _ := T = true
  quotientUniversalProperty := by
    intro T
    constructor
    · intro h
      exact ⟨PUnit.unit, h⟩
    · intro h
      rcases h with ⟨_Q, hT⟩
      exact hT

def toyMonodromyAction :
    MonodromyAction.{0, 0, 0, 0, 0, 0} toyPresentedPi where
  coefficient := { Ob := Bool, Sem := Bool, Eff := Bool }
  rho _ := CoefficientAutomorphism.id _
  rho_one := rfl
  rho_mul _ _ := rfl

def toyMeasuredSquareZero :
    MeasuredSquareMonodromy.{0, 0, 0, 0, 0, 0} toyMonodromyAction
      toyPresentationTwoComplex where
  Axis := Bool
  square := false
  boundaryElement := PUnit.unit
  boundaryTransport := CoefficientAutomorphism.id _
  boundaryTransport_eq_monodromy := rfl
  equalityDefect _ := 0
  axisDetectsIdentity _ := True
  zero_defect_detects _ _ := trivial
  mu _ := 0
  mu_eq_defect _ := rfl

def toyMeasuredSquareNonzero :
    MeasuredSquareMonodromy.{0, 0, 0, 0, 0, 0} toyMonodromyAction
      toyPresentationTwoComplex where
  Axis := Bool
  square := true
  boundaryElement := PUnit.unit
  boundaryTransport := CoefficientAutomorphism.id _
  boundaryTransport_eq_monodromy := rfl
  equalityDefect axis := if axis then 0 else 1
  axisDetectsIdentity axis := axis = true
  zero_defect_detects := by
    intro axis hzero
    cases axis <;> simp at hzero ⊢
  mu axis := if axis then 0 else 1
  mu_eq_defect _ := rfl

def toySquareFillingProblem :
    SquareMonodromyFillingProblem.{0, 0, 0, 0, 0, 0} toyMeasuredSquareNonzero where
  axis := false
  SelectedAxisFilling := False
  filling_implies_mu_zero := by
    intro h
    cases h

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

def toyTransportDescentZero :
    TransportDescentProblem.{0, 0, 0, 0, 0, 0}
      (Pi := toyPresentedPi) (M := toyMonodromyAction) (K := toyPresentationTwoComplex) true where
  Square := PUnit
  measured _ := toyMeasuredSquareZero
  relationBoundaryZero_iff_sendsRelators := by
    constructor
    · intro _h
      rfl
    · intro _h square axis
      cases square
      cases axis <;> rfl

def toyTransportDescentNonzero :
    TransportDescentProblem.{0, 0, 0, 0, 0, 0}
      (Pi := toyPresentedPi) (M := toyMonodromyAction) (K := toyPresentationTwoComplex) false where
  Square := PUnit
  measured _ := toyMeasuredSquareNonzero
  relationBoundaryZero_iff_sendsRelators := by
    constructor
    · intro h
      have hfalse := h PUnit.unit false
      cases hfalse
    · intro hfalse
      cases hfalse

def concreteTransportDescentZeroToyModel :
    TransportDescentZeroToyModel.{0, 0, 0, 0, 0, 0} toyTransportDescentZero where
  finiteSquares := inferInstance
  zeroBoundaryCase := by
    intro square axis
    cases square
    cases axis <;> rfl

def concreteTransportDescentNonzeroToyModel :
    TransportDescentNonzeroToyModel.{0, 0, 0, 0, 0, 0} toyTransportDescentNonzero where
  finiteSquares := inferInstance
  nonzeroBoundaryCase := by
    intro h
    have hfalse := h PUnit.unit false
    cases hfalse

theorem concreteTransportDescentZero_descends :
    ∃ Q : toyPresentedPi.QuotientTransport,
      toyPresentedPi.FactorsThroughQuotient true Q :=
  TransportDescentZeroToyModel.zero_case_descends concreteTransportDescentZeroToyModel

theorem concreteTransportDescentNonzero_not_descend :
    ¬ ∃ Q : toyPresentedPi.QuotientTransport,
      toyPresentedPi.FactorsThroughQuotient false Q :=
  TransportDescentNonzeroToyModel.nonzero_case_not_descend concreteTransportDescentNonzeroToyModel

def toyRefactorGroupoid :
    RefactorGroupoid.{0, 0, 0, 0, 0, 0} toyEndpointReading where
  Object := Bool
  state := id
  Hom _ _ := PUnit
  toRefactorEquivalent _ := trivial
  id _ := PUnit.unit
  inv _ := PUnit.unit
  comp _ _ := PUnit.unit
  id_comp _ := rfl
  comp_id _ := rfl
  assoc _ _ _ := rfl
  inv_comp _ := rfl
  comp_inv _ := rfl

def toyGaloisData :
    OperationInvariantGaloisData.{0, 0, 0, 0, 0, 0} toyRefactorGroupoid where
  Invariant := Bool
  Preserves _ _ := True
  id_preserves _ _ := trivial
  inv_preserves _ _ _ := trivial
  comp_preserves _ _ _ _ _ := trivial

def concreteRefactorGaloisToyModel :
    RefactorGaloisToyModel.{0, 0, 0, 0, 0, 0} toyGaloisData where
  finiteInvariant := by
    change Fintype Bool
    infer_instance
  selectedOperations := fun {_a _b} _g => True
  selectedInvariants := fun i => i = true

theorem concreteRefactorGaloisToyModel_fires :
    RefactorMorphismFamilySubset concreteRefactorGaloisToyModel.selectedOperations
        (toyGaloisData.Ops concreteRefactorGaloisToyModel.selectedInvariants) ↔
      toyGaloisData.InvFamSubset concreteRefactorGaloisToyModel.selectedInvariants
        (toyGaloisData.Inv concreteRefactorGaloisToyModel.selectedOperations) :=
  RefactorGaloisToyModel.verifies_galois_connection concreteRefactorGaloisToyModel

def toyArchitectureStackBase : ArchitectureStackBase.{0} where
  Context := Bool
  Overlap _ _ := PUnit
  TripleOverlap _ _ _ := PUnit
  restrict _ _ := PUnit
  idRestrict _ := PUnit.unit
  compRestrict _ _ := PUnit.unit
  id_comp _ := rfl
  comp_id _ := rfl
  assoc _ _ _ := rfl
  overlapContext := fun {a} {_b} _o => a
  overlap_left _ := PUnit.unit
  overlap_right _ := PUnit.unit
  tripleContext := fun {a} {_b} {_c} _t => a
  triple_to_leftOverlap _ _ := PUnit.unit
  triple_to_rightOverlap _ _ := PUnit.unit
  triple_to_outerOverlap _ _ := PUnit.unit

def toyDecompositionGroupoid : DecompositionGroupoid.{0} where
  Object := Bool
  Hom _ _ := PUnit
  equivalenceKind _ := DecompositionEquivalenceKind.refactor
  id _ := PUnit.unit
  inv _ := PUnit.unit
  comp _ _ := PUnit.unit
  id_comp _ := rfl
  comp_id _ := rfl
  assoc _ _ _ := rfl
  inv_comp _ := rfl
  comp_inv _ := rfl

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
  localDecomposition i := i
  overlapCompatible := True
  overlapCompatible_cert := trivial
  effectiveDescent := True
  effectiveDescent_cert := trivial

def toyGerbeObstructionData :
    GerbeObstructionData.{0} toyDecompositionStack where
  GerbeClass := Bool
  zero := false
  gerbeClass := true
  nonzero := True
  nonzero_cert := by
    intro _h h
    cases h
  automorphismSheaf := Bool
  autSheafDefined := True
  autSheafDefined_cert := trivial
  nonAbelianReading := True
  nonAbelianReading_cert := trivial

def toyNoCanonicalDecompositionData :
    NoCanonicalDecompositionData.{0} toyGerbeObstructionData where
  localDecompositionsExist := True
  localDecompositionsExist_cert := trivial
  globalCanonicalDecomposition := False
  soundness := by
    intro h
    cases h

def concreteDecompositionGerbeToyModel :
    DecompositionGerbeToyModel.{0} toyGerbeObstructionData where
  finiteLocalIndex := by
    change Fintype Bool
    infer_instance
  noCanonicalData := toyNoCanonicalDecompositionData
  nonzeroGerbe := trivial

theorem concreteDecompositionGerbeToyModel_fires :
    ¬ toyNoCanonicalDecompositionData.globalCanonicalDecomposition :=
  DecompositionGerbeToyModel.verifies_no_canonical_decomposition
    concreteDecompositionGerbeToyModel

end SingularityMonodromyStackPart6
end FiniteModel
end AAT.AG
