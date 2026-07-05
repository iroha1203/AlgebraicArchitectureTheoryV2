import Formal.AG.Examples.FiniteModel
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

end SingularityMonodromyStackPart6
end FiniteModel
end AAT.AG
