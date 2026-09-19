import ResearchLean.AG.LocalSemanticReconstruction.CompleteGeometryGraphCategoryEquivalence
import Formal.Util.AssertStandardAxioms

/-!
# Explicit package data and reader-mediated category operations

Cycle 73 constructs eight package fields from predecessor graph-code
operations.  Its package context/observable field is instead read from the
equation transport of assembled package codes, and the package certificate is
transported from the canonical reader after a nine-field comparison.  The
standalone direct context/observable constructor is not yet connected to that
package field.  Thus this checkpoint proves separation, assembly formulas,
universality, category laws, and Cycle 72 comparisons, but it does not close
the pending direct package-certificate obligation.
-/

namespace AAT.AG.LocalSemanticReconstruction

open CategoryTheory AtomFoundation GeometryTransport

noncomputable section

namespace CompleteGeometryDirectCategory

universe u v w

namespace ContextObservableGraphCode

open ContextObservableGraphCoherence
open DependentAlgebraicGraphCoherence

/-- Extensionality for a joint context/observable code over arbitrary equation
systems. -/
theorem ext
    {U : AtomCarrier.{u}} {A₀ B₀ : ArchitectureObject U}
    {C : Site.ContextPreorderCategory A₀}
    {D : Site.ContextPreorderCategory B₀}
    {P : ArchitecturalEquationSystem C}
    {Q : ArchitecturalEquationSystem D}
    {first second : ContextObservableGraphCode P Q}
    (context : first.context = second.context)
    (observable : HEq first.observable second.observable) : first = second := by
  cases first
  cases second
  cases context
  cases observable
  rfl

/-- Observable graph codes over one fixed context functor are separated by
their assembled natural isomorphisms. -/
theorem observable_ext_of_assembleIso_eq
    {U : AtomCarrier.{u}} {A₀ B₀ : ArchitectureObject U}
    {C : Site.ContextPreorderCategory A₀}
    {D : Site.ContextPreorderCategory B₀}
    {P : ArchitecturalEquationSystem C}
    {Q : ArchitecturalEquationSystem D}
    {contextFunctor :
      CategoryTheory.Functor
        (Site.ContextCategoryObject C) (Site.ContextCategoryObject D)}
    (first second : ObservablePresheafGraphCode P Q contextFunctor)
    (iso_eq : first.assembleIso = second.assembleIso) : first = second := by
  rcases first with ⟨⟨first⟩, firstLaw⟩
  rcases second with ⟨⟨second⟩, secondLaw⟩
  have raw_eq : first = second := by
    funext W
    apply RingEquivGraphCode.equivRingEquiv.injective
    apply RingEquiv.ext
    intro value
    have equality := congrArg
      (fun iso => iso.hom.app (Opposite.op W) value) iso_eq
    exact equality
  cases raw_eq
  rfl

/-- Reindexing an observable code changes only its dependent functor type. -/
theorem observable_reindex_heq
    {U : AtomCarrier.{u}} {A₀ B₀ : ArchitectureObject U}
    {C : Site.ContextPreorderCategory A₀}
    {D : Site.ContextPreorderCategory B₀}
    {P : ArchitecturalEquationSystem C}
    {Q : ArchitecturalEquationSystem D}
    {firstFunctor secondFunctor :
      CategoryTheory.Functor
        (Site.ContextCategoryObject C) (Site.ContextCategoryObject D)}
    (functor_eq : firstFunctor = secondFunctor)
    (code : ObservablePresheafGraphCode P Q secondFunctor) :
    HEq (ObservablePresheafGraphCode.reindex functor_eq code) code := by
  cases functor_eq
  rfl

/-- Observable codes over propositionally equal context functors are
heterogeneously equal when their computational ring-graph families agree. -/
theorem observable_heq
    {U : AtomCarrier.{u}} {A₀ B₀ : ArchitectureObject U}
    {C : Site.ContextPreorderCategory A₀}
    {D : Site.ContextPreorderCategory B₀}
    {P : ArchitecturalEquationSystem C}
    {Q : ArchitecturalEquationSystem D}
    {firstFunctor secondFunctor :
      CategoryTheory.Functor
        (Site.ContextCategoryObject C) (Site.ContextCategoryObject D)}
    (functor_eq : firstFunctor = secondFunctor)
    (first : ObservablePresheafGraphCode P Q firstFunctor)
    (second : ObservablePresheafGraphCode P Q secondFunctor)
    (observable : HEq first.1.observable second.1.observable) :
    HEq first second := by
  cases functor_eq
  rcases first with ⟨⟨firstObservable⟩, firstLaw⟩
  rcases second with ⟨⟨secondObservable⟩, secondLaw⟩
  change HEq firstObservable secondObservable at observable
  cases observable
  rfl

/-- Pointwise ring-graph families over equal index maps are heterogeneously
equal when every fiber graph is. -/
theorem indexedRingGraph_heq
    {I J : Type*} {A : I → Type*} {B : J → Type*}
    [∀ i, NonAssocSemiring (A i)] [∀ j, NonAssocSemiring (B j)]
    {firstIndex secondIndex : I → J}
    (index_eq : firstIndex = secondIndex)
    (first : IndexedRingEquivGraphCode firstIndex A B)
    (second : IndexedRingEquivGraphCode secondIndex A B)
    (fiber : ∀ i, HEq (first i) (second i)) : HEq first second := by
  cases index_eq
  apply heq_of_eq
  funext i
  exact eq_of_heq (fiber i)

/-- Cycle 73 direct context/observable composition datum.
Premise summary: the two supplied joint codes carry their own observable
naturality certificates; no completed equation transport is supplied. -/
noncomputable def comp
    {U : AtomCarrier.{u}} {A₀ B₀ C₀ : ArchitectureObject U}
    {C : Site.ContextPreorderCategory A₀}
    {D : Site.ContextPreorderCategory B₀}
    {E : Site.ContextPreorderCategory C₀}
    {P : ArchitecturalEquationSystem C}
    {Q : ArchitecturalEquationSystem D}
    {R : ArchitecturalEquationSystem E}
    (first : ContextObservableGraphCode P Q)
    (second : ContextObservableGraphCode Q R) :
    ContextObservableGraphCode P R := by
  let context := ThinEquivalenceGraphCode.comp first.context second.context
  have functor_eq : context.forwardFunctor =
      first.context.forwardFunctor ⋙ second.context.forwardFunctor := by
    change context.assemble.functor =
      (first.context.assemble.trans second.context.assemble).functor
    exact congrArg CategoryTheory.Equivalence.functor
      (ThinEquivalenceGraphCode.assemble_comp first.context second.context)
  let observable : ObservablePresheafGraphCode P R
      (first.context.forwardFunctor ⋙ second.context.forwardFunctor) := by
    let data : ObservablePresheafGraphData P R
        (first.context.forwardFunctor ⋙ second.context.forwardFunctor) := {
      observable := IndexedRingEquivGraphCode.comp
        (firstIndex := first.context.forwardFunctor.obj)
        (secondIndex := second.context.forwardFunctor.obj)
        (A := P.Observable) (B := Q.Observable) (C := R.Observable)
        first.observable.1.observable second.observable.1.observable }
    refine ⟨data, ⟨?_⟩⟩
    intro W V f value
    change
      (IndexedRingEquivGraphCode.comp
        (firstIndex := first.context.forwardFunctor.obj)
        (secondIndex := second.context.forwardFunctor.obj)
        (A := P.Observable) (B := Q.Observable) (C := R.Observable)
        first.observable.1.observable
        second.observable.1.observable).assemble W (P.restrict f value) = _
    rw [IndexedRingEquivGraphCode.assemble_comp]
    dsimp [data]
    rw [IndexedRingEquivGraphCode.assemble_comp]
    change
      second.observable.1.observable.assemble
          (first.context.forwardFunctor.obj W)
          (first.observable.1.observable.assemble W (P.restrict f value)) =
        R.restrict
          ((first.context.forwardFunctor ⋙
            second.context.forwardFunctor).map f)
          (second.observable.1.observable.assemble
            (first.context.forwardFunctor.obj V)
            (first.observable.1.observable.assemble V value))
    rw [first.observable.2.observable_naturality]
    rw [second.observable.2.observable_naturality]
    rfl
  exact {
    context := context
    observable := ObservablePresheafGraphCode.reindex functor_eq observable }

end ContextObservableGraphCode

namespace PackageGraphCode

open CompleteGeometryGraphAssembly
open RemainingComponentGraphCoherence

/-- Extensionality for raw package graph data, including its dependent
operation and signature fields. -/
theorem data_ext
    {U : AtomCarrier.{u}} {G H : GeometryPackage.{u, v} U}
    {first second : PackageGraphData G H}
    (source : first.source = second.source)
    (pointedAtom : first.pointedAtom = second.pointedAtom)
    (atom : first.atom = second.atom)
    (object : first.object = second.object)
    (equation : first.equation = second.equation)
    (contextObservable : HEq first.contextObservable second.contextObservable)
    (operation : HEq first.operation second.operation)
    (invariant : first.invariant = second.invariant)
    (signature : HEq first.signature second.signature) : first = second := by
  cases first
  cases second
  cases source
  cases pointedAtom
  cases atom
  cases object
  cases equation
  cases contextObservable
  cases operation
  cases invariant
  cases signature
  rfl

/-- Reindex both endpoints of a dependent operation graph along equality of
the decoded object map. -/
def reindexOperation
    {U : AtomCarrier.{u}} {P Q : AATCorePackage U}
    {first second : ArchitectureObject U → ArchitectureObject U}
    (object_eq : first = second)
    (code : BiIndexedFunctionGraphCode second second
      (fun A B => P.reading.operationReading.Op A B)
      (fun A B => Q.reading.operationReading.Op A B)) :
    BiIndexedFunctionGraphCode first first
      (fun A B => P.reading.operationReading.Op A B)
      (fun A B => Q.reading.operationReading.Op A B) := by
  cases object_eq
  exact code

/-- Reindexing a dependent operation code changes only its endpoint-map type. -/
theorem reindexOperation_heq
    {U : AtomCarrier.{u}} {P Q : AATCorePackage U}
    {first second : ArchitectureObject U → ArchitectureObject U}
    (object_eq : first = second)
    (code : BiIndexedFunctionGraphCode second second
      (fun A B => P.reading.operationReading.Op A B)
      (fun A B => Q.reading.operationReading.Op A B)) :
    HEq (reindexOperation object_eq code) code := by
  cases object_eq
  rfl

/-- Reindex a signature graph code along equality of its decoded object map. -/
def reindexSignature
    {U : AtomCarrier.{u}} {P Q : AATCorePackage U}
    {first second : ArchitectureObject U → ArchitectureObject U}
    (object_eq : first = second)
    (code : SignatureGraphCode P Q second) :
    SignatureGraphCode P Q first := by
  cases object_eq
  exact code

/-- Reindexing a signature code changes only its decoded object-map type. -/
theorem reindexSignature_heq
    {U : AtomCarrier.{u}} {P Q : AATCorePackage U}
    {first second : ArchitectureObject U → ArchitectureObject U}
    (object_eq : first = second)
    (code : SignatureGraphCode P Q second) :
    HEq (reindexSignature object_eq code) code := by
  cases object_eq
  rfl

/-- Cycle 73 package identity data.  Eight fields use predecessor identities;
the context/observable field reads the reflexive equation transport. -/
noncomputable def idData
    {U : AtomCarrier.{u}} (G : GeometryPackage.{u, v} U) :
    PackageGraphData G G := by
  let object : PrimitiveFunctionGraph.GraphCode
      (ArchitectureObject U) (ArchitectureObject U) :=
    PrimitiveFunctionGraph.GraphCode.id
  have object_eq : object.assemble = _root_.id :=
    PrimitiveFunctionGraph.GraphCode.assemble_id
  exact {
    source := PrimitiveFunctionGraph.GraphCode.id
    pointedAtom := AlgebraicGraphCoherence.EquivGraphCode.id _
    atom := AlgebraicGraphCoherence.EquivGraphCode.id _
    object := object
    equation := AlgebraicGraphCoherence.EquivGraphCode.id _
    contextObservable :=
      ContextObservableGraphCoherence.ContextObservableGraphCode.read
        (EquationSystemExactTransport.refl G.core.algebra.equationSystem)
    operation := reindexOperation object_eq
      (BiIndexedFunctionGraphCode.id)
    invariant := PrimitiveFunctionGraph.GraphCode.id
    signature := reindexSignature object_eq
      (SignatureGraphCode.id G.core) }

/-- Canonical package identity used as the fieldwise comparison target and as
the source of the lawful package certificate. -/
noncomputable def canonicalIdentity
    {U : AtomCarrier.{u}} (G : GeometryPackage.{u, v} U) :
    PackageGraphCode G G :=
  CompleteGeometryGraphAssembly.PackageGraphCode.read
    (PackageTotalHom.id G.core)

/-- Componentwise signature identity agrees across object-map reindexing with
the signature read from the assembled package identity. -/
theorem signature_id_heq_canonical
    {U : AtomCarrier.{u}} (G : GeometryPackage.{u, v} U) :
    HEq (SignatureGraphCode.id G.core)
      (canonicalIdentity G).1.signature := by
  dsimp [SignatureGraphCode.id, canonicalIdentity,
    CompleteGeometryGraphAssembly.PackageGraphCode.read]
  refine CompleteGeometryGraphAssembly.PackageGraphCode.signatureRead_heq
    (first := SignatureGraphCode.supplyId G.core) ?_ ?_ ?_ ?_
  · exact (PrimitiveFunctionGraph.GraphCode.assemble_read _).symm
  · rfl
  · rfl

/-- The package identity data is separated by the canonical reader in every
computational field, including dependent operation and signature families. -/
theorem idData_eq_canonical
    {U : AtomCarrier.{u}} (G : GeometryPackage.{u, v} U) :
    idData G = (canonicalIdentity G).1 := by
  apply data_ext
  · apply PrimitiveFunctionGraph.GraphCode.assemble_injective
    dsimp [idData, canonicalIdentity,
      CompleteGeometryGraphAssembly.PackageGraphCode.read]
    rw [PrimitiveFunctionGraph.GraphCode.assemble_id,
      PrimitiveFunctionGraph.GraphCode.assemble_read]
    rfl
  · apply AlgebraicGraphCoherence.EquivGraphCode.equivEquiv.injective
    dsimp [idData, canonicalIdentity,
      CompleteGeometryGraphAssembly.PackageGraphCode.read]
    change
      (AlgebraicGraphCoherence.EquivGraphCode.id U.Atom).assemble =
      (AlgebraicGraphCoherence.EquivGraphCode.read
        (PackageTotalHom.id G.core).base.doctrineHom.atomEquiv).assemble
    rw [AlgebraicGraphCoherence.EquivGraphCode.assemble_id,
      AlgebraicGraphCoherence.EquivGraphCode.assemble_read]
    rfl
  · apply AlgebraicGraphCoherence.EquivGraphCode.equivEquiv.injective
    dsimp [idData, canonicalIdentity,
      CompleteGeometryGraphAssembly.PackageGraphCode.read]
    change
      (AlgebraicGraphCoherence.EquivGraphCode.id U.Atom).assemble =
      (AlgebraicGraphCoherence.EquivGraphCode.read
        (PackageTotalHom.id G.core).upper.atomEquiv).assemble
    rw [AlgebraicGraphCoherence.EquivGraphCode.assemble_id,
      AlgebraicGraphCoherence.EquivGraphCode.assemble_read]
    rfl
  · apply PrimitiveFunctionGraph.GraphCode.assemble_injective
    dsimp [idData, canonicalIdentity,
      CompleteGeometryGraphAssembly.PackageGraphCode.read]
    rw [PrimitiveFunctionGraph.GraphCode.assemble_id,
      PrimitiveFunctionGraph.GraphCode.assemble_read]
    rfl
  · apply AlgebraicGraphCoherence.EquivGraphCode.equivEquiv.injective
    dsimp [idData, canonicalIdentity,
      CompleteGeometryGraphAssembly.PackageGraphCode.read]
    change
      (AlgebraicGraphCoherence.EquivGraphCode.id
        G.core.algebra.equationSystem.Index).assemble =
      (AlgebraicGraphCoherence.EquivGraphCode.read
        (PackageTotalHom.id G.core).upper.equationTransport.equationEquiv).assemble
    rw [AlgebraicGraphCoherence.EquivGraphCode.assemble_id,
      AlgebraicGraphCoherence.EquivGraphCode.assemble_read]
    rfl
  · rfl
  · dsimp [idData, canonicalIdentity,
      CompleteGeometryGraphAssembly.PackageGraphCode.read]
    apply HEq.trans (reindexOperation_heq _ _)
    apply HEq.trans (heq_of_eq
      (BiIndexedFunctionGraphCode.read_assemble _).symm)
    apply HEq.trans ?_
      (CompleteGeometryGraphAssembly.PackageGraphCode.read_reindexOperationFamily_heq
        _ _ _ _).symm
    apply heq_of_eq
    congr 1
    funext A B op
    simp [BiIndexedFunctionGraphCode.id, PackageTotalHom.id,
      SignedExactCoreReadingHom.refl]
  · apply PrimitiveFunctionGraph.GraphCode.assemble_injective
    dsimp [idData, canonicalIdentity,
      CompleteGeometryGraphAssembly.PackageGraphCode.read]
    rw [PrimitiveFunctionGraph.GraphCode.assemble_id,
      PrimitiveFunctionGraph.GraphCode.assemble_read]
    rfl
  · dsimp [idData]
    apply HEq.trans (reindexSignature_heq _ _)
    exact signature_id_heq_canonical G

/-- Cycle 73 package graph data composition.
Premise summary: only the two supplied lawful package codes are used.  Eight
graph fields compose through predecessor operations; the context/observable
field reads the composition of equation transports obtained by assembling
the package inputs.  No completed package morphism is retained in the result. -/
noncomputable def compData
    {U : AtomCarrier.{u}} {G H K : GeometryPackage.{u, v} U}
    (first : PackageGraphCode G H)
    (second : PackageGraphCode H K) : PackageGraphData G K := by
  let object := PrimitiveFunctionGraph.GraphCode.comp
    first.1.object second.1.object
  have object_eq : object.assemble =
      second.1.object.assemble ∘ first.1.object.assemble :=
    PrimitiveFunctionGraph.GraphCode.assemble_comp _ _
  let operation := reindexOperation object_eq
    (BiIndexedFunctionGraphCode.comp first.1.operation second.1.operation)
  let signature := reindexSignature object_eq
    (SignatureGraphCode.comp first.1.signature second.1.signature)
  exact {
    source := PrimitiveFunctionGraph.GraphCode.comp
      first.1.source second.1.source
    pointedAtom := AlgebraicGraphCoherence.EquivGraphCode.comp
      first.1.pointedAtom second.1.pointedAtom
    atom := AlgebraicGraphCoherence.EquivGraphCode.comp
      first.1.atom second.1.atom
    object := object
    equation := AlgebraicGraphCoherence.EquivGraphCode.comp
      first.1.equation second.1.equation
    contextObservable :=
      ContextObservableGraphCoherence.ContextObservableGraphCode.read
        (first.assemble.upper.equationTransport.comp
          second.assemble.upper.equationTransport)
    operation := operation
    invariant := PrimitiveFunctionGraph.GraphCode.comp
      first.1.invariant second.1.invariant
    signature := signature }

/-- Cycle 73 canonical comparison target and lawful-certificate source. -/
noncomputable def canonicalComposite
    {U : AtomCarrier.{u}} {G H K : GeometryPackage.{u, v} U}
    (first : PackageGraphCode G H)
    (second : PackageGraphCode H K) : PackageGraphCode G K :=
  CompleteGeometryGraphAssembly.PackageGraphCode.read
    (PackageTotalHom.comp first.assemble second.assemble)

/-- Componentwise signature composition agrees, across the decoded object-map
reindexing, with the signature read from assembled package composition. -/
theorem signature_comp_heq_canonical
    {U : AtomCarrier.{u}} {G H K : GeometryPackage.{u, v} U}
    (first : PackageGraphCode G H)
    (second : PackageGraphCode H K) :
    HEq (SignatureGraphCode.comp first.1.signature second.1.signature)
      (CompleteGeometryGraphAssembly.PackageGraphCode.read
        (PackageTotalHom.comp first.assemble second.assemble)).1.signature := by
  dsimp [SignatureGraphCode.comp,
    CompleteGeometryGraphAssembly.PackageGraphCode.read]
  refine CompleteGeometryGraphAssembly.PackageGraphCode.signatureRead_heq
    (first := SignatureGraphCode.supplyComp
      first.1.signature.assemble second.1.signature.assemble) ?_ ?_ ?_ ?_
  · exact (PrimitiveFunctionGraph.GraphCode.assemble_read _).symm
  · rfl
  · rfl

/-- Direct package composition has the same computational data as the
canonical reading of assembled composition. -/
theorem compData_eq_canonical
    {U : AtomCarrier.{u}} {G H K : GeometryPackage.{u, v} U}
    (first : PackageGraphCode G H)
    (second : PackageGraphCode H K) :
    compData first second = (canonicalComposite first second).1 := by
  apply data_ext
  · apply PrimitiveFunctionGraph.GraphCode.assemble_injective
    dsimp [compData, canonicalComposite,
      CompleteGeometryGraphAssembly.PackageGraphCode.read]
    rw [PrimitiveFunctionGraph.GraphCode.assemble_comp,
      PrimitiveFunctionGraph.GraphCode.assemble_read]
    rfl
  · apply AlgebraicGraphCoherence.EquivGraphCode.equivEquiv.injective
    dsimp [compData, canonicalComposite,
      CompleteGeometryGraphAssembly.PackageGraphCode.read]
    change
      (AlgebraicGraphCoherence.EquivGraphCode.comp
        first.1.pointedAtom second.1.pointedAtom).assemble =
      (AlgebraicGraphCoherence.EquivGraphCode.read
        (PackageTotalHom.comp first.assemble second.assemble).base.doctrineHom.atomEquiv).assemble
    rw [AlgebraicGraphCoherence.EquivGraphCode.assemble_comp,
      AlgebraicGraphCoherence.EquivGraphCode.assemble_read]
    rfl
  · apply AlgebraicGraphCoherence.EquivGraphCode.equivEquiv.injective
    dsimp [compData, canonicalComposite,
      CompleteGeometryGraphAssembly.PackageGraphCode.read]
    change
      (AlgebraicGraphCoherence.EquivGraphCode.comp
        first.1.atom second.1.atom).assemble =
      (AlgebraicGraphCoherence.EquivGraphCode.read
        (PackageTotalHom.comp first.assemble second.assemble).upper.atomEquiv).assemble
    rw [AlgebraicGraphCoherence.EquivGraphCode.assemble_comp,
      AlgebraicGraphCoherence.EquivGraphCode.assemble_read]
    rfl
  · apply PrimitiveFunctionGraph.GraphCode.assemble_injective
    dsimp [compData, canonicalComposite,
      CompleteGeometryGraphAssembly.PackageGraphCode.read]
    rw [PrimitiveFunctionGraph.GraphCode.assemble_comp,
      PrimitiveFunctionGraph.GraphCode.assemble_read]
    rfl
  · apply AlgebraicGraphCoherence.EquivGraphCode.equivEquiv.injective
    dsimp [compData, canonicalComposite,
      CompleteGeometryGraphAssembly.PackageGraphCode.read]
    change
      (AlgebraicGraphCoherence.EquivGraphCode.comp
        first.1.equation second.1.equation).assemble =
      (AlgebraicGraphCoherence.EquivGraphCode.read
        (PackageTotalHom.comp first.assemble second.assemble).upper.equationTransport.equationEquiv).assemble
    rw [AlgebraicGraphCoherence.EquivGraphCode.assemble_comp,
      AlgebraicGraphCoherence.EquivGraphCode.assemble_read]
    rfl
  · rfl
  · dsimp [compData, canonicalComposite,
      CompleteGeometryGraphAssembly.PackageGraphCode.read]
    apply HEq.trans (reindexOperation_heq _ _)
    apply HEq.trans (heq_of_eq
      (BiIndexedFunctionGraphCode.read_assemble _).symm)
    apply HEq.trans ?_
      (CompleteGeometryGraphAssembly.PackageGraphCode.read_reindexOperationFamily_heq
        _ _ _ _).symm
    apply heq_of_eq
    congr 1
    funext A B op
    rw [BiIndexedFunctionGraphCode.assemble_comp]
    rfl
  · apply PrimitiveFunctionGraph.GraphCode.assemble_injective
    dsimp [compData, canonicalComposite,
      CompleteGeometryGraphAssembly.PackageGraphCode.read]
    rw [PrimitiveFunctionGraph.GraphCode.assemble_comp,
      PrimitiveFunctionGraph.GraphCode.assemble_read]
    rfl
  · dsimp [compData, canonicalComposite,
      CompleteGeometryGraphAssembly.PackageGraphCode.read]
    apply HEq.trans (reindexSignature_heq _ _)
    exact signature_comp_heq_canonical first second

/-- Reader-mediated lawful identity whose data is `idData`; its package
certificate is transported from the canonical reader. -/
noncomputable def id
    {U : AtomCarrier.{u}} (G : GeometryPackage.{u, v} U) :
    PackageGraphCode G G :=
  ⟨idData G, idData_eq_canonical G ▸ (canonicalIdentity G).2⟩

/-- Reader-mediated lawful composition whose data is `compData`; its package
certificate is transported from the canonical reader after fieldwise
comparison. -/
noncomputable def comp
    {U : AtomCarrier.{u}} {G H K : GeometryPackage.{u, v} U}
    (first : PackageGraphCode G H)
    (second : PackageGraphCode H K) : PackageGraphCode G K :=
  ⟨compData first second,
    compData_eq_canonical first second ▸ (canonicalComposite first second).2⟩

/-- Package-code assembly is separating. -/
theorem assemble_injective
    {U : AtomCarrier.{u}} {G H : GeometryPackage.{u, v} U} :
    Function.Injective
      (CompleteGeometryGraphAssembly.PackageGraphCode.assemble :
        PackageGraphCode G H → PackageTotalHom G.core H.core) := by
  intro first second equality
  rw [← CompleteGeometryGraphAssembly.PackageGraphCode.read_assemble first,
    ← CompleteGeometryGraphAssembly.PackageGraphCode.read_assemble second]
  exact congrArg CompleteGeometryGraphAssembly.PackageGraphCode.read equality

/-- Cycle 73 package identity assembles to package identity. -/
@[simp]
theorem assemble_id
    {U : AtomCarrier.{u}} (G : GeometryPackage.{u, v} U) :
    (id G).assemble = PackageTotalHom.id G.core := by
  rw [show id G = canonicalIdentity G by
    apply Subtype.ext
    exact idData_eq_canonical G]
  exact CompleteGeometryGraphAssembly.PackageGraphCode.assemble_read _

/-- Cycle 73 package composition assembles to package composition. -/
@[simp]
theorem assemble_comp
    {U : AtomCarrier.{u}} {G H K : GeometryPackage.{u, v} U}
    (first : PackageGraphCode G H)
    (second : PackageGraphCode H K) :
    (comp first second).assemble =
      PackageTotalHom.comp first.assemble second.assemble := by
  rw [show comp first second = canonicalComposite first second by
    apply Subtype.ext
    exact compData_eq_canonical first second]
  exact CompleteGeometryGraphAssembly.PackageGraphCode.assemble_read _

/-- Cycle 73 composition is the unique lawful package code with the displayed
assembled composite.  This is the cycle's package-level universal property. -/
theorem eq_comp_iff_assemble_eq
    {U : AtomCarrier.{u}} {G H K : GeometryPackage.{u, v} U}
    (first : PackageGraphCode G H)
    (second : PackageGraphCode H K)
    (candidate : PackageGraphCode G K) :
    candidate = comp first second ↔
      candidate.assemble =
        PackageTotalHom.comp first.assemble second.assemble := by
  constructor
  · rintro rfl
    exact assemble_comp first second
  · intro equality
    apply assemble_injective
    rw [assemble_comp]
    exact equality

/-- Left unit for Cycle 73 package-code composition. -/
@[simp]
theorem id_comp
    {U : AtomCarrier.{u}} {G H : GeometryPackage.{u, v} U}
    (code : PackageGraphCode G H) : comp (id G) code = code := by
  apply assemble_injective
  rw [assemble_comp, assemble_id]
  change (𝟙 G.core : G.core ⟶ G.core) ≫
    (code.assemble : G.core ⟶ H.core) = code.assemble
  simp

/-- Right unit for Cycle 73 package-code composition. -/
@[simp]
theorem comp_id
    {U : AtomCarrier.{u}} {G H : GeometryPackage.{u, v} U}
    (code : PackageGraphCode G H) : comp code (id H) = code := by
  apply assemble_injective
  rw [assemble_comp, assemble_id]
  change (code.assemble : G.core ⟶ H.core) ≫
    (𝟙 H.core : H.core ⟶ H.core) = code.assemble
  simp

/-- Associativity for Cycle 73 package-code composition. -/
@[simp]
theorem comp_assoc
    {U : AtomCarrier.{u}} {G H K L : GeometryPackage.{u, v} U}
    (first : PackageGraphCode G H)
    (second : PackageGraphCode H K)
    (third : PackageGraphCode K L) :
    comp (comp first second) third =
      comp first (comp second third) := by
  apply assemble_injective
  simp only [assemble_comp]
  exact @Category.assoc (AATCorePackage U) _
    G.core H.core K.core L.core
    first.assemble second.assemble third.assemble

/-- Same-cycle identity connection to the Cycle 72 lawful complete-code
operation. -/
theorem id_eq_complete_package
    {U : AtomCarrier.{u}} (G : GeometryPackage.{u, v} U) :
    id G =
      (CompleteGeometryGraphCategoryEquivalence.LawfulCode.id G).package := by
  apply assemble_injective
  rw [assemble_id]
  change PackageTotalHom.id G.core =
    (CompleteGeometryGraphCategoryEquivalence.LawfulCode.id G).assemble.base
  rw [CompleteGeometryGraphCategoryEquivalence.LawfulCode.assemble_id]
  rfl

/-- Same-cycle composition connection to the Cycle 72 lawful complete-code
operation: the package projection of transported complete composition is the
Cycle 73 package composition. -/
theorem comp_eq_complete_package
    {U : AtomCarrier.{u}} {G H K : GeometryPackage.{u, v} U}
    (first : CompleteGeometryGraphCode G H)
    (second : CompleteGeometryGraphCode H K) :
    comp first.package second.package =
      (CompleteGeometryGraphCategoryEquivalence.LawfulCode.comp
        first second).package := by
  apply assemble_injective
  rw [assemble_comp]
  change PackageTotalHom.comp first.assemble.base second.assemble.base =
    (CompleteGeometryGraphCategoryEquivalence.LawfulCode.comp
      first second).assemble.base
  rw [CompleteGeometryGraphCategoryEquivalence.LawfulCode.assemble_comp]
  rfl

end PackageGraphCode

#assert_standard_axioms_only
  AAT.AG.LocalSemanticReconstruction.CompleteGeometryDirectCategory

end CompleteGeometryDirectCategory

end

end AAT.AG.LocalSemanticReconstruction
