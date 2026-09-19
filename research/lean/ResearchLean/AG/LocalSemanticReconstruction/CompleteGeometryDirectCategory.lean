import ResearchLean.AG.LocalSemanticReconstruction.CompleteGeometryGraphCategoryEquivalence
import Formal.Util.AssertStandardAxioms

/-!
# Direct package category operations and common-surface comparisons

Cycle 74 replaces the remaining reader-mediated package field and certificate
route by direct context/observable identity and composition together with all
fourteen `IsPackageGraphCode` laws.  Exact assembly, package universality,
category laws, canonical comparisons, and the Cycle 72/common-graph
connections are retained in the same module.  The complete-geometry outer
fields and independent local-object assembly remain separate obligations.
-/

namespace AAT.AG.LocalSemanticReconstruction

open CategoryTheory AtomFoundation GeometryTransport

noncomputable section

namespace CompleteGeometryDirectCategory

universe u v w

namespace ContextObservableGraphCode

open ContextObservableGraphCoherence
open DependentAlgebraicGraphCoherence

/-- Cycle 74 direct joint identity code.
Premise summary: one equation system; context and observable identity graphs
and observable naturality are constructed locally. -/
noncomputable def id
    {U : AtomCarrier.{u}} {A₀ : ArchitectureObject U}
    {C : Site.ContextPreorderCategory A₀}
    (P : ArchitecturalEquationSystem C) :
    ContextObservableGraphCode P P := by
  let context := ThinEquivalenceGraphCode.id
    (Site.ContextCategoryObject C)
  have functor_eq : context.forwardFunctor =
      CategoryTheory.Functor.id (Site.ContextCategoryObject C) := by
    change context.assemble.functor = _
    exact congrArg CategoryTheory.Equivalence.functor
      (ThinEquivalenceGraphCode.assemble_id _)
  let observable : ObservablePresheafGraphCode P P
      (CategoryTheory.Functor.id (Site.ContextCategoryObject C)) := by
    let data : ObservablePresheafGraphData P P
        (CategoryTheory.Functor.id (Site.ContextCategoryObject C)) := {
      observable := fun W => RingEquivGraphCode.id (P.Observable W) }
    refine ⟨data, ⟨?_⟩⟩
    intro W V f value
    change (RingEquivGraphCode.id (P.Observable W)).assemble
        (P.restrict f value) =
      P.restrict f ((RingEquivGraphCode.id (P.Observable V)).assemble value)
    simp
  exact {
    context := context
    observable := ObservablePresheafGraphCode.reindex functor_eq observable }

/-- The direct joint identity has the identity context map.
Premise summary: one equation system and one context object. -/
@[simp]
theorem id_context_obj
    {U : AtomCarrier.{u}} {A₀ : ArchitectureObject U}
    {C : Site.ContextPreorderCategory A₀}
    (P : ArchitecturalEquationSystem C)
    (W : Site.ContextCategoryObject C) :
    (id P).context.forwardCode.assemble W = W := by
  change (id P).context.assemble.functor.obj W = W
  rw [show (id P).context.assemble =
      CategoryTheory.Equivalence.refl by
    dsimp [id]
    exact ThinEquivalenceGraphCode.assemble_id _]
  rfl

/-- Extensionality for a joint context/observable code over arbitrary equation
systems.  Premise summary: equality of the context field and heterogeneous
equality of the dependent observable field. -/
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
their assembled natural isomorphisms.  Premise summary: equality of the two
assembled isomorphisms on that fixed functor. -/
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

/-- Reindexing an observable code changes only its dependent functor type.
Premise summary: an equality of context functors and one code over its target. -/
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

/-- Reindexing does not change observable evaluation.
Premise summary: functor equality, one observable code, and one fiber value. -/
theorem observable_reindex_apply_heq
    {U : AtomCarrier.{u}} {A₀ B₀ : ArchitectureObject U}
    {C : Site.ContextPreorderCategory A₀}
    {D : Site.ContextPreorderCategory B₀}
    {P : ArchitecturalEquationSystem C}
    {Q : ArchitecturalEquationSystem D}
    {firstFunctor secondFunctor :
      CategoryTheory.Functor
        (Site.ContextCategoryObject C) (Site.ContextCategoryObject D)}
    (functor_eq : firstFunctor = secondFunctor)
    (code : ObservablePresheafGraphCode P Q secondFunctor)
    (W : Site.ContextCategoryObject C) (value : P.Observable W) :
    HEq ((ObservablePresheafGraphCode.reindex functor_eq code).1.observable
      |>.assemble W value) (code.1.observable.assemble W value) := by
  cases functor_eq
  rfl

/-- Fiber evaluation of the direct joint identity is heterogeneous identity.
Premise summary: one equation system, context object, and observable value. -/
theorem id_observable_apply_heq
    {U : AtomCarrier.{u}} {A₀ : ArchitectureObject U}
    {C : Site.ContextPreorderCategory A₀}
    (P : ArchitecturalEquationSystem C)
    (W : Site.ContextCategoryObject C) (value : P.Observable W) :
    HEq ((id P).observable.1.observable.assemble W value) value := by
  let context := ThinEquivalenceGraphCode.id
    (Site.ContextCategoryObject C)
  have functor_eq : context.forwardFunctor =
      CategoryTheory.Functor.id (Site.ContextCategoryObject C) := by
    change context.assemble.functor = _
    exact congrArg CategoryTheory.Equivalence.functor
      (ThinEquivalenceGraphCode.assemble_id _)
  let observable : ObservablePresheafGraphCode P P
      (CategoryTheory.Functor.id (Site.ContextCategoryObject C)) := by
    let data : ObservablePresheafGraphData P P
        (CategoryTheory.Functor.id (Site.ContextCategoryObject C)) := {
      observable := fun X => RingEquivGraphCode.id (P.Observable X) }
    refine ⟨data, ⟨?_⟩⟩
    intro X Y f x
    change (RingEquivGraphCode.id (P.Observable X)).assemble
        (P.restrict f x) =
      P.restrict f ((RingEquivGraphCode.id (P.Observable Y)).assemble x)
    simp
  change HEq
    ((ObservablePresheafGraphCode.reindex functor_eq observable).1.observable
      |>.assemble W value) value
  apply HEq.trans (observable_reindex_apply_heq functor_eq observable W value)
  exact heq_of_eq (by
    change (RingEquivGraphCode.id (P.Observable W)).assemble value = value
    simp)

/-- Observable codes over propositionally equal context functors are
heterogeneously equal when their computational ring-graph families agree.
Premise summary: functor equality plus heterogeneous equality of raw data. -/
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
equal when every fiber graph is.  Premise summary: index-map equality and a
fiberwise heterogeneous equality. -/
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

/-- Cycle 74 direct context/observable composition datum.
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

/-- The direct joint composite has the composite context map.
Premise summary: two composable joint codes and one source context. -/
theorem comp_context_obj
    {U : AtomCarrier.{u}} {A₀ B₀ C₀ : ArchitectureObject U}
    {C : Site.ContextPreorderCategory A₀}
    {D : Site.ContextPreorderCategory B₀}
    {E : Site.ContextPreorderCategory C₀}
    {P : ArchitecturalEquationSystem C}
    {Q : ArchitecturalEquationSystem D}
    {R : ArchitecturalEquationSystem E}
    (first : ContextObservableGraphCode P Q)
    (second : ContextObservableGraphCode Q R)
    (W : Site.ContextCategoryObject C) :
    (comp first second).context.forwardCode.assemble W =
      second.context.forwardCode.assemble
        (first.context.forwardCode.assemble W) := by
  change (comp first second).context.assemble.functor.obj W = _
  rw [show (comp first second).context.assemble =
      first.context.assemble.trans second.context.assemble by
    dsimp [comp]
    exact ThinEquivalenceGraphCode.assemble_comp _ _]
  rfl

/-- Fiber evaluation of direct joint composition is pointwise composition.
Premise summary: two composable joint codes and one source observable value. -/
theorem comp_observable_apply_heq
    {U : AtomCarrier.{u}} {A₀ B₀ C₀ : ArchitectureObject U}
    {C : Site.ContextPreorderCategory A₀}
    {D : Site.ContextPreorderCategory B₀}
    {E : Site.ContextPreorderCategory C₀}
    {P : ArchitecturalEquationSystem C}
    {Q : ArchitecturalEquationSystem D}
    {R : ArchitecturalEquationSystem E}
    (first : ContextObservableGraphCode P Q)
    (second : ContextObservableGraphCode Q R)
    (W : Site.ContextCategoryObject C) (value : P.Observable W) :
    HEq ((comp first second).observable.1.observable.assemble W value)
      (second.observable.1.observable.assemble
        (first.context.forwardCode.assemble W)
        (first.observable.1.observable.assemble W value)) := by
  dsimp only [comp]
  apply HEq.trans (observable_reindex_apply_heq _ _ W value)
  exact heq_of_eq (by
    rw [IndexedRingEquivGraphCode.assemble_comp]
    rfl)

end ContextObservableGraphCode

namespace PackageGraphCode

open CompleteGeometryGraphAssembly
open RemainingComponentGraphCoherence

/-- Direct-image transport of Atom families composes.
Premise summary: one family and two Atom functions. -/
theorem atomFamily_transport_comp
    {U : AtomCarrier.{u}} (F : AtomFamily U)
    (first second : U.Atom → U.Atom) :
    (F.transport first).transport second =
      F.transport (second ∘ first) := by
  ext target
  constructor
  · rintro ⟨middle, ⟨source, hsource, rfl⟩, rfl⟩
    exact ⟨source, hsource, rfl⟩
  · rintro ⟨source, hsource, rfl⟩
    exact ⟨first source, ⟨source, hsource, rfl⟩, rfl⟩

/-- Direct-image transport of Atom configurations composes.
Premise summary: one configuration and two Atom functions. -/
theorem atomConfiguration_transport_comp
    {U : AtomCarrier.{u}} (C : AtomConfiguration U)
    (first second : U.Atom → U.Atom) :
    (C.transport first).transport second =
      C.transport (second ∘ first) := by
  ext
  · constructor
    · rintro ⟨middle, ⟨source, hsource, rfl⟩, rfl⟩
      exact ⟨source, hsource, rfl⟩
    · rintro ⟨source, hsource, rfl⟩
      exact ⟨first source, ⟨source, hsource, rfl⟩, rfl⟩
  · constructor
    · rintro ⟨middle₁, middle₂,
        ⟨source₁, source₂, h, rfl, rfl⟩, rfl, rfl⟩
      exact ⟨source₁, source₂, h, rfl, rfl⟩
    · rintro ⟨source₁, source₂, h, rfl, rfl⟩
      exact ⟨first source₁, first source₂,
        ⟨source₁, source₂, h, rfl, rfl⟩, rfl, rfl⟩
  · constructor
    · rintro ⟨middle₁, middle₂,
        ⟨source₁, source₂, h, rfl, rfl⟩, rfl, rfl⟩
      exact ⟨source₁, source₂, h, rfl, rfl⟩
    · rintro ⟨source₁, source₂, h, rfl, rfl⟩
      exact ⟨first source₁, first source₂,
        ⟨source₁, source₂, h, rfl, rfl⟩, rfl, rfl⟩

/-- Extensionality for raw package graph data, including its dependent
operation and signature fields.  Premise summary: equality or heterogeneous
equality for each of the nine displayed fields. -/
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
the decoded object map.  Premise summary: object-map equality and one code
over its target endpoints. -/
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

/-- Reindexing a dependent operation code changes only its endpoint-map type.
Premise summary: the same object-map equality and target-indexed code. -/
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

/-- Reindexing does not change evaluation of a dependent operation code.
Premise summary: object-map equality, one code, and one operation value. -/
theorem reindexOperation_apply_heq
    {U : AtomCarrier.{u}} {P Q : AATCorePackage U}
    {first second : ArchitectureObject U → ArchitectureObject U}
    (object_eq : first = second)
    (code : BiIndexedFunctionGraphCode second second
      (fun A B => P.reading.operationReading.Op A B)
      (fun A B => Q.reading.operationReading.Op A B))
    (A B) (op : P.reading.operationReading.Op A B) :
    HEq ((reindexOperation object_eq code).assemble A B op)
      (code.assemble A B op) := by
  cases object_eq
  rfl

/-- Operation naturality transports with its object and configuration maps.
Premise summary: equality of object maps, heterogeneous equality of the
configuration families, and one lawful operation code. -/
theorem isOperationNatural_reindex
    {U : AtomCarrier.{u}} {P Q : AATCorePackage U}
    {first second : ArchitectureObject U → ArchitectureObject U}
    (object_eq : first = second)
    (firstConfiguration : ∀ A,
      ConfigurationHom A.configuration (first A).configuration)
    (secondConfiguration : ∀ A,
      ConfigurationHom A.configuration (second A).configuration)
    (configuration_eq : HEq firstConfiguration secondConfiguration)
    (code : BiIndexedFunctionGraphCode second second
      (fun A B => P.reading.operationReading.Op A B)
      (fun A B => Q.reading.operationReading.Op A B))
    (law : IsOperationNatural P Q second secondConfiguration code.assemble) :
    IsOperationNatural P Q first firstConfiguration
      (reindexOperation object_eq code).assemble := by
  cases object_eq
  have equality : firstConfiguration = secondConfiguration :=
    eq_of_heq configuration_eq
  cases equality
  exact law

/-- Configuration families over equal object maps are heterogeneously equal
when their atom maps agree pointwise.
Premise summary: object-map equality and pointwise atom-map equality. -/
theorem configurationFamily_heq
    {U : AtomCarrier.{u}}
    {first second : ArchitectureObject U → ArchitectureObject U}
    (object_eq : first = second)
    (firstConfiguration : ∀ A,
      ConfigurationHom A.configuration (first A).configuration)
    (secondConfiguration : ∀ A,
      ConfigurationHom A.configuration (second A).configuration)
    (atom_eq : ∀ A,
      (firstConfiguration A).atomMap = (secondConfiguration A).atomMap) :
    HEq firstConfiguration secondConfiguration := by
  cases object_eq
  apply heq_of_eq
  funext A
  apply ConfigurationHom.ext
  exact atom_eq A

/-- Reindex a signature graph code along equality of its decoded object map.
Premise summary: object-map equality and one signature code over its target. -/
def reindexSignature
    {U : AtomCarrier.{u}} {P Q : AATCorePackage U}
    {first second : ArchitectureObject U → ArchitectureObject U}
    (object_eq : first = second)
    (code : SignatureGraphCode P Q second) :
    SignatureGraphCode P Q first := by
  cases object_eq
  exact code

/-- Reindexing a signature code changes only its decoded object-map type.
Premise summary: the same object-map equality and target-indexed signature. -/
theorem reindexSignature_heq
    {U : AtomCarrier.{u}} {P Q : AATCorePackage U}
    {first second : ArchitectureObject U → ArchitectureObject U}
    (object_eq : first = second)
    (code : SignatureGraphCode P Q second) :
    HEq (reindexSignature object_eq code) code := by
  cases object_eq
  rfl

/-- Cycle 74 package identity data.  Every field uses its predecessor identity,
including the joint context/observable constructor.  Premise summary: only the
endpoint package is supplied. -/
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
      ContextObservableGraphCode.id G.core.algebra.equationSystem
    operation := reindexOperation object_eq
      (BiIndexedFunctionGraphCode.id)
    invariant := PrimitiveFunctionGraph.GraphCode.id
    signature := reindexSignature object_eq
      (SignatureGraphCode.id G.core) }

/-- The direct identity data's configuration family is the identity family.
Premise summary: an arbitrary proof of the displayed configuration equation;
proof irrelevance prevents it from affecting the computational map. -/
theorem idData_configurationMap_heq
    {U : AtomCarrier.{u}} (G : GeometryPackage.{u, v} U)
    (configuration_eq : ∀ A,
      ((idData G).object.assemble A).configuration =
        A.configuration.transport (idData G).atom.assemble) :
    HEq (fun A : ArchitectureObject U =>
      (idData G).configurationMap configuration_eq A)
      (fun A : ArchitectureObject U =>
        ConfigurationHom.id A.configuration) := by
  have object_eq : (idData G).object.assemble = _root_.id :=
    PrimitiveFunctionGraph.GraphCode.assemble_id
  apply configurationFamily_heq object_eq
  intro A
  rw [CompleteGeometryGraphAssembly.PackageGraphData.configurationMap_atomMap]
  simp only [idData, AlgebraicGraphCoherence.EquivGraphCode.assemble_id,
    ConfigurationHom.id]
  funext atom
  rfl

/-- Cycle 74 direct identity certificate for the displayed package data.
Premise summary: only the endpoint package; no canonical reader certificate is
imported. -/
theorem idData_lawful
    {U : AtomCarrier.{u}} (G : GeometryPackage.{u, v} U) :
    IsPackageGraphCode (idData G) := by
  refine {
    equation_role_eq := ?_
    violationCoordinate_eq := ?_
    equationResidual_eq := ?_
    normalize_eq := ?_
    extraction_iff := ?_
    source_eq := ?_
    atom_eq := ?_
    extraction_eq := ?_
    composition_eq := ?_
    object_formation_eq := ?_
    configuration_eq := ?_
    detectorCode_eq := ?_
    operation_naturality := ?_
    invariant_transport := ?_ }
  · simp [idData]
  · intro W i atom
    apply eq_of_heq
    apply HEq.trans
      (ContextObservableGraphCode.id_observable_apply_heq
        G.core.algebra.equationSystem W _)
    have hcontext :
        (idData G).contextObservable.context.assemble.functor.obj W = W := by
      change (ContextObservableGraphCode.id
        G.core.algebra.equationSystem).context.forwardCode.assemble W = W
      exact ContextObservableGraphCode.id_context_obj _ _
    have hequation : (idData G).equation.assemble i = i := by
      simp [idData]
    have hatom : (idData G).atom.assemble atom = atom := by
      simp [idData]
    rw [hequation, hatom]
    exact CompleteGeometryGraphAssembly.PackageGraphCode.dependent_apply_heq
      hcontext.symm (fun X =>
        G.core.algebra.equationSystem.violationCoordinate X i atom)
  · intro W A i atom
    apply eq_of_heq
    apply HEq.trans
      (ContextObservableGraphCode.id_observable_apply_heq
        G.core.algebra.equationSystem W _)
    have hcontext :
        (idData G).contextObservable.context.assemble.functor.obj W = W := by
      change (ContextObservableGraphCode.id
        G.core.algebra.equationSystem).context.forwardCode.assemble W = W
      exact ContextObservableGraphCode.id_context_obj _ _
    have hobject : (idData G).object.assemble A = A := by
      simp [idData]
    have hequation : (idData G).equation.assemble i = i := by
      simp [idData]
    have hatom : (idData G).atom.assemble atom = atom := by
      simp [idData]
    rw [hobject, hequation, hatom]
    exact CompleteGeometryGraphAssembly.PackageGraphCode.dependent_apply_heq
      hcontext.symm (fun X =>
        G.core.algebra.equationSystem.equationResidual X A i atom)
  · simp [idData]
  · simp [idData]
  · simp [idData]
  · simp [idData]
  · simp [idData]
  · simp [idData]
  · simp [idData]
  · simp [idData]
  · simp [idData]
  · intro A B op
    let configuration_eq : ∀ X,
        ((idData G).object.assemble X).configuration =
          X.configuration.transport (idData G).atom.assemble := by
      intro X
      simp [idData]
    let object_eq : (idData G).object.assemble = _root_.id :=
      PrimitiveFunctionGraph.GraphCode.assemble_id
    have law := isOperationNatural_reindex object_eq
      (fun X => (idData G).configurationMap configuration_eq X)
      (fun X => ConfigurationHom.id X.configuration)
      (idData_configurationMap_heq G configuration_eq)
      BiIndexedFunctionGraphCode.id (LawfulOperationGraphCode.id G.core).2
    exact law A B op
  · intro i
    have hobject : (idData G).object.assemble = _root_.id := by
      exact PrimitiveFunctionGraph.GraphCode.assemble_id
    have hinvariant : (idData G).invariant.assemble = _root_.id := by
      exact PrimitiveFunctionGraph.GraphCode.assemble_id
    rw [hobject, hinvariant]
    exact Invariant.transportedAlong_refl
      (G.core.reading.invariantReading.invariant i) _root_.id

/-- Canonical package identity used only as a fieldwise comparison target.
Premise summary: the endpoint package determines the completed identity read
here; the direct lawful certificate is constructed separately. -/
noncomputable def canonicalIdentity
    {U : AtomCarrier.{u}} (G : GeometryPackage.{u, v} U) :
    PackageGraphCode G G :=
  CompleteGeometryGraphAssembly.PackageGraphCode.read
    (PackageTotalHom.id G.core)

/-- Componentwise signature identity agrees across object-map reindexing with
the signature read from the assembled package identity.  Premise summary:
only the endpoint package is supplied. -/
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
computational field, including dependent operation and signature families.
Premise summary: only the endpoint package is supplied. -/
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

/-- Cycle 74 package graph data composition.
Premise summary: only the two supplied lawful package codes are used.  Every
graph field composes through predecessor operations, including direct joint
context/observable composition.  No completed package morphism is retained in
the result. -/
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
      ContextObservableGraphCode.comp first.1.contextObservable
        second.1.contextObservable
    operation := operation
    invariant := PrimitiveFunctionGraph.GraphCode.comp
      first.1.invariant second.1.invariant
    signature := signature }

/-- The composite data's configuration family is the pointwise composite of
the two input families.
Premise summary: the input configuration laws and the output configuration
law; all three are local package certificates. -/
theorem compData_configurationMap_heq
    {U : AtomCarrier.{u}} {G H K : GeometryPackage.{u, v} U}
    (first : PackageGraphCode G H)
    (second : PackageGraphCode H K)
    (configuration_eq : ∀ A,
      ((compData first second).object.assemble A).configuration =
        A.configuration.transport (compData first second).atom.assemble) :
    HEq (fun A : ArchitectureObject U =>
      (compData first second).configurationMap configuration_eq A)
      (fun A : ArchitectureObject U => ConfigurationHom.comp
        (second.configurationMap (first.1.object.assemble A))
        (first.configurationMap A)) := by
  have object_eq : (compData first second).object.assemble =
      second.1.object.assemble ∘ first.1.object.assemble :=
    PrimitiveFunctionGraph.GraphCode.assemble_comp _ _
  apply configurationFamily_heq object_eq
  intro A
  rw [CompleteGeometryGraphAssembly.PackageGraphData.configurationMap_atomMap]
  simp only [ConfigurationHom.comp]
  rw [first.configurationMap_atomMap, second.configurationMap_atomMap]
  exact congrArg DFunLike.coe
    (AlgebraicGraphCoherence.EquivGraphCode.assemble_comp
      first.1.atom second.1.atom)

/-- Cycle 74 direct composition certificate for the displayed package data.
Premise summary: the two input package certificates; no canonical reader
certificate is imported. -/
theorem compData_lawful
    {U : AtomCarrier.{u}} {G H K : GeometryPackage.{u, v} U}
    (first : PackageGraphCode G H)
    (second : PackageGraphCode H K) :
    IsPackageGraphCode (compData first second) := by
  refine {
    equation_role_eq := ?_
    violationCoordinate_eq := ?_
    equationResidual_eq := ?_
    normalize_eq := ?_
    extraction_iff := ?_
    source_eq := ?_
    atom_eq := ?_
    extraction_eq := ?_
    composition_eq := ?_
    object_formation_eq := ?_
    configuration_eq := ?_
    detectorCode_eq := ?_
    operation_naturality := ?_
    invariant_transport := ?_ }
  · intro i
    simp only [compData, AlgebraicGraphCoherence.EquivGraphCode.assemble_comp,
      Equiv.trans_apply]
    exact (second.2.equation_role_eq _).trans
      (first.2.equation_role_eq i)
  · intro W i atom
    apply eq_of_heq
    apply HEq.trans (ContextObservableGraphCode.comp_observable_apply_heq
      first.1.contextObservable second.1.contextObservable W _)
    have value_eq :
        second.1.contextObservable.observable.1.observable.assemble
            (first.1.contextObservable.context.assemble.functor.obj W)
            (first.1.contextObservable.observable.1.observable.assemble W
              (G.core.algebra.equationSystem.violationCoordinate W i atom)) =
          K.core.algebra.equationSystem.violationCoordinate
            (second.1.contextObservable.context.assemble.functor.obj
              (first.1.contextObservable.context.assemble.functor.obj W))
            (second.1.equation.assemble (first.1.equation.assemble i))
            (second.1.atom.assemble (first.1.atom.assemble atom)) := by
      calc
        _ = second.1.contextObservable.observable.1.observable.assemble
            (first.1.contextObservable.context.assemble.functor.obj W)
            (H.core.algebra.equationSystem.violationCoordinate
              (first.1.contextObservable.context.assemble.functor.obj W)
              (first.1.equation.assemble i)
              (first.1.atom.assemble atom)) := by
                rw [first.2.violationCoordinate_eq]
        _ = _ := second.2.violationCoordinate_eq _ _ _
    apply (heq_of_eq value_eq).trans
    have context_eq := ContextObservableGraphCode.comp_context_obj
      first.1.contextObservable second.1.contextObservable W
    apply HEq.trans
      (CompleteGeometryGraphAssembly.PackageGraphCode.dependent_apply_heq
        context_eq.symm (fun X =>
        K.core.algebra.equationSystem.violationCoordinate X
          (second.1.equation.assemble (first.1.equation.assemble i))
          (second.1.atom.assemble (first.1.atom.assemble atom))))
    exact heq_of_eq (by
      simp [compData, AlgebraicGraphCoherence.EquivGraphCode.assemble_comp])
  · intro W A i atom
    apply eq_of_heq
    apply HEq.trans (ContextObservableGraphCode.comp_observable_apply_heq
      first.1.contextObservable second.1.contextObservable W _)
    have value_eq :
        second.1.contextObservable.observable.1.observable.assemble
            (first.1.contextObservable.context.assemble.functor.obj W)
            (first.1.contextObservable.observable.1.observable.assemble W
              (G.core.algebra.equationSystem.equationResidual W A i atom)) =
          K.core.algebra.equationSystem.equationResidual
            (second.1.contextObservable.context.assemble.functor.obj
              (first.1.contextObservable.context.assemble.functor.obj W))
            (second.1.object.assemble (first.1.object.assemble A))
            (second.1.equation.assemble (first.1.equation.assemble i))
            (second.1.atom.assemble (first.1.atom.assemble atom)) := by
      calc
        _ = second.1.contextObservable.observable.1.observable.assemble
            (first.1.contextObservable.context.assemble.functor.obj W)
            (H.core.algebra.equationSystem.equationResidual
              (first.1.contextObservable.context.assemble.functor.obj W)
              (first.1.object.assemble A) (first.1.equation.assemble i)
              (first.1.atom.assemble atom)) := by
                rw [first.2.equationResidual_eq]
        _ = _ := second.2.equationResidual_eq _ _ _ _
    apply (heq_of_eq value_eq).trans
    have context_eq := ContextObservableGraphCode.comp_context_obj
      first.1.contextObservable second.1.contextObservable W
    apply HEq.trans
      (CompleteGeometryGraphAssembly.PackageGraphCode.dependent_apply_heq
        context_eq.symm (fun X =>
        K.core.algebra.equationSystem.equationResidual X
          (second.1.object.assemble (first.1.object.assemble A))
          (second.1.equation.assemble (first.1.equation.assemble i))
          (second.1.atom.assemble (first.1.atom.assemble atom))))
    exact heq_of_eq (by simp [compData,
      PrimitiveFunctionGraph.GraphCode.assemble_comp,
      AlgebraicGraphCoherence.EquivGraphCode.assemble_comp])
  · intro source
    simp only [compData, PrimitiveFunctionGraph.GraphCode.assemble_comp,
      Function.comp_apply]
    rw [second.2.normalize_eq, first.2.normalize_eq]
  · intro source atom
    simp only [compData, PrimitiveFunctionGraph.GraphCode.assemble_comp,
      AlgebraicGraphCoherence.EquivGraphCode.assemble_comp,
      Function.comp_apply, Equiv.trans_apply]
    exact (first.2.extraction_iff source atom).trans
      (second.2.extraction_iff _ _)
  · simp only [compData, PrimitiveFunctionGraph.GraphCode.assemble_comp,
      Function.comp_apply]
    rw [first.2.source_eq, second.2.source_eq]
  · simp only [compData]
    rw [AlgebraicGraphCoherence.EquivGraphCode.assemble_comp,
      AlgebraicGraphCoherence.EquivGraphCode.assemble_comp,
      first.2.atom_eq, second.2.atom_eq]
  · simp only [compData,
      AlgebraicGraphCoherence.EquivGraphCode.assemble_comp]
    rw [second.2.extraction_eq, first.2.extraction_eq,
      atomFamily_transport_comp]
    rfl
  · intro F hF
    simp only [compData,
      AlgebraicGraphCoherence.EquivGraphCode.assemble_comp]
    have secondLaw := second.2.composition_eq
      (F.transport first.1.atom.assemble)
      (hF.transport first.1.atom.assemble)
    calc
      K.core.reading.composition.compose
          (F.transport (second.1.atom.assemble ∘ first.1.atom.assemble))
          _ =
        (H.core.reading.composition.compose
          (F.transport first.1.atom.assemble)
          (hF.transport first.1.atom.assemble)).transport
            second.1.atom.assemble := by
              simpa only [atomFamily_transport_comp] using secondLaw
      _ = ((G.core.reading.composition.compose F hF).transport
            first.1.atom.assemble).transport second.1.atom.assemble := by
          exact congrArg (fun C => C.transport second.1.atom.assemble)
            (first.2.composition_eq F hF)
      _ = _ := by
        simpa using atomConfiguration_transport_comp
          (G.core.reading.composition.compose F hF)
          first.1.atom.assemble second.1.atom.assemble
  · intro C
    simp only [compData, PrimitiveFunctionGraph.GraphCode.assemble_comp,
      AlgebraicGraphCoherence.EquivGraphCode.assemble_comp,
      Function.comp_apply]
    rw [first.2.object_formation_eq C, second.2.object_formation_eq]
    exact congrArg K.core.reading.objectReading.object
      (atomConfiguration_transport_comp C first.1.atom.assemble
        second.1.atom.assemble)
  · intro A
    simp only [compData, PrimitiveFunctionGraph.GraphCode.assemble_comp,
      AlgebraicGraphCoherence.EquivGraphCode.assemble_comp,
      Function.comp_apply]
    rw [second.2.configuration_eq, first.2.configuration_eq]
    exact atomConfiguration_transport_comp A.configuration
      first.1.atom.assemble second.1.atom.assemble
  · intro i
    simp only [compData, AlgebraicGraphCoherence.EquivGraphCode.assemble_comp,
      Equiv.trans_apply]
    calc
      K.core.algebra.circuits.code
          (second.1.equation.assemble (first.1.equation.assemble i)) =
        (H.core.algebra.circuits.code
          (first.1.equation.assemble i)).transport second.1.atom.assemble :=
            second.2.detectorCode_eq _
      _ = ((G.core.algebra.circuits.code i).transport
          first.1.atom.assemble).transport second.1.atom.assemble := by
            rw [first.2.detectorCode_eq]
      _ = _ := CircuitDetectorCode.transport_trans _ _ _
  · let firstOperation : LawfulOperationGraphCode G.core H.core
        first.1.object.assemble first.configurationMap :=
      ⟨first.1.operation, first.2.operation_naturality⟩
    let secondOperation : LawfulOperationGraphCode H.core K.core
        second.1.object.assemble second.configurationMap :=
      ⟨second.1.operation, second.2.operation_naturality⟩
    let configuration_eq : ∀ A,
        ((compData first second).object.assemble A).configuration =
          A.configuration.transport (compData first second).atom.assemble := by
      intro A
      simp only [compData, PrimitiveFunctionGraph.GraphCode.assemble_comp,
        AlgebraicGraphCoherence.EquivGraphCode.assemble_comp,
        Function.comp_apply]
      rw [second.2.configuration_eq, first.2.configuration_eq]
      exact atomConfiguration_transport_comp A.configuration
        first.1.atom.assemble second.1.atom.assemble
    let object_eq : (compData first second).object.assemble =
        second.1.object.assemble ∘ first.1.object.assemble :=
      PrimitiveFunctionGraph.GraphCode.assemble_comp _ _
    exact isOperationNatural_reindex object_eq
      (fun A => (compData first second).configurationMap configuration_eq A)
      (fun A => ConfigurationHom.comp
        (second.configurationMap (first.1.object.assemble A))
        (first.configurationMap A))
      (compData_configurationMap_heq first second configuration_eq)
      (BiIndexedFunctionGraphCode.comp first.1.operation second.1.operation)
      (LawfulOperationGraphCode.comp firstOperation secondOperation).2
  · simp only [compData, PrimitiveFunctionGraph.GraphCode.assemble_comp]
    let firstInvariant :
        LawfulInvariantGraphCode G.core H.core first.1.object.assemble
        := ⟨first.1.invariant, first.2.invariant_transport⟩
    let secondInvariant :
        LawfulInvariantGraphCode H.core K.core second.1.object.assemble
        := ⟨second.1.invariant, second.2.invariant_transport⟩
    have law := (LawfulInvariantGraphCode.comp
      firstInvariant secondInvariant).2
    rw [LawfulInvariantGraphCode.assemble_comp] at law
    exact law

/-- Canonical package composite used only as a fieldwise comparison target.
Premise summary: two lawful package codes are assembled and composed; the
direct lawful certificate is constructed separately. -/
noncomputable def canonicalComposite
    {U : AtomCarrier.{u}} {G H K : GeometryPackage.{u, v} U}
    (first : PackageGraphCode G H)
    (second : PackageGraphCode H K) : PackageGraphCode G K :=
  CompleteGeometryGraphAssembly.PackageGraphCode.read
    (PackageTotalHom.comp first.assemble second.assemble)

/-- Componentwise signature composition agrees, across the decoded object-map
reindexing, with the signature read from assembled package composition.
Premise summary: the two supplied lawful package codes. -/
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

/-- The displayed direct package composition data equals the canonical reading
of assembled composition.  Premise summary: the two supplied lawful package
codes; this comparison is not used to construct the direct certificate. -/
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

/-- Cycle 74 lawful identity whose data and fourteen package laws are closed
directly.  Premise summary: only the endpoint package; the canonical reader
certificate is not used. -/
noncomputable def id
    {U : AtomCarrier.{u}} (G : GeometryPackage.{u, v} U) :
    PackageGraphCode G G :=
  ⟨idData G, idData_lawful G⟩

/-- Cycle 74 lawful composition whose data and fourteen package laws are
closed directly from the input codes.  Premise summary: two lawful package
codes; the canonical reader certificate is not used. -/
noncomputable def comp
    {U : AtomCarrier.{u}} {G H K : GeometryPackage.{u, v} U}
    (first : PackageGraphCode G H)
    (second : PackageGraphCode H K) : PackageGraphCode G K :=
  ⟨compData first second, compData_lawful first second⟩

/-- Package-code assembly is separating.  Premise summary: equality of the
assembled package morphisms; Cycle 71 read-after-assemble recovers the codes. -/
theorem assemble_injective
    {U : AtomCarrier.{u}} {G H : GeometryPackage.{u, v} U} :
    Function.Injective
      (CompleteGeometryGraphAssembly.PackageGraphCode.assemble :
        PackageGraphCode G H → PackageTotalHom G.core H.core) := by
  intro first second equality
  rw [← CompleteGeometryGraphAssembly.PackageGraphCode.read_assemble first,
    ← CompleteGeometryGraphAssembly.PackageGraphCode.read_assemble second]
  exact congrArg CompleteGeometryGraphAssembly.PackageGraphCode.read equality

/-- Cycle 74 package identity assembles to package identity.  Premise summary:
only the endpoint package; fieldwise comparison supplies the reduction. -/
@[simp]
theorem assemble_id
    {U : AtomCarrier.{u}} (G : GeometryPackage.{u, v} U) :
    (id G).assemble = PackageTotalHom.id G.core := by
  rw [show id G = canonicalIdentity G by
    apply Subtype.ext
    exact idData_eq_canonical G]
  exact CompleteGeometryGraphAssembly.PackageGraphCode.assemble_read _

/-- Cycle 74 package composition assembles to package composition.  Premise
summary: the two supplied lawful package codes and their assembled morphisms. -/
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

/-- Cycle 74 composition is the unique lawful package code with the displayed
assembled composite.  This is the cycle's package-level universal property.
Premise summary: two lawful inputs and an arbitrary lawful candidate. -/
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

/-- Left unit for Cycle 74 package-code composition.  Premise summary: an
arbitrary lawful package code; assembly separation reflects the unit law. -/
@[simp]
theorem id_comp
    {U : AtomCarrier.{u}} {G H : GeometryPackage.{u, v} U}
    (code : PackageGraphCode G H) : comp (id G) code = code := by
  apply assemble_injective
  rw [assemble_comp, assemble_id]
  change (𝟙 G.core : G.core ⟶ G.core) ≫
    (code.assemble : G.core ⟶ H.core) = code.assemble
  simp

/-- Right unit for Cycle 74 package-code composition.  Premise summary: an
arbitrary lawful package code; assembly separation reflects the unit law. -/
@[simp]
theorem comp_id
    {U : AtomCarrier.{u}} {G H : GeometryPackage.{u, v} U}
    (code : PackageGraphCode G H) : comp code (id H) = code := by
  apply assemble_injective
  rw [assemble_comp, assemble_id]
  change (code.assemble : G.core ⟶ H.core) ≫
    (𝟙 H.core : H.core ⟶ H.core) = code.assemble
  simp

/-- Associativity for Cycle 74 package-code composition.  Premise summary:
three composable lawful package codes; assembly reflects associativity. -/
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
operation.  Premise summary: the common endpoint package; assembly separation
compares the two package projections. -/
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
Cycle 74 package composition.  Premise summary: two composable lawful complete
codes; their package projections are compared by assembly separation. -/
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

/-- Cycle 74 couples direct identity with both the Cycle 72 package projection
and the accepted common graph identity.
Premise summary: one endpoint package; no additional certificate. -/
theorem id_cycle72_and_commonSurface
    {U : AtomCarrier.{u}} (G : GeometryPackage.{u, v} U) :
    id G =
        (CompleteGeometryGraphCategoryEquivalence.LawfulCode.id G).package ∧
      (CompleteGeometryGraphCategoryEquivalence.LawfulCode.id G).completeMapGraphs =
        CompleteGeometryGraphCategory.CompleteMapGraphs.id G := by
  constructor
  · exact id_eq_complete_package G
  · change CompleteGeometryFunctionGraphSeparation.readCompleteMapGraphs
        (CompleteGeometryGraphCategoryEquivalence.LawfulCode.id G).assemble = _
    rw [CompleteGeometryGraphCategoryEquivalence.LawfulCode.assemble_id,
      CompleteGeometryGraphCategory.readCompleteMapGraphs_id]

/-- Cycle 74 couples direct composition with both the Cycle 72 package
projection and composition on the accepted common graph surface.
Premise summary: two composable lawful complete codes. -/
theorem comp_cycle72_and_commonSurface
    {U : AtomCarrier.{u}} {G H K : GeometryPackage.{u, v} U}
    (first : CompleteGeometryGraphCode G H)
    (second : CompleteGeometryGraphCode H K) :
    comp first.package second.package =
        (CompleteGeometryGraphCategoryEquivalence.LawfulCode.comp
          first second).package ∧
      (CompleteGeometryGraphCategoryEquivalence.LawfulCode.comp
          first second).completeMapGraphs =
        CompleteGeometryGraphCategory.CompleteMapGraphs.comp
          first.completeMapGraphs second.completeMapGraphs := by
  constructor
  · exact comp_eq_complete_package first second
  · change CompleteGeometryFunctionGraphSeparation.readCompleteMapGraphs
        (CompleteGeometryGraphCategoryEquivalence.LawfulCode.comp
          first second).assemble =
      CompleteGeometryGraphCategory.CompleteMapGraphs.comp
        (CompleteGeometryFunctionGraphSeparation.readCompleteMapGraphs
          first.assemble)
        (CompleteGeometryFunctionGraphSeparation.readCompleteMapGraphs
          second.assemble)
    rw [CompleteGeometryGraphCategoryEquivalence.LawfulCode.assemble_comp,
      CompleteGeometryGraphCategory.readCompleteMapGraphs_comp]

end PackageGraphCode

#assert_standard_axioms_only
  AAT.AG.LocalSemanticReconstruction.CompleteGeometryDirectCategory

end CompleteGeometryDirectCategory

end

end AAT.AG.LocalSemanticReconstruction
