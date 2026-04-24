import Formal.Arch.Decomposable
import Formal.Arch.LSP

namespace Formal.Arch

/-- Two-node cycle used as the smallest non-decomposable dependency graph. -/
inductive TwoCycleComponent where
  | a
  | b
  deriving DecidableEq

namespace TwoCycleComponent

/-- `a` depends on `b`, and `b` depends on `a`. -/
inductive edge : TwoCycleComponent → TwoCycleComponent → Prop where
  | a_b : edge a b
  | b_a : edge b a

/-- The two-node cycle graph. -/
def graph : ArchGraph TwoCycleComponent where
  edge := edge

/-- A two-node dependency cycle cannot be strictly layered. -/
theorem not_decomposable : ¬ Decomposable graph := by
  intro h
  rcases h with ⟨layer, hLayer⟩
  have hab : layer b < layer a := hLayer edge.a_b
  have hba : layer a < layer b := hLayer edge.b_a
  exact Nat.lt_asymm hab hba

end TwoCycleComponent

/--
A non-vacuous local-contract-style counterexample: components have
responsibilities, an abstraction projection, and public observations, but the
dependency graph still contains a cycle.
-/
inductive PaymentComponent where
  | orderService
  | paymentPort
  | paymentAdapter
  deriving DecidableEq

namespace PaymentComponent

/-- Responsibility labels for the payment example. -/
inductive Responsibility where
  | orderOrchestration
  | paymentAbstraction
  | concretePaymentIntegration
  deriving DecidableEq

/-- Public behavior labels observed through the abstraction boundary. -/
inductive PublicBehavior where
  | orderWorkflow
  | paymentContract
  deriving DecidableEq

/-- The abstraction seen by clients. -/
def projection : PaymentComponent → PaymentComponent
  | orderService => orderService
  | paymentPort => paymentPort
  | paymentAdapter => paymentPort

/-- Nontrivial responsibility assignment. -/
def responsibility : PaymentComponent → Responsibility
  | orderService => Responsibility.orderOrchestration
  | paymentPort => Responsibility.paymentAbstraction
  | paymentAdapter => Responsibility.concretePaymentIntegration

/-- Public observation forgets the concrete adapter behind the payment port. -/
def observation : PaymentComponent → PublicBehavior
  | orderService => PublicBehavior.orderWorkflow
  | paymentPort => PublicBehavior.paymentContract
  | paymentAdapter => PublicBehavior.paymentContract

/-- The adapter and the port agree on public behavior. -/
theorem adapter_observes_as_port :
    observation paymentAdapter = observation paymentPort := rfl

/-- The adapter projects to the payment abstraction. -/
theorem adapter_projects_to_port :
    projection paymentAdapter = paymentPort := rfl

/-- A small dependency cycle with nontrivial abstraction and observation data. -/
inductive edge : PaymentComponent → PaymentComponent → Prop where
  | order_port : edge orderService paymentPort
  | port_adapter : edge paymentPort paymentAdapter
  | adapter_order : edge paymentAdapter orderService

/-- The non-vacuous local-contract-style counterexample graph. -/
def graph : ArchGraph PaymentComponent where
  edge := edge

/-- The local-contract-style payment example is still not decomposable. -/
theorem not_decomposable : ¬ Decomposable graph := by
  intro h
  rcases h with ⟨layer, hLayer⟩
  have h1 : layer paymentPort < layer orderService := hLayer edge.order_port
  have h2 : layer paymentAdapter < layer paymentPort := hLayer edge.port_adapter
  have h3 : layer orderService < layer paymentAdapter := hLayer edge.adapter_order
  exact Nat.lt_irrefl (layer orderService) (Nat.lt_trans h3 (Nat.lt_trans h2 h1))

end PaymentComponent

/--
A direction-only counterexample: concrete adapters depend on abstractions, but
the abstraction layer itself contains a cycle.
-/
inductive AbstractCycleComponent where
  | orderPort
  | paymentPort
  | orderAdapter
  | paymentAdapter
  deriving DecidableEq

namespace AbstractCycleComponent

/-- Abstract view of the stronger counterexample. -/
inductive Port where
  | order
  | payment
  deriving DecidableEq

/-- Concrete adapters project to their ports; ports project to themselves. -/
def projection : AbstractCycleComponent → Port
  | orderPort => Port.order
  | orderAdapter => Port.order
  | paymentPort => Port.payment
  | paymentAdapter => Port.payment

/--
Concrete dependencies point toward abstractions, but the abstraction layer has
`OrderPort <-> PaymentPort`.
-/
inductive edge : AbstractCycleComponent → AbstractCycleComponent → Prop where
  | order_payment : edge orderPort paymentPort
  | payment_order : edge paymentPort orderPort
  | orderAdapter_order : edge orderAdapter orderPort
  | paymentAdapter_payment : edge paymentAdapter paymentPort

/-- The abstraction-cycle graph. -/
def graph : ArchGraph AbstractCycleComponent where
  edge := edge

/--
Even with concrete-to-abstract adapter dependencies, abstract cycles block
decomposition. This is a DIP-direction-only counterexample, not a full
`DIPCompatible` example.
-/
theorem not_decomposable : ¬ Decomposable graph := by
  intro h
  rcases h with ⟨layer, hLayer⟩
  have h1 : layer paymentPort < layer orderPort := hLayer edge.order_payment
  have h2 : layer orderPort < layer paymentPort := hLayer edge.payment_order
  exact Nat.lt_asymm h1 h2

end AbstractCycleComponent

/--
Strong abstract-layer-cycle example: projection, representative stability, and
LSP all hold, but the dependency graph is still not decomposable.
-/
inductive StrongAbstractCycleComponent where
  | orderPort
  | paymentPort
  | orderAdapter
  | paymentAdapter
  deriving DecidableEq

namespace StrongAbstractCycleComponent

/-- Abstract ports exposed by the implementation components. -/
inductive Port where
  | order
  | payment
  deriving DecidableEq

/-- Public behavior labels. -/
inductive Behavior where
  | order
  | payment
  deriving DecidableEq

/-- Projection from implementation components to abstract ports. -/
def projection : InterfaceProjection StrongAbstractCycleComponent Port where
  expose
    | orderPort => Port.order
    | orderAdapter => Port.order
    | paymentPort => Port.payment
    | paymentAdapter => Port.payment

/-- Observations depend only on the projected abstract port. -/
def observation : Observation StrongAbstractCycleComponent Behavior where
  observe
    | orderPort => Behavior.order
    | orderAdapter => Behavior.order
    | paymentPort => Behavior.payment
    | paymentAdapter => Behavior.payment

/-- The observation factors through `projection`. -/
theorem observation_factors : ObservationFactorsThrough projection observation := by
  refine ⟨?_, ?_⟩
  · intro p
    cases p
    · exact Behavior.order
    · exact Behavior.payment
  · intro x
    cases x <;> rfl

/-- LSP holds because observations factor through the abstraction. -/
theorem lspCompatible : LSPCompatible projection observation :=
  lspCompatible_of_observationFactorsThrough observation_factors

/--
Dependencies:
`OrderPort -> PaymentPort`, `OrderAdapter -> PaymentPort`,
`PaymentPort -> OrderPort`, and `PaymentAdapter -> OrderPort`.
-/
inductive edge : StrongAbstractCycleComponent → StrongAbstractCycleComponent → Prop where
  | orderPort_paymentPort : edge orderPort paymentPort
  | orderAdapter_paymentPort : edge orderAdapter paymentPort
  | paymentPort_orderPort : edge paymentPort orderPort
  | paymentAdapter_orderPort : edge paymentAdapter orderPort

/-- The strong abstract-cycle graph. -/
def graph : ArchGraph StrongAbstractCycleComponent where
  edge := edge

/-- Abstract graph induced by the strong abstract-cycle example. -/
inductive abstractEdge : Port → Port → Prop where
  | order_payment : abstractEdge Port.order Port.payment
  | payment_order : abstractEdge Port.payment Port.order

/-- The abstract graph for the port-level cycle. -/
def abstractGraph : AbstractGraph Port where
  edge := abstractEdge

/-- Every concrete edge is represented at the abstract level. -/
theorem projectionSound : ProjectionSound graph projection abstractGraph := by
  intro c d h
  cases h <;> constructor

/-- The abstract graph has no edge beyond those induced by concrete edges. -/
theorem projectionComplete : ProjectionComplete graph projection abstractGraph := by
  intro a b h
  cases h with
  | order_payment =>
      exact ⟨orderPort, paymentPort, rfl, rfl, edge.orderPort_paymentPort⟩
  | payment_order =>
      exact ⟨paymentPort, orderPort, rfl, rfl, edge.paymentPort_orderPort⟩

/-- Projection is exact for the strong abstract-cycle example. -/
theorem projectionExact : ProjectionExact graph projection abstractGraph :=
  ⟨projectionSound, projectionComplete⟩

/-- Components in the same abstraction induce the same abstract outgoing dependencies. -/
theorem representativeStable : RepresentativeStable graph projection := by
  intro c₁ c₂ hSame a
  constructor
  · intro hDep
    rcases hDep with ⟨d, hEdge, hProj⟩
    cases c₁ <;> cases c₂ <;> cases hSame <;> cases hEdge <;>
      first
        | exact ⟨paymentPort, edge.orderPort_paymentPort, hProj⟩
        | exact ⟨paymentPort, edge.orderAdapter_paymentPort, hProj⟩
        | exact ⟨orderPort, edge.paymentPort_orderPort, hProj⟩
        | exact ⟨orderPort, edge.paymentAdapter_orderPort, hProj⟩
  · intro hDep
    rcases hDep with ⟨d, hEdge, hProj⟩
    cases c₁ <;> cases c₂ <;> cases hSame <;> cases hEdge <;>
      first
        | exact ⟨paymentPort, edge.orderPort_paymentPort, hProj⟩
        | exact ⟨paymentPort, edge.orderAdapter_paymentPort, hProj⟩
        | exact ⟨orderPort, edge.paymentPort_orderPort, hProj⟩
        | exact ⟨orderPort, edge.paymentAdapter_orderPort, hProj⟩

/-- The example satisfies the current strong operational `DIPCompatible`. -/
theorem dipCompatible : DIPCompatible graph projection abstractGraph :=
  ⟨projectionSound, representativeStable⟩

/-- The example also satisfies exact projection plus representative stability. -/
theorem strongDIPCompatible : StrongDIPCompatible graph projection abstractGraph :=
  ⟨projectionExact, representativeStable⟩

/-- Despite DIP/LSP compatibility, the abstract-layer cycle blocks decomposition. -/
theorem not_decomposable : ¬ Decomposable graph := by
  intro h
  rcases h with ⟨layer, hLayer⟩
  have h1 : layer paymentPort < layer orderPort := hLayer edge.orderPort_paymentPort
  have h2 : layer orderPort < layer paymentPort := hLayer edge.paymentPort_orderPort
  exact Nat.lt_asymm h1 h2

end StrongAbstractCycleComponent

end Formal.Arch
