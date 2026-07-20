import Formal.AG.SingularityMonodromyStack.OperationHomotopy

noncomputable section

open BigOperators

namespace AAT.AG
namespace SingularityMonodromyStack

universe u v y z

/--
VI.定義10.1: selected coefficient object for monodromy.

The three carriers represent the obstruction, semantic, and effect readings on
which a supplied monodromy representation may act. This structure does not
construct such an action automatically from AAT geometry.
-/
structure MonodromyCoefficientObject where
  Ob : Type z
  Sem : Type z
  Eff : Type z

/-- VI.定義10.1: product automorphism of the selected coefficient object. -/
structure CoefficientAutomorphism (C : MonodromyCoefficientObject.{z}) where
  obAut : C.Ob ≃ C.Ob
  semAut : C.Sem ≃ C.Sem
  effAut : C.Eff ≃ C.Eff

namespace CoefficientAutomorphism

/-- VI.定義10.1: identity coefficient automorphism. -/
def id (C : MonodromyCoefficientObject.{z}) : CoefficientAutomorphism C where
  obAut := Equiv.refl C.Ob
  semAut := Equiv.refl C.Sem
  effAut := Equiv.refl C.Eff

/-- VI.定義10.1: composition of selected coefficient automorphisms. -/
def comp {C : MonodromyCoefficientObject.{z}}
    (f g : CoefficientAutomorphism C) : CoefficientAutomorphism C where
  obAut := f.obAut.trans g.obAut
  semAut := f.semAut.trans g.semAut
  effAut := f.effAut.trans g.effAut

end CoefficientAutomorphism

/--
VI.定義10.1: selected monodromy action.

`rho` is supplied representation data from the presented architecture
fundamental group into the selected coefficient automorphisms. The identity and
multiplication laws are explicit fields; no monodromy is inferred for
unselected loops or unselected coefficient readings.
-/
structure MonodromyAction {U : AtomCarrier.{u}} {A : ArchitectureObject U}
    {S : Site.AATSite A} {P : StratumReadingParameter S}
    {k : Type v} [CommRing k]
    {X : ArchitectureStratum.{u, v, y} P k}
    {G : OperationCategoryData.{u, v, y, z} X}
    {R : RefactorEndpointReading.{u, v, y, z} G}
    {H : HomotopyGeneratorFamily.{u, v, y, z} R}
    {base : G.State}
    (Pi : PresentedArchitectureFundamentalGroup.{u, v, y, z} H base) where
  coefficient : MonodromyCoefficientObject.{z}
  rho : Pi.Pi1 -> CoefficientAutomorphism coefficient
  rho_one : rho 1 = CoefficientAutomorphism.id coefficient
  rho_mul :
    ∀ gamma delta : Pi.Pi1,
      rho (gamma * delta) = CoefficientAutomorphism.comp (rho gamma) (rho delta)

namespace MonodromyAction

variable {U : AtomCarrier.{u}} {A : ArchitectureObject U}
variable {S : Site.AATSite A} {P : StratumReadingParameter S}
variable {k : Type v} [CommRing k]
variable {X : ArchitectureStratum.{u, v, y} P k}
variable {G : OperationCategoryData.{u, v, y, z} X}
variable {R : RefactorEndpointReading.{u, v, y, z} G}
variable {H : HomotopyGeneratorFamily.{u, v, y, z} R}
variable {base : G.State}
variable {Pi : PresentedArchitectureFundamentalGroup.{u, v, y, z} H base}

/-- VI.定義10.1: evaluate `Mon_gamma` as the supplied representation. -/
def Mon_gamma (M : MonodromyAction.{u, v, y, z} Pi) (gamma : Pi.Pi1) :
    CoefficientAutomorphism M.coefficient :=
  M.rho gamma

/-- VI.定義10.1: `Mon_gamma` is definitionally `rho gamma`. -/
theorem mon_gamma_eq_rho
    (M : MonodromyAction.{u, v, y, z} Pi) (gamma : Pi.Pi1) :
    M.Mon_gamma gamma = M.rho gamma :=
  rfl

/-- VI.定義10.1: monodromy sends the identity loop to identity coefficients. -/
theorem rho_one_holds
    (M : MonodromyAction.{u, v, y, z} Pi) :
    M.rho 1 = CoefficientAutomorphism.id M.coefficient :=
  M.rho_one

/-- VI.定義10.1: monodromy respects multiplication in the presented group. -/
theorem rho_mul_holds
    (M : MonodromyAction.{u, v, y, z} Pi)
    (gamma delta : Pi.Pi1) :
    M.rho (gamma * delta) =
      CoefficientAutomorphism.comp (M.rho gamma) (M.rho delta) :=
  M.rho_mul gamma delta

/-- VI.定義10.3: obstruction-sheaf component of a selected monodromy action. -/
def obstructionMonodromy
    (M : MonodromyAction.{u, v, y, z} Pi) (gamma : Pi.Pi1) :
    M.coefficient.Ob ≃ M.coefficient.Ob :=
  (M.Mon_gamma gamma).obAut

/-- VI.定義10.3: selected monodromy debt predicate. -/
def MonodromyDebt
    (M : MonodromyAction.{u, v, y, z} Pi) (gamma : Pi.Pi1) : Prop :=
  M.obstructionMonodromy gamma ≠ (CoefficientAutomorphism.id M.coefficient).obAut

/-- VI.定義10.3: monodromy debt is exactly nonidentity obstruction monodromy. -/
theorem monodromyDebt_iff
    (M : MonodromyAction.{u, v, y, z} Pi) (gamma : Pi.Pi1) :
    M.MonodromyDebt gamma ↔
      M.obstructionMonodromy gamma ≠
        (CoefficientAutomorphism.id M.coefficient).obAut :=
  Iff.rfl

end MonodromyAction

/--
VI.定義10.2: finite Gauss-Manin system.

The object family is finite and each selected fiber is a finite-dimensional
`k`-vector space. Transport is supplied along selected operation paths and is
functorial by explicit identity and composition laws.
-/
structure FiniteGaussManinSystem {U : AtomCarrier.{u}} {A : ArchitectureObject U}
    {S : Site.AATSite A} {P : StratumReadingParameter S}
    {k : Type v} [Field k]
    {X : ArchitectureStratum.{u, v, y} P k}
    (G : OperationCategoryData.{u, v, y, z} X) where
  Object : Type z
  [objectFintype : Fintype Object]
  objectState : Object -> G.State
  Fiber : Object -> Type z
  [fiberAddCommGroup : (a : Object) -> AddCommGroup (Fiber a)]
  [fiberModule : (a : Object) -> Module k (Fiber a)]
  [fiberFiniteDimensional : (a : Object) -> FiniteDimensional k (Fiber a)]
  transport :
    {a b : Object} ->
      OperationPath G (objectState a) (objectState b) -> Fiber a →ₗ[k] Fiber b
  transport_id :
    ∀ a : Object,
      transport (OperationPath.id (G := G) (objectState a)) = LinearMap.id
  transport_comp :
    ∀ {a b c : Object}
      (alpha : OperationPath G (objectState a) (objectState b))
      (beta : OperationPath G (objectState b) (objectState c)),
      transport (OperationPath.concat alpha beta) = (transport beta).comp (transport alpha)

attribute [instance] FiniteGaussManinSystem.objectFintype
attribute [instance] FiniteGaussManinSystem.fiberAddCommGroup
attribute [instance] FiniteGaussManinSystem.fiberModule
attribute [instance] FiniteGaussManinSystem.fiberFiniteDimensional

namespace FiniteGaussManinSystem

variable {U : AtomCarrier.{u}} {A : ArchitectureObject U}
variable {S : Site.AATSite A} {P : StratumReadingParameter S}
variable {k : Type v} [Field k]
variable {X : ArchitectureStratum.{u, v, y} P k}
variable {G : OperationCategoryData.{u, v, y, z} X}

/-- VI.定義10.2: selected Gauss-Manin identity transport. -/
theorem transport_id_holds
    (GM : FiniteGaussManinSystem.{u, v, y, z} G)
    (a : GM.Object) :
    GM.transport (OperationPath.id (G := G) (GM.objectState a)) = LinearMap.id :=
  GM.transport_id a

/-- VI.定義10.2: selected Gauss-Manin transport is functorial for path composition. -/
theorem transport_comp_holds
    (GM : FiniteGaussManinSystem.{u, v, y, z} G)
    {a b c : GM.Object}
    (alpha : OperationPath G (GM.objectState a) (GM.objectState b))
    (beta : OperationPath G (GM.objectState b) (GM.objectState c)) :
    GM.transport (OperationPath.concat alpha beta) =
      (GM.transport beta).comp (GM.transport alpha) :=
  GM.transport_comp alpha beta

/-- VI.定義10.2: selected loop transport as an automorphism package. -/
structure LoopMonodromy
    (GM : FiniteGaussManinSystem.{u, v, y, z} G)
    (a : GM.Object)
    (gamma : OperationPath G (GM.objectState a) (GM.objectState a)) where
  toLinearEquiv : GM.Fiber a ≃ₗ[k] GM.Fiber a
  toLinearEquiv_eq_transport : toLinearEquiv.toLinearMap = GM.transport gamma

/-- VI.定義10.2: expose the selected Gauss-Manin loop transport map. -/
theorem loopMonodromy_eq_transport
    {GM : FiniteGaussManinSystem.{u, v, y, z} G}
    {a : GM.Object}
    {gamma : OperationPath G (GM.objectState a) (GM.objectState a)}
    (rho : LoopMonodromy GM a gamma) :
    rho.toLinearEquiv.toLinearMap = GM.transport gamma :=
  rho.toLinearEquiv_eq_transport

end FiniteGaussManinSystem

/--
VI.定義10.4: selected measured square monodromy.

The measured square is indexed by a selected 2-cell and a selected axis family.
`mu` is an equality-defect reading for the boundary-loop transport; zero and
detection semantics are supplied by the selected axis data.
-/
structure MeasuredSquareMonodromy {U : AtomCarrier.{u}} {A : ArchitectureObject U}
    {S : Site.AATSite A} {P : StratumReadingParameter S}
    {k : Type v} [CommRing k]
    {X : ArchitectureStratum.{u, v, y} P k}
    {G : OperationCategoryData.{u, v, y, z} X}
    {R : RefactorEndpointReading.{u, v, y, z} G}
    {H : HomotopyGeneratorFamily.{u, v, y, z} R}
    {base : G.State}
    {Pi : PresentedArchitectureFundamentalGroup.{u, v, y, z} H base}
    (M : MonodromyAction.{u, v, y, z} Pi)
    (K : PresentationTwoComplex.{u, v, y, z} H) where
  Axis : Type z
  square : K.TwoCell
  boundaryElement : Pi.Pi1
  boundaryTransport : CoefficientAutomorphism M.coefficient
  boundaryTransport_eq_monodromy : boundaryTransport = M.Mon_gamma boundaryElement
  equalityDefect : Axis -> Nat
  axisDetectsIdentity : Axis -> Prop
  zero_defect_detects :
    ∀ x : Axis, equalityDefect x = 0 -> axisDetectsIdentity x
  mu : Axis -> Nat
  mu_eq_defect : ∀ x : Axis, mu x = equalityDefect x

namespace MeasuredSquareMonodromy

variable {U : AtomCarrier.{u}} {A : ArchitectureObject U}
variable {S : Site.AATSite A} {P : StratumReadingParameter S}
variable {k : Type v} [CommRing k]
variable {X : ArchitectureStratum.{u, v, y} P k}
variable {G : OperationCategoryData.{u, v, y, z} X}
variable {R : RefactorEndpointReading.{u, v, y, z} G}
variable {H : HomotopyGeneratorFamily.{u, v, y, z} R}
variable {base : G.State}
variable {Pi : PresentedArchitectureFundamentalGroup.{u, v, y, z} H base}
variable {M : MonodromyAction.{u, v, y, z} Pi}
variable {K : PresentationTwoComplex.{u, v, y, z} H}

/-- VI.定義10.4: `mu_x(sigma)` is the selected equality-defect reading. -/
theorem mu_eq_defect_holds
    (Q : MeasuredSquareMonodromy.{u, v, y, z} M K)
    (axis : Q.Axis) :
    Q.mu axis = Q.equalityDefect axis :=
  Q.mu_eq_defect axis

/-- VI.定義10.4: boundary-loop transport is the selected monodromy action. -/
theorem boundaryTransport_eq_monodromy_holds
    (Q : MeasuredSquareMonodromy.{u, v, y, z} M K) :
    Q.boundaryTransport = M.Mon_gamma Q.boundaryElement :=
  Q.boundaryTransport_eq_monodromy

/-- VI.定義10.4: zero defect is read by the selected axis detector. -/
theorem axis_detects_of_mu_zero
    (Q : MeasuredSquareMonodromy.{u, v, y, z} M K)
    {axis : Q.Axis} (hzero : Q.mu axis = 0) :
    Q.axisDetectsIdentity axis :=
  Q.zero_defect_detects axis ((Q.mu_eq_defect axis).symm.trans hzero)

end MeasuredSquareMonodromy

/--
VI.定義10.6: Architectural Monodromy Index over a finite measured square
family.

The value is a selected weighted sum for one selected axis. The measurement
verdict and distance-value interpretation belong to later measurement-facing
work and are not asserted here.
-/
structure ArchitecturalMonodromyIndex where
  Axis : Type z
  Square : Type z
  [squareFintype : Fintype Square]
  selectedAxis : Axis
  weight : Square -> Nat
  weight_positive : ∀ square : Square, 0 < weight square
  mu : Square -> Axis -> Nat
  value : Nat
  value_eq_weighted_sum :
    value = ∑ square : Square, weight square * mu square selectedAxis

attribute [instance] ArchitecturalMonodromyIndex.squareFintype

namespace ArchitecturalMonodromyIndex

/-- VI.定義10.6: expose the selected AMI weighted-sum equation. -/
theorem value_eq_weighted_sum_holds
    (A : ArchitecturalMonodromyIndex.{z}) :
    A.value = ∑ square : A.Square, A.weight square * A.mu square A.selectedAxis :=
  A.value_eq_weighted_sum

/-- VI.定義10.6: AMI weights are positive by selected data. -/
theorem weight_positive_holds
    (A : ArchitecturalMonodromyIndex.{z}) (square : A.Square) :
    0 < A.weight square :=
  A.weight_positive square

end ArchitecturalMonodromyIndex

end SingularityMonodromyStack
end AAT.AG
