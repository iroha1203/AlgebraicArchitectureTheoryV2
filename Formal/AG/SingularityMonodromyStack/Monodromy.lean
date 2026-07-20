import Formal.AG.SingularityMonodromyStack.OperationHomotopy

noncomputable section

open BigOperators

namespace AAT.AG
namespace SingularityMonodromyStack

universe u v w x y z

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

/-- VI.定義10.1: coefficient automorphisms are equal componentwise. -/
@[ext]
theorem ext {C : MonodromyCoefficientObject.{z}}
    {f g : CoefficientAutomorphism C}
    (hOb : f.obAut = g.obAut)
    (hSem : f.semAut = g.semAut)
    (hEff : f.effAut = g.effAut) :
    f = g := by
  cases f
  cases g
  cases hOb
  cases hSem
  cases hEff
  rfl

/-- VI.定義10.1: identity coefficient automorphism. -/
def id (C : MonodromyCoefficientObject.{z}) : CoefficientAutomorphism C where
  obAut := Equiv.refl C.Ob
  semAut := Equiv.refl C.Sem
  effAut := Equiv.refl C.Eff

/-- VI.定義10.1: composition of selected coefficient automorphisms. -/
def comp {C : MonodromyCoefficientObject.{z}}
    (f g : CoefficientAutomorphism C) : CoefficientAutomorphism C where
  obAut := g.obAut.trans f.obAut
  semAut := g.semAut.trans f.semAut
  effAut := g.effAut.trans f.effAut

/-- VI.定義10.1: inverse selected coefficient automorphism. -/
def inv {C : MonodromyCoefficientObject.{z}}
    (f : CoefficientAutomorphism C) : CoefficientAutomorphism C where
  obAut := f.obAut.symm
  semAut := f.semAut.symm
  effAut := f.effAut.symm

/-- VI.定義10.1: multiplication uses the standard automorphism composition order. -/
instance {C : MonodromyCoefficientObject.{z}} : Mul (CoefficientAutomorphism C) :=
  ⟨comp⟩

/-- VI.定義10.1: the identity element is the componentwise identity automorphism. -/
instance {C : MonodromyCoefficientObject.{z}} : One (CoefficientAutomorphism C) :=
  ⟨id C⟩

/-- VI.定義10.1: inversion is the componentwise inverse automorphism. -/
instance {C : MonodromyCoefficientObject.{z}} : Inv (CoefficientAutomorphism C) :=
  ⟨inv⟩

/-- VI.定義10.1: componentwise composition makes coefficient automorphisms a group. -/
instance {C : MonodromyCoefficientObject.{z}} : Group (CoefficientAutomorphism C) where
  mul_assoc := by
    intro a b c
    apply ext <;> apply Equiv.ext <;> intro x <;> rfl
  one_mul := by
    intro a
    apply ext <;> apply Equiv.ext <;> intro x <;> rfl
  mul_one := by
    intro a
    apply ext <;> apply Equiv.ext <;> intro x <;> rfl
  inv_mul_cancel := by
    intro a
    apply ext
    · apply Equiv.ext
      intro x
      change a.obAut.symm (a.obAut x) = x
      exact a.obAut.symm_apply_apply x
    · apply Equiv.ext
      intro x
      change a.semAut.symm (a.semAut x) = x
      exact a.semAut.symm_apply_apply x
    · apply Equiv.ext
      intro x
      change a.effAut.symm (a.effAut x) = x
      exact a.effAut.symm_apply_apply x

end CoefficientAutomorphism

/--
VI.定義10.1: selected monodromy action.

`rho` is a representation of the Mathlib presented architecture fundamental
group on the selected coefficient automorphisms.
-/
structure MonodromyAction {U : AtomCarrier.{u}} {A : ArchitectureObject U}
    {S : Site.AATSite A} {P : StratumReadingParameter S}
    {k : Type v} [CommRing k]
    {X : ArchitectureStratum.{u, v, w, x, y} P k}
    {G : OperationCategoryData.{u, v, w, x, y, z} X}
    {R : RefactorEndpointReading.{u, v, w, x, y, z} G}
    {H : HomotopyGeneratorFamily.{u, v, w, x, y, z} R}
    {base : G.State}
    (Pi : PresentedArchitectureFundamentalGroup.{u, v, w, x, y, z} H base) where
  coefficient : MonodromyCoefficientObject.{z}
  rho : Pi.pi1AAT →* CoefficientAutomorphism coefficient

namespace MonodromyAction

variable {U : AtomCarrier.{u}} {A : ArchitectureObject U}
variable {S : Site.AATSite A} {P : StratumReadingParameter S}
variable {k : Type v} [CommRing k]
variable {X : ArchitectureStratum.{u, v, w, x, y} P k}
variable {G : OperationCategoryData.{u, v, w, x, y, z} X}
variable {R : RefactorEndpointReading.{u, v, w, x, y, z} G}
variable {H : HomotopyGeneratorFamily.{u, v, w, x, y, z} R}
variable {base : G.State}
variable {Pi : PresentedArchitectureFundamentalGroup.{u, v, w, x, y, z} H base}

/--
VI.定義10.1: construct the monodromy representation from selected generator
actions that kill every selected relator.

Implementation note: this uses `PresentedGroup.toGroup` directly, so the
representation is defined on `Pi.pi1AAT` itself. No separately supplied
comparison from the legacy `Pi.Pi1` carrier is used.
-/
def ofPresentedGenerators
    (Pi : PresentedArchitectureFundamentalGroup.{u, v, w, x, y, z} H base)
    (coefficient : MonodromyCoefficientObject.{z})
    (generatorAction :
      FormalEdgeStep.{u, v, w, x, y, z} G -> CoefficientAutomorphism coefficient)
    (relators_map_to_one :
      ∀ r ∈ Pi.presentedRelators, FreeGroup.lift generatorAction r = 1) :
    MonodromyAction.{u, v, w, x, y, z} Pi where
  coefficient := coefficient
  rho := Pi.presentedGroupLift generatorAction relators_map_to_one

/-- VI.定義10.1: evaluate `Mon_gamma` as the supplied representation. -/
def Mon_gamma (M : MonodromyAction.{u, v, w, x, y, z} Pi) (gamma : Pi.pi1AAT) :
    CoefficientAutomorphism M.coefficient :=
  M.rho gamma

/-- VI.定義10.1: `Mon_gamma` is definitionally `rho gamma`. -/
theorem mon_gamma_eq_rho
    (M : MonodromyAction.{u, v, w, x, y, z} Pi) (gamma : Pi.pi1AAT) :
    M.Mon_gamma gamma = M.rho gamma :=
  rfl

/-- VI.定義10.1: the presented representation evaluates to its selected generator action. -/
theorem mon_gamma_presented_generator
    (Pi : PresentedArchitectureFundamentalGroup.{u, v, w, x, y, z} H base)
    (coefficient : MonodromyCoefficientObject.{z})
    (generatorAction :
      FormalEdgeStep.{u, v, w, x, y, z} G -> CoefficientAutomorphism coefficient)
    (relators_map_to_one :
      ∀ r ∈ Pi.presentedRelators, FreeGroup.lift generatorAction r = 1)
    (step : FormalEdgeStep.{u, v, w, x, y, z} G) :
    (ofPresentedGenerators Pi coefficient generatorAction relators_map_to_one).Mon_gamma
        (PresentedGroup.of step) = generatorAction step :=
  Pi.presentedGroupLift_of generatorAction relators_map_to_one step

/-- VI.定義10.1: every selected relator has identity monodromy. -/
theorem mon_gamma_presented_relator
    (M : MonodromyAction.{u, v, w, x, y, z} Pi)
    {word : Pi.FreeWord} (hword : Pi.Relator word) :
    M.Mon_gamma (Pi.presentedQuotientMap word) = 1 := by
  rw [Pi.presentedRelator_maps_to_identity hword]
  exact M.rho.map_one

/-- VI.定義10.1: monodromy sends the identity loop to identity coefficients. -/
theorem rho_one_holds
    (M : MonodromyAction.{u, v, w, x, y, z} Pi) :
    M.rho 1 = CoefficientAutomorphism.id M.coefficient :=
  M.rho.map_one

/-- VI.定義10.1: monodromy respects multiplication in the presented group. -/
theorem rho_mul_holds
    (M : MonodromyAction.{u, v, w, x, y, z} Pi)
    (gamma delta : Pi.pi1AAT) :
    M.rho (gamma * delta) =
      CoefficientAutomorphism.comp (M.rho gamma) (M.rho delta) :=
  M.rho.map_mul gamma delta

/-- VI.定義10.3: obstruction-sheaf component of a selected monodromy action. -/
def obstructionMonodromy
    (M : MonodromyAction.{u, v, w, x, y, z} Pi) (gamma : Pi.pi1AAT) :
    M.coefficient.Ob ≃ M.coefficient.Ob :=
  (M.Mon_gamma gamma).obAut

/-- VI.定義10.3: selected monodromy debt predicate. -/
def MonodromyDebt
    (M : MonodromyAction.{u, v, w, x, y, z} Pi) (gamma : Pi.pi1AAT) : Prop :=
  M.obstructionMonodromy gamma ≠ (CoefficientAutomorphism.id M.coefficient).obAut

/-- VI.定義10.3: monodromy debt is exactly nonidentity obstruction monodromy. -/
theorem monodromyDebt_iff
    (M : MonodromyAction.{u, v, w, x, y, z} Pi) (gamma : Pi.pi1AAT) :
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
    {X : ArchitectureStratum.{u, v, w, x, y} P k}
    (G : OperationCategoryData.{u, v, w, x, y, z} X) where
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
variable {X : ArchitectureStratum.{u, v, w, x, y} P k}
variable {G : OperationCategoryData.{u, v, w, x, y, z} X}

/-- VI.定義10.2: selected Gauss-Manin identity transport. -/
theorem transport_id_holds
    (GM : FiniteGaussManinSystem.{u, v, w, x, y, z} G)
    (a : GM.Object) :
    GM.transport (OperationPath.id (G := G) (GM.objectState a)) = LinearMap.id :=
  GM.transport_id a

/-- VI.定義10.2: selected Gauss-Manin transport is functorial for path composition. -/
theorem transport_comp_holds
    (GM : FiniteGaussManinSystem.{u, v, w, x, y, z} G)
    {a b c : GM.Object}
    (alpha : OperationPath G (GM.objectState a) (GM.objectState b))
    (beta : OperationPath G (GM.objectState b) (GM.objectState c)) :
    GM.transport (OperationPath.concat alpha beta) =
      (GM.transport beta).comp (GM.transport alpha) :=
  GM.transport_comp alpha beta

/-- VI.定義10.2: selected loop transport as an automorphism package. -/
structure LoopMonodromy
    (GM : FiniteGaussManinSystem.{u, v, w, x, y, z} G)
    (a : GM.Object)
    (gamma : OperationPath G (GM.objectState a) (GM.objectState a)) where
  toLinearEquiv : GM.Fiber a ≃ₗ[k] GM.Fiber a
  toLinearEquiv_eq_transport : toLinearEquiv.toLinearMap = GM.transport gamma

/-- VI.定義10.2: expose the selected Gauss-Manin loop transport map. -/
theorem loopMonodromy_eq_transport
    {GM : FiniteGaussManinSystem.{u, v, w, x, y, z} G}
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
    {X : ArchitectureStratum.{u, v, w, x, y} P k}
    {G : OperationCategoryData.{u, v, w, x, y, z} X}
    {R : RefactorEndpointReading.{u, v, w, x, y, z} G}
    {H : HomotopyGeneratorFamily.{u, v, w, x, y, z} R}
    {base : G.State}
    {Pi : PresentedArchitectureFundamentalGroup.{u, v, w, x, y, z} H base}
    (M : MonodromyAction.{u, v, w, x, y, z} Pi)
    (K : PresentationTwoComplex.{u, v, w, x, y, z} H) where
  Axis : Type z
  square : K.TwoCell
  boundaryElement : Pi.pi1AAT
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
variable {X : ArchitectureStratum.{u, v, w, x, y} P k}
variable {G : OperationCategoryData.{u, v, w, x, y, z} X}
variable {R : RefactorEndpointReading.{u, v, w, x, y, z} G}
variable {H : HomotopyGeneratorFamily.{u, v, w, x, y, z} R}
variable {base : G.State}
variable {Pi : PresentedArchitectureFundamentalGroup.{u, v, w, x, y, z} H base}
variable {M : MonodromyAction.{u, v, w, x, y, z} Pi}
variable {K : PresentationTwoComplex.{u, v, w, x, y, z} H}

/-- VI.定義10.4: `mu_x(sigma)` is the selected equality-defect reading. -/
theorem mu_eq_defect_holds
    (Q : MeasuredSquareMonodromy.{u, v, w, x, y, z} M K)
    (axis : Q.Axis) :
    Q.mu axis = Q.equalityDefect axis :=
  Q.mu_eq_defect axis

/-- VI.定義10.4: boundary-loop transport is the selected monodromy action. -/
theorem boundaryTransport_eq_monodromy_holds
    (Q : MeasuredSquareMonodromy.{u, v, w, x, y, z} M K) :
    Q.boundaryTransport = M.Mon_gamma Q.boundaryElement :=
  Q.boundaryTransport_eq_monodromy

/-- VI.定義10.4: zero defect is read by the selected axis detector. -/
theorem axis_detects_of_mu_zero
    (Q : MeasuredSquareMonodromy.{u, v, w, x, y, z} M K)
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
