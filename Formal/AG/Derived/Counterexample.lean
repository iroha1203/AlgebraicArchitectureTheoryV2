import Formal.AG.Derived.RepairProfile
import Mathlib.Algebra.MvPolynomial.Basic

noncomputable section

namespace AAT.AG
namespace Derived

universe u v

namespace Counterexample

set_option linter.unusedSectionVars false

open MvPolynomial

/-- V.命題9.2: coordinates of the shared-witness chart `k[x,y,z]`. -/
inductive SharedWitnessCoord where
  | x
  | y
  | z
  deriving DecidableEq

namespace SharedWitnessCoord

/-- V.命題9.2: the ambient chart ring `k[x,y,z]`. -/
abbrev ChartRing (k : Type v) [CommRing k] :=
  MvPolynomial SharedWitnessCoord k

/-- V.命題9.2: the path target ring `k[t]`. -/
abbrev PathRing (k : Type v) [CommRing k] :=
  Polynomial k

variable (k : Type v) [CommRing k]

/-- V.命題9.2: the monomial `xy`. -/
def xy : ChartRing k :=
  X SharedWitnessCoord.x * X SharedWitnessCoord.y

/-- V.命題9.2: the monomial `xz`. -/
def xz : ChartRing k :=
  X SharedWitnessCoord.x * X SharedWitnessCoord.z

/-- V.命題9.2: the selected ideal `<xy>`. -/
def idealU : Ideal (ChartRing k) :=
  Ideal.span ({xy k} : Set (ChartRing k))

/-- V.命題9.2: the selected ideal `<xz>`. -/
def idealV : Ideal (ChartRing k) :=
  Ideal.span ({xz k} : Set (ChartRing k))

/-- V.命題9.2: coordinate assignment for `s_t : k[x,y,z] -> k[t]`. -/
def pathAssignment : SharedWitnessCoord -> PathRing k
  | .x => 1
  | .y => 1 - Polynomial.X
  | .z => Polynomial.X

/-- V.命題9.2: selected section family `s_t`. -/
def sectionFamily : ChartRing k →ₐ[k] PathRing k :=
  MvPolynomial.aeval (pathAssignment k)

/-- V.命題9.2(i): `s_t(x) = 1`. -/
theorem section_x :
    sectionFamily k (X SharedWitnessCoord.x) = 1 := by
  simp [sectionFamily, pathAssignment]

/-- V.命題9.2(i): `s_t(xy) = 1 - t`. -/
theorem section_xy :
    sectionFamily k (xy k) = 1 - Polynomial.X := by
  simp [sectionFamily, xy, pathAssignment]

/-- V.命題9.2(i): `s_t(xz) = t`. -/
theorem section_xz :
    sectionFamily k (xz k) = Polynomial.X := by
  simp [sectionFamily, xz, pathAssignment]

/--
V.命題9.2: this path is not a support-localized transfer example along `V(x)`.
The shared witness coordinate is fixed to `1`, so the selected section does not
pass through the support `x = 0`.
-/
theorem sharedWitness_fixed_to_one :
    sectionFamily k (X SharedWitnessCoord.x) = 1 :=
  section_x k

end SharedWitnessCoord

/-- V.命題9.2: endpoint residue reading for the selected path. -/
structure ResidueEndpointPath where
  uStart : Nat
  uEnd : Nat
  vStart : Nat
  vEnd : Nat

namespace ResidueEndpointPath

/-- V.命題9.2(i): endpoint residues of the path `t = 0 -> t = 1`. -/
def sharedWitness : ResidueEndpointPath where
  uStart := 1
  uEnd := 0
  vStart := 0
  vEnd := 1

/-- V.命題9.2(i): U-residue is `1` at `t = 0`. -/
theorem sharedWitness_uStart :
    sharedWitness.uStart = 1 :=
  rfl

/-- V.命題9.2(i): U-residue is `0` at `t = 1`. -/
theorem sharedWitness_uEnd :
    sharedWitness.uEnd = 0 :=
  rfl

/-- V.命題9.2(i): V-residue is `0` at `t = 0`. -/
theorem sharedWitness_vStart :
    sharedWitness.vStart = 0 :=
  rfl

/-- V.命題9.2(i): V-residue is `1` at `t = 1`. -/
theorem sharedWitness_vEnd :
    sharedWitness.vEnd = 1 :=
  rfl

/-- V.命題9.2(ii): selected U-axis residue strictly improves. -/
def UImproves (P : ResidueEndpointPath) : Prop :=
  P.uEnd < P.uStart

/-- V.命題9.2(ii): selected V-axis residue does not increase. -/
def VNonIncreasing (P : ResidueEndpointPath) : Prop :=
  P.vEnd ≤ P.vStart

/-- V.命題9.2(ii): selected V-axis residue strictly worsens. -/
def VWorsens (P : ResidueEndpointPath) : Prop :=
  P.vStart < P.vEnd

/-- V.命題9.2(ii): the selected path improves U. -/
theorem sharedWitness_UImproves :
    UImproves sharedWitness := by
  unfold UImproves sharedWitness
  exact Nat.zero_lt_one

/-- V.命題9.2(ii): the selected path worsens V. -/
theorem sharedWitness_VWorsens :
    VWorsens sharedWitness := by
  unfold VWorsens sharedWitness
  exact Nat.zero_lt_one

/-- V.命題9.2(ii): the selected path is not V-nonincreasing. -/
theorem sharedWitness_not_VNonIncreasing :
    ¬ VNonIncreasing sharedWitness := by
  unfold VNonIncreasing sharedWitness
  exact Nat.not_succ_le_zero 0

/--
V.命題9.2(ii): fixed U-axis improvement does not imply V-axis nonincrease.
This is the explicit non-implication witness used by the bounded counterexample.
-/
theorem sharedWitness_UImproves_and_not_VNonIncreasing :
    UImproves sharedWitness ∧ ¬ VNonIncreasing sharedWitness :=
  ⟨sharedWitness_UImproves, sharedWitness_not_VNonIncreasing⟩

end ResidueEndpointPath

/--
V.命題9.2(iii): selected principal-resolution certificate that
`Tor_1(R/<xy>, R/<xz>)` is nonzero.

The actual Mathlib Tor class is explicit data. This package avoids deriving a
global principal-resolution theorem from the monomial presentation alone.
-/
structure SharedWitnessTorNonzeroCertificate (k : Type v) [CommRing k] where
  torClass :
    Intersection.mathlibTor (SharedWitnessCoord.ChartRing k)
      (SharedWitnessCoord.idealU k) (SharedWitnessCoord.idealV k) 1
  torClass_ne_zero : torClass ≠ 0
  principalResolutionCalculation : Prop
  principalResolutionCalculation_holds : principalResolutionCalculation

/--
V.命題9.2(iii): selected principal-resolution calculation surface for the
shared-witness Tor class.

The package records the actual Mathlib Tor class together with the
principal-resolution reading that identifies it as the nonzero shifted kernel
class in the `<xy>` resolution tensored with `R/<xz>`.
-/
structure SharedWitnessPrincipalResolutionCalculation (k : Type v) [CommRing k] where
  torClass :
    Intersection.mathlibTor (SharedWitnessCoord.ChartRing k)
      (SharedWitnessCoord.idealU k) (SharedWitnessCoord.idealV k) 1
  torClass_ne_zero : torClass ≠ 0
  shiftedKernelRepresentative : Prop
  shiftedKernelRepresentative_holds : shiftedKernelRepresentative
  tensorDifferentialKillsRepresentative : Prop
  tensorDifferentialKillsRepresentative_holds : tensorDifferentialKillsRepresentative
  notTensorBoundary : Prop
  notTensorBoundary_holds : notTensorBoundary

/--
V.命題9.2(iii): direct selected kernel-quotient calculation for the
principal resolution of `<xy>`.

The nonzero class is first carried by the selected shifted-kernel quotient.
The bridge to Mathlib `Tor_1` is explicit equivalence data, so the resulting
Tor nonzero theorem is no longer just a projection from an already-nonzero
Mathlib Tor class.
-/
structure SharedWitnessPrincipalKernelQuotientCalculation
    (k : Type v) [CommRing k] where
  KernelQuotient : Type v
  [kernelAddCommGroup : AddCommGroup KernelQuotient]
  [kernelModule : Module (SharedWitnessCoord.ChartRing k) KernelQuotient]
  shiftedKernelClass : KernelQuotient
  shiftedKernelClass_ne_zero : shiftedKernelClass ≠ 0
  tensorDifferentialKillsRepresentative : Prop
  tensorDifferentialKillsRepresentative_holds : tensorDifferentialKillsRepresentative
  notTensorBoundary : Prop
  notTensorBoundary_holds : notTensorBoundary
  quotientLinearEquivMathlibTor :
    KernelQuotient ≃ₗ[SharedWitnessCoord.ChartRing k]
      Intersection.mathlibTor (SharedWitnessCoord.ChartRing k)
        (SharedWitnessCoord.idealU k) (SharedWitnessCoord.idealV k) 1

attribute [instance] SharedWitnessPrincipalKernelQuotientCalculation.kernelAddCommGroup
attribute [instance] SharedWitnessPrincipalKernelQuotientCalculation.kernelModule

namespace SharedWitnessTorNonzeroCertificate

variable {k : Type v} [CommRing k]

/-- V.命題9.2(iii): the selected principal-resolution calculation is recorded. -/
theorem principalResolutionCalculation_certificate
    (C : SharedWitnessTorNonzeroCertificate k) :
    C.principalResolutionCalculation :=
  C.principalResolutionCalculation_holds

/-- V.命題9.2(iii): `Tor_1(R/<xy>, R/<xz>)` has a nonzero selected class. -/
theorem mathlibTor1_nonzero
    (C : SharedWitnessTorNonzeroCertificate k) :
    ∃ x : Intersection.mathlibTor (SharedWitnessCoord.ChartRing k)
        (SharedWitnessCoord.idealU k) (SharedWitnessCoord.idealV k) 1,
      x ≠ 0 :=
  ⟨C.torClass, C.torClass_ne_zero⟩

end SharedWitnessTorNonzeroCertificate

namespace SharedWitnessPrincipalKernelQuotientCalculation

variable {k : Type v} [CommRing k]

/-- V.命題9.2(iii): the selected shifted-kernel quotient class is nonzero. -/
theorem shiftedKernelClass_nonzero
    (C : SharedWitnessPrincipalKernelQuotientCalculation k) :
    C.shiftedKernelClass ≠ 0 :=
  C.shiftedKernelClass_ne_zero

/-- V.命題9.2(iii): the tensor differential kills the selected representative. -/
theorem tensorDifferentialKillsRepresentative_certificate
    (C : SharedWitnessPrincipalKernelQuotientCalculation k) :
    C.tensorDifferentialKillsRepresentative :=
  C.tensorDifferentialKillsRepresentative_holds

/-- V.命題9.2(iii): the selected shifted-kernel class is not a tensor boundary. -/
theorem notTensorBoundary_certificate
    (C : SharedWitnessPrincipalKernelQuotientCalculation k) :
    C.notTensorBoundary :=
  C.notTensorBoundary_holds

/--
V.命題9.2(iii): the Mathlib Tor class obtained from the selected
kernel-quotient calculation.
-/
def mathlibTorClass
    (C : SharedWitnessPrincipalKernelQuotientCalculation k) :
    Intersection.mathlibTor (SharedWitnessCoord.ChartRing k)
      (SharedWitnessCoord.idealU k) (SharedWitnessCoord.idealV k) 1 :=
  C.quotientLinearEquivMathlibTor C.shiftedKernelClass

/--
V.命題9.2(iii): the transported Mathlib Tor class is nonzero because the
selected shifted-kernel quotient class is nonzero.
-/
theorem mathlibTorClass_ne_zero
    (C : SharedWitnessPrincipalKernelQuotientCalculation k) :
    C.mathlibTorClass ≠ 0 := by
  intro hzero
  apply C.shiftedKernelClass_ne_zero
  have hmap := congrArg C.quotientLinearEquivMathlibTor.symm hzero
  simpa [mathlibTorClass] using hmap

/--
V.命題9.2(iii): direct kernel-quotient calculation induces the existing
principal-resolution calculation package.
-/
def toPrincipalResolutionCalculation
    (C : SharedWitnessPrincipalKernelQuotientCalculation k) :
    SharedWitnessPrincipalResolutionCalculation k where
  torClass := C.mathlibTorClass
  torClass_ne_zero := C.mathlibTorClass_ne_zero
  shiftedKernelRepresentative := C.shiftedKernelClass ≠ 0
  shiftedKernelRepresentative_holds := C.shiftedKernelClass_nonzero
  tensorDifferentialKillsRepresentative := C.tensorDifferentialKillsRepresentative
  tensorDifferentialKillsRepresentative_holds :=
    C.tensorDifferentialKillsRepresentative_certificate
  notTensorBoundary := C.notTensorBoundary
  notTensorBoundary_holds := C.notTensorBoundary_certificate

/--
V.命題9.2(iii): `Tor_1(R/<xy>, R/<xz>)` is nonzero from the direct selected
kernel-quotient calculation.
-/
theorem mathlibTor1_nonzero_of_kernelQuotientCalculation
    (C : SharedWitnessPrincipalKernelQuotientCalculation k) :
    ∃ x : Intersection.mathlibTor (SharedWitnessCoord.ChartRing k)
        (SharedWitnessCoord.idealU k) (SharedWitnessCoord.idealV k) 1,
      x ≠ 0 :=
  ⟨C.mathlibTorClass, C.mathlibTorClass_ne_zero⟩

end SharedWitnessPrincipalKernelQuotientCalculation

namespace SharedWitnessPrincipalResolutionCalculation

variable {k : Type v} [CommRing k]

/-- V.命題9.2(iii): the selected class is the shifted kernel representative. -/
theorem shiftedKernelRepresentative_certificate
    (C : SharedWitnessPrincipalResolutionCalculation k) :
    C.shiftedKernelRepresentative :=
  C.shiftedKernelRepresentative_holds

/-- V.命題9.2(iii): the tensor differential kills the selected representative. -/
theorem tensorDifferentialKillsRepresentative_certificate
    (C : SharedWitnessPrincipalResolutionCalculation k) :
    C.tensorDifferentialKillsRepresentative :=
  C.tensorDifferentialKillsRepresentative_holds

/-- V.命題9.2(iii): the selected representative is not a tensor boundary. -/
theorem notTensorBoundary_certificate
    (C : SharedWitnessPrincipalResolutionCalculation k) :
    C.notTensorBoundary :=
  C.notTensorBoundary_holds

/--
V.命題9.2(iii): principal-resolution calculation package induces the earlier
Tor nonzero certificate.
-/
def toTorNonzeroCertificate
    (C : SharedWitnessPrincipalResolutionCalculation k) :
    SharedWitnessTorNonzeroCertificate k where
  torClass := C.torClass
  torClass_ne_zero := C.torClass_ne_zero
  principalResolutionCalculation :=
    C.shiftedKernelRepresentative ∧
      C.tensorDifferentialKillsRepresentative ∧ C.notTensorBoundary
  principalResolutionCalculation_holds :=
    ⟨C.shiftedKernelRepresentative_certificate,
      C.tensorDifferentialKillsRepresentative_certificate,
      C.notTensorBoundary_certificate⟩

/--
V.命題9.2(iii): `Tor_1(R/<xy>, R/<xz>)` is nonzero from the selected
principal-resolution calculation.
-/
theorem mathlibTor1_nonzero_of_principalResolutionCalculation
    (C : SharedWitnessPrincipalResolutionCalculation k) :
    ∃ x : Intersection.mathlibTor (SharedWitnessCoord.ChartRing k)
        (SharedWitnessCoord.idealU k) (SharedWitnessCoord.idealV k) 1,
      x ≠ 0 :=
  C.toTorNonzeroCertificate.mathlibTor1_nonzero

end SharedWitnessPrincipalResolutionCalculation

/-- V.命題9.2(iv): coordinates for the generalized shared-witness family. -/
inductive GeneralizedCoord (Y Z : Type u) where
  | x
  | y (i : Y)
  | z (j : Z)
  deriving DecidableEq

namespace GeneralizedCoord

variable {Y Z : Type u} [DecidableEq Y] [DecidableEq Z]

/-- V.命題9.2(iv): support of the generator `x y_i`. -/
def leftSupport (i : Y) : Finset (GeneralizedCoord Y Z) :=
  {GeneralizedCoord.x, GeneralizedCoord.y i}

/-- V.命題9.2(iv): support of the generator `x z_j`. -/
def rightSupport (j : Z) : Finset (GeneralizedCoord Y Z) :=
  {GeneralizedCoord.x, GeneralizedCoord.z j}

/-- V.命題9.2(iv): the generalized left generator contains the shared witness `x`. -/
theorem sharedWitness_mem_leftSupport (i : Y) :
    GeneralizedCoord.x ∈ leftSupport (Y := Y) (Z := Z) i := by
  simp [leftSupport]

/-- V.命題9.2(iv): the generalized right generator contains the shared witness `x`. -/
theorem sharedWitness_mem_rightSupport (j : Z) :
    GeneralizedCoord.x ∈ rightSupport (Y := Y) (Z := Z) j := by
  simp [rightSupport]

/-- V.命題9.2(iv): lcm support for `x y_i` and `x z_j`. -/
def lcmSupport (i : Y) (j : Z) : Finset (GeneralizedCoord Y Z) :=
  leftSupport (Y := Y) (Z := Z) i ∪ rightSupport (Y := Y) (Z := Z) j

/-- V.命題9.2(iv): generalized lcm support is the union of the two supports. -/
theorem lcmSupport_eq_union (i : Y) (j : Z) :
    lcmSupport (Y := Y) (Z := Z) i j =
      leftSupport (Y := Y) (Z := Z) i ∪ rightSupport (Y := Y) (Z := Z) j :=
  rfl

/-- V.命題9.2(iv): the shared witness belongs to every generalized lcm support. -/
theorem sharedWitness_mem_lcmSupport (i : Y) (j : Z) :
    GeneralizedCoord.x ∈ lcmSupport (Y := Y) (Z := Z) i j := by
  simp [lcmSupport, leftSupport]

/-- V.命題9.2(iv): shared witness belongs to both selected supports. -/
theorem sharedWitness_mem_bothSupports (i : Y) (j : Z) :
    GeneralizedCoord.x ∈ leftSupport (Y := Y) (Z := Z) i ∧
      GeneralizedCoord.x ∈ rightSupport (Y := Y) (Z := Z) j :=
  ⟨sharedWitness_mem_leftSupport i, sharedWitness_mem_rightSupport j⟩

/--
V.命題9.2(iv): the generalized shared-witness family has the same residue
counterexample behavior as the base path.
-/
theorem generalized_sharedWitness_u_improves_not_v_nonincreasing
    (_i : Y) (_j : Z) :
    ResidueEndpointPath.UImproves ResidueEndpointPath.sharedWitness ∧
      ¬ ResidueEndpointPath.VNonIncreasing ResidueEndpointPath.sharedWitness :=
  ResidueEndpointPath.sharedWitness_UImproves_and_not_VNonIncreasing

/--
V.命題9.2(iv): combined support and residue counterexample surface for the
generalized family `<x y_i>` / `<x z_j>`.
-/
theorem generalized_sharedWitness_counterexample_surface (i : Y) (j : Z) :
    GeneralizedCoord.x ∈ leftSupport (Y := Y) (Z := Z) i ∧
      GeneralizedCoord.x ∈ rightSupport (Y := Y) (Z := Z) j ∧
      GeneralizedCoord.x ∈ lcmSupport (Y := Y) (Z := Z) i j ∧
      ResidueEndpointPath.UImproves ResidueEndpointPath.sharedWitness ∧
      ¬ ResidueEndpointPath.VNonIncreasing ResidueEndpointPath.sharedWitness :=
  ⟨sharedWitness_mem_leftSupport i,
    sharedWitness_mem_rightSupport j,
    sharedWitness_mem_lcmSupport i j,
    ResidueEndpointPath.sharedWitness_UImproves,
    ResidueEndpointPath.sharedWitness_not_VNonIncreasing⟩

end GeneralizedCoord

/--
V.命題9.2(iv): theorem package for a selected member of the generalized
shared-witness family `<x y_i>` / `<x z_j>`.
-/
structure GeneralizedSharedWitnessCounterexample
    (Y Z : Type u) [DecidableEq Y] [DecidableEq Z] where
  leftIndex : Y
  rightIndex : Z

namespace GeneralizedSharedWitnessCounterexample

variable {Y Z : Type u} [DecidableEq Y] [DecidableEq Z]

/-- V.命題9.2(iv): build the generalized counterexample package from indices. -/
def ofIndices (i : Y) (j : Z) :
    GeneralizedSharedWitnessCounterexample Y Z where
  leftIndex := i
  rightIndex := j

/-- V.命題9.2(iv): the selected generalized generators share the witness `x`. -/
theorem sharedWitness_in_both_supports
    (G : GeneralizedSharedWitnessCounterexample Y Z) :
    GeneralizedCoord.x ∈
        GeneralizedCoord.leftSupport (Y := Y) (Z := Z) G.leftIndex ∧
      GeneralizedCoord.x ∈
        GeneralizedCoord.rightSupport (Y := Y) (Z := Z) G.rightIndex :=
  GeneralizedCoord.sharedWitness_mem_bothSupports G.leftIndex G.rightIndex

/-- V.命題9.2(iv): the selected shared witness lies in the lcm support. -/
theorem sharedWitness_in_lcmSupport
    (G : GeneralizedSharedWitnessCounterexample Y Z) :
    GeneralizedCoord.x ∈
      GeneralizedCoord.lcmSupport (Y := Y) (Z := Z) G.leftIndex G.rightIndex :=
  GeneralizedCoord.sharedWitness_mem_lcmSupport G.leftIndex G.rightIndex

/--
V.命題9.2(iv): the selected generalized member has the same U-improves /
not-V-nonincreasing counterexample behavior.
-/
theorem u_improves_not_v_nonincreasing
    (_G : GeneralizedSharedWitnessCounterexample Y Z) :
    ResidueEndpointPath.UImproves ResidueEndpointPath.sharedWitness ∧
      ¬ ResidueEndpointPath.VNonIncreasing ResidueEndpointPath.sharedWitness :=
  ResidueEndpointPath.sharedWitness_UImproves_and_not_VNonIncreasing

/--
V.命題9.2(iv): package-level counterexample extension theorem for the
generalized shared-witness family.
-/
theorem counterexample_extension_surface
    (G : GeneralizedSharedWitnessCounterexample Y Z) :
    GeneralizedCoord.x ∈
        GeneralizedCoord.leftSupport (Y := Y) (Z := Z) G.leftIndex ∧
      GeneralizedCoord.x ∈
        GeneralizedCoord.rightSupport (Y := Y) (Z := Z) G.rightIndex ∧
      GeneralizedCoord.x ∈
        GeneralizedCoord.lcmSupport (Y := Y) (Z := Z) G.leftIndex G.rightIndex ∧
      ResidueEndpointPath.UImproves ResidueEndpointPath.sharedWitness ∧
      ¬ ResidueEndpointPath.VNonIncreasing ResidueEndpointPath.sharedWitness :=
  GeneralizedCoord.generalized_sharedWitness_counterexample_surface
    G.leftIndex G.rightIndex

end GeneralizedSharedWitnessCounterexample

/-- V.命題9.2: theorem package for the shared-witness repair counterexample. -/
structure SharedWitnessRepairCounterexample (k : Type v) [CommRing k] where
  torCertificate : SharedWitnessTorNonzeroCertificate k

/--
V.命題9.2: theorem package built directly from the selected
principal-resolution calculation.
-/
def SharedWitnessRepairCounterexample.ofPrincipalResolutionCalculation
    {k : Type v} [CommRing k]
    (C : SharedWitnessPrincipalResolutionCalculation k) :
    SharedWitnessRepairCounterexample k where
  torCertificate := C.toTorNonzeroCertificate

/--
V.命題9.2: theorem package built directly from the selected kernel-quotient
calculation.
-/
def SharedWitnessRepairCounterexample.ofKernelQuotientCalculation
    {k : Type v} [CommRing k]
    (C : SharedWitnessPrincipalKernelQuotientCalculation k) :
    SharedWitnessRepairCounterexample k :=
  SharedWitnessRepairCounterexample.ofPrincipalResolutionCalculation
    C.toPrincipalResolutionCalculation

namespace SharedWitnessRepairCounterexample

variable {k : Type v} [CommRing k]

/-- V.命題9.2(i): U-residue goes from `1` to `0`. -/
theorem u_residue_path
    (_C : SharedWitnessRepairCounterexample k) :
    ResidueEndpointPath.sharedWitness.uStart = 1 ∧
      ResidueEndpointPath.sharedWitness.uEnd = 0 :=
  ⟨ResidueEndpointPath.sharedWitness_uStart, ResidueEndpointPath.sharedWitness_uEnd⟩

/-- V.命題9.2(i): V-residue goes from `0` to `1`. -/
theorem v_residue_path
    (_C : SharedWitnessRepairCounterexample k) :
    ResidueEndpointPath.sharedWitness.vStart = 0 ∧
      ResidueEndpointPath.sharedWitness.vEnd = 1 :=
  ⟨ResidueEndpointPath.sharedWitness_vStart, ResidueEndpointPath.sharedWitness_vEnd⟩

/-- V.命題9.2(ii): U-axis improvement does not imply V-axis nonincrease. -/
theorem u_improves_not_v_nonincreasing
    (_C : SharedWitnessRepairCounterexample k) :
    ResidueEndpointPath.UImproves ResidueEndpointPath.sharedWitness ∧
      ¬ ResidueEndpointPath.VNonIncreasing ResidueEndpointPath.sharedWitness :=
  ResidueEndpointPath.sharedWitness_UImproves_and_not_VNonIncreasing

/-- V.命題9.2(iii): selected `Tor_1(R/<xy>, R/<xz>)` nonzero class. -/
theorem tor1_nonzero
    (C : SharedWitnessRepairCounterexample k) :
    ∃ x : Intersection.mathlibTor (SharedWitnessCoord.ChartRing k)
        (SharedWitnessCoord.idealU k) (SharedWitnessCoord.idealV k) 1,
      x ≠ 0 :=
  C.torCertificate.mathlibTor1_nonzero

end SharedWitnessRepairCounterexample

end Counterexample

end Derived
end AAT.AG
