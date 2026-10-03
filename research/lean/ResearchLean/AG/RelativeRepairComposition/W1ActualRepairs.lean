import ResearchLean.AG.RelativeRepairComposition.W1AuthoredOperations
import ResearchLean.AG.RelativeRepairComposition.W1Regions

/-!
# All independent actual W1 repairs and their original parameters

## Implementation notes

RealRepairs is the existing independently specified NativeAffine.Repair of
the original input, not a coordinate image. The four values at zero recover
every original affine operation using its given linear part and physical
anchors. Conversely, the authored-word evaluations construct an actual repair
from parameters satisfying precisely the two derived Laws and permissions.
-/
namespace AAT.AG.RelativeRepairComposition.W1ActualRepairs
open CategoryTheory TransportCoherence TransportCoherence.Arbitrary AbelianLiftingObstruction
open NativeAffine W1AffineInput W1AuthoredOperations W1Regions

/-- The four original translation values; data precedes either derived Law or permission predicate. -/
structure Parameters where
  /-- The original shared always-edge e correction. -/
  u : ZMod 3
  /-- The entire private always-edge a correction. -/
  h : ZMod 3
  /-- The original candidate b correction. -/
  z : ZMod 3
  /-- The original candidate c correction. -/
  v : ZMod 3
  deriving DecidableEq

/-- The two scalar equations derived from the complete original authored affine words. -/
def Equations (negative : Bool) (x y : ZMod 3) (p : Parameters) : Prop :=
  p.u + p.z = x ∧
    (if negative then p.u - p.z + p.v = y else p.u + 2 * p.h + p.z + p.v = y)

/-- A forbidden original candidate has exactly zero correction; the always edges retain their whole kernels. -/
def Allowed (S : Set (EdgeName (K := geometry))) (p : Parameters) : Prop :=
  (name edgeB ∉ S → p.z = 0) ∧ (name edgeC ∉ S → p.v = 0)

/-- Independently supplied actual operations retain the original linear parts, both authored Laws and all physical fixed edges. -/
abbrev RealRepairs (negative : Bool) (x y : ZMod 3) (S : Set (EdgeName (K := geometry))) :=
  NativeAffine.Repair geometry (reference negative x y) comparison (fixedEdges S)

/-- Every independent actual operation is recovered from its given original linear component and actual value at zero. -/
theorem actual_operation_apply {negative : Bool} {x y : ZMod 3}
    {S : Set (EdgeName (K := geometry))} (R : RealRepairs negative x y S)
    {i j : geometry.Vertex} (e : geometry.Edge i j) (t : ZMod 3) :
    R.operation e t = (reference negative x y e).linear t + R.operation e 0 := by
  rw [NativeAffine.operation_apply, R.linear]

/-- Extraction retains all four original actual operation values, including the entire private h. -/
def parameters {negative : Bool} {x y : ZMod 3} {S : Set (EdgeName (K := geometry))}
    (R : RealRepairs negative x y S) : Parameters :=
  ⟨R.operation (i := ()) (j := ()) edgeE 0,
    R.operation (i := ()) (j := ()) edgeA 0,
    R.operation (i := ()) (j := ()) edgeB 0,
    R.operation (i := ()) (j := ()) edgeC 0⟩

/-- The complete parameter operation family equals every independent original operation, on all six names. -/
theorem parameters_operations {negative : Bool} {x y : ZMod 3}
    {S : Set (EdgeName (K := geometry))} (R : RealRepairs negative x y S) :
    @operation negative x y (parameters R).u (parameters R).h (parameters R).z (parameters R).v =
      @R.operation := by
  have hrx := R.fixed_value (name edgeRx) (rx_fixed S)
  have hry := R.fixed_value (name edgeRy) (ry_fixed S)
  change R.operation (i := ()) (j := ()) edgeRx = reference negative x y edgeRx at hrx
  change R.operation (i := ()) (j := ()) edgeRy = reference negative x y edgeRy at hry
  funext i j e
  cases i
  cases j
  ext t
  fin_cases e
  · change operation negative x y (parameters R).u (parameters R).h (parameters R).z (parameters R).v (i := ()) (j := ()) edgeE t = R.operation (i := ()) (j := ()) edgeE t
    rw [operation_e_apply, actual_operation_apply]
    simp only [geometry, reference, edgeE, edgeA, edgeRx, edgeRy, if_neg (by decide : (0 : Fin 6) ≠ 1),
      if_neg (by decide : (0 : Fin 6) ≠ 4), if_neg (by decide : (0 : Fin 6) ≠ 5), parameters]
    rfl
  · change operation negative x y (parameters R).u (parameters R).h (parameters R).z (parameters R).v (i := ()) (j := ()) edgeA t = R.operation (i := ()) (j := ()) edgeA t
    rw [operation_a_apply, actual_operation_apply]
    simp only [reference, edgeA, parameters]
    cases negative <;> rfl
  · change operation negative x y (parameters R).u (parameters R).h (parameters R).z (parameters R).v (i := ()) (j := ()) edgeB t = R.operation (i := ()) (j := ()) edgeB t
    rw [operation_b_apply, actual_operation_apply]
    simp only [geometry, reference, edgeB, edgeA, edgeRx, edgeRy, if_neg (by decide : (2 : Fin 6) ≠ 1),
      if_neg (by decide : (2 : Fin 6) ≠ 4), if_neg (by decide : (2 : Fin 6) ≠ 5), parameters]
    rfl
  · change operation negative x y (parameters R).u (parameters R).h (parameters R).z (parameters R).v (i := ()) (j := ()) edgeC t = R.operation (i := ()) (j := ()) edgeC t
    rw [operation_c_apply, actual_operation_apply]
    simp only [geometry, reference, edgeC, edgeA, edgeRx, edgeRy, if_neg (by decide : (3 : Fin 6) ≠ 1),
      if_neg (by decide : (3 : Fin 6) ≠ 4), if_neg (by decide : (3 : Fin 6) ≠ 5), parameters]
    rfl
  · change operation negative x y (parameters R).u (parameters R).h (parameters R).z (parameters R).v (i := ()) (j := ()) edgeRx t = R.operation (i := ()) (j := ()) edgeRx t
    rw [operation_rx_apply, hrx]
    simp [geometry, reference, edgeA, edgeRx, add_comm]
  · change operation negative x y (parameters R).u (parameters R).h (parameters R).z (parameters R).v (i := ()) (j := ()) edgeRy t = R.operation (i := ()) (j := ()) edgeRy t
    rw [operation_ry_apply, hry]
    simp [geometry, reference, edgeA, edgeRx, edgeRy, add_comm]

/-- The native full affine zero translation is the identity operation used in both comparisons. -/
theorem zero_translation : translation (k := ZMod 3) (0 : ZMod 3) = (1 : Op) := by
  ext t
  exact zero_add t

/-- The original actual affine face of any repair recovers its derived scalar Law, for either a linear part. -/
theorem parameters_equations {negative : Bool} {x y : ZMod 3}
    {S : Set (EdgeName (K := geometry))} (R : RealRepairs negative x y S) :
    Equations negative x y (parameters R) := by
  have hfirst := R.face false
  have hsecond := R.face true
  rw [← parameters_operations R] at hfirst hsecond
  simp only [comparison, zero_translation, one_mul] at hfirst hsecond
  refine ⟨(first_law_iff negative x y _ _ _ _).mp hfirst, ?_⟩
  cases negative
  · exact (second_identity_law_iff x y _ _ _ _).mp hsecond
  · exact (second_negative_law_iff x y _ _ _ _).mp hsecond

/-- Literal fixed candidate operations recover precisely the two zero masks on the same original names. -/
theorem parameters_allowed {negative : Bool} {x y : ZMod 3}
    {S : Set (EdgeName (K := geometry))} (R : RealRepairs negative x y S) :
    Allowed S (parameters R) := by
  constructor
  · intro hb
    have he := congrArg (fun g : Op => g 0) (R.fixed_value (name edgeB) ((b_fixed_iff S).mpr hb))
    simpa [geometry, parameters, name, reference, edgeA, edgeB, edgeRx, edgeRy] using he
  · intro hc
    have he := congrArg (fun g : Op => g 0) (R.fixed_value (name edgeC) ((c_fixed_iff S).mpr hc))
    simpa [geometry, parameters, name, reference, edgeA, edgeC, edgeRx, edgeRy] using he

/-- The derived equations reconstruct both full authored affine Laws. -/
theorem operation_faces (negative : Bool) (x y : ZMod 3) (p : Parameters)
    (he : Equations negative x y p) (f : geometry.TwoCell) :
    translation (k := ZMod 3) (comparison f) *
        GroupExtension.pathValue geometry (operation negative x y p.u p.h p.z p.v) (geometry.twoLeft f) =
      GroupExtension.pathValue geometry (operation negative x y p.u p.h p.z p.v) (geometry.twoRight f) := by
  rw [comparison, zero_translation, one_mul]
  cases f
  · exact (first_law_iff negative x y _ _ _ _).mpr he.1
  · cases negative
    · exact (second_identity_law_iff x y _ _ _ _).mpr he.2
    · exact (second_negative_law_iff x y _ _ _ _).mpr he.2

/-- Every original parameter operation retains the complete original affine linear component. -/
theorem operation_linear (negative : Bool) (x y : ZMod 3) (p : Parameters)
    {i j : geometry.Vertex} (e : geometry.Edge i j) :
    (operation negative x y p.u p.h p.z p.v e).linear = (reference negative x y e).linear := by
  change projection (operation negative x y p.u p.h p.z p.v e) = projection (reference negative x y e)
  rw [operation, map_mul, projection_translation, one_mul]

/-- The same original rx,ry anchors and forbidden candidate masks reconstruct every literal fixed operation. -/
theorem operation_fixed (negative : Bool) (x y : ZMod 3)
    (S : Set (EdgeName (K := geometry))) (p : Parameters) (ha : Allowed S p)
    (e : EdgeName (K := geometry)) (he : e ∈ fixedEdges S) :
    operation negative x y p.u p.h p.z p.v e.2.2 = reference negative x y e.2.2 := by
  rcases he with (he | he) | ⟨(he | he), hn⟩ <;> subst e
  · ext t
    change operation negative x y p.u p.h p.z p.v (i := ()) (j := ()) edgeRx t = reference negative x y edgeRx t
    rw [operation_rx_apply]
    simp [geometry, reference, edgeA, edgeRx, add_comm]
  · ext t
    change operation negative x y p.u p.h p.z p.v (i := ()) (j := ()) edgeRy t = reference negative x y edgeRy t
    rw [operation_ry_apply]
    simp [geometry, reference, edgeA, edgeRx, edgeRy, add_comm]
  · ext t
    change operation negative x y p.u p.h p.z p.v (i := ()) (j := ()) edgeB t = reference negative x y edgeB t
    rw [operation_b_apply, ha.1 hn]
    simp [geometry, reference, edgeA, edgeB, edgeRx, edgeRy]
  · ext t
    change operation negative x y p.u p.h p.z p.v (i := ()) (j := ()) edgeC t = reference negative x y edgeC t
    rw [operation_c_apply, ha.2 hn]
    simp [geometry, reference, edgeA, edgeC, edgeRx, edgeRy]

/-- Parameters satisfying the derived Laws and masks construct an independent actual repair on the original input. -/
noncomputable def actualRepair (negative : Bool) (x y : ZMod 3)
    (S : Set (EdgeName (K := geometry))) (p : Parameters)
    (he : Equations negative x y p) (ha : Allowed S p) : RealRepairs negative x y S where
  operation := operation negative x y p.u p.h p.z p.v
  linear := operation_linear negative x y p
  face := operation_faces negative x y p he
  fixed_value := operation_fixed negative x y S p ha

/-- Reconstruction returns every full original parameter, including h without a kernel restriction. -/
theorem actualRepair_parameters (negative : Bool) (x y : ZMod 3)
    (S : Set (EdgeName (K := geometry))) (p : Parameters)
    (he : Equations negative x y p) (ha : Allowed S p) :
    parameters (actualRepair negative x y S p he ha) = p := by
  cases p
  simp only [parameters, actualRepair, operation_e_apply, operation_a_apply,
    operation_b_apply, operation_c_apply, zero_add]
  simp [linearA_apply]

/-- Extraction followed by reconstruction recovers every independent original affine repair. -/
theorem parameters_actualRepair {negative : Bool} {x y : ZMod 3}
    {S : Set (EdgeName (K := geometry))} (R : RealRepairs negative x y S) :
    actualRepair negative x y S (parameters R) (parameters_equations R) (parameters_allowed R) = R := by
  apply NativeAffine.Repair.ext
  intro i j e
  exact congrFun (congrFun (congrFun (parameters_operations R) i) j) e

/-- All independent actual W1 repairs correspond in both directions to precisely the derived equations and masks. -/
noncomputable def actualParametersEquiv (negative : Bool) (x y : ZMod 3)
    (S : Set (EdgeName (K := geometry))) :
    RealRepairs negative x y S ≃ {p : Parameters // Equations negative x y p ∧ Allowed S p} where
  toFun R := ⟨parameters R, parameters_equations R, parameters_allowed R⟩
  invFun p := actualRepair negative x y S p.1 p.2.1 p.2.2
  left_inv := parameters_actualRepair
  right_inv p := Subtype.ext (actualRepair_parameters negative x y S p.1 p.2.1 p.2.2)

/-- The same full native tower and all physical supports have exactly the independent actual W1 parameterization. -/
noncomputable def nativeParametersEquiv (negative : Bool) (x y : ZMod 3)
    (S : Set (EdgeName (K := geometry))) :
    SupportedRepair (originalTower negative x y) (fixedEdges S) ≃
      {p : Parameters // Equations negative x y p ∧ Allowed S p} :=
  (NativeAffine.repairEquivalence geometry (reference negative x y) (reference negative x y)
    comparison (linear_faces negative x y) (fixedEdges S)).trans
      (actualParametersEquiv negative x y S)

end AAT.AG.RelativeRepairComposition.W1ActualRepairs
#assert_standard_axioms_only AAT.AG.RelativeRepairComposition.W1ActualRepairs
