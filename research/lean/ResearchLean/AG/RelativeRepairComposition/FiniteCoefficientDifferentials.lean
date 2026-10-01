import Formal.Util.AssertStandardAxioms
import ResearchLean.AG.RelativeRepairComposition.FiniteFamilyCoordinates
import ResearchLean.AG.RelativeRepairComposition.RelativeCoverComplex

/-!
# Executable original differentials with linear full-kernel transport

## Implementation notes

Closed-region values are extended using the input membership decision. The
computed maps use the original authored paths and pastings. The comparison
with accepted relative differentials uses restriction and closed incidence,
without asserting that zero extension is a chain map.
-/
namespace AAT.AG.RelativeRepairComposition
open TransportCoherence AbelianLiftingObstruction
universe uk uG uA
namespace FiniteFamily
variable {k : Type uk} [Field k]
variable {I : Type uG} (A : I → Type uA)
variable [∀ i, AddCommGroup (A i)] [∀ i, Module k (A i)]
variable (s : Set I) [DecidablePred (· ∈ s)]

/-- Computable degreewise extension uses the explicit input membership decision. -/
def extend : (∀ i : s, A i.1) →ₗ[k] (∀ i, A i) where
  toFun b i := if hi : i ∈ s then b ⟨i,hi⟩ else 0
  map_add' b c := by funext i; by_cases hi : i ∈ s <;> simp [hi]
  map_smul' t b := by funext i; by_cases hi : i ∈ s <;> simp [hi]

/-- Restricting the computed extension keeps all original included values. -/
theorem restrict_extend (b : ∀ i : s, A i.1) : Family.restrict A s (extend (k := k) A s b) = b := by
  funext i
  change (if hi : i.1 ∈ s then b ⟨i.1,hi⟩ else 0) = b i
  simp only [dif_pos i.2]

end FiniteFamily
namespace FiniteCoefficients
variable {k : Type uk} [Field k]
variable {K : FiniteTransportPresentation.{uG}} (M : LocalCoefficients.{uG,uA} K)
variable [∀ v, Module k (M.A v)]
variable (hlinear : ∀ {i j : K.Vertex} (e : K.Edge i j) (t : k) (x : M.A i),
  M.edge e (t • x) = t • M.edge e x)

/-- Edge coefficient modules use the complete original target-vertex module. -/
instance edgeModules : ∀ e : EdgeName (K := K), Module k (M.A e.2.1) := fun _ => inferInstance

/-- Face coefficient modules use the same original target-vertex module. -/
instance faceModules : ∀ f : K.TwoCell, Module k (M.A (K.twoTarget f)) := fun _ => inferInstance


include hlinear in
/-- The actual full-kernel path transport is linear on every typed original path. -/
theorem pathTransport_smul {i j : K.Vertex} (w : K.Path i j) (t : k) (x : M.A i) :
    M.pathTransport w (t • x) = t • M.pathTransport w x := by
  induction w with
  | nil i => rfl
  | cons e tail ih =>
    change M.pathTransport tail (M.edge e (t • x)) = t • M.pathTransport tail (M.edge e x)
    rw [hlinear,ih]

include hlinear in
/-- Every occurrence of an original edge is counted linearly in path correction. -/
theorem pathCorrection_smul (h : C1 M) (t : k) {i j : K.Vertex} (w : K.Path i j) :
    pathCorrection M (t • h) w = t • pathCorrection M h w := by
  induction w with
  | nil i => simp only [pathCorrection_nil,smul_zero]
  | cons e tail ih =>
    simp only [pathCorrection_cons,Pi.smul_apply,pathTransport_smul M hlinear,ih,smul_add]

include hlinear in
/-- The same original vertex differential is linear. -/
theorem d0_smul (b : C0 M) (t : k) : d0 M (t • b) = t • d0 M b := by
  funext e
  change t • b e.2.1 - M.edge e.2.2 (t • b e.1) = t • (b e.2.1 - M.edge e.2.2 (b e.1))
  rw [hlinear,smul_sub]

include hlinear in
/-- The same two authored face paths give a linear face differential. -/
theorem d1_smul (h : C1 M) (t : k) : d1 M (t • h) = t • d1 M h := by
  funext f
  simp only [d1,Pi.smul_apply,pathCorrection_smul M hlinear,smul_sub]

variable (U P : ClosedRegion K)
variable [DecidablePred (· ∈ U.vertices)] [DecidablePred (· ∈ U.edges)]

/-- The complete original relative vertex family has the pointwise coefficient module. -/
instance relative0Module : Module k (RelativeCover.C0 M U P) :=
  FiniteFamily.relativeModule M.A U.vertices P.vertices

/-- The complete original relative edge family has the same pointwise coefficient module. -/
instance relative1Module : Module k (RelativeCover.C1 M U P) :=
  FiniteFamily.relativeModule (fun e : EdgeName (K := K) => M.A e.2.1) U.edges P.edges

/-- The complete original relative face family has the same pointwise coefficient module. -/
instance relative2Module : Module k (RelativeCover.C2 M U P) :=
  FiniteFamily.relativeModule (fun f => M.A (K.twoTarget f)) U.faces P.faces


/-- The complete original relative triple family has the same pointwise coefficient module. -/
instance relative3Module : Module k (RelativeCover.C3 M U P) :=
  FiniteFamily.relativeModule (fun t => M.A (K.threeTarget t)) U.triples P.triples


omit [DecidablePred (· ∈ U.edges)] in
/-- The computed vertex extension restricts to the same original relative values. -/
theorem restrict_extend0 (b : RelativeCover.C0 M U P) :
    ClosedRegion.r0 M U (FiniteFamily.extend (k := k) M.A U.vertices b.1) = b.1 :=
  FiniteFamily.restrict_extend M.A U.vertices b.1

omit [DecidablePred (· ∈ U.vertices)] in
/-- The computed edge extension restricts to the same original relative values. -/
theorem restrict_extend1 (h : RelativeCover.C1 M U P) :
    ClosedRegion.r1 M U (FiniteFamily.extend (k := k) (fun e : EdgeName (K := K) => M.A e.2.1) U.edges h.1) = h.1 :=
  FiniteFamily.restrict_extend (fun e : EdgeName (K := K) => M.A e.2.1) U.edges h.1

/-- Compute the relative vertex differential using the original full transport. -/
def differential0 : RelativeCover.C0 M U P →ₗ[k] RelativeCover.C1 M U P where
  toFun b := ⟨ClosedRegion.r1 M U (d0 M (FiniteFamily.extend (k := k) M.A U.vertices b.1)),by
    have h := ClosedRegion.r_d0 M U (FiniteFamily.extend (k := k) M.A U.vertices b.1)
    rw [restrict_extend0 M U P b] at h
    rw [h]
    exact RelativeCover.d0_mem M U P b⟩
  map_add' b c := by
    apply Subtype.ext
    change ClosedRegion.r1 M U (d0 M (FiniteFamily.extend (k := k) M.A U.vertices (b.1 + c.1))) = _
    rw [map_add,d0_add,map_add]
    rfl
  map_smul' t b := by
    apply Subtype.ext
    change ClosedRegion.r1 M U (d0 M (FiniteFamily.extend (k := k) M.A U.vertices (t • b.1))) = _
    rw [map_smul,d0_smul M hlinear]
    rfl

/-- Compute the relative face differential using both original authored paths. -/
def differential1 : RelativeCover.C1 M U P →ₗ[k] RelativeCover.C2 M U P where
  toFun h := ⟨ClosedRegion.r2 M U (d1 M (FiniteFamily.extend (k := k) (fun e : EdgeName (K := K) => M.A e.2.1) U.edges h.1)),by
    have hh := ClosedRegion.r_d1 M U (FiniteFamily.extend (k := k) (fun e : EdgeName (K := K) => M.A e.2.1) U.edges h.1)
    rw [restrict_extend1 M U P h] at hh
    rw [hh]
    exact RelativeCover.d1_mem M U P h⟩
  map_add' h h' := by
    apply Subtype.ext
    change ClosedRegion.r2 M U (d1 M (FiniteFamily.extend (k := k) (fun e : EdgeName (K := K) => M.A e.2.1) U.edges (h.1 + h'.1))) = _
    rw [map_add,d1_add,map_add]
    rfl
  map_smul' t h := by
    apply Subtype.ext
    change ClosedRegion.r2 M U (d1 M (FiniteFamily.extend (k := k) (fun e : EdgeName (K := K) => M.A e.2.1) U.edges (t • h.1))) = _
    rw [map_smul,d1_smul M hlinear]
    rfl

omit [DecidablePred (· ∈ U.edges)] in
/-- The computed vertex map is exactly the accepted original relative differential. -/
theorem differential0_eq (b : RelativeCover.C0 M U P) :
    differential0 M hlinear U P b = RelativeCover.d0 M U P b := by
  apply Subtype.ext
  have h := ClosedRegion.r_d0 M U (FiniteFamily.extend (k := k) M.A U.vertices b.1)
  rw [restrict_extend0 M U P b] at h
  exact h

omit [DecidablePred (· ∈ U.vertices)] in
/-- The computed face map is exactly the accepted original relative differential. -/
theorem differential1_eq (h : RelativeCover.C1 M U P) :
    differential1 M hlinear U P h = RelativeCover.d1 M U P h := by
  apply Subtype.ext
  have hh := ClosedRegion.r_d1 M U (FiniteFamily.extend (k := k) (fun e : EdgeName (K := K) => M.A e.2.1) U.edges h.1)
  rw [restrict_extend1 M U P h] at hh
  exact hh

/-- The same original complex supplies the zero-composition law for the computed maps. -/
theorem differential1_differential0 (b : RelativeCover.C0 M U P) :
    differential1 M hlinear U P (differential0 M hlinear U P b) = 0 := by
  rw [differential0_eq,differential1_eq,RelativeCover.d1_d0]

end FiniteCoefficients
end AAT.AG.RelativeRepairComposition

#assert_standard_axioms_only AAT.AG.RelativeRepairComposition
