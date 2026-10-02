import ResearchLean.AG.RelativeRepairComposition.SubdivisionCoefficientMaps
import ResearchLean.AG.RelativeRepairComposition.FiniteCoefficientDifferentials
import Mathlib.Algebra.Module.TransferInstance

/-!
# Linear structure on the same full actual subdivided kernels

The original vertex modules are retained. Scalar multiplication on the entire
fresh actual kernel is transported along the first actual kernel equivalence.
The second transport is then linear by its actual composite with the first.

## Implementation notes

Transporting the module retains the categorical kernel carrier and its actual
inclusion. Replacing that carrier by a vector space would lose the literal
cochain and defect values used by the original always quotient.
-/
namespace AAT.AG.RelativeRepairComposition.Subdivision.LinearCoefficients
open CategoryTheory TransportCoherence TransportCoherence.Arbitrary AbelianLiftingObstruction
universe uk uG uE uB uD vE vB vD
variable {k : Type uk} [Field k]
variable {K : FiniteTransportPresentation.{uG}}
variable {E : Type uE} {B : Type uB} {D : Type uD}
variable [Category.{vE} E] [Category.{vB} B] [Category.{vD} D]
variable {p : E ⥤ B} {q : B ⥤ D}
variable (T : OriginalTowerPresentation K p q) (chosen : EdgeName (K := K))
variable (F : Factorization T chosen)
variable [∀ v, Module k (T.toTower.localCoefficients.A v)]

/-- All original modules and the complete fresh kernel module come from the same first transport. -/
noncomputable def coefficientModules :
    ∀ v : (presentation K chosen).Vertex,
      Module k ((originalTower T chosen F).toTower.localCoefficients.A v)
  | .inl v => inferInstanceAs (Module k (T.toTower.localCoefficients.A v))
  | .inr _ => (rho1AddEquiv T chosen F).symm.module k

attribute [local instance] coefficientModules

/-- The entire actual first kernel equivalence is linear for the generated fresh module. -/
noncomputable def rho1LinearEquiv : T.toTower.localCoefficients.A chosen.1 ≃ₗ[k]
    (originalTower T chosen F).toTower.localCoefficients.A (.inr ()) where
  toAddEquiv := rho1AddEquiv T chosen F
  map_smul' t x := by
    change rho1AddEquiv T chosen F (t • x) =
      rho1AddEquiv T chosen F (t • (rho1AddEquiv T chosen F).symm (rho1AddEquiv T chosen F x))
    rw [AddEquiv.symm_apply_apply]

/-- Linear first transport has the unchanged full actual kernel value. -/
theorem rho1LinearEquiv_value (x : T.toTower.localCoefficients.A chosen.1) :
    rho1LinearEquiv (k := k) T chosen F x = rho1AddEquiv T chosen F x := rfl

/-- The actual first transport respects scalar multiplication on the whole generated kernel. -/
theorem rho1_smul (t : k) (x : T.toTower.localCoefficients.A chosen.1) :
    rho1AddEquiv T chosen F (t • x) = t • rho1AddEquiv T chosen F x :=
  (rho1LinearEquiv (k := k) T chosen F).map_smul t x

variable (hlinear : ∀ {i j : K.Vertex} (e : K.Edge i j) (t : k)
  (x : T.toTower.localCoefficients.A i),
  T.toTower.localCoefficients.edge e (t • x) = t • T.toTower.localCoefficients.edge e x)

include hlinear

/-- The second full actual transport is linear because its composite is the original transport. -/
theorem rho2_smul (t : k)
    (a : (originalTower T chosen F).toTower.localCoefficients.A (.inr ())) :
    rho2AddEquiv T chosen F (t • a) = t • rho2AddEquiv T chosen F a := by
  obtain ⟨x,rfl⟩ := (rho1AddEquiv T chosen F).surjective a
  have hs : rho1AddEquiv T chosen F (t • x) = t • rho1AddEquiv T chosen F x :=
    (rho1LinearEquiv (k := k) T chosen F).map_smul t x
  rw [← hs]
  change rho2AddEquiv T chosen F (rho1AddEquiv T chosen F (t • x)) =
    t • rho2AddEquiv T chosen F (rho1AddEquiv T chosen F x)
  rw [← coefficient_transport_comp,← coefficient_transport_comp,hlinear]

/-- Both generated full factor transports are linear without supplied preservation certificates. -/
noncomputable def rho2LinearEquiv :
    (originalTower T chosen F).toTower.localCoefficients.A (.inr ()) ≃ₗ[k]
      T.toTower.localCoefficients.A chosen.2.1 where
  toAddEquiv := rho2AddEquiv T chosen F
  map_smul' := rho2_smul T chosen F hlinear

/-- Linear second transport has the same actual full-kernel value. -/
theorem rho2LinearEquiv_value
    (a : (originalTower T chosen F).toTower.localCoefficients.A (.inr ())) :
    rho2LinearEquiv T chosen F hlinear a = rho2AddEquiv T chosen F a := rfl

/-- The same earlier additive second transport respects the generated full-kernel scalars. -/
theorem rho2Add_smul (t : k)
    (a : (originalTower T chosen F).toTower.localCoefficients.A (.inr ())) :
    rho2Add T chosen F (t • a) =
      (let b : T.toTower.localCoefficients.A chosen.2.1 := rho2Add T chosen F a
       t • b) := by
  simpa only [← rho2AddEquiv_value] using rho2_smul T chosen F hlinear t a

/-- Every retained edge and both factors have linear full actual kernel transport. -/
theorem edge_linear {i j : (presentation K chosen).Vertex}
    (e : (presentation K chosen).Edge i j) : ∀ (t : k)
      (x : (originalTower T chosen F).toTower.localCoefficients.A i),
      (originalTower T chosen F).toTower.localCoefficients.edge e (t • x) =
        t • (originalTower T chosen F).toTower.localCoefficients.edge e x := by
  apply edge_induction chosen _ _ _ _ e
  · intro f hf t x
    rw [coefficient_edge_old]
    exact hlinear f.2.2 t x
  · intro t x
    rw [coefficient_edge_first]
    exact (rho1LinearEquiv (k := k) T chosen F).map_smul t x
  · intro t x
    rw [coefficient_edge_second]
    exact rho2_smul T chosen F hlinear t x

end AAT.AG.RelativeRepairComposition.Subdivision.LinearCoefficients
#assert_standard_axioms_only AAT.AG.RelativeRepairComposition.Subdivision.LinearCoefficients
