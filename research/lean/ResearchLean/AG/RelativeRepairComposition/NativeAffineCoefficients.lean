import ResearchLean.AG.RelativeRepairComposition.NativeAffineTower
import Mathlib.Algebra.Module.TransferInstance

/-! # Whole native kernel coordinates and the original linear transport -/
namespace AAT.AG.RelativeRepairComposition.NativeAffine
open CategoryTheory TransportCoherence TransportCoherence.Arbitrary AbelianLiftingObstruction
universe uk uA uG
variable {k : Type uk} [Field k] {A : Type uA} [AddCommGroup A] [Module k A]
variable (K : FiniteTransportPresentation.{uG})
variable (L R : ∀ {i j : K.Vertex}, K.Edge i j → Operations k A)
variable (c : K.TwoCell → A)
variable (hfaces : ∀ f : K.TwoCell,
  (GroupExtension.pathValue K R (K.twoLeft f)).linear =
    (GroupExtension.pathValue K R (K.twoRight f)).linear)
local notation "π" => projection (k := k) (A := A)
local notation "M" => TowerPresentation.localCoefficients
  (OriginalTowerPresentation.toTower (tower K L R c hfaces))

/-- Every original native coefficient is precisely a vector in the whole translation space. -/
noncomputable def coefficient (v : K.Vertex) : (M).A v ≃+ A :=
  ((GroupExtension.kernelEquiv π).symm.trans (kernelEquiv (k := k) (A := A))).toAdditive

/-- Scalar multiplication is transported on the whole actual native kernel. -/
noncomputable instance coefficientModule (v : K.Vertex) : Module k ((M).A v) :=
  (coefficient K L R c hfaces v).module k

/-- The whole kernel coordinate comparison is linear for the generated module. -/
noncomputable def linearCoefficient (v : K.Vertex) : (M).A v ≃ₗ[k] A where
  toAddEquiv := coefficient K L R c hfaces v
  map_smul' t x := (coefficient K L R c hfaces v).apply_symm_apply
    (t • coefficient K L R c hfaces v x)

/-- Reconstructing a coefficient gives the same original affine translation operation. -/
theorem coefficient_inverse_value (v : K.Vertex) (a : A) :
    FiberAut.hom (kernelInclusion (GroupExtension.projection π)
      (GroupExtension.terminal (A ≃ₗ[k] A)) ((tower K L R c hfaces).original.object v)
      (Additive.toMul ((coefficient K L R c hfaces v).symm a))) =
        translation (k := k) a := rfl

/-- Including any full original coefficient evaluates its coordinate translation. -/
theorem coefficient_inclusion (v : K.Vertex) (x : (M).A v) :
    FiberAut.hom (kernelInclusion (GroupExtension.projection π)
      (GroupExtension.terminal (A ≃ₗ[k] A)) ((tower K L R c hfaces).original.object v) (Additive.toMul x)) =
        translation (k := k) (coefficient K L R c hfaces v x) := by
  have h := coefficient_inverse_value K L R c hfaces v (coefficient K L R c hfaces v x)
  rw [AddEquiv.symm_apply_apply] at h
  exact h

/-- The generated real kernel transport is exactly the original reference linear component. -/
theorem edge_coefficient {i j : K.Vertex} (e : K.Edge i j) (x : (M).A i) :
    coefficient K L R c hfaces j ((M).edge e x) =
      (R e).linear (coefficient K L R c hfaces i x) := by
  have ht := GroupExtension.transport_hom π (R e) (Additive.toMul x)
  have he : FiberAut.hom (kernelInclusion (GroupExtension.projection π)
      (GroupExtension.terminal (A ≃ₗ[k] A)) ((tower K L R c hfaces).original.object j)
      (Additive.toMul ((M).edge e x))) =
    R e * FiberAut.hom (kernelInclusion (GroupExtension.projection π)
      (GroupExtension.terminal (A ≃ₗ[k] A)) ((tower K L R c hfaces).original.object i) (Additive.toMul x)) * (R e)⁻¹ := by
    change FiberAut.hom (kernelInclusion (GroupExtension.projection π)
      (GroupExtension.terminal (A ≃ₗ[k] A)) _
      (kernelTransportHom (GroupExtension.projection π)
        (GroupExtension.terminal (A ≃ₗ[k] A))
        ((tower K L R c hfaces).toTower.upper.edgeLift e)
        ((tower K L R c hfaces).toTower.upper.edgeStrong e)
        ((tower K L R c hfaces).toTower.lowerStrong e) (Additive.toMul x))) = _
    simpa only [tower_reference_edge] using ht
  rw [coefficient_inclusion, coefficient_inclusion, conjugation_translation] at he
  have hh := congrArg (fun g : Operations k A => g 0) he
  simpa using hh

/-- All original kernel transports are linear on the full generated native modules. -/
theorem edge_linear {i j : K.Vertex} (e : K.Edge i j) (t : k) (x : (M).A i) :
    (M).edge e (t • x) = t • (M).edge e x := by
  apply (linearCoefficient K L R c hfaces j).injective
  change coefficient K L R c hfaces j ((M).edge e (t • x)) =
    coefficient K L R c hfaces j (t • (M).edge e x)
  have hs0 := (linearCoefficient K L R c hfaces i).map_smul t x
  have hs1 := (linearCoefficient K L R c hfaces j).map_smul t ((M).edge e x)
  change coefficient K L R c hfaces i (t • x) =
    t • coefficient K L R c hfaces i x at hs0
  change coefficient K L R c hfaces j (t • (M).edge e x) =
    t • coefficient K L R c hfaces j ((M).edge e x) at hs1
  rw [edge_coefficient, hs0, hs1, edge_coefficient, map_smul]

end AAT.AG.RelativeRepairComposition.NativeAffine
#assert_standard_axioms_only AAT.AG.RelativeRepairComposition
