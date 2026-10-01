import ResearchLean.AG.RelativeRepairComposition.SubdivisionGeometry
import ResearchLean.AG.AbelianLiftingObstruction.OriginalTowerPresentation

/-!
# Actual two-factor data and transport from the same original tower

The only new input is an intermediate object and its actual two strong factors,
with bijective full kernel transports and product the selected old reference.

## Implementation notes

The record contains primitive arrows and the input conditions allowed by GOAL E.
It contains no repair, equivalent category, complex decomposition or vanishing
field. An additional commutativity assumption at the new object was rejected:
surjectivity of the first actual kernel transport derives it from the old full
kernel. Composition is proved by the actual transport squares and uniqueness,
so the collapse formula retains the original categorical operations.
-/
namespace AAT.AG.RelativeRepairComposition.Subdivision
open CategoryTheory TransportCoherence TransportCoherence.Arbitrary AbelianLiftingObstruction
universe uG uE uB uD vE vB vD
variable {K : FiniteTransportPresentation.{uG}}
variable {E : Type uE} {B : Type uB} {D : Type uD}
variable [Category.{vE} E] [Category.{vB} B] [Category.{vD} D]
variable {p : E ⥤ B} {q : B ⥤ D}

/-- A specified actual subdivision inside the same original tower, before any repair is chosen. -/
structure Factorization (T : OriginalTowerPresentation K p q) (chosen : EdgeName (K := K)) where
  /-- The actual intermediate object at the new vertex. -/
  middle : E
  /-- The first actual reference factor starts at the original selected source. -/
  first : T.original.object chosen.1 ⟶ middle
  /-- The second actual reference factor ends at the original selected target. -/
  second : middle ⟶ T.original.object chosen.2.1
  /-- Their actual categorical composite is the old selected reference, not the old original edge. -/
  composite : first ≫ second = T.toTower.upper.edgeLift chosen.2.2
  /-- The first actual factor is strongly cocartesian for the whole projection. -/
  firstStrong : (p ⋙ q).IsStronglyCocartesian ((p ⋙ q).map first) first
  /-- The second actual factor is strongly cocartesian for the whole projection. -/
  secondStrong : (p ⋙ q).IsStronglyCocartesian ((p ⋙ q).map second) second
  /-- Its first projected actual factor is strongly cocartesian for the lower projection. -/
  firstLowerStrong : q.IsStronglyCocartesian ((p ⋙ q).map first) (p.map first)
  /-- Its second projected actual factor is strongly cocartesian for the lower projection. -/
  secondLowerStrong : q.IsStronglyCocartesian ((p ⋙ q).map second) (p.map second)
  /-- The first generated transport uses the full actual kernel and is bijective. -/
  firstBijective : Function.Bijective (kernelTransportHom p q first firstStrong firstLowerStrong)
  /-- The second generated transport uses the full actual kernel and is bijective. -/
  secondBijective : Function.Bijective (kernelTransportHom p q second secondStrong secondLowerStrong)

variable (T : OriginalTowerPresentation K p q) (chosen : EdgeName (K := K))
variable (F : Factorization T chosen)

/-- The actual first-factor transport on the entire original source kernel. -/
noncomputable def rho1 : Kernel p q (T.original.object chosen.1) →* Kernel p q F.middle :=
  kernelTransportHom p q F.first F.firstStrong F.firstLowerStrong

/-- The actual second-factor transport on the entire new-object kernel. -/
noncomputable def rho2 : Kernel p q F.middle →* Kernel p q (T.original.object chosen.2.1) :=
  kernelTransportHom p q F.second F.secondStrong F.secondLowerStrong

/-- The new actual kernel is commutative because the first actual transport is surjective. -/
theorem middle_kernel_comm (a b : Kernel p q F.middle) : a * b = b * a := by
  obtain ⟨x,rfl⟩ := F.firstBijective.2 a
  obtain ⟨y,rfl⟩ := F.firstBijective.2 b
  rw [← map_mul,← map_mul,T.kernelComm chosen.1 x y]

/-- The original full kernel transport is exactly the composite of the two actual factor transports. -/
theorem transport_comp :
    kernelTransportHom p q (T.toTower.upper.edgeLift chosen.2.2)
      (T.toTower.upper.edgeStrong chosen.2.2) (T.toTower.lowerStrong chosen.2.2) =
        (rho2 T chosen F).comp (rho1 T chosen F) := by
  apply MonoidHom.ext
  intro a
  symm
  apply kernelTransportHom_unique
  change T.toTower.upper.edgeLift chosen.2.2 ≫
    FiberAut.hom (kernelInclusion p q _ ((rho2 T chosen F) ((rho1 T chosen F) a))) = _
  rw [← F.composite]
  calc
    (F.first ≫ F.second) ≫ FiberAut.hom (kernelInclusion p q _
        ((rho2 T chosen F) ((rho1 T chosen F) a))) =
      F.first ≫ (F.second ≫ FiberAut.hom (kernelInclusion p q _
        ((rho2 T chosen F) ((rho1 T chosen F) a)))) := Category.assoc _ _ _
    _ = F.first ≫ (FiberAut.hom (kernelInclusion p q _ ((rho1 T chosen F) a)) ≫ F.second) := by
      rw [rho2,kernelTransportHom_fac]
    _ = (F.first ≫ FiberAut.hom (kernelInclusion p q _ ((rho1 T chosen F) a))) ≫ F.second :=
      (Category.assoc _ _ _).symm
    _ = (FiberAut.hom (kernelInclusion p q _ a) ≫ F.first) ≫ F.second := by
      rw [rho1,kernelTransportHom_fac]
      rfl
    _ = FiberAut.hom (kernelInclusion p q _ a) ≫ (F.first ≫ F.second) := Category.assoc _ _ _

/-- Actual corrected factors collapse to their composite reference with the full transported kernel correction. -/
theorem corrected_factor_product (a : Kernel p q F.middle)
    (b : Kernel p q (T.original.object chosen.2.1)) :
    (F.first ≫ FiberAut.hom (kernelInclusion p q _ a)) ≫
      (F.second ≫ FiberAut.hom (kernelInclusion p q _ b)) =
      T.toTower.upper.edgeLift chosen.2.2 ≫
        FiberAut.hom (kernelInclusion p q _ (b * (rho2 T chosen F) a)) := by
  rw [← F.composite,map_mul]
  change (F.first ≫ FiberAut.hom (kernelInclusion p q _ a)) ≫
      (F.second ≫ FiberAut.hom (kernelInclusion p q _ b)) =
    (F.first ≫ F.second) ≫
      (FiberAut.hom (kernelInclusion p q _ ((rho2 T chosen F) a)) ≫
        FiberAut.hom (kernelInclusion p q _ b))
  rw [← Category.assoc (F.first ≫ F.second)]
  rw [Category.assoc F.first F.second, rho2, kernelTransportHom_fac]
  simp only [Category.assoc]

end AAT.AG.RelativeRepairComposition.Subdivision
#assert_standard_axioms_only AAT.AG.RelativeRepairComposition.Subdivision
