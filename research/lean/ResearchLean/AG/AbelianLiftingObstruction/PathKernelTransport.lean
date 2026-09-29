import ResearchLean.AG.AbelianLiftingObstruction.Cohomology

/-!
# Actual kernel transport along the original finite paths

G-129 A: strong transport of the actual kernel composes along the original
arrows. This identifies recursive local-coefficient transport with the unique
strongly cocartesian transport of each evaluated path.
-/

namespace AAT.AG.AbelianLiftingObstruction

open CategoryTheory TransportCoherence TransportCoherence.Arbitrary

universe uG uE uB uD vE vB vD

variable {E : Type uE} {B : Type uB} {D : Type uD}
variable [Category.{vE} E] [Category.{vB} B] [Category.{vD} D]

/-- API: the generated kernel transport of a composite is the composite of generated transports. -/
theorem kernelTransportHom_comp (p : E ⥤ B) (q : B ⥤ D)
    {X Y Z : E} {σ : (p ⋙ q).obj X ⟶ (p ⋙ q).obj Y}
    {τ : (p ⋙ q).obj Y ⟶ (p ⋙ q).obj Z}
    (f : X ⟶ Y) (g : Y ⟶ Z)
    (hf : (p ⋙ q).IsStronglyCocartesian σ f)
    (hg : (p ⋙ q).IsStronglyCocartesian τ g)
    (hpf : q.IsStronglyCocartesian σ (p.map f))
    (hpg : q.IsStronglyCocartesian τ (p.map g)) :
    kernelTransportHom p q (f ≫ g)
      (by letI : (p ⋙ q).IsStronglyCocartesian σ f := hf
          letI : (p ⋙ q).IsStronglyCocartesian τ g := hg
          exact (Functor.IsStronglyCocartesian.comp (p ⋙ q) :
            (p ⋙ q).IsStronglyCocartesian (σ ≫ τ) (f ≫ g)))
      (by letI := hpf; letI := hpg
          simpa only [p.map_comp] using
            (Functor.IsStronglyCocartesian.comp q :
              q.IsStronglyCocartesian (σ ≫ τ) (p.map f ≫ p.map g))) =
      (kernelTransportHom p q g hg hpg).comp (kernelTransportHom p q f hf hpf) := by
  apply MonoidHom.ext
  intro a
  symm
  apply kernelTransportHom_unique
  calc
    (f ≫ g) ≫ FiberAut.hom (kernelInclusion p q Z
        (kernelTransportHom p q g hg hpg (kernelTransportHom p q f hf hpf a))) =
        f ≫ (g ≫ FiberAut.hom (kernelInclusion p q Z
          (kernelTransportHom p q g hg hpg (kernelTransportHom p q f hf hpf a)))) :=
          Category.assoc _ _ _
    _ = f ≫ (FiberAut.hom (kernelInclusion p q Y
          (kernelTransportHom p q f hf hpf a)) ≫ g) := by
          rw [kernelTransportHom_fac]
    _ = (f ≫ FiberAut.hom (kernelInclusion p q Y
          (kernelTransportHom p q f hf hpf a))) ≫ g := (Category.assoc _ _ _).symm
    _ = (FiberAut.hom (kernelInclusion p q X a) ≫ f) ≫ g := by
          rw [kernelTransportHom_fac]
    _ = FiberAut.hom (kernelInclusion p q X a) ≫ (f ≫ g) := Category.assoc _ _ _

end AAT.AG.AbelianLiftingObstruction

#assert_standard_axioms_only AAT.AG.AbelianLiftingObstruction
