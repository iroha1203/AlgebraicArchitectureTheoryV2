import ResearchLean.AG.AbelianLiftingObstruction.Tower
import ResearchLean.AG.AbelianLiftingObstruction.StrongTransport

/-!
# Transport on the actual kernel

G-129 A: applying the first projection to the defining factorization and using
lower-stage strong uniqueness yields the projection square. Its restriction
constructs the kernel homomorphism; only bijectivity is retained as hypothesis.
-/

namespace AAT.AG.AbelianLiftingObstruction

open CategoryTheory TransportCoherence.Arbitrary

universe uE uB uD vE vB vD
variable {E : Type uE} {B : Type uB} {D : Type uD}
variable [Category.{vE} E] [Category.{vB} B] [Category.{vD} D]

/-- G-129 A: the actual strong transport commutes with the actual projection. -/
theorem fiberPushforward_transport (p : E ⥤ B) (q : B ⥤ D) {X Y : E}
    {σ : (p ⋙ q).obj X ⟶ (p ⋙ q).obj Y} (f : X ⟶ Y)
    (hf : (p ⋙ q).IsStronglyCocartesian σ f)
    (hpf : q.IsStronglyCocartesian σ (p.map f)) (a : FiberAut (p ⋙ q) X) :
    fiberPushforward p q Y (fiberTransportHom (p ⋙ q) f hf a) =
      fiberTransportHom q (p.map f) hpf (fiberPushforward p q X a) := by
  apply FiberAut.ext_of_strong_fac (p.map f) hpf
  change p.map f ≫ p.map (FiberAut.hom (fiberTransportHom (p ⋙ q) f hf a)) = _
  rw [← p.map_comp, fiberTransportHom_fac, p.map_comp, fiberTransportHom_fac]
  rfl

/-- G-129 A: restrict the generated homomorphism to the actual kernel. -/
noncomputable def kernelTransportHom (p : E ⥤ B) (q : B ⥤ D) {X Y : E}
    {σ : (p ⋙ q).obj X ⟶ (p ⋙ q).obj Y} (f : X ⟶ Y)
    (hf : (p ⋙ q).IsStronglyCocartesian σ f)
    (hpf : q.IsStronglyCocartesian σ (p.map f)) : Kernel p q X →* Kernel p q Y where
  toFun a := ⟨fiberTransportHom (p ⋙ q) f hf a.1, by
    change fiberPushforward p q Y (fiberTransportHom (p ⋙ q) f hf a.1) = 1
    rw [fiberPushforward_transport p q f hf hpf, a.2, map_one]⟩
  map_one' := Subtype.ext (map_one (fiberTransportHom (p ⋙ q) f hf))
  map_mul' a b := Subtype.ext (map_mul (fiberTransportHom (p ⋙ q) f hf) a.1 b.1)

/-- API: inclusion recovers the original fiber transport homomorphism. -/
@[simp] theorem kernelTransportHom_inclusion (p : E ⥤ B) (q : B ⥤ D) {X Y : E}
    {σ : (p ⋙ q).obj X ⟶ (p ⋙ q).obj Y} (f : X ⟶ Y)
    (hf : (p ⋙ q).IsStronglyCocartesian σ f)
    (hpf : q.IsStronglyCocartesian σ (p.map f)) (a : Kernel p q X) :
    kernelInclusion p q Y (kernelTransportHom p q f hf hpf a) =
      fiberTransportHom (p ⋙ q) f hf (kernelInclusion p q X a) := rfl

/-- G-129 A: the kernel transport satisfies the original arrow factorization. -/
theorem kernelTransportHom_fac (p : E ⥤ B) (q : B ⥤ D) {X Y : E}
    {σ : (p ⋙ q).obj X ⟶ (p ⋙ q).obj Y} (f : X ⟶ Y)
    (hf : (p ⋙ q).IsStronglyCocartesian σ f)
    (hpf : q.IsStronglyCocartesian σ (p.map f)) (a : Kernel p q X) :
    f ≫ FiberAut.hom (kernelInclusion p q Y (kernelTransportHom p q f hf hpf a)) =
      FiberAut.hom (kernelInclusion p q X a) ≫ f :=
  fiberTransportHom_fac (p ⋙ q) f hf a.1

/-- API: the same factorization uniquely determines the actual kernel element. -/
theorem kernelTransportHom_unique (p : E ⥤ B) (q : B ⥤ D) {X Y : E}
    {σ : (p ⋙ q).obj X ⟶ (p ⋙ q).obj Y} (f : X ⟶ Y)
    (hf : (p ⋙ q).IsStronglyCocartesian σ f)
    (hpf : q.IsStronglyCocartesian σ (p.map f)) (a : Kernel p q X) (b : Kernel p q Y)
    (h : f ≫ FiberAut.hom (kernelInclusion p q Y b) =
      FiberAut.hom (kernelInclusion p q X a) ≫ f) : b = kernelTransportHom p q f hf hpf a := by
  apply kernelInclusion_injective p q Y
  exact fiberTransport_unique (p ⋙ q) f hf a.1 b.1 h

/-- G-129 A condition 2: bijectivity upgrades the constructed map to an equivalence. -/
noncomputable def kernelTransportEquiv (p : E ⥤ B) (q : B ⥤ D) {X Y : E}
    {σ : (p ⋙ q).obj X ⟶ (p ⋙ q).obj Y} (f : X ⟶ Y)
    (hf : (p ⋙ q).IsStronglyCocartesian σ f)
    (hpf : q.IsStronglyCocartesian σ (p.map f))
    (hbij : Function.Bijective (kernelTransportHom p q f hf hpf)) :
    Kernel p q X ≃* Kernel p q Y :=
  MulEquiv.ofBijective (kernelTransportHom p q f hf hpf) hbij

/-- API: the equivalence still evaluates to the generated kernel transport. -/
@[simp] theorem kernelTransportEquiv_apply (p : E ⥤ B) (q : B ⥤ D) {X Y : E}
    {σ : (p ⋙ q).obj X ⟶ (p ⋙ q).obj Y} (f : X ⟶ Y)
    (hf : (p ⋙ q).IsStronglyCocartesian σ f)
    (hpf : q.IsStronglyCocartesian σ (p.map f))
    (hbij : Function.Bijective (kernelTransportHom p q f hf hpf)) (a : Kernel p q X) :
    kernelTransportEquiv p q f hf hpf hbij a = kernelTransportHom p q f hf hpf a := rfl

end AAT.AG.AbelianLiftingObstruction

#assert_standard_axioms_only AAT.AG.AbelianLiftingObstruction
