import ResearchLean.AG.AbelianLiftingObstruction.KernelComparison
import Mathlib.Algebra.Group.Equiv.TypeTags

/-!
# Identity, additive transport, and independence of the chosen edge lift

G-129 A: the derived maps are exposed on the additive coefficient type.
The reselection theorem compares lifts of the same core value on the same
original edge. The identity calculation discharges bijectivity in the
concrete geometry input's identity-edge specialization.
-/

namespace AAT.AG.AbelianLiftingObstruction

open CategoryTheory TransportCoherence.Arbitrary

universe uE uB uD vE vB vD
variable {E : Type uE} {B : Type uB} {D : Type uD}
variable [Category.{vE} E] [Category.{vB} B] [Category.{vD} D]

/-- API: identity arrows have their strong lifting property without any input premise. -/
theorem identityStrong (r : E ⥤ B) (X : E) :
    r.IsStronglyCocartesian (𝟙 (r.obj X)) (𝟙 X) := by
  letI : r.IsHomLift (𝟙 (r.obj X)) (Iso.refl X).hom := CategoryTheory.IsHomLift.id rfl
  exact Functor.IsStronglyCocartesian.of_iso r (𝟙 (r.obj X)) (Iso.refl X)

/-- G-129 A / concrete geometry input: identity transport is the identity on the whole kernel. -/
theorem kernelTransport_identity (p : E ⥤ B) (q : B ⥤ D) (X : E) :
    kernelTransportHom p q (𝟙 X) (identityStrong (p ⋙ q) X)
      (by simpa only [p.map_id] using identityStrong q (p.obj X)) =
      MonoidHom.id (Kernel p q X) := by
  apply MonoidHom.ext
  intro a
  symm
  apply kernelTransportHom_unique
  simp

/-- G-129 A condition 1: install commutativity on the inherited actual kernel group. -/
def kernelCommGroup (p : E ⥤ B) (q : B ⥤ D) (X : E)
    (hcomm : ∀ a b : Kernel p q X, a * b = b * a) : CommGroup (Kernel p q X) :=
  { inferInstanceAs (Group (Kernel p q X)) with mul_comm := hcomm }

/-- G-129 (A1): the additive coefficient type is exactly the actual multiplicative kernel. -/
abbrev KernelCoefficient (p : E ⥤ B) (q : B ⥤ D) (X : E) := Additive (Kernel p q X)

/-- G-129 A: additivize the constructed transport equivalence using the native type tag. -/
noncomputable def kernelTransportAddEquiv (p : E ⥤ B) (q : B ⥤ D) {X Y : E}
    {σ : (p ⋙ q).obj X ⟶ (p ⋙ q).obj Y} (f : X ⟶ Y)
    (hf : (p ⋙ q).IsStronglyCocartesian σ f)
    (hpf : q.IsStronglyCocartesian σ (p.map f))
    (hbij : Function.Bijective (kernelTransportHom p q f hf hpf)) :
    KernelCoefficient p q X ≃+ KernelCoefficient p q Y :=
  (kernelTransportEquiv p q f hf hpf hbij).toAdditive

/-- API: additivization does not alter the actual transported kernel element. -/
@[simp] theorem kernelTransportAddEquiv_apply (p : E ⥤ B) (q : B ⥤ D) {X Y : E}
    {σ : (p ⋙ q).obj X ⟶ (p ⋙ q).obj Y} (f : X ⟶ Y)
    (hf : (p ⋙ q).IsStronglyCocartesian σ f)
    (hpf : q.IsStronglyCocartesian σ (p.map f))
    (hbij : Function.Bijective (kernelTransportHom p q f hf hpf)) (a : Kernel p q X) :
    kernelTransportAddEquiv p q f hf hpf hbij (Additive.ofMul a) =
      Additive.ofMul (kernelTransportHom p q f hf hpf a) := rfl

/-- G-129 A: lifts of the same core value on the same original edge give identical transport. -/
theorem kernelTransport_independent_lift (p : E ⥤ B) (q : B ⥤ D) {X Y : E}
    {σ : (p ⋙ q).obj X ⟶ (p ⋙ q).obj Y} (L : X ⟶ Y)
    (a b : FiberAut (p ⋙ q) Y)
    (hcore : fiberPushforward p q Y a = fiberPushforward p q Y b)
    (ha : (p ⋙ q).IsStronglyCocartesian σ (L ≫ FiberAut.hom a))
    (hb : (p ⋙ q).IsStronglyCocartesian σ (L ≫ FiberAut.hom b))
    (hpa : q.IsStronglyCocartesian σ (p.map (L ≫ FiberAut.hom a)))
    (hpb : q.IsStronglyCocartesian σ (p.map (L ≫ FiberAut.hom b)))
    (hcomm : ∀ x y : Kernel p q Y, x * y = y * x) :
    kernelTransportHom p q (L ≫ FiberAut.hom a) ha hpa =
      kernelTransportHom p q (L ≫ FiberAut.hom b) hb hpb := by
  let d := liftDifference p q Y a b hcore
  apply kernelTransport_eq_of_kernel_comparison p q (L ≫ FiberAut.hom b)
    (L ≫ FiberAut.hom a) hb ha hpb hpa hcomm d
  rw [Category.assoc]
  exact congrArg (fun k => L ≫ k)
    (congrArg FiberAut.hom (liftDifference_mul p q Y a b hcore))

end AAT.AG.AbelianLiftingObstruction

#assert_standard_axioms_only AAT.AG.AbelianLiftingObstruction
