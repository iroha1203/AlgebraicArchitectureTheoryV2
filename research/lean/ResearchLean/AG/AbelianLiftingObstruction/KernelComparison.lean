import ResearchLean.AG.AbelianLiftingObstruction.KernelTransport

/-!
# Kernel transport under reselection and face comparison

G-129 A: an actual endpoint comparison intertwines the two generated
transports. Kernel commutativity removes changes of lift over the same core.
Core alignment identifies the canonical and authored projections, so their
kernel-valued difference yields the authored face conjugacy law.
-/

namespace AAT.AG.AbelianLiftingObstruction

open CategoryTheory TransportCoherence.Arbitrary

universe uE uB uD vE vB vD
variable {E : Type uE} {B : Type uB} {D : Type uD}
variable [Category.{vE} E] [Category.{vB} B] [Category.{vD} D]

/-- API: a comparison of actual lifts intertwines their generated fiber transports. -/
theorem fiberTransport_comparison (r : E ⥤ B) {X Y : E}
    {σ : r.obj X ⟶ r.obj Y} (f g : X ⟶ Y)
    (hf : r.IsStronglyCocartesian σ f) (hg : r.IsStronglyCocartesian σ g)
    (m : FiberAut r Y) (hfg : f ≫ FiberAut.hom m = g) (a : FiberAut r X) :
    fiberTransportHom r g hg a * m = m * fiberTransportHom r f hf a := by
  apply FiberAut.ext_of_strong_fac f hf
  change f ≫ (FiberAut.hom m ≫ FiberAut.hom (fiberTransportHom r g hg a)) =
    f ≫ (FiberAut.hom (fiberTransportHom r f hf a) ≫ FiberAut.hom m)
  simp only [← Category.assoc]
  rw [hfg, fiberTransportHom_fac, fiberTransportHom_fac, Category.assoc, hfg]

section Tower

variable (p : E ⥤ B) (q : B ⥤ D) {X Y : E}
variable {σ : (p ⋙ q).obj X ⟶ (p ⋙ q).obj Y} (f g : X ⟶ Y)
variable (hf : (p ⋙ q).IsStronglyCocartesian σ f)
variable (hg : (p ⋙ q).IsStronglyCocartesian σ g)
variable (hpf : q.IsStronglyCocartesian σ (p.map f))
variable (hpg : q.IsStronglyCocartesian σ (p.map g))

/-- G-129 A: a kernel correction does not change kernel transport in the abelian case. -/
theorem kernelTransport_eq_of_kernel_comparison
    (hcomm : ∀ a b : Kernel p q Y, a * b = b * a)
    (d : Kernel p q Y) (hfg : f ≫ FiberAut.hom (kernelInclusion p q Y d) = g) :
    kernelTransportHom p q g hg hpg = kernelTransportHom p q f hf hpf := by
  apply MonoidHom.ext
  intro a
  apply kernelInclusion_injective p q Y
  apply mul_right_cancel (b := kernelInclusion p q Y d)
  have h := fiberTransport_comparison (p ⋙ q) f g hf hg
    (kernelInclusion p q Y d) hfg (kernelInclusion p q X a)
  change kernelInclusion p q Y (kernelTransportHom p q g hg hpg a) *
      kernelInclusion p q Y d = kernelInclusion p q Y d *
      kernelInclusion p q Y (kernelTransportHom p q f hf hpf a) at h
  rw [h]
  exact (map_mul (kernelInclusion p q Y) d _).symm.trans
    ((congrArg (kernelInclusion p q Y) (hcomm d _)).trans
      (map_mul (kernelInclusion p q Y) _ d))

include hpf in
/-- G-129 A/B: core alignment identifies the canonical and authored projections. -/
theorem canonical_comparison_pushforward (u : FiberAut (p ⋙ q) Y)
    (halign : p.map f ≫ p.map (FiberAut.hom u) = p.map g) :
    fiberPushforward p q Y (canonicalFiberComparator (p ⋙ q) σ f g hf hg) =
      fiberPushforward p q Y u := by
  apply FiberAut.ext_of_strong_fac (p.map f) hpf
  change p.map f ≫ p.map (FiberAut.hom (canonicalFiberComparator (p ⋙ q) σ f g hf hg)) =
    p.map f ≫ p.map (FiberAut.hom u)
  rw [← p.map_comp, canonicalFiberComparator_fac]
  exact halign.symm

/-- G-129 A/B: the actual authored defect is in the actual kernel before vanishing. -/
noncomputable def faceKernelDefect (u : FiberAut (p ⋙ q) Y)
    (halign : p.map f ≫ p.map (FiberAut.hom u) = p.map g) : Kernel p q Y :=
  liftDifference p q Y u (canonicalFiberComparator (p ⋙ q) σ f g hf hg)
    (canonical_comparison_pushforward p q f g hf hg hpf u halign).symm

/-- API: defect inclusion has the original noncommutative order `u * m⁻¹`. -/
theorem faceKernelDefect_inclusion (u : FiberAut (p ⋙ q) Y)
    (halign : p.map f ≫ p.map (FiberAut.hom u) = p.map g) :
    kernelInclusion p q Y (faceKernelDefect p q f g hf hg hpf u halign) =
      u * (canonicalFiberComparator (p ⋙ q) σ f g hf hg)⁻¹ := rfl

/-- G-129 A: abelian defect changes canonical intertwining to authored intertwining. -/
theorem kernelTransport_authored_intertwining
    (hcomm : ∀ a b : Kernel p q Y, a * b = b * a)
    (u : FiberAut (p ⋙ q) Y)
    (halign : p.map f ≫ p.map (FiberAut.hom u) = p.map g) (a : Kernel p q X) :
    kernelInclusion p q Y (kernelTransportHom p q g hg hpg a) * u =
      u * kernelInclusion p q Y (kernelTransportHom p q f hf hpf a) := by
  let m := canonicalFiberComparator (p ⋙ q) σ f g hf hg
  let d := faceKernelDefect p q f g hf hg hpf u halign
  let i := kernelInclusion p q Y
  let tf := kernelTransportHom p q f hf hpf a
  let tg := kernelTransportHom p q g hg hpg a
  have hd : i d * m = u := liftDifference_mul p q Y u m _
  have hc : i tg * i d = i d * i tg := by
    rw [← map_mul, ← map_mul, hcomm tg d]
  have ht : i tg * m = m * i tf :=
    fiberTransport_comparison (p ⋙ q) f g hf hg m
      (canonicalFiberComparator_fac (p ⋙ q) σ f g hf hg) a.1
  change i tg * u = u * i tf
  calc
    i tg * u = i tg * (i d * m) := by rw [hd]
    _ = (i tg * i d) * m := (mul_assoc _ _ _).symm
    _ = (i d * i tg) * m := by rw [hc]
    _ = i d * (i tg * m) := mul_assoc _ _ _
    _ = i d * (m * i tf) := by rw [ht]
    _ = (i d * m) * i tf := (mul_assoc _ _ _).symm
    _ = u * i tf := by rw [hd]

/-- G-129 A: the two face transports differ by authored conjugation on the same kernel. -/
theorem kernelTransport_face_conjugacy
    (hcomm : ∀ a b : Kernel p q Y, a * b = b * a)
    (u : FiberAut (p ⋙ q) Y)
    (halign : p.map f ≫ p.map (FiberAut.hom u) = p.map g) (a : Kernel p q X) :
    kernelInclusion p q Y (kernelTransportHom p q g hg hpg a) =
      u * kernelInclusion p q Y (kernelTransportHom p q f hf hpf a) * u⁻¹ := by
  have h := kernelTransport_authored_intertwining p q f g hf hg hpf hpg hcomm u halign a
  calc
    _ = (_ * u) * u⁻¹ := (mul_inv_cancel_right _ u).symm
    _ = _ := congrArg (fun x => x * u⁻¹) h

/-- G-129 A condition 3: centralization is exactly equality of face transports.
Surjectivity is the part of condition 2 used in the reverse implication. -/
theorem centralizes_iff_kernelTransport_eq
    (hcomm : ∀ a b : Kernel p q Y, a * b = b * a)
    (u : FiberAut (p ⋙ q) Y)
    (halign : p.map f ≫ p.map (FiberAut.hom u) = p.map g)
    (hsurj : Function.Surjective (kernelTransportHom p q f hf hpf)) :
    (∀ b : Kernel p q Y, u * kernelInclusion p q Y b = kernelInclusion p q Y b * u) ↔
      kernelTransportHom p q g hg hpg = kernelTransportHom p q f hf hpf := by
  constructor
  · intro hc
    apply MonoidHom.ext
    intro a
    apply kernelInclusion_injective p q Y
    apply mul_right_cancel (b := u)
    exact (kernelTransport_authored_intertwining p q f g hf hg hpf hpg
      hcomm u halign a).trans (hc _)
  · intro heq b
    obtain ⟨a, rfl⟩ := hsurj b
    have h := kernelTransport_authored_intertwining p q f g hf hg hpf hpg hcomm u halign a
    rw [heq] at h
    exact h.symm

end Tower

end AAT.AG.AbelianLiftingObstruction

#assert_standard_axioms_only AAT.AG.AbelianLiftingObstruction
