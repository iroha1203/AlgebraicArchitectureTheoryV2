import ResearchLean.AG.TransportCoherence.ArbitraryFinitePresentation

/-!
# Actual kernels of a tower

G-129 (A1): the projection is induced by the given functor on the same
automorphisms. Its kernel is compared with the fiber group of that functor.

## Implementation notes

The kernel is `MonoidHom.ker`, with its inherited multiplication. No abstract
extension or commutativity certificate replaces the actual projection.
All constructions work before imposing the abelian-kernel hypothesis.
-/

namespace AAT.AG.AbelianLiftingObstruction

open CategoryTheory TransportCoherence.Arbitrary

universe uE uB uD vE vB vD

variable {E : Type uE} {B : Type uB} {D : Type uD}
variable [Category.{vE} E] [Category.{vB} B] [Category.{vD} D]

/-- G-129 (A1): the actual projection on composite-fiber automorphisms. -/
def fiberPushforward (p : E ⥤ B) (q : B ⥤ D) (X : E) :
    FiberAut (p ⋙ q) X →* FiberAut q (p.obj X) where
  toFun a := ⟨p.mapIso a.1, a.2⟩
  map_one' := by apply Subtype.ext; apply Iso.ext; exact p.map_id X
  map_mul' a b := by apply Subtype.ext; apply Iso.ext; exact p.map_comp _ _

/-- API: projection retains the original forward arrow under `p`. -/
@[simp] theorem fiberPushforward_hom (p : E ⥤ B) (q : B ⥤ D) (X : E)
    (a : FiberAut (p ⋙ q) X) :
    FiberAut.hom (fiberPushforward p q X a) = p.map (FiberAut.hom a) := rfl

/-- API: trivial pushforward means that the original arrow is `p`-vertical. -/
theorem fiberPushforward_eq_one_iff (p : E ⥤ B) (q : B ⥤ D) (X : E)
    (a : FiberAut (p ⋙ q) X) :
    fiberPushforward p q X a = 1 ↔ p.map (FiberAut.hom a) = 𝟙 (p.obj X) := by
  constructor
  · intro h
    exact congrArg FiberAut.hom h
  · intro h
    apply Subtype.ext
    exact Iso.ext h

/-- G-129 (A1): coefficients before additivization, as the actual kernel. -/
abbrev Kernel (p : E ⥤ B) (q : B ⥤ D) (X : E) :=
  (fiberPushforward p q X).ker

/-- API: inclusion of the actual kernel into the composite-fiber group. -/
def kernelInclusion (p : E ⥤ B) (q : B ⥤ D) (X : E) :
    Kernel p q X →* FiberAut (p ⋙ q) X := (fiberPushforward p q X).ker.subtype

/-- API: the inclusion is injective, with no finiteness hypothesis. -/
theorem kernelInclusion_injective (p : E ⥤ B) (q : B ⥤ D) (X : E) :
    Function.Injective (kernelInclusion p q X) := Subtype.val_injective

/-- API: every included kernel element is vertical for the first projection. -/
@[simp] theorem kernelInclusion_map (p : E ⥤ B) (q : B ⥤ D) (X : E)
    (a : Kernel p q X) :
    p.map (FiberAut.hom (kernelInclusion p q X a)) = 𝟙 (p.obj X) :=
  (fiberPushforward_eq_one_iff p q X a.1).mp a.2

/-- G-129 A/D: the actual kernel is the first functor's fiber group.
Both directions keep the complete original automorphism. -/
def kernelEquivFiberAut (p : E ⥤ B) (q : B ⥤ D) (X : E) :
    Kernel p q X ≃* FiberAut p X where
  toFun a := ⟨a.1.1, kernelInclusion_map p q X a⟩
  invFun a := ⟨⟨a.1, by
      change q.map (p.map a.1.hom) = 𝟙 _
      rw [a.2, q.map_id]⟩,
    (fiberPushforward_eq_one_iff p q X _).mpr a.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl

/-- API: the kernel/fiber comparison preserves forward arrows literally. -/
@[simp] theorem kernelEquivFiberAut_hom (p : E ⥤ B) (q : B ⥤ D) (X : E)
    (a : Kernel p q X) :
    FiberAut.hom (kernelEquivFiberAut p q X a) =
      FiberAut.hom (kernelInclusion p q X a) := rfl

/-- API: the kernel/fiber comparison preserves inverse arrows literally. -/
@[simp] theorem kernelEquivFiberAut_inv (p : E ⥤ B) (q : B ⥤ D) (X : E)
    (a : Kernel p q X) :
    FiberAut.inv (kernelEquivFiberAut p q X a) =
      FiberAut.inv (kernelInclusion p q X a) := rfl

/-- G-129 A: two lifts of the same core element differ by the actual kernel. -/
def liftDifference (p : E ⥤ B) (q : B ⥤ D) (X : E)
    (a b : FiberAut (p ⋙ q) X)
    (h : fiberPushforward p q X a = fiberPushforward p q X b) : Kernel p q X :=
  ⟨a * b⁻¹, by change fiberPushforward p q X (a * b⁻¹) = 1
               rw [map_mul, map_inv, h, mul_inv_cancel]⟩

/-- API: multiplying the difference by the old lift recovers the new lift. -/
theorem liftDifference_mul (p : E ⥤ B) (q : B ⥤ D) (X : E)
    (a b : FiberAut (p ⋙ q) X)
    (h : fiberPushforward p q X a = fiberPushforward p q X b) :
    kernelInclusion p q X (liftDifference p q X a b h) * b = a := by
  exact inv_mul_cancel_right a b

end AAT.AG.AbelianLiftingObstruction

#assert_standard_axioms_only AAT.AG.AbelianLiftingObstruction
