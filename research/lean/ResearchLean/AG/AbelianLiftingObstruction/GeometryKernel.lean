import ResearchLean.AG.AbelianLiftingObstruction.GeometryInput
import ResearchLean.AG.AbelianLiftingObstruction.PairCoefficients

/-!
# Commutativity of the entire concrete geometry kernel

G-129 completion condition 4: all three realization comparisons are forced to
be identity by the selected point-probe restrictions. Coefficients therefore
detect the full actual `InnerFiberAut`, and commutativity of integral-pair ring
automorphisms implies commutativity of the entire kernel.

## Implementation notes

The proof first treats arbitrary geometry morphisms over the identity core.
It then applies that result to the actual kernel, retaining all components in
`GeomReadHom.ext` and `GeometryTotalHom.ext`. The coefficient-swap witness is
in this same kernel. No commutativity or faithfulness premise is supplied.
-/

namespace AAT.AG.AbelianLiftingObstruction.GeometryKernel

open CategoryTheory AtomFoundation GeometryTransport CrossStageCoherence
open GeometryInput

/-- API: over the identity core, support naturality fixes every component. -/
theorem support_eq_id (F : GeomReadHom package package (PackageTotalHom.id core))
    (W : package.site.category) (x : W.ctx.Support) : F.supportComp W x = x :=
  PointedContexts.support_family_eq_id F.supportComp
    (fun w x => F.support_naturality w x) W x

/-- API: over the identity core, axis naturality fixes every component. -/
theorem axis_eq_id (F : GeomReadHom package package (PackageTotalHom.id core))
    (W : package.site.category) (x : W.ctx.Axis) : F.axisComp W x = x :=
  PointedContexts.axis_family_eq_id F.axisComp
    (fun w x => F.axis_naturality w x) W x

/-- API: over the identity core, observable naturality fixes every component. -/
theorem observable_eq_id (F : GeomReadHom package package (PackageTotalHom.id core))
    (W : package.site.category) (x : W.ctx.Observable) : F.observableComp W x = x :=
  PointedContexts.observable_family_eq_id F.observableComp
    (fun w x => F.observable_naturality w x) W x

/-- G-129 concrete input: coefficients detect every geometry component over identity. -/
theorem geometry_ext {F T : GeomReadHom package package (PackageTotalHom.id core)}
    (h : F.coefficientHom = T.coefficientHom) : F = T := by
  apply GeomReadHom.ext h
  · apply heq_of_eq
    funext W x
    rw [support_eq_id, support_eq_id]
  · apply heq_of_eq
    funext W x
    rw [axis_eq_id, axis_eq_id]
  · apply heq_of_eq
    funext W x
    rw [observable_eq_id, observable_eq_id]

/-- API: the coefficient comparison also detects dependent total morphisms. -/
theorem vertical_geometry_heq
    {f g : PackageTotalHom package.core package.core}
    (F : GeomReadHom package package f) (T : GeomReadHom package package g)
    (hf : f = 𝟙 package.core) (hg : g = 𝟙 package.core)
    (h : F.coefficientHom = T.coefficientHom) : HEq F T := by
  subst f
  subst g
  exact heq_of_eq (geometry_ext h)

/-- G-129 concrete kernel: equality includes the original full automorphism. -/
theorem inner_ext {a b : InnerFiberAut package}
    (h : a.1.1.hom.geometry.coefficientHom = b.1.1.hom.geometry.coefficientHom) :
    a = b := by
  apply Subtype.ext
  apply Subtype.ext
  apply Iso.ext
  apply GeometryTotalHom.ext (a.2.trans b.2.symm)
  exact vertical_geometry_heq a.1.1.hom.geometry b.1.1.hom.geometry a.2 b.2 h

/-- The actual inverse geometry morphism supplies the inverse coefficient map. -/
noncomputable def coefficientEquiv (a : InnerFiberAut package) :
    package.Coefficient ≃+* package.Coefficient where
  toFun := a.1.1.hom.geometry.coefficientHom
  invFun := a.1.1.inv.geometry.coefficientHom
  left_inv x := congrArg
    (fun k : package ⟶ package => k.geometry.coefficientHom x) a.1.1.hom_inv_id
  right_inv x := congrArg
    (fun k : package ⟶ package => k.geometry.coefficientHom x) a.1.1.inv_hom_id
  map_mul' := a.1.1.hom.geometry.coefficientHom.map_mul
  map_add' := a.1.1.hom.geometry.coefficientHom.map_add

/-- API: the coefficient equivalence has precisely the original forward map. -/
@[simp] theorem coefficientEquiv_toRingHom (a : InnerFiberAut package) :
    (coefficientEquiv a).toRingHom = a.1.1.hom.geometry.coefficientHom := rfl

/-- G-129 completion condition 4: the entire actual kernel is abelian. -/
theorem inner_mul_comm (a b : InnerFiberAut package) : a * b = b * a := by
  apply inner_ext
  exact PairCoefficients.comp_comm (coefficientEquiv a) (coefficientEquiv b)

/-- The concrete commutative group structure retains the inherited group operations. -/
noncomputable instance innerCommGroup : CommGroup (InnerFiberAut package) :=
  { inferInstanceAs (Group (InnerFiberAut package)) with mul_comm := inner_mul_comm }

/-- G-129 completion condition 4: the same abelian kernel is nontrivial. -/
instance innerNontrivial : Nontrivial (InnerFiberAut package) :=
  ⟨⟨innerSwap, 1, innerSwap_ne_one⟩⟩

/-- API for the later obstruction computation: every actual kernel element squares to one. -/
theorem inner_square (a : InnerFiberAut package) : a * a = 1 := by
  apply inner_ext
  exact PairCoefficients.square (coefficientEquiv a)

/-- The authored coefficient swap is not a square in this same actual kernel. -/
theorem innerSwap_not_square (a : InnerFiberAut package) : a * a ≠ innerSwap := by
  rw [inner_square]
  exact Ne.symm innerSwap_ne_one

end AAT.AG.AbelianLiftingObstruction.GeometryKernel

#assert_standard_axioms_only AAT.AG.AbelianLiftingObstruction.GeometryKernel
