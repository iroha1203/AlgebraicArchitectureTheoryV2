import Formal.SHIGURE.Part2.Schemes.RelativeSpecOnStack

/-! # Naturality of the relative spectrum over a fixed structure

Restriction uses the actual functor of pairs induced by the test morphism.
The pseudofunctor's composition comparison identifies the iterated pullback
of the structure with pullback along the composite. Under the categorical
fiber equivalence this agrees with precomposing the representing map.
-/

namespace SHIGURE.SchemeDescent

open CategoryTheory CategoryTheory.Functor

noncomputable section

universe u

section CommutativeSquare

variable {A B C D : Type*} [Category* A] [Category* B] [Category* C] [Category* D]
  (p : A ⥤ B) (q : C ⥤ D) (G : A ⥤ C) (H : B ⥤ D) (square : G ⋙ q = p ⋙ H) (M : B)

/-- A commuting square of functors induces the functor between their actual fibers. -/
private def fiberFunctorOfSquare : p.Fiber M ⥤ q.Fiber (H.obj M) := by
  let j : p.Fiber M ⥤ A := Fiber.fiberInclusion
  have constant : (j ⋙ G) ⋙ q = (Functor.const (p.Fiber M)).obj (H.obj M) := calc
    _ = j ⋙ (G ⋙ q) := rfl
    _ = j ⋙ (p ⋙ H) := congrArg (j ⋙ ·) square
    _ = (j ⋙ p) ⋙ H := rfl
    _ = (Functor.const (p.Fiber M)).obj M ⋙ H :=
      congrArg (· ⋙ H) Fiber.fiberInclusion_comp_eq_const
    _ = (Functor.const (p.Fiber M)).obj (H.obj M) :=
      Functor.ext_of_iso (Functor.constComp (p.Fiber M) M H) (fun _ => rfl)
  exact Fiber.inducedFunctor constant

end CommutativeSquare

/-- Equality of object values suffices to compare functors into a discrete category. -/
private def discreteNatIsoOfPointwise {C : Type*} [Category* C] {U : Type*}
    (A B : C ⥤ Discrete U) (h : ∀ x, (A.obj x).as = (B.obj x).as) : A ≅ B :=
  NatIso.ofComponents (fun x => eqToIso (Discrete.ext (h x))) (by intros; apply Subsingleton.elim)

namespace QuasiCoherentAlgebraOnStack

open AlgebraicGeometry CategoryTheory.Pseudofunctor Opposite

universe a b

variable {F : Pseudofunctor (LocallyDiscrete (Scheme.{u})ᵒᵖ) Cat.{a,b}}
  (D : QuasiCoherentAlgebraOnStack F)
  {R S T : Scheme.{u}} (f : S ⟶ T) (g : R ⟶ S) (N : F.obj (.mk (op T)))

/-- First restrict the relative spectrum along the actual stack functor. -/
private def fiberRestrictionBase :=
  fiberFunctorOfSquare (D.relativeSpecForgetFiber S) (D.relativeSpecForgetFiber R)
    (D.relativeSpecOnStack.map g.op.toLoc).toFunctor (F.map g.op.toLoc).toFunctor
    (D.relativeSpecForgetFiber_restrict g) ((F.map f.op.toLoc).toFunctor.obj N)

/-- Restrict in the actual stack and identify the iterated pullback of the
fixed structure with its pullback along the composite. -/
def fixedStructureFiberRestriction :
    (D.relativeSpecForgetFiber S).Fiber ((F.map f.op.toLoc).toFunctor.obj N) ⥤
      (D.relativeSpecForgetFiber R).Fiber ((F.map (g ≫ f).op.toLoc).toFunctor.obj N) :=
  D.fiberRestrictionBase f g N ⋙
    elementsFiberTransport (D.sectionsFunctor R) _
      ((Cat.Hom.toNatIso (F.mapComp f.op.toLoc g.op.toLoc)).app N).symm

private theorem fiberRestrictionBase_section
    (s : (D.relativeSpecForgetFiber S).Fiber ((F.map f.op.toLoc).toFunctor.obj N)) :
    elementsFiberSection (D.sectionsFunctor R) _ ((D.fiberRestrictionBase f g N).obj s) =
      D.restrictedSection g _ (elementsFiberSection (D.sectionsFunctor S) _ s) := by
  let M := (F.map f.op.toLoc).toFunctor.obj N
  let H := (F.map g.op.toLoc).toFunctor
  rcases s with ⟨⟨Y, s⟩, h⟩
  change Y = M at h
  subst Y
  let t := D.restrictedSection g M s
  change elementsFiberSection (D.sectionsFunctor R) (H.obj M)
      (Fiber.mk (a := (D.sectionsFunctor R).elementsMk (H.obj M) t)
        (p := CategoryOfElements.π (D.sectionsFunctor R)) rfl) =
    D.restrictedSection g M
      (elementsFiberSection (D.sectionsFunctor S) M
        (Fiber.mk (a := (D.sectionsFunctor S).elementsMk M s)
          (p := CategoryOfElements.π (D.sectionsFunctor S)) rfl))
  rw [elementsFiberSection_mk, elementsFiberSection_mk]

private theorem fixedStructureFiberRestriction_section
    (s : (D.relativeSpecForgetFiber S).Fiber ((F.map f.op.toLoc).toFunctor.obj N)) :
    elementsFiberSection (D.sectionsFunctor R) _ ((D.fixedStructureFiberRestriction f g N).obj s) =
      D.fiberwiseSections.normalizedSection N f g (g ≫ f) rfl
        (elementsFiberSection (D.sectionsFunctor S) _ s) := by
  unfold fixedStructureFiberRestriction
  rw [Functor.comp_obj, elementsFiberTransport_section, D.fiberRestrictionBase_section]
  exact (D.fiberwiseSections.normalizedSection_comp N f g _).symm

/-- Precomposition by a map of the original test schemes. -/
def relativeSpecTestPrecompose :
    Discrete (Over.mk f ⟶ Over.mk (D.algebra (⟨T, N⟩ : CoGrothendieck F)).projection) ⥤
      Discrete (Over.mk (g ≫ f) ⟶ Over.mk (D.algebra (⟨T, N⟩ : CoGrothendieck F)).projection) :=
  Discrete.functor fun t => ⟨(Over.homMk g rfl : Over.mk (g ≫ f) ⟶ Over.mk f) ≫ t⟩

private theorem fixedStructureFiber_naturality_obj
    (s : (D.relativeSpecForgetFiber S).Fiber ((F.map f.op.toLoc).toFunctor.obj N)) :
    ((D.fixedStructureFiberRestriction f g N ⋙ (D.fixedStructureFiber (g ≫ f) N).functor).obj s).as =
      (((D.fixedStructureFiber f N).functor ⋙ D.relativeSpecTestPrecompose f g N).obj s).as := by
  change (D.sectionsOnTestEquiv (g ≫ f) N).symm
      (((elementsFiberEquivDiscrete (D.sectionsFunctor R) _).functor.obj
        ((D.fixedStructureFiberRestriction f g N).obj s)).as) =
    (Over.homMk g rfl : Over.mk (g ≫ f) ⟶ Over.mk f) ≫
      (D.sectionsOnTestEquiv f N).symm (((elementsFiberEquivDiscrete (D.sectionsFunctor S) _).functor.obj s).as)
  rw [elementsFiberEquivDiscrete_obj_as, elementsFiberEquivDiscrete_obj_as,
    D.fixedStructureFiberRestriction_section]
  exact (D.affineRepresentation N).naturality f g (g ≫ f) rfl _

/-- Restricting the actual fixed-structure fiber agrees, under its B.7
equivalence, with precomposition by the test morphism. -/
def fixedStructureFiber_naturality :
    D.fixedStructureFiberRestriction f g N ⋙ (D.fixedStructureFiber (g ≫ f) N).functor ≅
      (D.fixedStructureFiber f N).functor ⋙ D.relativeSpecTestPrecompose f g N :=
  discreteNatIsoOfPointwise _ _ (D.fixedStructureFiber_naturality_obj f g N)

end QuasiCoherentAlgebraOnStack


end

end SHIGURE.SchemeDescent
