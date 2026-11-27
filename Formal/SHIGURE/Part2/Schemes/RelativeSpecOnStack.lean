import Formal.SHIGURE.Part2.Schemes.QuasiCoherentAlgebraOnStack
import Formal.SHIGURE.Part2.Schemes.AffineRepresentedSectionDescent
import Formal.SHIGURE.Part2.Schemes.SectionFiberDiscrete

/-! # The relative spectrum of a quasi-coherent algebra on a stack

For a fixed structure over a scheme, Lemma B.7 represents the section
family by an affine scheme. The equivalence on all test schemes is
natural for the actual restriction of the algebra. The comparison for
pairs uses base-stack descent and the effective descent of affine sections.
-/

namespace SHIGURE.SchemeDescent

open AlgebraicGeometry CategoryTheory CategoryTheory.Pseudofunctor Opposite TopologicalSpace

noncomputable section

universe u a b

namespace QuasiCoherentAlgebraOnStack

variable {F : Pseudofunctor (LocallyDiscrete (Scheme.{u})ᵒᵖ) Cat.{a,b}}
  (C : QuasiCoherentAlgebraOnStack F)

/-- The affine-scheme representative from B.7 reads back into the
direct image algebra of the actual test scheme. -/
private theorem sectionsOnTestSymm_directImage {S T : Scheme.{u}} (f : S ⟶ T)
    (N : F.obj (.mk (op T))) (s : C.sections ((F.map f.op.toLoc).toFunctor.obj N)) :
    let D := C.algebra (⟨T, N⟩ : CoGrothendieck F)
    (D.homEquivDirectImage.trans D.directImageMapsEquivSheaves) ((C.sectionsOnTestEquiv f N).symm s) =
      C.sectionDirectImageEquiv f N s := by
  have h := C.sectionDirectImageEquiv_sectionsOnTest f N ((C.sectionsOnTestEquiv f N).symm s)
  rw [Equiv.apply_symm_apply] at h
  exact h.symm

/-- For an object of the base stack, the section family over all its test
schemes is naturally represented by its B.7 affine projection. -/
def affineRepresentation {T : Scheme.{u}} (N : F.obj (.mk (op T))) :
    AffineRepresentedSections C.fiberwiseSections N where
  total := (C.algebra (⟨T, N⟩ : CoGrothendieck F)).spec
  projection := (C.algebra (⟨T, N⟩ : CoGrothendieck F)).projection
  affine := inferInstance
  sections f := (C.sectionsOnTestEquiv f N).symm
  naturality := by
    intro S R f g h eq s
    subst h
    let D := C.algebra (⟨T, N⟩ : CoGrothendieck F)
    let E := D.homEquivDirectImage (g := g ≫ f) |>.trans D.directImageMapsEquivSheaves
    let A := C.fiberwiseSections
    let p := (F.mapComp f.op.toLoc g.op.toLoc).inv.toNatTrans.app N
    have direct :
        A.normalizedSection N f g (g ≫ f) rfl s =
          (C.sectionsFunctor R).map p
            (C.restrictedSection g ((F.map f.op.toLoc).toFunctor.obj N) s) :=
      A.normalizedSection_comp N f g s
    change (C.sectionsOnTestEquiv (g ≫ f) N).symm (A.normalizedSection N f g (g ≫ f) rfl s) =
      (Over.homMk g rfl : Over.mk (g ≫ f) ⟶ Over.mk f) ≫ (C.sectionsOnTestEquiv f N).symm s
    apply E.injective
    dsimp only [E]
    rw [D.homEquivSheaves_precomp, C.sectionsOnTestSymm_directImage,
      C.sectionsOnTestSymm_directImage, direct]
    exact C.sectionDirectImage_refine f g N s

/-- The relative spectrum over the stack pairs each structure with an
algebra map to the structure sheaf. Its arrows preserve that map. -/
def relativeSpecOnStack :
    Pseudofunctor (LocallyDiscrete (Scheme.{u})ᵒᵖ) Cat.{a,max b u} :=
  C.fiberwiseSections.pseudofunctor

/-- The projection at a test scheme forgets the chosen algebra map. -/
def relativeSpecForgetFiber (T : Scheme.{u}) :
    C.relativeSpecOnStack.obj (.mk (op T)) ⥤ F.obj (.mk (op T)) :=
  CategoryOfElements.π (C.sectionsFunctor T)

/-- Forgetting the section commutes with restriction along a test morphism. -/
theorem relativeSpecForgetFiber_restrict {S T : Scheme.{u}} (f : S ⟶ T) :
    (C.relativeSpecOnStack.map f.op.toLoc).toFunctor ⋙ C.relativeSpecForgetFiber S =
      C.relativeSpecForgetFiber T ⋙ (F.map f.op.toLoc).toFunctor := rfl

/-- If the base fiber is a groupoid, arrows preserving the section are
precisely structure isomorphisms preserving the section. -/
theorem relativeSpecOnStack_isGroupoid (T : Scheme.{u}) [IsGroupoid (F.obj (.mk (op T)))] :
    IsGroupoid (C.relativeSpecOnStack.obj (.mk (op T))) := by
  let P := C.sectionsFunctor T
  change IsGroupoid P.Elements
  haveI : (CategoryOfElements.π P).ReflectsIsomorphisms := by infer_instance
  exact isGroupoid_of_reflects_iso (CategoryOfElements.π P)

/-- Fixing a structure and pulling it back to a test scheme gives the
discrete category of maps into its affine relative spectrum over the base. -/
def fixedStructureFiber {S T : Scheme.{u}} (f : S ⟶ T) (N : F.obj (.mk (op T))) :
    (C.relativeSpecForgetFiber S).Fiber ((F.map f.op.toLoc).toFunctor.obj N) ≌
      Discrete (Over.mk f ⟶ Over.mk (C.algebra (⟨T, N⟩ : CoGrothendieck F)).projection) :=
  (elementsFiberEquivDiscrete (C.sectionsFunctor S) _).trans
    (Discrete.equivalence (C.sectionsOnTestEquiv f N).symm)

/-- The relative spectrum of a quasi-coherent algebra on an fppf stack
is an fppf stack, by effective descent of the base objects and affine sections. -/
theorem relativeSpecOnStack_isFppfStack [F.IsStack fppfTopology] :
    C.relativeSpecOnStack.IsStack fppfTopology :=
  affinelyRepresentedSections_isFppfStack C.fiberwiseSections (fun _ N => C.affineRepresentation N)

end QuasiCoherentAlgebraOnStack

end

end SHIGURE.SchemeDescent
