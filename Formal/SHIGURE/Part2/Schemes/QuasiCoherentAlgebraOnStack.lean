import Formal.SHIGURE.Part2.Schemes.StackAlgebraDirectImage
import Formal.SHIGURE.Part2.Schemes.StackCartesianArrows
import Formal.SHIGURE.Part2.Schemes.FiberwiseSectionDescent

/-! # Quasi-coherent algebras and their sections over stack objects

## Implementation notes

A test object belongs to the category of elements of the base
pseudofunctor. Its algebra is recorded by its affine-open presentation,
the input to B.7. The test-arrow transition is adjoint to the map of
pulled-back algebras. Composition of direct images keeps the original
maps on functions, and the Cartesian condition expresses the pullback
isomorphism for the algebra. This records the coherent algebra data
before constructing the representing scheme and comparing its sections.
-/

namespace SHIGURE.SchemeDescent

open AlgebraicGeometry CategoryTheory CategoryTheory.Pseudofunctor Opposite TopologicalSpace

noncomputable section

universe u a b

/-- A quasi-coherent algebra on the fppf stack is given on its actual
category of test objects. A transition over a map of schemes is written as
the adjoint map into the direct image. On a Cartesian arrow its mate is
the pullback isomorphism of the algebra. -/
structure QuasiCoherentAlgebraOnStack
    (F : Pseudofunctor (LocallyDiscrete (Scheme.{u})ᵒᵖ) Cat.{a,b}) where
  algebra (T : CoGrothendieck F) : QuasiCoherentAlgebra T.base
  transition {S T : CoGrothendieck F} (f : S ⟶ T) :
    (algebra T).algebraSheaf ⟶ (pushforwardAlgebra f.base).obj (algebra S).algebraSheaf
  transition_id (T : CoGrothendieck F) :
    transition (𝟙 T) = (pushforwardAlgebraId T.base).inv.app (algebra T).algebraSheaf
  transition_comp {R S T : CoGrothendieck F} (f : R ⟶ S) (g : S ⟶ T) :
    transition (f ≫ g) =
      transition g ≫ (pushforwardAlgebra g.base).map (transition f) ≫
        (pushforwardAlgebraComp g.base f.base).hom.app (algebra R).algebraSheaf
  cartesian {S T : Scheme.{u}} (f : S ⟶ T) (N : F.obj (.mk (op T))) :
    IsIso (((pullbackAlgebraAdjunction f).homEquiv (algebra (⟨T, N⟩ : CoGrothendieck F)).algebraSheaf
      (algebra (CoGrothendieck.domainCartesianLift N f)).algebraSheaf).symm
        (transition (CoGrothendieck.cartesianLift N f)))

namespace QuasiCoherentAlgebraOnStack

variable {F : Pseudofunctor (LocallyDiscrete (Scheme.{u})ᵒᵖ) Cat.{a,b}}
  (C : QuasiCoherentAlgebraOnStack F)

/-- The sheaf of algebras assigned to a test object is the actual
quasi-coherent algebra sheaf in the scheme fiber. -/
abbrev sheafAt {T : Scheme.{u}} (N : F.obj (.mk (op T))) :=
  (C.algebra (⟨T, N⟩ : CoGrothendieck F)).algebraSheaf

/-- The cartesian comparison is the mate of the specified restriction map. -/
def algebraPullbackIso {S T : Scheme.{u}} (f : S ⟶ T) (N : F.obj (.mk (op T))) :
    (pullbackAlgebra f).obj (C.sheafAt N) ≅ C.sheafAt ((F.map f.op.toLoc).toFunctor.obj N) := by
  let e := ((pullbackAlgebraAdjunction f).homEquiv (C.sheafAt N)
    (C.sheafAt ((F.map f.op.toLoc).toFunctor.obj N))).symm
      (C.transition (CoGrothendieck.cartesianLift N f))
  haveI : IsIso e := C.cartesian f N
  exact asIso e

/-- Sections on a single test scheme are maps of the algebra into the
actual base structure sheaf. -/
abbrev sections {T : Scheme.{u}} (N : F.obj (.mk (op T))) :=
  C.sheafAt N ⟶ Under.mk (𝟙 T.sheaf)

/-- For a fixed object over T, sections of its actual pullback to S have the
B.7 affine scheme interpretation using the pullback comparison of the algebra. -/
def sectionsOnTestEquiv {S T : Scheme.{u}} (f : S ⟶ T) (N : F.obj (.mk (op T))) :
    (Over.mk f ⟶ Over.mk (C.algebra (⟨T, N⟩ : CoGrothendieck F)).projection) ≃
      C.sections ((F.map f.op.toLoc).toFunctor.obj N) :=
  ((C.algebra (⟨T, N⟩ : CoGrothendieck F)).homEquivAlgebraSheaf (g := f)).trans
    (C.algebraPullbackIso f N).homFromEquiv

end QuasiCoherentAlgebraOnStack

namespace QuasiCoherentAlgebraOnStack

variable {F : Pseudofunctor (LocallyDiscrete (Scheme.{u})ᵒᵖ) Cat.{a,b}}
  (C : QuasiCoherentAlgebraOnStack F)

/-- Sections of the Cartesian algebra become maps from the global
algebra into the direct image of functions on the test scheme. -/
def sectionDirectImageEquiv {S T : Scheme.{u}} (f : S ⟶ T) (N : F.obj (.mk (op T))) :
    C.sections ((F.map f.op.toLoc).toFunctor.obj N) ≃
      (C.sheafAt N ⟶ directImageStructure f) :=
  (C.algebraPullbackIso f N).symm.homFromEquiv.trans (pullbackAlgebraHomEquiv f (C.sheafAt N))

/-- Under the adjunction, the section comparison first uses the given
algebra transition, then takes the direct image of the section. -/
theorem sectionDirectImageEquiv_apply {S T : Scheme.{u}} (f : S ⟶ T) (N : F.obj (.mk (op T)))
    (s : C.sections ((F.map f.op.toLoc).toFunctor.obj N)) :
    C.sectionDirectImageEquiv f N s =
      C.transition (CoGrothendieck.cartesianLift N f) ≫ (pushforwardAlgebra f).map s ≫
        (pushforwardAlgebraUnitIso f).hom := by
  let adj := pullbackAlgebraAdjunction f
  let e := C.algebraPullbackIso f N
  let t := C.transition (CoGrothendieck.cartesianLift N f)
  have mate : adj.homEquiv _ _ e.hom = t := by
    change adj.homEquiv _ _ ((adj.homEquiv _ _).symm t) = t
    exact Equiv.apply_symm_apply _ _
  change adj.homEquiv _ _ (e.hom ≫ s) ≫ (pushforwardAlgebraUnitIso f).hom = _
  rw [adj.homEquiv_naturality_right, mate, Category.assoc]

/-- The test comparison of sections is the exact direct-image form of B.7. -/
theorem sectionDirectImageEquiv_sectionsOnTest {S T : Scheme.{u}}
    (f : S ⟶ T) (N : F.obj (.mk (op T)))
    (g : Over.mk f ⟶ Over.mk (C.algebra (⟨T, N⟩ : CoGrothendieck F)).projection) :
    C.sectionDirectImageEquiv f N (C.sectionsOnTestEquiv f N g) =
      ((C.algebra (⟨T, N⟩ : CoGrothendieck F)).homEquivDirectImage.trans
        (C.algebra (⟨T, N⟩ : CoGrothendieck F)).directImageMapsEquivSheaves) g := by
  let D := C.algebra (⟨T, N⟩ : CoGrothendieck F)
  let E := pullbackAlgebraHomEquiv f D.algebraSheaf
  let e := C.algebraPullbackIso f N
  let x := (D.homEquivDirectImage.trans D.directImageMapsEquivSheaves) g
  change E (e.hom ≫ e.inv ≫ E.symm x) = x
  rw [e.hom_inv_id_assoc, Equiv.apply_symm_apply]

end QuasiCoherentAlgebraOnStack

namespace QuasiCoherentAlgebraOnStack

variable {F : Pseudofunctor (LocallyDiscrete (Scheme.{u})ᵒᵖ) Cat.{a,b}}
  (C : QuasiCoherentAlgebraOnStack F)

/-- Equal test arrows have the same algebra transition after identifying their base maps. -/
private theorem transition_heq {S T : CoGrothendieck F} {f g : S ⟶ T} (eq : f = g) :
    HEq (C.transition f) (C.transition g) := by
  subst g
  rfl

/-- The algebra maps attached to structure morphisms on a fixed test
scheme form a contravariant functor to the actual algebra sheaves. -/
def algebraFunctor (T : Scheme.{u}) : (F.obj (.mk (op T)))ᵒᵖ ⥤ Under T.sheaf where
  obj N := C.sheafAt N.unop
  map {M N} f := C.transition ((CoGrothendieck.ι F T).map f.unop) ≫
    (pushforwardAlgebraId T).hom.app (C.sheafAt N.unop)
  map_id N := by
    let P := CoGrothendieck.ι F T
    let h : P.map (𝟙 N.unop) = 𝟙 (P.obj N.unop) := P.map_id _
    have transport : C.transition (P.map (𝟙 N.unop)) = C.transition (𝟙 (P.obj N.unop)) :=
      eq_of_heq (C.transition_heq h)
    change C.transition (P.map (𝟙 N.unop)) ≫ _ = _
    rw [transport, C.transition_id]
    exact Iso.inv_hom_id_app (pushforwardAlgebraId T) _
  map_comp {L M N} f g := by
    let P := CoGrothendieck.ι F T
    let h : P.map (g.unop ≫ f.unop) = P.map g.unop ≫ P.map f.unop := P.map_comp _ _
    have transport :
        C.transition (P.map (g.unop ≫ f.unop)) = C.transition (P.map g.unop ≫ P.map f.unop) :=
      eq_of_heq (C.transition_heq h)
    change C.transition (P.map (g.unop ≫ f.unop)) ≫ _ = _
    rw [transport, C.transition_comp]
    apply Under.UnderMorphism.ext
    apply Sheaf.hom_ext
    ext1
    funext U
    let fU := (C.transition (P.map f.unop)).right.val.app U
    let gU := (C.transition (P.map g.unop)).right.val.app U
    let R := (C.sheafAt M.unop).right.val.obj U
    let S := (C.sheafAt N.unop).right.val.obj U
    change fU ≫ gU ≫ 𝟙 S ≫ 𝟙 S = (fU ≫ 𝟙 R) ≫ gU ≫ 𝟙 S
    simp only [Category.comp_id]
    exact (congrArg (fun h => h ≫ gU ≫ 𝟙 S) (Category.comp_id fU)).symm

/-- A morphism of structures acts on the sections by precomposition with
its contravariant algebra map. -/
def sectionsFunctor (T : Scheme.{u}) : F.obj (.mk (op T)) ⥤ Type u where
  obj N := C.sections N
  map f := fun s => (C.algebraFunctor T).map f.op ≫ s
  map_id N := by
    funext s
    change (C.algebraFunctor T).map (𝟙 (op N)) ≫ s = s
    rw [(C.algebraFunctor T).map_id, Category.id_comp]
  map_comp f g := by
    funext s
    change (C.algebraFunctor T).map (g.op ≫ f.op) ≫ s =
      (C.algebraFunctor T).map g.op ≫ (C.algebraFunctor T).map f.op ≫ s
    rw [(C.algebraFunctor T).map_comp, Category.assoc]

/-- The unit algebra maps to the direct image by the original scheme map on functions. -/
def baseAlgebraToDirectImage {S T : Scheme.{u}} (f : S ⟶ T) :
    Under.mk (𝟙 T.sheaf) ⟶ directImageStructure f :=
  Under.mkIdInitial.to (directImageStructure f)

/-- Pull a section back through the actual Cartesian algebra comparison. -/
def restrictedSection {S T : Scheme.{u}} (f : S ⟶ T) (N : F.obj (.mk (op T))) (s : C.sections N) :
    C.sections ((F.map f.op.toLoc).toFunctor.obj N) :=
  (C.sectionDirectImageEquiv f N).symm (s ≫ baseAlgebraToDirectImage f)

/-- The restricted section is the unique one inducing the original section
followed by pullback of functions over the new test scheme. -/
theorem restrictedSection_directImage {S T : Scheme.{u}} (f : S ⟶ T) (N : F.obj (.mk (op T)))
    (s : C.sections N) :
    C.sectionDirectImageEquiv f N (C.restrictedSection f N s) = s ≫ baseAlgebraToDirectImage f :=
  Equiv.apply_symm_apply _ _

/-- Restriction of the algebra maps commutes with the original Cartesian
transitions and the vertical maps of the stack. -/
theorem verticalAlgebra_cartesian {S T : Scheme.{u}} (f : S ⟶ T)
    {M N : F.obj (.mk (op T))} (m : M ⟶ N) :
    C.transition (CoGrothendieck.cartesianLift N f) ≫
      (pushforwardAlgebra f).map ((C.algebraFunctor S).map ((F.map f.op.toLoc).toFunctor.map m).op) =
    (C.algebraFunctor T).map m.op ≫ C.transition (CoGrothendieck.cartesianLift M f) := by
  let p := CoGrothendieck.cartesianLift M f
  let q := (CoGrothendieck.ι F T).map m
  let r := (CoGrothendieck.ι F S).map ((F.map f.op.toLoc).toFunctor.map m)
  let s := CoGrothendieck.cartesianLift N f
  have arrows : p ≫ q = r ≫ s :=
    (cartesianLift_vertical F f m).trans (vertical_cartesianLift F f N _).symm
  have same : C.transition (p ≫ q) = C.transition (r ≫ s) := eq_of_heq (C.transition_heq arrows)
  have eq := (C.transition_comp r s).symm.trans (same.symm.trans (C.transition_comp p q))
  apply Under.UnderMorphism.ext
  apply Sheaf.hom_ext
  ext1
  funext U
  let V := (Opens.map f.base).obj U.unop
  let a := (C.transition s).right.val.app U
  let e := (C.transition r).right.val.app (op V)
  let b := (C.transition q).right.val.app U
  let d := (C.transition p).right.val.app U
  let R := (C.sheafAt ((F.map f.op.toLoc).toFunctor.obj M)).right.val.obj (op V)
  let Q := (C.sheafAt M).right.val.obj U
  have point : a ≫ e ≫ 𝟙 R = b ≫ d ≫ 𝟙 R :=
    congrArg (fun k => k.right.val.app U) eq
  have core : a ≫ e = b ≫ d :=
    (congrArg (a ≫ ·) (Category.comp_id e)).symm.trans
      (point.trans (congrArg (b ≫ ·) (Category.comp_id d)))
  change a ≫ (e ≫ 𝟙 R) = (b ≫ 𝟙 Q) ≫ d
  exact (congrArg (a ≫ ·) (Category.comp_id e)).trans
    (core.trans (congrArg (· ≫ d) (Category.comp_id b)).symm)

/-- Pullback acts naturally on the actual algebra sections. -/
def restriction (S T : Scheme.{u}) (f : S ⟶ T) :
    C.sectionsFunctor T ⟶ (F.map f.op.toLoc).toFunctor ⋙ C.sectionsFunctor S where
  app N := C.restrictedSection f N
  naturality M N m := by
    funext t
    apply (C.sectionDirectImageEquiv f N).injective
    let p := CoGrothendieck.cartesianLift M f
    let q := CoGrothendieck.cartesianLift N f
    let A := (C.algebraFunctor T).map m.op
    let B := (C.algebraFunctor S).map ((F.map f.op.toLoc).toFunctor.map m).op
    let P := pushforwardAlgebra f
    let u := C.restrictedSection f M t
    let k := (pushforwardAlgebraUnitIso f).hom
    let b := baseAlgebraToDirectImage f
    change C.sectionDirectImageEquiv f N (C.restrictedSection f N (A ≫ t)) =
      C.sectionDirectImageEquiv f N (B ≫ u)
    rw [C.restrictedSection_directImage, C.sectionDirectImageEquiv_apply, P.map_comp]
    have h : C.transition q ≫ P.map B = A ≫ C.transition p := C.verticalAlgebra_cartesian f m
    have pull : C.transition p ≫ P.map u ≫ k = t ≫ b :=
      (C.sectionDirectImageEquiv_apply f M u).symm.trans (C.restrictedSection_directImage f M t)
    change (A ≫ t) ≫ b = C.transition q ≫ (P.map B ≫ P.map u) ≫ k
    calc
      _ = A ≫ (t ≫ b) := Category.assoc _ _ _
      _ = A ≫ C.transition p ≫ P.map u ≫ k := congrArg (A ≫ ·) pull.symm
      _ = (A ≫ C.transition p) ≫ P.map u ≫ k := (Category.assoc _ _ _).symm
      _ = (C.transition q ≫ P.map B) ≫ P.map u ≫ k := congrArg (· ≫ P.map u ≫ k) h.symm
      _ = _ := by simp only [Category.assoc]

/-- Transport of a section along the inverse of the pseudofunctor's
composition comparison is compatible with the actual direct images. -/
theorem compositeSection_directImage {R S T : Scheme.{u}} (f : S ⟶ T) (g : R ⟶ S)
    (N : F.obj (.mk (op T)))
    (s : C.sections ((F.map g.op.toLoc).toFunctor.obj ((F.map f.op.toLoc).toFunctor.obj N))) :
    C.sectionDirectImageEquiv (g ≫ f) N
        ((C.sectionsFunctor R).map ((F.mapComp f.op.toLoc g.op.toLoc).inv.toNatTrans.app N) s) =
      C.transition (CoGrothendieck.cartesianLift N f) ≫
        (pushforwardAlgebra f).map (C.sectionDirectImageEquiv g ((F.map f.op.toLoc).toFunctor.obj N) s) ≫
          (QuasiCoherentAlgebra.directImageStructure_comp f g).hom := by
  let N' := (F.map f.op.toLoc).toFunctor.obj N
  let N'' := (F.map g.op.toLoc).toFunctor.obj N'
  let e := (F.mapComp f.op.toLoc g.op.toLoc).inv.toNatTrans.app N
  let p := CoGrothendieck.cartesianLift N f
  let q := CoGrothendieck.cartesianLift N' g
  let r := (CoGrothendieck.ι F R).map e
  let k := CoGrothendieck.cartesianLift N (g ≫ f)
  have arrows : q ≫ p = r ≫ k :=
    (cartesianLift_comp F f g N).trans (vertical_cartesianLift F (g ≫ f) N e).symm
  have same : C.transition (q ≫ p) = C.transition (r ≫ k) := eq_of_heq (C.transition_heq arrows)
  have eq := (C.transition_comp r k).symm.trans (same.symm.trans (C.transition_comp q p))
  rw [C.sectionDirectImageEquiv_apply, C.sectionDirectImageEquiv_apply]
  apply Under.UnderMorphism.ext
  apply Sheaf.hom_ext
  ext1
  funext U
  let V := (Opens.map f.base).obj U.unop
  let W := (Opens.map g.base).obj V
  let a := (C.transition k).right.val.app U
  let b := (C.transition r).right.val.app (op W)
  let c := (C.transition p).right.val.app U
  let d := (C.transition q).right.val.app (op V)
  let S₀ := (C.sheafAt N'').right.val.obj (op W)
  let S₁ := R.sheaf.val.obj (op W)
  let sW := s.right.val.app (op W)
  have point : a ≫ b ≫ 𝟙 S₀ = c ≫ d ≫ 𝟙 S₀ :=
    congrArg (fun x => x.right.val.app U) eq
  have core : a ≫ b = c ≫ d :=
    (congrArg (a ≫ ·) (Category.comp_id b)).symm.trans
      (point.trans (congrArg (c ≫ ·) (Category.comp_id d)))
  change a ≫ ((b ≫ 𝟙 S₀) ≫ sW) ≫ 𝟙 S₁ = c ≫ (d ≫ sW ≫ 𝟙 S₁) ≫ 𝟙 S₁
  have applied := congrArg (· ≫ sW) core
  simpa only [Category.assoc, Category.comp_id] using applied

/-- On the actual test objects, the direct image comparison for a
composite agrees with the pullback of their structure functions. -/
theorem pushforwardUnit_directImageMap {R S T : Scheme.{u}} (f : S ⟶ T) (g : R ⟶ S) :
    (pushforwardAlgebraUnitIso f).hom ≫ directImageStructureMap
      (Over.homMk g rfl : Over.mk (g ≫ f) ⟶ Over.mk f) =
    (pushforwardAlgebra f).map (baseAlgebraToDirectImage g) ≫
      (QuasiCoherentAlgebra.directImageStructure_comp f g).hom := by
  apply Under.UnderMorphism.ext
  apply Sheaf.hom_ext
  ext1
  funext U
  let V := f ⁻¹ᵁ U.unop
  let W := g ⁻¹ᵁ V
  change 𝟙 Γ(S, V) ≫ g.appLE V W le_rfl =
    (baseAlgebraToDirectImage g).right.val.app (op V) ≫ 𝟙 Γ(R, W)
  rw [baseAlgebraToDirectImage, Under.mkIdInitial_to_right]
  exact (Category.id_comp _).trans ((g.appLE_eq_app).trans (Category.comp_id _).symm)

/-- Restriction of a section over a test scheme corresponds to
precomposition of its B.7 map with the next test morphism. -/
theorem sectionDirectImage_refine {R S T : Scheme.{u}} (f : S ⟶ T) (g : R ⟶ S)
    (N : F.obj (.mk (op T))) (t : C.sections ((F.map f.op.toLoc).toFunctor.obj N)) :
    C.sectionDirectImageEquiv (g ≫ f) N
        ((C.sectionsFunctor R).map ((F.mapComp f.op.toLoc g.op.toLoc).inv.toNatTrans.app N)
          (C.restrictedSection g ((F.map f.op.toLoc).toFunctor.obj N) t)) =
      C.sectionDirectImageEquiv f N t ≫ directImageStructureMap
        (Over.homMk g rfl : Over.mk (g ≫ f) ⟶ Over.mk f) := by
  let N' := (F.map f.op.toLoc).toFunctor.obj N
  let P := pushforwardAlgebra f
  let a := C.transition (CoGrothendieck.cartesianLift N f)
  let c := (QuasiCoherentAlgebra.directImageStructure_comp f g).hom
  let d := directImageStructureMap (Over.homMk g rfl : Over.mk (g ≫ f) ⟶ Over.mk f)
  let b := (pushforwardAlgebraUnitIso f).hom
  let e := baseAlgebraToDirectImage g
  rw [C.compositeSection_directImage, C.restrictedSection_directImage,
    C.sectionDirectImageEquiv_apply, P.map_comp]
  change a ≫ (P.map t ≫ P.map e) ≫ c = (a ≫ P.map t ≫ b) ≫ d
  simp only [Category.assoc]
  exact congrArg (fun k => a ≫ P.map t ≫ k) (pushforwardUnit_directImageMap f g).symm

/-- The unit algebra comparison agrees with the identity test scheme. -/
theorem baseAlgebraToDirectImage_identity (T : Scheme.{u}) :
    baseAlgebraToDirectImage (𝟙 T) = (directImageStructure_id T).inv := by
  exact Under.mkIdInitial.hom_ext _ _

/-- The unit algebra maps coherently into the functions of nested tests. -/
theorem baseAlgebraToDirectImage_comp {R S T : Scheme.{u}} (f : S ⟶ T) (g : R ⟶ S) :
    baseAlgebraToDirectImage f ≫ directImageStructureMap
      (Over.homMk g rfl : Over.mk (g ≫ f) ⟶ Over.mk f) =
      baseAlgebraToDirectImage (g ≫ f) :=
  Under.mkIdInitial.hom_ext _ _

/-- Pullback along the identity uses precisely the unit comparison in
the pseudofunctor of base structures. -/
theorem restriction_identity {T : Scheme.{u}} (N : F.obj (.mk (op T))) (s : C.sections N) :
    (C.sectionsFunctor T).map ((F.mapId (.mk (op T))).hom.toNatTrans.app N)
      (C.restrictedSection (𝟙 T) N s) = s := by
  let e := (F.mapId (.mk (op T))).hom.toNatTrans.app N
  let p := CoGrothendieck.cartesianLift N (𝟙 T)
  let q := (CoGrothendieck.ι F T).map e
  let t := C.restrictedSection (𝟙 T) N s
  let f := baseAlgebraToDirectImage (𝟙 T)
  haveI : IsIso f := by
    change IsIso (baseAlgebraToDirectImage (𝟙 T))
    rw [baseAlgebraToDirectImage_identity]
    infer_instance
  apply (cancel_mono f).1
  have proj : C.transition p = C.transition q := eq_of_heq
    (C.transition_heq (cartesianLift_identity F N))
  have comparison :
      C.sectionDirectImageEquiv (𝟙 T) N t = ((C.sectionsFunctor T).map e t) ≫ f := by
    rw [C.sectionDirectImageEquiv_apply, proj]
    apply Under.UnderMorphism.ext
    apply Sheaf.hom_ext
    ext1
    funext U
    let a := (C.transition q).right.val.app U
    let tU := t.right.val.app U
    change a ≫ tU ≫ 𝟙 (T.sheaf.val.obj U) =
      ((a ≫ 𝟙 _) ≫ tU) ≫ f.right.val.app U
    rw [show f.right = (directImageStructure (𝟙 T)).hom from Under.mkIdInitial_to_right _]
    change a ≫ tU ≫ 𝟙 (T.sheaf.val.obj U) =
      ((a ≫ 𝟙 _) ≫ tU) ≫ Scheme.Hom.app (𝟙 T) U.unop
    rw [Scheme.Hom.id_app]
    simp only [Category.assoc, Category.id_comp]
    rfl
  exact comparison.symm.trans (C.restrictedSection_directImage (𝟙 T) N s)

/-- Iterated restriction of algebra sections uses the actual composition
comparison for base structures. -/
theorem restriction_composition {R S T : Scheme.{u}} (f : S ⟶ T) (g : R ⟶ S)
    (N : F.obj (.mk (op T))) (s : C.sections N) :
    (C.sectionsFunctor R).map ((F.mapComp f.op.toLoc g.op.toLoc).hom.toNatTrans.app N)
      (C.restrictedSection (g ≫ f) N s) =
      C.restrictedSection g ((F.map f.op.toLoc).toFunctor.obj N) (C.restrictedSection f N s) := by
  let N' := (F.map f.op.toLoc).toFunctor.obj N
  let t := C.restrictedSection f N s
  let u := C.restrictedSection g N' t
  let e := (Cat.Hom.toNatIso (F.mapComp f.op.toLoc g.op.toLoc)).app N
  have h : (C.sectionsFunctor R).map e.inv u = C.restrictedSection (g ≫ f) N s := by
    apply (C.sectionDirectImageEquiv (g ≫ f) N).injective
    change C.sectionDirectImageEquiv (g ≫ f) N
        ((C.sectionsFunctor R).map ((F.mapComp f.op.toLoc g.op.toLoc).inv.toNatTrans.app N)
          (C.restrictedSection g N' t)) = _
    rw [C.sectionDirectImage_refine, C.restrictedSection_directImage (g ≫ f) N s]
    have eq : C.sectionDirectImageEquiv f N t = s ≫ baseAlgebraToDirectImage f :=
      C.restrictedSection_directImage f N s
    rw [eq, Category.assoc, baseAlgebraToDirectImage_comp]
  exact (congrArg ((C.sectionsFunctor R).map e.hom) h).symm.trans
    (FunctorToTypes.map_hom_map_inv_apply (C.sectionsFunctor R) e _)

/-- The sections of the quasi-coherent algebra of a stack object form
the actual functorial family used in the relative spectrum of B.3. -/
def fiberwiseSections : FiberwiseSections F where
  fiber T := C.sectionsFunctor T.as.unop
  restrict {S T} f := C.restriction T.as.unop S.as.unop f.as.unop
  restrict_id _ N s := C.restriction_identity N s
  restrict_comp f g N s := C.restriction_composition f.as.unop g.as.unop N s

end QuasiCoherentAlgebraOnStack

end

end SHIGURE.SchemeDescent
