import Formal.SHIGURE.Part2.Schemes.RelativeSpecFixedFiber
import Formal.SHIGURE.Part2.Schemes.StackAlgebraFromSheaves
import Formal.SHIGURE.Part2.Schemes.AffineAlgebraPresentations
import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.Polynomial.Eval.Defs

/-! # Affine representations of sections and a reduction of the base ring

The identity represents a single choice of section. A constant two-valued
family fails the empty-scheme test for representability. The structure
algebra on a stack exercises the construction through the original
algebra sheaves and the actual change from integers to integers modulo two.
The affine-line example distinguishes the sections with coordinates zero
and one after the same change in the actual fixed-structure category.
-/

namespace SHIGURE.SchemeDescent

open AlgebraicGeometry CategoryTheory CategoryTheory.Bicategory CategoryTheory.Pseudofunctor
open CategoryTheory.Limits Opposite TopologicalSpace

noncomputable section

/-- A single possible structure over every actual test scheme. -/
private def oneStructure : Pseudofunctor (LocallyDiscrete Scheme.{0}ᵒᵖ) Cat.{0,0} :=
  ((Functor.const (Scheme.{0}ᵒᵖ)).obj (Cat.of (Discrete PUnit.{1}))).toPseudoFunctor'

/-- A constant family on all the test schemes, with identity restrictions. -/
private def constantSections (A : Type) : FiberwiseSections oneStructure where
  fiber _ := (Functor.const (Discrete PUnit.{1})).obj A
  restrict _ := 𝟙 _
  restrict_id _ _ _ := rfl
  restrict_comp _ _ _ _ := rfl

/-- The unique choice of section over each test scheme is represented by
the identity, an affine scheme over the chosen base. -/
def identityAffineSectionRepresentation (X : Scheme.{0}) :
    AffineRepresentedSections (constantSections PUnit.{1}) (X := X) ⟨PUnit.unit⟩ where
  total := X
  projection := 𝟙 X
  affine := inferInstance
  sections f :=
    { toFun := fun _ => (Over.mkIdTerminal (X := X)).from (Over.mk f)
      invFun := fun _ => PUnit.unit
      left_inv := fun s => by
        change PUnit.unit = s
        cases s
        rfl
      right_inv := fun _ => (Over.mkIdTerminal (X := X)).hom_ext _ _ }
  naturality _ _ _ _ _ := (Over.mkIdTerminal (X := X)).hom_ext _ _

/-- Two constant distinct sections cannot be represented by a scheme over
the base. Testing at the empty scheme would identify the two sections. -/
theorem constantTwoSections_not_affinelyRepresented (X : Scheme.{0}) :
    ¬ Nonempty (AffineRepresentedSections (constantSections Bool) (X := X) ⟨PUnit.unit⟩) := by
  rintro ⟨E⟩
  let f : (⊥_ Scheme.{0}) ⟶ X := initial.to X
  let e := E.sections f
  have equal : e true = e false := by
    apply Over.OverMorphism.ext
    apply initial.hom_ext
  cases e.injective equal


universe u a b

private theorem structureAlgebra_isQuasiCoherent (X : Scheme.{u}) :
    IsQuasiCoherentSheafAlgebra (Under.mk (𝟙 X.sheaf)) := by
  apply (isQuasiCoherentSheafAlgebra_iff_eachAlgebraPresentation _).2
  intro U
  let R := Γ(X, U.val)
  let f := U.property.fromSpec
  let P := pullbackAlgebra f
  haveI : P.IsLeftAdjoint := (pullbackAlgebraAdjunction f).isLeftAdjoint
  let I := (Under.mkIdInitial (X := X.sheaf)).isInitialObj P
  refine ⟨R, 𝟙 R, ⟨?_⟩⟩
  rw [Spec.map_id]
  exact (I.uniqueUpToIso Under.mkIdInitial) ≪≫ (directImageStructure_id (Spec R)).symm

/-- The structure sheaves on the test schemes give an actual algebra on
every stack. Their Cartesian transition is the comparison of the two
initial algebras, since algebra pullback is a left adjoint. -/
private def unitAlgebraOnStack (F : Pseudofunctor (LocallyDiscrete (Scheme.{u})ᵒᵖ) Cat.{a,b}) :
    QuasiCoherentAlgebraOnStack F := by
  refine QuasiCoherentAlgebraOnStack.ofSheaves (fun T => Under.mk (𝟙 T.base.sheaf))
    (fun T => structureAlgebra_isQuasiCoherent T.base)
    (fun {_ _} _ => Under.mkIdInitial.to _) (fun _ => Under.mkIdInitial.hom_ext _ _)
    (fun _ _ => Under.mkIdInitial.hom_ext _ _) ?_
  intro S T f N
  let P := pullbackAlgebra f
  haveI : P.IsLeftAdjoint := (pullbackAlgebraAdjunction f).isLeftAdjoint
  let I := (Under.mkIdInitial (X := T.sheaf)).isInitialObj P
  let e := I.uniqueUpToIso (Under.mkIdInitial (X := S.sheaf))
  let m := ((pullbackAlgebraAdjunction f).homEquiv
    (Under.mk (𝟙 T.sheaf)) (Under.mk (𝟙 S.sheaf))).symm (Under.mkIdInitial.to _)
  change IsIso m
  have hm : m = e.hom := I.hom_ext _ _
  rw [hm]
  infer_instance

/-- Reduction modulo two defines the map of affine test schemes. -/
private def integerToTwo :
    CommRingCat.of ℤ ⟶ CommRingCat.of (ZMod 2) :=
  CommRingCat.ofHom (Int.castRingHom _)

/-- The actual fixed fiber for the structure algebra on the integer
spectrum restricts to the spectrum of `ZMod 2` by precomposition.
This test uses the sheaf input conversion and the categorical comparison. -/
def structureAlgebra_fixedFiber_integerToTwo
    {F : Pseudofunctor (LocallyDiscrete (Scheme.{0})ᵒᵖ) Cat.{a,b}}
    (N : F.obj (.mk (op (Spec (CommRingCat.of ℤ))))) :
    let D := unitAlgebraOnStack F
    let f := 𝟙 (Spec (CommRingCat.of ℤ))
    let g := Spec.map integerToTwo
    D.fixedStructureFiberRestriction f g N ⋙ (D.fixedStructureFiber (g ≫ f) N).functor ≅
      (D.fixedStructureFiber f N).functor ⋙ D.relativeSpecTestPrecompose f g N :=
  (unitAlgebraOnStack F).fixedStructureFiber_naturality _ _ N



private abbrev Z := Spec (CommRingCat.of ℤ)
private abbrev L := Spec (CommRingCat.of (Polynomial ℤ))

/-- The affine line over the integer spectrum is induced by the coefficient inclusion. -/
private def lineOverIntegers : L ⟶ Z :=
  Spec.map (CommRingCat.ofHom (Polynomial.C : ℤ →+* Polynomial ℤ))

/-- Use the affine line’s original algebra from B.7 on the integer spectrum. -/
private def lineAlgebra : QuasiCoherentAlgebra Z :=
  QuasiCoherentAlgebra.ofAffine lineOverIntegers

/-- The map of a test scheme to the integer spectrum is its terminal morphism. -/
private def toIntegers (T : Scheme.{0}) : T ⟶ Z := specZIsTerminal.from T

/-- Pull back the original affine-line algebra to the test scheme using B.7. -/
private def line (T : Scheme.{0}) : QuasiCoherentAlgebra T :=
  lineAlgebra.baseChange (toIntegers T)

/-- The affine line over a test scheme retains its map to the original affine line. -/
private def lineCoordinate (T : Scheme.{0}) : (line T).spec ⟶ lineAlgebra.spec :=
  (lineAlgebra.baseChangeIso (toIntegers T)).hom ≫ pullback.fst _ _

private theorem lineCartesian (T : Scheme.{0}) :
    IsPullback (lineCoordinate T) (line T).projection lineAlgebra.projection (toIntegers T) :=
  lineAlgebra.baseChange_isPullback (toIntegers T)

private theorem lineCartesianComp {S T : Scheme.{0}} (f : S ⟶ T) :
    IsPullback (lineCoordinate S) (line S).projection lineAlgebra.projection (f ≫ toIntegers T) := by
  rw [specZIsTerminal.hom_ext (f ≫ toIntegers T) (toIntegers S)]
  exact lineCartesian S

/-- The map of pulled-back affine lines preserves the coordinate and covers the given test map. -/
private def lineMap {S T : Scheme.{0}} (f : S ⟶ T) : (line S).spec ⟶ (line T).spec :=
  (lineCartesian T).lift (lineCoordinate S) ((line S).projection ≫ f)
    (by rw [(lineCartesianComp f).w, Category.assoc])

@[reassoc]
private theorem lineMap_projection {S T : Scheme.{0}} (f : S ⟶ T) :
    lineMap f ≫ (line T).projection = (line S).projection ≫ f :=
  (lineCartesian T).lift_snd _ _ _

private theorem lineMap_coordinate {S T : Scheme.{0}} (f : S ⟶ T) :
    lineMap f ≫ lineCoordinate T = lineCoordinate S :=
  (lineCartesian T).lift_fst _ _ _

private theorem lineMap_identity (T : Scheme.{0}) : lineMap (𝟙 T) = 𝟙 (line T).spec := by
  apply (lineCartesian T).hom_ext
  · rw [lineMap_coordinate, Category.id_comp]
  · rw [lineMap_projection, Category.comp_id, Category.id_comp]

private theorem lineMap_comp {R S T : Scheme.{0}} (f : S ⟶ T) (g : R ⟶ S) :
    lineMap (g ≫ f) = lineMap g ≫ lineMap f := by
  apply (lineCartesian T).hom_ext
  · rw [lineMap_coordinate, Category.assoc, lineMap_coordinate, lineMap_coordinate]
  · simp only [Category.assoc, lineMap_projection, lineMap_projection_assoc]

private theorem lineSquare {S T : Scheme.{0}} (f : S ⟶ T) :
    IsPullback (lineMap f) (line S).projection (line T).projection f :=
  (lineCartesianComp f).of_right' (lineCartesian T)

/-- Pull functions back along the induced map of affine lines over the test morphism. -/
private def lineTransition {S T : Scheme.{0}} (f : S ⟶ T) :
    (line T).algebraSheaf ⟶ (pushforwardAlgebra f).obj (line S).algebraSheaf :=
  directImageStructureMap (Over.homMk (lineMap f) (lineMap_projection f)) ≫
    (QuasiCoherentAlgebra.directImageStructure_comp f (line S).projection).inv

private theorem lineTransition_identity (T : Scheme.{0}) :
    lineTransition (𝟙 T) = (pushforwardAlgebraId T).inv.app (line T).algebraSheaf := by
  apply Under.UnderMorphism.ext
  apply Sheaf.hom_ext
  ext1
  funext U
  let V := (line T).projection ⁻¹ᵁ U.unop
  change (lineMap (𝟙 T)).appLE V V _ ≫ 𝟙 _ = 𝟙 _
  rw [Category.comp_id]
  calc
    _ = Scheme.Hom.appLE (𝟙 (line T).spec) V V le_rfl := by congr 1; exact lineMap_identity T
    _ = _ := (Scheme.Hom.appLE_eq_app (𝟙 (line T).spec) (U := V)).trans (Scheme.Hom.id_app V)


private theorem lineTransition_comp {R S T : Scheme.{0}} (f : S ⟶ T) (g : R ⟶ S) :
    lineTransition (g ≫ f) = lineTransition f ≫ (pushforwardAlgebra f).map (lineTransition g) ≫
      (pushforwardAlgebraComp f g).hom.app (line R).algebraSheaf := by
  apply Under.UnderMorphism.ext
  apply Sheaf.hom_ext
  ext1
  funext U
  change (lineMap (g ≫ f)).appLE _ _ _ ≫ 𝟙 _ =
    ((lineMap f).appLE _ _ _ ≫ 𝟙 _) ≫ (((lineMap g).appLE _ _ _ ≫ 𝟙 _) ≫ 𝟙 _)
  simp only [Category.comp_id]
  rw [Scheme.Hom.appLE_comp_appLE]
  congr 1
  exact lineMap_comp f g


private theorem transportedAdjunction_homEquiv {C D : Type*} [Category* C] [Category* D]
    {F : C ⥤ D} {G H : D ⥤ C} (A : F ⊣ G) (e : G ≅ H)
    {X : C} {Y : D} (m : F.obj X ⟶ Y) :
    (A.ofNatIsoRight e).homEquiv X Y m = A.homEquiv X Y m ≫ e.hom.app Y := by
  unfold Adjunction.ofNatIsoRight
  rw [Adjunction.mkOfHomEquiv_homEquiv]
  rfl

private theorem pullbackAlgebraHomEquiv_right {S T : Scheme.{0}} (f : S ⟶ T)
    (C : Under T.sheaf) (D : Under S.sheaf) (m : (pullbackAlgebra f).obj C ⟶ D) :
    let A := TopCat.Sheaf.pullbackPushforwardAdjunction CommRingCat f.base
    let a := (TopCat.Sheaf.pullback CommRingCat f.base).map C.hom
    letI : HasPushoutsAlong (pullbackStructureHom f) := by
      intro W h
      change @HasPushout (Sheaf (Opens.grothendieckTopology (S : TopCat)) CommRingCat) _ _ _ _
        h (pullbackStructureHom f)
      infer_instance
    ((pullbackAlgebraAdjunction f).homEquiv C D m).right =
      A.homEquiv C.right D.right (pushout.inl a (pullbackStructureHom f) ≫ m.right) := by
  let A := TopCat.Sheaf.pullbackPushforwardAdjunction CommRingCat f.base
  letI : HasPushoutsAlong (pullbackStructureHom f) := by
    intro W h
    change @HasPushout (Sheaf (Opens.grothendieckTopology (S : TopCat)) CommRingCat) _ _ _ _
      h (pullbackStructureHom f)
    infer_instance
  change ((pullbackAlgebraAdjunction f).homEquiv C D m).right =
    A.homEquiv C.right D.right (pushout.inl _ (pullbackStructureHom f) ≫ m.right)
  unfold pullbackAlgebraAdjunction
  rw [transportedAdjunction_homEquiv]
  change ((((Under.postAdjunctionLeft A).comp (Under.mapPushoutAdj (pullbackStructureHom f))).homEquiv
      C D m).right) ≫ 𝟙 _ = _
  rw [Category.comp_id, Adjunction.comp_homEquiv]
  let n := ((Under.mapPushoutAdj (pullbackStructureHom f)).homEquiv _ D) m
  change (((Under.postAdjunctionLeft A).homEquiv C ((Under.map (pullbackStructureHom f)).obj D)) n).right =
    A.homEquiv C.right D.right (pushout.inl _ (pullbackStructureHom f) ≫ m.right)
  rw [Adjunction.homEquiv_apply (Under.postAdjunctionLeft A)]
  have hn : n.right = pushout.inl _ (pullbackStructureHom f) ≫ m.right := by
    dsimp only [n]
    unfold Under.mapPushoutAdj
    rw [Adjunction.mkOfHomEquiv_homEquiv]
    rfl
  change A.unit.app C.right ≫ (TopCat.Sheaf.pushforward CommRingCat f.base).map n.right = _
  rw [hn, Adjunction.homEquiv_apply A]


private theorem lineTransition_cartesian {S T : Scheme.{0}} (f : S ⟶ T) :
    IsIso (((pullbackAlgebraAdjunction f).homEquiv (line T).algebraSheaf (line S).algebraSheaf).symm
      (lineTransition f)) := by
  let A := TopCat.Sheaf.pullbackPushforwardAdjunction CommRingCat f.base
  let a := (TopCat.Sheaf.pullback CommRingCat f.base).map (line T).algebraSheaf.hom
  let b := pullbackStructureHom f
  let m := ((pullbackAlgebraAdjunction f).homEquiv
    (line T).algebraSheaf (line S).algebraSheaf).symm (lineTransition f)
  let square := affinePullbackAlgebra_isPushout (lineSquare f)
  letI : HasPushoutsAlong b := by
    intro W h
    change @HasPushout (Sheaf (Opens.grothendieckTopology (S : TopCat)) CommRingCat) _ _ _ _ h b
    infer_instance
  have onLeft : pushout.inl a b ≫ m.right = affinePullbackMate (lineSquare f) := by
    apply (A.homEquiv (line T).algebraSheaf.right (line S).algebraSheaf.right).injective
    rw [← pullbackAlgebraHomEquiv_right f (line T).algebraSheaf (line S).algebraSheaf m]
    dsimp only [m]
    rw [Equiv.apply_symm_apply]
    unfold affinePullbackMate
    dsimp only [A, QuasiCoherentAlgebra.algebraSheaf]
    rw [Equiv.apply_symm_apply]
    rfl
  let e : (pullbackAlgebra f).obj (line T).algebraSheaf ≅ (line S).algebraSheaf := by
    refine Under.isoMk square.isoPushout.symm ?_
    exact square.inr_isoPushout_inv
  have equal : m = e.hom := by
    apply Under.UnderMorphism.ext
    apply pushout.hom_ext
    · exact onLeft.trans square.inl_isoPushout_inv.symm
    · exact (Under.w m).trans (Under.w e.hom).symm
  change IsIso m
  rw [equal]
  infer_instance

set_option maxRecDepth 2048 in
set_option maxHeartbeats 650000 in
/-- The Cartesian family of affine lines gives the test algebras independently of the structure. -/
private def affineLineAlgebraOnStack (F : Pseudofunctor (LocallyDiscrete (Scheme.{0})ᵒᵖ) Cat.{a,b}) :
    QuasiCoherentAlgebraOnStack F where
  algebra T := line T.base
  transition f := lineTransition f.base
  transition_id T := lineTransition_identity T.base
  transition_comp f g := lineTransition_comp g.base f.base
  cartesian {S T} f _ := by
    change IsIso (((pullbackAlgebraAdjunction f).homEquiv (line T).algebraSheaf (line S).algebraSheaf).symm
      (lineTransition f))
    exact lineTransition_cartesian f


private abbrev reduction := Spec.map integerToTwo

/-- Evaluation at an integer defines the corresponding point of the affine line. -/
private def evaluation (a : ℤ) : Z ⟶ L :=
  Spec.map (CommRingCat.ofHom (Polynomial.evalRingHom a))

/-- Take the section given by the chosen evaluation, via the actual pullback square. -/
private def lineSection (a : ℤ) : Over.mk (𝟙 Z) ⟶ Over.mk (line Z).projection := by
  let e := QuasiCoherentAlgebra.recoverAffineIso lineOverIntegers
  let c := evaluation a ≫ e.inv
  let h : c ≫ lineAlgebra.projection = 𝟙 Z ≫ toIntegers Z := specZIsTerminal.hom_ext _ _
  exact Over.homMk ((lineCartesian Z).lift c (𝟙 Z) h) ((lineCartesian Z).lift_snd _ _ _)

private theorem lineSectionEvaluation (a : ℤ) :
    (lineSection a).left ≫ lineCoordinate Z ≫ (QuasiCoherentAlgebra.recoverAffineIso lineOverIntegers).hom =
      evaluation a := by
  rw [← Category.assoc]
  have c : (lineSection a).left ≫ lineCoordinate Z =
      evaluation a ≫ (QuasiCoherentAlgebra.recoverAffineIso lineOverIntegers).inv :=
    (lineCartesian Z).lift_fst _ _ _
  rw [c, Category.assoc, Iso.inv_hom_id, Category.comp_id]

private theorem reducedEvaluations_ne : reduction ≫ evaluation 0 ≠ reduction ≫ evaluation 1 := by
  intro equal
  unfold reduction evaluation at equal
  rw [← Spec.map_comp, ← Spec.map_comp] at equal
  have ring := Spec.map_injective equal
  have value := congrArg (fun (g : CommRingCat.of (Polynomial ℤ) ⟶ CommRingCat.of (ZMod 2)) =>
    g.hom Polynomial.X) ring
  have zeroOne : (0 : ZMod 2) = 1 := by
    simpa only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom,
      Polynomial.coe_evalRingHom, Polynomial.eval_X, map_zero, map_one] using value
  exact zero_ne_one zeroOne

private theorem reducedLineSections_ne :
    (Over.homMk reduction rfl : Over.mk (reduction ≫ 𝟙 Z) ⟶ Over.mk (𝟙 Z)) ≫ lineSection 0 ≠
      (Over.homMk reduction rfl : Over.mk (reduction ≫ 𝟙 Z) ⟶ Over.mk (𝟙 Z)) ≫ lineSection 1 := by
  intro equal
  have coordinates := congrArg
    (fun (t : Over.mk (reduction ≫ 𝟙 Z) ⟶ Over.mk (line Z).projection) =>
      t.left ≫ lineCoordinate Z ≫ (QuasiCoherentAlgebra.recoverAffineIso lineOverIntegers).hom) equal
  change (reduction ≫ (lineSection 0).left) ≫ _ = (reduction ≫ (lineSection 1).left) ≫ _ at coordinates
  simp only [Category.assoc, lineSectionEvaluation] at coordinates
  exact reducedEvaluations_ne coordinates

/-- The sections of the affine-line algebra with coordinates 0 and 1
remain distinct in the actual fixed fiber after reduction modulo two. -/
theorem affineLine_fixedFiber_zero_one_after_reduction :
    let D := affineLineAlgebraOnStack oneStructure
    let b : oneStructure.obj (.mk (op Z)) := ⟨PUnit.unit⟩
    let E := D.fixedStructureFiber (𝟙 Z) b
    let res := D.fixedStructureFiberRestriction (𝟙 Z) reduction b
    res.obj (E.inverse.obj ⟨lineSection 0⟩) ≠ res.obj (E.inverse.obj ⟨lineSection 1⟩) := by
  let D := affineLineAlgebraOnStack oneStructure
  let b : oneStructure.obj (.mk (op Z)) := ⟨PUnit.unit⟩
  let E := D.fixedStructureFiber (𝟙 Z) b
  let G := D.fixedStructureFiber (reduction ≫ 𝟙 Z) b
  let res := D.fixedStructureFiberRestriction (𝟙 Z) reduction b
  let pre := D.relativeSpecTestPrecompose (𝟙 Z) reduction b
  let compare := D.fixedStructureFiber_naturality (𝟙 Z) reduction b
  have values (a : ℤ) :
      (G.functor.obj (res.obj (E.inverse.obj ⟨lineSection a⟩))).as =
        (pre.obj ⟨lineSection a⟩).as :=
    Discrete.eq_of_hom ((compare.hom.app (E.inverse.obj ⟨lineSection a⟩)) ≫
      pre.map (E.counitIso.app ⟨lineSection a⟩).hom)
  change res.obj (E.inverse.obj ⟨lineSection 0⟩) ≠ res.obj (E.inverse.obj ⟨lineSection 1⟩)
  intro equal
  have mapped := congrArg (fun s => (G.functor.obj s).as) equal
  exact reducedLineSections_ne ((values 0).symm.trans (mapped.trans (values 1)))

end

end SHIGURE.SchemeDescent
