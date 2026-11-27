import Formal.SHIGURE.Part2.Schemes.RelativeSpecFixedFiber
import Formal.SHIGURE.Part2.Schemes.StackAlgebraFromSheaves
import Formal.SHIGURE.Part2.Schemes.AffineAlgebraPresentations
import Mathlib.Data.ZMod.Basic

/-! # Affine representations of sections and a reduction of the base ring

The identity represents a single choice of section. A constant two-valued
family fails the empty-scheme test for representability. The structure
algebra on a stack exercises the construction through the original
algebra sheaves and the actual change from integers to integers modulo two.
-/

namespace SHIGURE.SchemeDescent

open AlgebraicGeometry CategoryTheory CategoryTheory.Bicategory CategoryTheory.Pseudofunctor
open CategoryTheory.Limits Opposite

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


end

end SHIGURE.SchemeDescent
