import Formal.SHIGURE.Part2.Realizations.CoefficientModels
import Formal.SHIGURE.Part2.Realizations.ZariskiModels

/-!
# The copying mode as a coefficient realization

The mode takes actual sheaf arrows as carrier maps and uses the preservation
conditions of the primitive sheaf structure. The admissible objects are
Zariski locally split. The Law test is subsheaf inclusion on the test site.
-/

open AlgebraicGeometry CategoryTheory Opposite

universe u

noncomputable section

namespace SHIGURE

/-- The affine coefficient scheme associated to a specified ring. -/
def CoefficientRing.spec (R : CoefficientRing.{u}) : Scheme.{u} :=
  letI := R.ring
  Spec (CommRingCat.of R.Carrier)

/-- A coefficient ring map acts contravariantly on affine coefficient schemes. -/
def CoefficientRing.specMap {R S : CoefficientRing.{u}} (f : R.Hom S) : S.spec ⟶ R.spec :=
  letI := R.ring
  letI := S.ring
  Spec.map (CommRingCat.ofHom f)

namespace Copying

/-- Copying preservation means that the entire family of sheaf arrows is a
structure-preserving map of the primitive realizations. -/
def copyingStructureRule (sig : Signature.{u}) (S : Scheme.{u}) :
    StructureRule (fun _ : sig.SortType => Cat.of (ZariskiSheaf S))
      (SheafStructure sig (Scheme.zariskiTopology.over S)) where
  carrier A := A.carrier
  preserves f := ∃ h : SheafStructure.Hom _ _, h.onSort = f
  preserves_id A := ⟨SheafStructure.Hom.id A, rfl⟩
  preserves_comp := by
    rintro A B D f g ⟨f', rfl⟩ ⟨g', rfl⟩
    exact ⟨f'.comp g', rfl⟩

/-- A family of structured sheaf maps determines exactly one preserving family
in the general structure rule, and every preserving family arises this way. -/
def copyingStructureHomEquiv (sig : Signature.{u}) (S : Scheme.{u})
    (A B : (copyingStructureRule sig S).Category) :
    (A ⟶ B) ≃ SheafStructure.Hom A B where
  toFun h := h.property.choose
  invFun h := ⟨h.onSort, ⟨h, rfl⟩⟩
  left_inv h := Subtype.ext h.property.choose_spec
  right_inv h := SheafStructure.Hom.ext (Exists.choose_spec (⟨h, rfl⟩ :
    ∃ f : SheafStructure.Hom A B, f.onSort = h.onSort))

/-- A designated state of a sheaf structure is its section over the coefficient scheme. -/
private abbrev states {sig : Signature.{u}} {S : Scheme.{u}}
    (A : SheafStructure sig (Scheme.zariskiTopology.over S)) (s : sig.SortType) :=
  (A.carrier s).val.obj (op (Over.mk (𝟙 S)))

/-- Pull a designated state back to the new coefficient scheme. -/
private def changeStates {sig : Signature.{u}} {S S' : Scheme.{u}}
    (f : S' ⟶ S) (A : SheafStructure sig (Scheme.zariskiTopology.over S)) (s : sig.SortType) :
    states A s → states (restrictStructure f A) s :=
  let g : (Over.map f).obj (Over.mk (𝟙 S')) ⟶ Over.mk (𝟙 S) :=
    Over.homMk f (by simp)
  (A.carrier s).val.map g.op

/-- The concrete copying realization mode of Definition 4.1. -/
def copyingMode (base : CoefficientRing.{u}) (T : Theory.{u}) :
    CoefficientRealizationMode base T where
  Object R := SheafStructure T.signature (Scheme.zariskiTopology.over R.scalars.spec)
  Carrier R _ := Cat.of (ZariskiSheaf R.scalars.spec)
  rule R := copyingStructureRule T.signature R.scalars.spec
  admissible _ := IsZariskiSplit T
  Native := Structure T.signature
  nativeStates A := A.carrier
  States _ := states
  realizeNative R := constantStructure R.scalars.spec
  nativePoints R _ _ x := nativeState R.scalars.spec (Over.mk (𝟙 R.scalars.spec)) x
  change f := restrictStructure (CoefficientRing.specMap f)
  changePoints f := changeStates (CoefficientRing.specMap f)
  holds _ A l := A.holdsLaw (T.law l)

/-- The copying meaning of a selected primitive presentation in its coefficient algebra. -/
abbrev SelectedCopyingModels {P : PrimitivePresentation.{u}} (U : DeclarationContext P)
    {base : CoefficientRing.{u}} (R : CoefficientAlgebra base) :=
  (copyingMode base (DeclarationContext.Selected.presentation U).theory).Models R

end Copying

end SHIGURE
