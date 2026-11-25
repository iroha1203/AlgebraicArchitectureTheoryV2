import Formal.SHIGURE.Part2.Tensor.DomainNativeMaps
import Formal.SHIGURE.Part2.Tensor.ExpressionBaseChange

/-!
# Models of written tensor equations with specified submodule diagrams

The tensor equations use the typed expression evaluator. The semantic
arrows carry the full primitive diagrams, including the relation and
partial-domain inclusions and their value maps.
-/

open CategoryTheory SHIGURE.TensorRealization

universe u

noncomputable section

namespace SHIGURE.TensorDomainStructure

variable {k : Type u} [CommRing k] {sig : Signature.{u}} {L : Type u}

/-- Use the written equations as the required Laws of the given primitive signature. -/
def equationPresentation (laws : L → TensorLaw k sig) : RealizationTheory.{u} :=
  ⟨sig, L, TensorLaw k sig, laws⟩

/-- The tensor meaning category with submodule diagrams at a fixed coefficient algebra. -/
abbrev EquationModels (R : Type u) [CommRing R] [Algebra k R] (laws : L → TensorLaw k sig) :=
  Models (equationPresentation laws)
    (fun (A : TensorDomainStructure R sig) law => (law.mapScalars (algebraMap k R)).holds A.toTensorStructure)

/-- The fixed-coefficient equation model category includes exactly all the preserving linear arrows. -/
def equationModelHomEquiv {R : Type u} [CommRing R] [Algebra k R] (laws : L → TensorLaw k sig)
    (A B : EquationModels R laws) : (A ⟶ B) ≃ LinearArrow A.obj B.obj :=
  modelHomEquiv (equationPresentation laws) _ A B

/-- The extension of a native equation model satisfies the written equations after changing their coefficients. -/
def extendEquationModel (R : Type u) [CommRing R] [Algebra k R] (laws : L → TensorLaw k sig)
    (A : Diagrams k sig) (hA : A.AdmitsBaseChange) (holds : ∀ l, (laws l).holds A.toTensorStructure) :
    EquationModels R laws :=
  ⟨extend R A hA, fun l => tensorLaw_holds_baseChange (R := R) (holds l)⟩

/-- Every component of a natural family between native models is an arrow of their actual coefficient models. -/
def NaturalDomainHom.equationModelApp {A B : Diagrams k sig}
    {hA : A.AdmitsBaseChange} {hB : B.AdmitsBaseChange} (f : NaturalDomainHom hA hB)
    (R : Type u) [CommRing R] [Algebra k R] (laws : L → TensorLaw k sig)
    (holdsA : ∀ l, (laws l).holds A.toTensorStructure) (holdsB : ∀ l, (laws l).holds B.toTensorStructure) :
    extendEquationModel R laws A hA holdsA ⟶ extendEquationModel R laws B hB holdsB :=
  ObjectProperty.homMk (f.app R)

end SHIGURE.TensorDomainStructure
