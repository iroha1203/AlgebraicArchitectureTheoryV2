import Formal.SHIGURE.Part1.CoefficientReading
import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory

/-!
# Semantic categories for coefficient schemes

Definition 4.1 takes the models of the required Laws inside the category of
admissible realizations. The existing coefficient scheme specifies the four
rules and the structure-preserving arrows.

## Implementation notes

The Law conditions restrict objects through mathlib's full subcategory.
Constructing another type of arrows would repeat the preservation and
composition rules of the coefficient scheme.
-/

universe u v

namespace SHIGURE.CoefficientScheme

open CategoryTheory

variable {P : PrimitivePresentation.{u}} {U : DeclarationContext P} {base : CoefficientRing.{u}}
variable (σ : CoefficientScheme.{u, v} U base)

/-- The retained required Laws are true under the interpretation of the realization scheme. -/
def SatisfiesRequired (R : CoefficientAlgebra base) :
    letI := σ.category R
    ObjectProperty (σ.Realization R) :=
  fun a => ∀ (name : P.theory.LawName) (kept : Declaration.law name.val ∈ U.declarations),
    σ.holdsLaw R a name.val kept

/-- The semantic objects of Definition 4.1 at a fixed coefficient algebra. -/
abbrev SemanticModels (R : CoefficientAlgebra base) :=
  letI := σ.category R
  (σ.SatisfiesRequired R).FullSubcategory

/-- The semantic category of Definition 4.1 inherits all admissible arrows between its models. -/
instance semanticModelsCategory (R : CoefficientAlgebra base) : Category.{u} (σ.SemanticModels R) :=
  letI := σ.category R
  ObjectProperty.FullSubcategory.category _

/-- Forget the Law evidence to the category of admissible realizations at the given coefficients. -/
def semanticModelInclusion (R : CoefficientAlgebra base) :
    letI := σ.category R
    σ.SemanticModels R ⥤ σ.Realization R :=
  letI := σ.category R
  (σ.SatisfiesRequired R).ι

end SHIGURE.CoefficientScheme
