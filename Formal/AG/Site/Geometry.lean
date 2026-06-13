import Formal.AG.Site.Adequate

namespace AAT.AG
namespace Site

universe u

open CategoryTheory

/--
II.定義8.1: the AAT site attached to an architecture object.

This packages the context preorder `ArchCtx(A)` together with the selected
coverage requirements and overlap package whose generated topology is `J_U`.
It does not construct presheaves, sheaves, descent data, or Cech complexes.
-/
structure AATSite {U : AtomCarrier.{u}} (A : ArchitectureObject U) where
  contextPreorder : ContextPreorderCategory A
  lawUniverse : LawUniverse U
  signature : ArchitectureSignature U
  requirements : CoverageRequirements A lawUniverse signature
  overlap : ContextOverlapPullback contextPreorder

namespace AATSite

/-- II.定義8.1: the object whose contexts form the site category. -/
def architectureObject {U : AtomCarrier.{u}} {A : ArchitectureObject U}
    (_S : AATSite A) : ArchitectureObject U :=
  A

/-- II.定義8.1: the Mathlib category of architecture contexts. -/
abbrev category {U : AtomCarrier.{u}} {A : ArchitectureObject U}
    (S : AATSite A) :=
  ContextCategoryObject S.contextPreorder

/-- II.定義8.1: the AAT Grothendieck topology `J_U` on `ArchCtx(A)`. -/
def topology {U : AtomCarrier.{u}} {A : ArchitectureObject U}
    (S : AATSite A) : GrothendieckTopology S.category :=
  AATGrothendieckTopology S.requirements S.overlap

/-- II.定義8.1: the topology component is definitionally the generated `J_U`. -/
theorem topology_eq {U : AtomCarrier.{u}} {A : ArchitectureObject U}
    (S : AATSite A) :
    S.topology = AATGrothendieckTopology S.requirements S.overlap :=
  rfl

/-- II.定義8.1: the generated topology contains the top cover. -/
theorem top_mem {U : AtomCarrier.{u}} {A : ArchitectureObject U}
    (S : AATSite A) (base : S.category) :
    (⊤ : Sieve base) ∈ S.topology base :=
  AATGrothendieckTopology.top_mem S.requirements S.overlap base

end AATSite

/--
II.定義2.1: architecture geometry built from the Part I generated object.

The object component is exactly the `AATCorePackage` object supplied by
`PartIPrerequisites`; the site component is the selected `AATSite` on that
object. Later sheaf surfaces such as `O_X^U`, `I_Ob^U`, and `Flat_U(X)` should
be added in the presheaf/sheaf layer, not in this package.
-/
structure ArchitectureGeometry (P : PartIPrerequisites.{u}) where
  site : AATSite P.architectureObject

namespace ArchitectureGeometry

/-- II.定義2.1: the generated architecture object `A_S^V` of the geometry. -/
def generatedObject {P : PartIPrerequisites.{u}}
    (_X : ArchitectureGeometry P) : ArchitectureObject P.carrier :=
  P.architectureObject

/-- II.定義2.1: the generated object is the object supplied by the Part I core. -/
theorem generatedObject_eq_core {P : PartIPrerequisites.{u}}
    (X : ArchitectureGeometry P) :
    X.generatedObject = P.core.object :=
  rfl

/-- II.定義2.1: the context preorder of `X_S^{V,U,J}`. -/
def contextPreorder {P : PartIPrerequisites.{u}} (X : ArchitectureGeometry P) :
    ContextPreorderCategory X.generatedObject :=
  X.site.contextPreorder

/-- II.定義2.1: the context category `ArchCtx(A_S^V)` of the geometry. -/
abbrev category {P : PartIPrerequisites.{u}} (X : ArchitectureGeometry P) :=
  X.site.category

/-- II.定義2.1: the selected topology `J_U` of the geometry. -/
def topology {P : PartIPrerequisites.{u}} (X : ArchitectureGeometry P) :
    GrothendieckTopology X.category :=
  X.site.topology

/-- II.定義2.1: the geometry topology is the site topology. -/
theorem topology_eq_site {P : PartIPrerequisites.{u}} (X : ArchitectureGeometry P) :
    X.topology = X.site.topology :=
  rfl

end ArchitectureGeometry

end Site
end AAT.AG
