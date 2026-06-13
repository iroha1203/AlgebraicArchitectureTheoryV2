import Formal.AG.Site.FinitePoset

namespace AAT.AG
namespace Site

universe u

open CategoryTheory

/--
II.§13 / R10: the AAT sheaf category on the selected site.

This is the bridge definition `AATSh(A,U,J) = Sh(ArchCtx(A), J_U)` using
Mathlib's category of sheaves of types. Later law algebra sheaves should enter
as objects of this category; they are not constructed here.
-/
abbrev AATSh {U : AtomCarrier.{u}} {A : ArchitectureObject U}
    (S : AATSite A) :=
  Sheaf S.topology (Type u)

namespace AATSh

/-- II.§13 / R10: the Mathlib forgetful functor from AAT sheaves to presheaves. -/
def toPresheafFunctor {U : AtomCarrier.{u}} {A : ArchitectureObject U}
    (S : AATSite A) :
    AATSh S ⥤ S.categoryᵒᵖ ⥤ Type u :=
  sheafToPresheaf S.topology (Type u)

/-- II.§13 / R10: read an object of `AATSh` as an AAT presheaf. -/
def underlyingPresheaf {U : AtomCarrier.{u}} {A : ArchitectureObject U}
    {S : AATSite A} (F : AATSh S) : AATPresheaf S :=
  F.val

/-- II.§13 / R10: an object of `AATSh` satisfies Mathlib's presieve sheaf condition. -/
theorem presieve_isSheaf {U : AtomCarrier.{u}} {A : ArchitectureObject U}
    {S : AATSite A} (F : AATSh S) :
    Presieve.IsSheaf S.topology F.underlyingPresheaf :=
  (isSheaf_iff_isSheaf_of_type (J := S.topology) F.underlyingPresheaf).1 F.cond

/-- II.§13 / R10: an object of `AATSh` satisfies the AAT sheaf condition. -/
theorem aatSheafCondition {U : AtomCarrier.{u}} {A : ArchitectureObject U}
    {S : AATSite A} (F : AATSh S) :
    AATSheafCondition S F.underlyingPresheaf :=
  (AATSheafCondition.iff_presieve_isSheaf S F.underlyingPresheaf).2
    F.presieve_isSheaf

/-- II.§13 / R10: bridge an object of `AATSh` to the AAT carrier package. -/
def toAATSheaf {U : AtomCarrier.{u}} {A : ArchitectureObject U}
    {S : AATSite A} (F : AATSh S) : AATSheaf S where
  carrier := F.underlyingPresheaf
  isSheaf := F.aatSheafCondition

end AATSh

end Site
end AAT.AG
