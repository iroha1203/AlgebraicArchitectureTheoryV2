import Formal.AG.Site.Sheaf

namespace AAT.AG
namespace Site

universe u

open CategoryTheory
open Opposite

/-- II.定義11.1: local sections attached to a cover of an AAT site. -/
abbrev AATLocalSectionFamily {U : AtomCarrier.{u}} {A : ArchitectureObject U}
    (S : AATSite A) (F : AATPresheaf S) {base : S.category}
    (cover : Sieve base) :=
  Presieve.FamilyOfElements F (cover : Presieve base)

/--
II.定義11.1: overlap agreement for local sections.

Mathlib records the usual equality after restricting two local sections to a
common refinement as `Presieve.FamilyOfElements.Compatible`.
-/
def AATOverlapAgreement {U : AtomCarrier.{u}} {A : ArchitectureObject U}
    {S : AATSite A} {F : AATPresheaf S} {base : S.category}
    {cover : Sieve base} (localSections : AATLocalSectionFamily S F cover) : Prop :=
  localSections.Compatible

/-- II.定義11.1: the cocycle condition is the compatible overlap agreement. -/
abbrev AATCocycleCondition {U : AtomCarrier.{u}} {A : ArchitectureObject U}
    {S : AATSite A} {F : AATPresheaf S} {base : S.category}
    {cover : Sieve base} (localSections : AATLocalSectionFamily S F cover) : Prop :=
  AATOverlapAgreement localSections

/--
II.定義11.1: gluing data for a cover.

The package contains the local section family and its overlap/cocycle
agreement. The global section is not part of the data.
-/
structure AATGluingData {U : AtomCarrier.{u}} {A : ArchitectureObject U}
    (S : AATSite A) (F : AATPresheaf S) {base : S.category}
    (cover : Sieve base) where
  localSections : AATLocalSectionFamily S F cover
  overlapAgreement : AATOverlapAgreement localSections

namespace AATGluingData

/-- II.定義11.1: the cocycle condition recorded by gluing data. -/
theorem cocycle {U : AtomCarrier.{u}} {A : ArchitectureObject U}
    {S : AATSite A} {F : AATPresheaf S} {base : S.category}
    {cover : Sieve base} (data : AATGluingData S F cover) :
    AATCocycleCondition data.localSections :=
  data.overlapAgreement

end AATGluingData

/--
II.定義11.2: a global section realizes the selected gluing data when it
amalgamates all local sections.
-/
def AATGlobalSectionRealizes {U : AtomCarrier.{u}} {A : ArchitectureObject U}
    {S : AATSite A} {F : AATPresheaf S} {base : S.category}
    {cover : Sieve base} (data : AATGluingData S F cover)
    (globalSection : F.obj (op base)) : Prop :=
  data.localSections.IsAmalgamation globalSection

/--
II.定義11.2: descent for a cover.

Every compatible local family has a unique global section which restricts back
to the chosen local sections.
-/
def AATDescent {U : AtomCarrier.{u}} {A : ArchitectureObject U}
    (S : AATSite A) (F : AATPresheaf S) {base : S.category}
    (cover : Sieve base) : Prop :=
  ∀ data : AATGluingData S F cover,
    ∃! globalSection : F.obj (op base), AATGlobalSectionRealizes data globalSection

namespace AATDescent

/-- II.定義11.2: descent exposes existence of the glued global section. -/
theorem exists_global {U : AtomCarrier.{u}} {A : ArchitectureObject U}
    {S : AATSite A} {F : AATPresheaf S} {base : S.category}
    {cover : Sieve base} (h : AATDescent S F cover)
    (data : AATGluingData S F cover) :
    ∃ globalSection : F.obj (op base), AATGlobalSectionRealizes data globalSection :=
  (h data).exists

end AATDescent

namespace AATSheafConditionFor

/-- II.定義11.2: the sheaf condition gives descent for the selected cover. -/
theorem descent {U : AtomCarrier.{u}} {A : ArchitectureObject U}
    {S : AATSite A} {F : AATPresheaf S} {base : S.category}
    {cover : Sieve base} (h : AATSheafConditionFor S F cover) :
    AATDescent S F cover := fun data =>
  h data.localSections data.overlapAgreement

end AATSheafConditionFor

namespace AATSheafCondition

/-- II.定義11.2: a sheaf on `J_U` satisfies descent for every selected cover. -/
theorem descent {U : AtomCarrier.{u}} {A : ArchitectureObject U}
    {S : AATSite A} {F : AATPresheaf S}
    (h : AATSheafCondition S F) {base : S.category}
    (cover : Sieve base) (hcover : cover ∈ S.topology base) :
    AATDescent S F cover :=
  (h.cover cover hcover).descent

end AATSheafCondition

namespace AATSheaf

/-- II.定義11.2: a packaged AAT sheaf satisfies descent for every `J_U` cover. -/
theorem descent {U : AtomCarrier.{u}} {A : ArchitectureObject U}
    {S : AATSite A} (F : AATSheaf S) {base : S.category}
    (cover : Sieve base) (hcover : cover ∈ S.topology base) :
    AATDescent S F.toPresheaf cover :=
  AATSheafCondition.descent F.isSheaf cover hcover

end AATSheaf

/--
II.定義12.1: a sheafification comparison relative to a chosen canonical map.

This records only the AAT-facing boundary `F_raw -> F_raw^+`; it does not
construct general sheafification for arbitrary sites.
-/
structure AATSheafificationComparison {U : AtomCarrier.{u}} {A : ArchitectureObject U}
    (S : AATSite A) where
  raw : AATPresheaf S
  plus : AATSheaf S
  canonical : raw ⟶ plus.toPresheaf

namespace AATSheafificationComparison

/-- II.定義12.1: the codomain of the canonical map is a sheaf. -/
theorem plus_isSheaf {U : AtomCarrier.{u}} {A : ArchitectureObject U}
    {S : AATSite A} (comparison : AATSheafificationComparison S) :
    Presieve.IsSheaf S.topology comparison.plus.toPresheaf :=
  comparison.plus.presieve_isSheaf

end AATSheafificationComparison

/--
II.定義12.1: the sheafification gap, relative to a chosen canonical map.

The gap is recorded as failure of the canonical comparison to be pointwise
bijective at some architecture context.
-/
def AATSheafificationGap {U : AtomCarrier.{u}} {A : ArchitectureObject U}
    {S : AATSite A} (comparison : AATSheafificationComparison S) : Prop :=
  ∃ base : S.category,
    ¬ Function.Bijective (comparison.canonical.app (op base))

end Site
end AAT.AG
