import Formal.AG.Site.Geometry
import Mathlib.CategoryTheory.Sites.Sheaf

namespace AAT.AG
namespace Site

universe u

open CategoryTheory

/-- II.定義9.1: a presheaf on the architecture context category. -/
abbrev AATPresheaf {U : AtomCarrier.{u}} {A : ArchitectureObject U}
    (S : AATSite A) :=
  S.categoryᵒᵖ ⥤ Type u

/-- II.定義9.1: raw Atom presheaf signature. -/
abbrev AtRaw {U : AtomCarrier.{u}} {A : ArchitectureObject U}
    (S : AATSite A) :=
  AATPresheaf S

/-- II.定義9.1: raw law presheaf signature. -/
abbrev LawRaw {U : AtomCarrier.{u}} {A : ArchitectureObject U}
    (S : AATSite A) :=
  AATPresheaf S

/-- II.定義9.1: raw signature-axis presheaf signature. -/
abbrev SigRaw {U : AtomCarrier.{u}} {A : ArchitectureObject U}
    (S : AATSite A) :=
  AATPresheaf S

/--
II.定義10.1: sheaf condition for a single `J_U` cover.

Mathlib's `Presieve.IsSheafFor` says every compatible family of local sections
has a unique amalgamating global section.
-/
def AATSheafConditionFor {U : AtomCarrier.{u}} {A : ArchitectureObject U}
    (S : AATSite A) (F : AATPresheaf S) {base : S.category}
    (cover : Sieve base) : Prop :=
  Presieve.IsSheafFor F (cover : Presieve base)

/--
II.定義10.1: sheaf condition for the AAT topology `J_U`.

The quantification ranges exactly over covers in `S.topology`; no
sheafification or descent object is constructed here.
-/
def AATSheafCondition {U : AtomCarrier.{u}} {A : ArchitectureObject U}
    (S : AATSite A) (F : AATPresheaf S) : Prop :=
  ∀ {base : S.category} (cover : Sieve base), cover ∈ S.topology base ->
    AATSheafConditionFor S F cover

namespace AATSheafCondition

/-- II.定義10.1: the condition exposes the selected cover-wise gluing property. -/
theorem cover {U : AtomCarrier.{u}} {A : ArchitectureObject U}
    {S : AATSite A} {F : AATPresheaf S}
    (h : AATSheafCondition S F) {base : S.category}
    (cover : Sieve base) (hcover : cover ∈ S.topology base) :
    AATSheafConditionFor S F cover :=
  h cover hcover

/--
II.定義10.1 bridge: the AAT sheaf condition is exactly Mathlib's
`Presieve.IsSheaf` condition for the topology `J_U`.
-/
theorem iff_presieve_isSheaf {U : AtomCarrier.{u}} {A : ArchitectureObject U}
    (S : AATSite A) (F : AATPresheaf S) :
    AATSheafCondition S F ↔ Presieve.IsSheaf S.topology F :=
  Iff.rfl

end AATSheafCondition

/-- II.定義10.2: a sheaf on the AAT site, as a presheaf plus the `J_U` condition. -/
structure AATSheaf {U : AtomCarrier.{u}} {A : ArchitectureObject U}
    (S : AATSite A) where
  carrier : AATPresheaf S
  isSheaf : AATSheafCondition S carrier

namespace AATSheaf

/-- II.定義10.2: read the underlying presheaf. -/
def toPresheaf {U : AtomCarrier.{u}} {A : ArchitectureObject U}
    {S : AATSite A} (F : AATSheaf S) : AATPresheaf S :=
  F.carrier

/-- II.定義10.2: the underlying presheaf satisfies Mathlib's sheaf condition. -/
theorem presieve_isSheaf {U : AtomCarrier.{u}} {A : ArchitectureObject U}
    {S : AATSite A} (F : AATSheaf S) :
    Presieve.IsSheaf S.topology F.toPresheaf :=
  (AATSheafCondition.iff_presieve_isSheaf S F.toPresheaf).1 F.isSheaf

end AATSheaf

/--
II.定義10.2: named raw presheaves and sheaves attached to an AAT site.

This is a carrier package only. It records the intended names for later
architecture sheaf surfaces, but it does not construct their sections or prove
descent statements.
-/
structure ArchitectureSheafFamily {U : AtomCarrier.{u}} {A : ArchitectureObject U}
    (S : AATSite A) where
  atRaw : AtRaw S
  lawRaw : LawRaw S
  sigRaw : SigRaw S
  At : AATSheaf S
  Law : AATSheaf S
  Sig : AATSheaf S
  State : AATSheaf S
  Eff : AATSheaf S
  Auth : AATSheaf S
  Sem : AATSheaf S
  Trace : AATSheaf S

namespace ArchitectureSheafFamily

/-- II.定義10.2: the named Atom sheaf satisfies the `J_U` sheaf condition. -/
theorem At_isSheaf {U : AtomCarrier.{u}} {A : ArchitectureObject U}
    {S : AATSite A} (F : ArchitectureSheafFamily S) :
    Presieve.IsSheaf S.topology F.At.toPresheaf :=
  F.At.presieve_isSheaf

/-- II.定義10.2: the named law sheaf satisfies the `J_U` sheaf condition. -/
theorem Law_isSheaf {U : AtomCarrier.{u}} {A : ArchitectureObject U}
    {S : AATSite A} (F : ArchitectureSheafFamily S) :
    Presieve.IsSheaf S.topology F.Law.toPresheaf :=
  F.Law.presieve_isSheaf

/-- II.定義10.2: the named signature sheaf satisfies the `J_U` sheaf condition. -/
theorem Sig_isSheaf {U : AtomCarrier.{u}} {A : ArchitectureObject U}
    {S : AATSite A} (F : ArchitectureSheafFamily S) :
    Presieve.IsSheaf S.topology F.Sig.toPresheaf :=
  F.Sig.presieve_isSheaf

/-- II.定義10.2: the named state sheaf satisfies the `J_U` sheaf condition. -/
theorem State_isSheaf {U : AtomCarrier.{u}} {A : ArchitectureObject U}
    {S : AATSite A} (F : ArchitectureSheafFamily S) :
    Presieve.IsSheaf S.topology F.State.toPresheaf :=
  F.State.presieve_isSheaf

/-- II.定義10.2: the named effect sheaf satisfies the `J_U` sheaf condition. -/
theorem Eff_isSheaf {U : AtomCarrier.{u}} {A : ArchitectureObject U}
    {S : AATSite A} (F : ArchitectureSheafFamily S) :
    Presieve.IsSheaf S.topology F.Eff.toPresheaf :=
  F.Eff.presieve_isSheaf

/-- II.定義10.2: the named authority sheaf satisfies the `J_U` sheaf condition. -/
theorem Auth_isSheaf {U : AtomCarrier.{u}} {A : ArchitectureObject U}
    {S : AATSite A} (F : ArchitectureSheafFamily S) :
    Presieve.IsSheaf S.topology F.Auth.toPresheaf :=
  F.Auth.presieve_isSheaf

/-- II.定義10.2: the named semantic sheaf satisfies the `J_U` sheaf condition. -/
theorem Sem_isSheaf {U : AtomCarrier.{u}} {A : ArchitectureObject U}
    {S : AATSite A} (F : ArchitectureSheafFamily S) :
    Presieve.IsSheaf S.topology F.Sem.toPresheaf :=
  F.Sem.presieve_isSheaf

/-- II.定義10.2: the named trace sheaf satisfies the `J_U` sheaf condition. -/
theorem Trace_isSheaf {U : AtomCarrier.{u}} {A : ArchitectureObject U}
    {S : AATSite A} (F : ArchitectureSheafFamily S) :
    Presieve.IsSheaf S.topology F.Trace.toPresheaf :=
  F.Trace.presieve_isSheaf

end ArchitectureSheafFamily

end Site
end AAT.AG
