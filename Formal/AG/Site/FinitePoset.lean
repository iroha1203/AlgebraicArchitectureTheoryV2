import Formal.AG.Site.Descent

namespace AAT.AG
namespace Site

universe u

/--
II.定義7.2B: finite poset AAT site regime.

This is the finite, cover-relative regime used by the Čech computation
surface. It records a selected finite context poset, a selected cover, the
witness-closure adequacy boundary, and a coefficient presheaf on the selected
AAT site. It does not claim every possible `ArchCtx(A)` is finite.
-/
structure FinitePosetAATSiteRegime {U : AtomCarrier.{u}}
    {A : ArchitectureObject U} (S : AATSite A) where
  ContextIndex : Type u
  finiteContextIndex : Finite ContextIndex
  context : ContextIndex -> ArchCtx A
  contextLe : ContextIndex -> ContextIndex -> Prop
  contextLe_refl : ∀ i : ContextIndex, contextLe i i
  contextLe_trans :
    ∀ {i j k : ContextIndex}, contextLe i j -> contextLe j k -> contextLe i k
  contextLe_antisymm :
    ∀ {i j : ContextIndex}, contextLe i j -> contextLe j i -> i = j
  contextLe_sound :
    ∀ {i j : ContextIndex}, contextLe i j -> S.contextPreorder.le (context i) (context j)
  contextMeet : ContextIndex -> ContextIndex -> ContextIndex
  contextMeet_le_left : ∀ i j : ContextIndex, contextLe (contextMeet i j) i
  contextMeet_le_right : ∀ i j : ContextIndex, contextLe (contextMeet i j) j
  context_le_meet :
    ∀ {i j k : ContextIndex}, contextLe k i -> contextLe k j ->
      contextLe k (contextMeet i j)
  base : S.category
  cover : AATCoverageFamily S.requirements S.overlap base
  finiteCoverIndex : Finite cover.Index
  nerveSimplex : Nat -> Type u
  finiteNerveSimplex : ∀ n : Nat, Finite (nerveSimplex n)
  simplexIndices : ∀ n : Nat, nerveSimplex n -> Fin (n + 1) -> cover.Index
  simplexOverlap : ∀ n : Nat, nerveSimplex n -> ArchCtx A
  simplexOverlap_le_patch :
    ∀ (n : Nat) (simplex : nerveSimplex n) (k : Fin (n + 1)),
      S.contextPreorder.le (simplexOverlap n simplex)
        (cover.patch (simplexIndices n simplex k))
  adequacyRequirements : UAdequacyRequirements S.contextPreorder S.requirements
  coverAdequate : UAdequateCover adequacyRequirements cover
  coefficient : AATPresheaf S

namespace FinitePosetAATSiteRegime

/-- II.定義7.2B: the selected context poset is finite. -/
theorem context_index_finite {U : AtomCarrier.{u}} {A : ArchitectureObject U}
    {S : AATSite A} (K : FinitePosetAATSiteRegime S) :
    Finite K.ContextIndex :=
  K.finiteContextIndex

/-- II.定義7.2B: selected context order maps into the site preorder. -/
theorem selected_context_le_sound {U : AtomCarrier.{u}} {A : ArchitectureObject U}
    {S : AATSite A} (K : FinitePosetAATSiteRegime S)
    {i j : K.ContextIndex} (h : K.contextLe i j) :
    S.contextPreorder.le (K.context i) (K.context j) :=
  K.contextLe_sound h

/-- II.定義7.2B: selected context order is antisymmetric. -/
theorem selected_context_le_antisymm {U : AtomCarrier.{u}} {A : ArchitectureObject U}
    {S : AATSite A} (K : FinitePosetAATSiteRegime S)
    {i j : K.ContextIndex} (hij : K.contextLe i j) (hji : K.contextLe j i) :
    i = j :=
  K.contextLe_antisymm hij hji

/-- II.定義7.2B: the selected cover is finite. -/
theorem cover_index_finite {U : AtomCarrier.{u}} {A : ArchitectureObject U}
    {S : AATSite A} (K : FinitePosetAATSiteRegime S) :
    Finite K.cover.Index :=
  K.finiteCoverIndex

/-- II.定義7.2B: the regime remembers a `U`-adequate cover. -/
theorem cover_is_uAdequate {U : AtomCarrier.{u}} {A : ArchitectureObject U}
    {S : AATSite A} (K : FinitePosetAATSiteRegime S) :
    UAdequateCover K.adequacyRequirements K.cover :=
  K.coverAdequate

end FinitePosetAATSiteRegime

/--
II.定義7.2B / 7.2C: an `n`-simplex of the cover nerve.

The simplex is represented by `n+1` selected cover indices and an explicit
overlap context mapping to every selected patch.
-/
abbrev FinitePosetCechSimplex {U : AtomCarrier.{u}} {A : ArchitectureObject U}
    {S : AATSite A} (K : FinitePosetAATSiteRegime S) (n : Nat) :=
  K.nerveSimplex n

namespace FinitePosetCechSimplex

/-- II.定義7.2B: the cover indices selected by a simplex. -/
def indices {U : AtomCarrier.{u}} {A : ArchitectureObject U}
    {S : AATSite A} {K : FinitePosetAATSiteRegime S} {n : Nat}
    (simplex : FinitePosetCechSimplex K n) :
    Fin (n + 1) -> K.cover.Index :=
  K.simplexIndices n simplex

/-- II.定義7.2B: the explicit overlap context of a simplex. -/
def overlap {U : AtomCarrier.{u}} {A : ArchitectureObject U}
    {S : AATSite A} {K : FinitePosetAATSiteRegime S} {n : Nat}
    (simplex : FinitePosetCechSimplex K n) : ArchCtx A :=
  K.simplexOverlap n simplex

/-- II.定義7.2B: the overlap context maps to every selected patch. -/
theorem overlap_le_patch {U : AtomCarrier.{u}} {A : ArchitectureObject U}
    {S : AATSite A} {K : FinitePosetAATSiteRegime S} {n : Nat}
    (simplex : FinitePosetCechSimplex K n) (k : Fin (n + 1)) :
    S.contextPreorder.le simplex.overlap (K.cover.patch (simplex.indices k)) :=
  K.simplexOverlap_le_patch n simplex k

/-- II.命題7.2C: the finite cover regime has finitely many selected simplices. -/
theorem finite {U : AtomCarrier.{u}} {A : ArchitectureObject U}
    {S : AATSite A} (K : FinitePosetAATSiteRegime S) (n : Nat) :
    Finite (FinitePosetCechSimplex K n) := by
  exact K.finiteNerveSimplex n

end FinitePosetCechSimplex

/-- II.定義7.2C: finite-poset cover-relative Čech `n`-cochains. -/
abbrev FinitePosetCechCochain {U : AtomCarrier.{u}} {A : ArchitectureObject U}
    {S : AATSite A} (K : FinitePosetAATSiteRegime S) (M : Type u) (n : Nat) :=
  FinitePosetCechSimplex K n -> M

/-- II.定義7.2C: the zero cochain in a coefficient type with zero. -/
def FinitePosetCechZeroCochain {U : AtomCarrier.{u}} {A : ArchitectureObject U}
    {S : AATSite A} (K : FinitePosetAATSiteRegime S) (M : Type u) [Zero M]
    (n : Nat) : FinitePosetCechCochain K M n :=
  fun _ => 0

/--
II.定義7.2C: finite-poset cover-relative Čech complex vocabulary.

The differential is explicit data. This file does not assert that this
cover-relative complex computes sheaf cohomology.
-/
structure FinitePosetCechComplex {U : AtomCarrier.{u}} {A : ArchitectureObject U}
    {S : AATSite A} (K : FinitePosetAATSiteRegime S) (M : Type u) [Zero M] where
  differential :
    ∀ n : Nat, FinitePosetCechCochain K M n -> FinitePosetCechCochain K M (n + 1)
  differential_zero :
    ∀ n : Nat, differential n (FinitePosetCechZeroCochain K M n) =
      FinitePosetCechZeroCochain K M (n + 1)

/--
II.定義7.2C: `C^n = 0` in the finite cover-relative vocabulary.

Because the present R9 surface is type-valued and cover-relative, vanishing is
recorded as subsingleton cochains in the selected degree.
-/
def FinitePosetCechCochainsVanish {U : AtomCarrier.{u}}
    {A : ArchitectureObject U} {S : AATSite A}
    (K : FinitePosetAATSiteRegime S) (M : Type u) (n : Nat) : Prop :=
  Subsingleton (FinitePosetCechCochain K M n)

/-- II.定義7.2C: `H^n = 0` in the same finite cover-relative vocabulary. -/
def FinitePosetCechCohomologyVanishes {U : AtomCarrier.{u}}
    {A : ArchitectureObject U} {S : AATSite A}
    (K : FinitePosetAATSiteRegime S) (M : Type u) (n : Nat) : Prop :=
  FinitePosetCechCochainsVanish K M n

/--
II.定義7.2C: the cover nerve has dimension at most `d`.

This is the finite-poset form of the dimension bound: no selected `n`-simplex
exists for `d < n`.
-/
def FinitePosetNerveDimension {U : AtomCarrier.{u}} {A : ArchitectureObject U}
    {S : AATSite A} (K : FinitePosetAATSiteRegime S) (d : Nat) : Prop :=
  ∀ {n : Nat}, d < n -> IsEmpty (FinitePosetCechSimplex K n)

/-- II.命題7.2C: the finite Čech complex has finitely many degree-`n` summands. -/
theorem finitePosetCechComplex_finite {U : AtomCarrier.{u}}
    {A : ArchitectureObject U} {S : AATSite A}
    (K : FinitePosetAATSiteRegime S) (n : Nat) :
    Finite (FinitePosetCechSimplex K n) :=
  FinitePosetCechSimplex.finite K n

/--
II.命題7.2C: above the nerve dimension, the selected Čech cochains vanish.
-/
theorem finitePosetCechCochains_vanish_above_nerveDimension
    {U : AtomCarrier.{u}} {A : ArchitectureObject U} {S : AATSite A}
    (K : FinitePosetAATSiteRegime S) (M : Type u) {d n : Nat}
    (hdim : FinitePosetNerveDimension K d) (hn : d < n) :
    FinitePosetCechCochainsVanish K M n := by
  letI : IsEmpty (FinitePosetCechSimplex K n) := hdim hn
  change Subsingleton (FinitePosetCechCochain K M n)
  exact inferInstance

/--
II.命題7.2C: above the nerve dimension, the finite cover-relative
cohomology vocabulary vanishes.
-/
theorem finitePosetCechCohomology_vanishes_above_nerveDimension
    {U : AtomCarrier.{u}} {A : ArchitectureObject U} {S : AATSite A}
    (K : FinitePosetAATSiteRegime S) (M : Type u) [Zero M]
    (_complex : FinitePosetCechComplex K M) {d n : Nat}
    (hdim : FinitePosetNerveDimension K d) (hn : d < n) :
    FinitePosetCechCohomologyVanishes K M n :=
  finitePosetCechCochains_vanish_above_nerveDimension K M hdim hn

end Site
end AAT.AG
