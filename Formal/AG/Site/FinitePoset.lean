import Formal.AG.Site.Descent

namespace AAT.AG
namespace Site

universe u

open CategoryTheory
open Opposite

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

/-- II.定義7.2C: the overlap object attached to a selected nerve simplex. -/
def FinitePosetCechOverlapObject {U : AtomCarrier.{u}} {A : ArchitectureObject U}
    {S : AATSite A} (K : FinitePosetAATSiteRegime S) (n : Nat)
    (simplex : FinitePosetCechSimplex K n) : S.category :=
  ContextCategoryObject.of S.contextPreorder (K.simplexOverlap n simplex)

/--
II.定義7.2C: the coefficient section read on an explicit nonempty
`(n+1)`-fold overlap.
-/
abbrev FinitePosetCechSection {U : AtomCarrier.{u}} {A : ArchitectureObject U}
    {S : AATSite A} (K : FinitePosetAATSiteRegime S) (n : Nat)
    (simplex : FinitePosetCechSimplex K n) : Type u :=
  K.coefficient.obj (op (FinitePosetCechOverlapObject K n simplex))

/--
II.定義7.2C: finite-poset cover-relative Čech `n`-cochains.

This is the selected finite product over nonempty `(n+1)`-fold overlaps:
each simplex is assigned a section of the coefficient presheaf on its explicit
overlap context.
-/
abbrev FinitePosetCechCochain {U : AtomCarrier.{u}} {A : ArchitectureObject U}
    {S : AATSite A} (K : FinitePosetAATSiteRegime S) (n : Nat) :=
  ∀ simplex : FinitePosetCechSimplex K n, FinitePosetCechSection K n simplex

/--
II.定義7.2C: face data for the selected finite nerve.

A face of an `(n+2)`-fold overlap is an `(n+1)`-fold overlap, and the
larger overlap maps to that face so the coefficient presheaf can restrict
sections along the corresponding context morphism.
-/
structure FinitePosetCechFaceData {U : AtomCarrier.{u}} {A : ArchitectureObject U}
    {S : AATSite A} (K : FinitePosetAATSiteRegime S) where
  face :
    ∀ n : Nat, FinitePosetCechSimplex K (n + 1) -> Fin (n + 2) ->
      FinitePosetCechSimplex K n
  faceOverlap_le :
    ∀ (n : Nat) (simplex : FinitePosetCechSimplex K (n + 1)) (i : Fin (n + 2)),
      S.contextPreorder.le (K.simplexOverlap (n + 1) simplex)
        (K.simplexOverlap n (face n simplex i))

/-- II.定義7.2C: restrict one face section to the larger selected overlap. -/
def FinitePosetCechFaceRestriction {U : AtomCarrier.{u}} {A : ArchitectureObject U}
    {S : AATSite A} {K : FinitePosetAATSiteRegime S}
    (D : FinitePosetCechFaceData K) {n : Nat}
    (cochain : FinitePosetCechCochain K n)
    (simplex : FinitePosetCechSimplex K (n + 1)) (i : Fin (n + 2)) :
    FinitePosetCechSection K (n + 1) simplex :=
  K.coefficient.map (homOfLE (D.faceOverlap_le n simplex i)).op
    (cochain (D.face n simplex i))

/--
II.定義7.2C: additive surface for the selected coefficient sections.

The actual coefficient object may be a module-valued presheaf in later layers.
Here the finite cover-relative surface only needs a zero section and a selected
finite alternating-combination operator on the face restrictions.
-/
structure FinitePosetCechAdditiveData {U : AtomCarrier.{u}} {A : ArchitectureObject U}
    {S : AATSite A} (K : FinitePosetAATSiteRegime S) where
  zeroSection :
    ∀ n : Nat, (simplex : FinitePosetCechSimplex K n) ->
      FinitePosetCechSection K n simplex
  combineFaces :
    ∀ n : Nat, (simplex : FinitePosetCechSimplex K (n + 1)) ->
      (Fin (n + 2) -> FinitePosetCechSection K (n + 1) simplex) ->
        FinitePosetCechSection K (n + 1) simplex
  combineFaces_zero :
    ∀ (n : Nat) (simplex : FinitePosetCechSimplex K (n + 1)),
      combineFaces n simplex (fun _ => zeroSection (n + 1) simplex) =
        zeroSection (n + 1) simplex

/-- II.定義7.2C: the zero cochain in the selected coefficient sections. -/
def FinitePosetCechZeroCochain {U : AtomCarrier.{u}} {A : ArchitectureObject U}
    {S : AATSite A} {K : FinitePosetAATSiteRegime S}
    (Z : FinitePosetCechAdditiveData K) (n : Nat) :
    FinitePosetCechCochain K n :=
  fun simplex => Z.zeroSection n simplex

/--
II.定義7.2C: finite-poset cover-relative Čech complex.

The differential is not arbitrary data: it is required to be the selected
finite alternating combination of the coefficient restriction maps along the
face inclusions, and it records `d ∘ d = 0`.
-/
structure FinitePosetCechComplex {U : AtomCarrier.{u}} {A : ArchitectureObject U}
    {S : AATSite A} (K : FinitePosetAATSiteRegime S) where
  additive : FinitePosetCechAdditiveData K
  faces : FinitePosetCechFaceData K
  differential :
    ∀ n : Nat, FinitePosetCechCochain K n -> FinitePosetCechCochain K (n + 1)
  differential_eq_restrictions :
    ∀ (n : Nat) (cochain : FinitePosetCechCochain K n)
      (simplex : FinitePosetCechSimplex K (n + 1)),
      differential n cochain simplex =
        additive.combineFaces n simplex
          (fun i => FinitePosetCechFaceRestriction faces cochain simplex i)
  differential_zero :
    ∀ n : Nat, differential n (FinitePosetCechZeroCochain additive n) =
      FinitePosetCechZeroCochain additive (n + 1)
  differential_comp_zero :
    ∀ (n : Nat) (cochain : FinitePosetCechCochain K n),
      differential (n + 1) (differential n cochain) =
        FinitePosetCechZeroCochain additive (n + 2)

namespace FinitePosetCechComplex

/-- II.定義7.2C: the differential is built from face restrictions. -/
theorem differential_from_restrictions {U : AtomCarrier.{u}} {A : ArchitectureObject U}
    {S : AATSite A} {K : FinitePosetAATSiteRegime S}
    (C : FinitePosetCechComplex K) (n : Nat)
    (cochain : FinitePosetCechCochain K n)
    (simplex : FinitePosetCechSimplex K (n + 1)) :
    C.differential n cochain simplex =
      C.additive.combineFaces n simplex
        (fun i => FinitePosetCechFaceRestriction C.faces cochain simplex i) :=
  C.differential_eq_restrictions n cochain simplex

/-- II.定義7.2C: the selected Čech differential squares to zero. -/
theorem differential_comp {U : AtomCarrier.{u}} {A : ArchitectureObject U}
    {S : AATSite A} {K : FinitePosetAATSiteRegime S}
    (C : FinitePosetCechComplex K) (n : Nat)
    (cochain : FinitePosetCechCochain K n) :
    C.differential (n + 1) (C.differential n cochain) =
      FinitePosetCechZeroCochain C.additive (n + 2) :=
  C.differential_comp_zero n cochain

end FinitePosetCechComplex

/-- II.定義7.2C: cocycles are the kernel of the selected Čech differential. -/
def FinitePosetCechCocycle {U : AtomCarrier.{u}} {A : ArchitectureObject U}
    {S : AATSite A} {K : FinitePosetAATSiteRegime S}
    (C : FinitePosetCechComplex K) (n : Nat) :=
  {cochain : FinitePosetCechCochain K n //
    C.differential n cochain = FinitePosetCechZeroCochain C.additive (n + 1)}

/-- II.定義7.2C: the zero cocycle in each selected degree. -/
def FinitePosetCechZeroCocycle {U : AtomCarrier.{u}} {A : ArchitectureObject U}
    {S : AATSite A} {K : FinitePosetAATSiteRegime S}
    (C : FinitePosetCechComplex K) (n : Nat) :
    FinitePosetCechCocycle C n :=
  ⟨FinitePosetCechZeroCochain C.additive n, C.differential_zero n⟩

/-- II.定義7.2C: a differential image, viewed as a cocycle by `d ∘ d = 0`. -/
def FinitePosetCechBoundaryCocycle {U : AtomCarrier.{u}} {A : ArchitectureObject U}
    {S : AATSite A} {K : FinitePosetAATSiteRegime S}
    (C : FinitePosetCechComplex K) (n : Nat)
    (cochain : FinitePosetCechCochain K n) :
    FinitePosetCechCocycle C (n + 1) :=
  ⟨C.differential n cochain, C.differential_comp_zero n cochain⟩

/--
II.定義7.2C: the image part of the finite selected kernel/image vocabulary.

Degree zero has no predecessor in this finite Nat-indexed surface. In positive
degree `n+1`, a cocycle is a coboundary exactly when its underlying cochain is
the differential of a selected degree-`n` cochain.
-/
def FinitePosetCechBoundaryImage {U : AtomCarrier.{u}}
    {A : ArchitectureObject U} {S : AATSite A} {K : FinitePosetAATSiteRegime S}
    (C : FinitePosetCechComplex K) :
    (n : Nat) -> FinitePosetCechCocycle C n -> Prop
  | 0, _ => False
  | n + 1, cocycle =>
      ∃ cochain : FinitePosetCechCochain K n,
        cocycle.1 = C.differential n cochain

/-- II.定義7.2C: every differential image lies in the boundary image predicate. -/
theorem FinitePosetCechBoundaryCocycle_mem_image {U : AtomCarrier.{u}}
    {A : ArchitectureObject U} {S : AATSite A} {K : FinitePosetAATSiteRegime S}
    (C : FinitePosetCechComplex K) (n : Nat)
    (cochain : FinitePosetCechCochain K n) :
    FinitePosetCechBoundaryImage C (n + 1)
      (FinitePosetCechBoundaryCocycle C n cochain) :=
  ⟨cochain, rfl⟩

/--
II.定義7.2C: selected kernel/image quotient relation on cocycles.

The relation is explicit because this file works with Type-valued coefficient
presheaves rather than a global abelian-group-valued coefficient theory. It is
nevertheless tied to the complex: every cocycle in the previous differential
image must become equivalent to the zero cocycle.
-/
structure FinitePosetCechCoboundaryRelation {U : AtomCarrier.{u}}
    {A : ArchitectureObject U} {S : AATSite A} {K : FinitePosetAATSiteRegime S}
    (C : FinitePosetCechComplex K) (n : Nat) where
  related : FinitePosetCechCocycle C n -> FinitePosetCechCocycle C n -> Prop
  refl : ∀ cocycle, related cocycle cocycle
  symm : ∀ {left right}, related left right -> related right left
  trans : ∀ {left mid right}, related left mid -> related mid right -> related left right
  kills_image :
    ∀ {cocycle : FinitePosetCechCocycle C n},
      FinitePosetCechBoundaryImage C n cocycle ->
        related (FinitePosetCechZeroCocycle C n) cocycle

namespace FinitePosetCechCoboundaryRelation

/--
II.定義7.2C: the selected quotient relation kills every differential image.
-/
theorem kills_differential_image {U : AtomCarrier.{u}}
    {A : ArchitectureObject U} {S : AATSite A} {K : FinitePosetAATSiteRegime S}
    {C : FinitePosetCechComplex K} {n : Nat}
    (R : FinitePosetCechCoboundaryRelation C n)
    {cocycle : FinitePosetCechCocycle C n}
    (himage : FinitePosetCechBoundaryImage C n cocycle) :
    R.related (FinitePosetCechZeroCocycle C n) cocycle :=
  R.kills_image himage

/--
II.定義7.2C: the selected quotient relation kills each concrete differential
image cocycle.
-/
theorem kills_boundary_cocycle {U : AtomCarrier.{u}}
    {A : ArchitectureObject U} {S : AATSite A} {K : FinitePosetAATSiteRegime S}
    {C : FinitePosetCechComplex K} {n : Nat}
    (R : FinitePosetCechCoboundaryRelation C (n + 1))
    (cochain : FinitePosetCechCochain K n) :
    R.related (FinitePosetCechZeroCocycle C (n + 1))
      (FinitePosetCechBoundaryCocycle C n cochain) :=
  R.kills_differential_image
    (FinitePosetCechBoundaryCocycle_mem_image C n cochain)

end FinitePosetCechCoboundaryRelation

/-- II.定義7.2C: setoid quotient by the selected image-killing relation. -/
def FinitePosetCechCoboundarySetoid {U : AtomCarrier.{u}}
    {A : ArchitectureObject U} {S : AATSite A} {K : FinitePosetAATSiteRegime S}
    {C : FinitePosetCechComplex K} {n : Nat}
    (R : FinitePosetCechCoboundaryRelation C n) :
    Setoid (FinitePosetCechCocycle C n) where
  r := R.related
  iseqv := ⟨R.refl, R.symm, R.trans⟩

/-- II.定義7.2C: finite selected cover-relative Čech cohomology. -/
abbrev FinitePosetCechCohomology {U : AtomCarrier.{u}}
    {A : ArchitectureObject U} {S : AATSite A} {K : FinitePosetAATSiteRegime S}
    (C : FinitePosetCechComplex K) (n : Nat)
    (R : FinitePosetCechCoboundaryRelation C n) :=
  Quotient (FinitePosetCechCoboundarySetoid R)

/--
II.定義7.2C: `C^n = 0` in the finite cover-relative vocabulary.

Vanishing is recorded as a subsingleton finite product of coefficient sections
on selected nonempty overlaps.
-/
def FinitePosetCechCochainsVanish {U : AtomCarrier.{u}}
    {A : ArchitectureObject U} {S : AATSite A}
    (K : FinitePosetAATSiteRegime S) (n : Nat) : Prop :=
  Subsingleton (FinitePosetCechCochain K n)

/-- II.定義7.2C: `H^n = 0` for the finite selected quotient vocabulary. -/
def FinitePosetCechCohomologyVanishes {U : AtomCarrier.{u}}
    {A : ArchitectureObject U} {S : AATSite A} {K : FinitePosetAATSiteRegime S}
    (C : FinitePosetCechComplex K) (n : Nat)
    (R : FinitePosetCechCoboundaryRelation C n) : Prop :=
  Subsingleton (FinitePosetCechCohomology C n R)

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
    (K : FinitePosetAATSiteRegime S) {d n : Nat}
    (hdim : FinitePosetNerveDimension K d) (hn : d < n) :
    FinitePosetCechCochainsVanish K n := by
  letI : IsEmpty (FinitePosetCechSimplex K n) := hdim hn
  change Subsingleton (FinitePosetCechCochain K n)
  exact inferInstance

/-- II.命題7.2C: above the nerve dimension, the selected cocycles vanish. -/
theorem finitePosetCechCocycles_vanish_above_nerveDimension
    {U : AtomCarrier.{u}} {A : ArchitectureObject U} {S : AATSite A}
    {K : FinitePosetAATSiteRegime S} (C : FinitePosetCechComplex K) {d n : Nat}
    (hdim : FinitePosetNerveDimension K d) (hn : d < n) :
    Subsingleton (FinitePosetCechCocycle C n) := by
  have hcochain : Subsingleton (FinitePosetCechCochain K n) :=
    finitePosetCechCochains_vanish_above_nerveDimension K hdim hn
  refine ⟨?_⟩
  intro left right
  have h : left.1 = right.1 := Subsingleton.elim left.1 right.1
  cases left
  cases right
  simp at h
  cases h
  rfl

/--
II.命題7.2C: above the nerve dimension, the finite cover-relative
Čech cohomology quotient vanishes.
-/
theorem finitePosetCechCohomology_vanishes_above_nerveDimension
    {U : AtomCarrier.{u}} {A : ArchitectureObject U} {S : AATSite A}
    {K : FinitePosetAATSiteRegime S} (C : FinitePosetCechComplex K)
    {d n : Nat} (R : FinitePosetCechCoboundaryRelation C n)
    (hdim : FinitePosetNerveDimension K d) (hn : d < n) :
    FinitePosetCechCohomologyVanishes C n R := by
  have hcocycle : Subsingleton (FinitePosetCechCocycle C n) :=
    finitePosetCechCocycles_vanish_above_nerveDimension C hdim hn
  refine ⟨?_⟩
  intro left right
  refine Quotient.inductionOn₂ left right ?_
  intro leftCocycle rightCocycle
  have h : leftCocycle = rightCocycle := Subsingleton.elim leftCocycle rightCocycle
  cases h
  rfl

end Site
end AAT.AG
