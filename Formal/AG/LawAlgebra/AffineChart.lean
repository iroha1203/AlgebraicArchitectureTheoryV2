import Formal.AG.LawAlgebra.Nullstellensatz
import Formal.AG.LawAlgebra.StandardScheme
import Formal.AG.LawAlgebra.StructuralRelation
import Mathlib.CategoryTheory.ConcreteCategory.EpiMono

noncomputable section

namespace AAT.AG
namespace LawAlgebra

universe u v w x

open CategoryTheory MvPolynomial Opposite

namespace AffineChart

set_option linter.unusedSectionVars false

variable (k : Type u) [CommRing k]

/--
III.定義8.1: decoration attached to the ordinary affine spectrum.

The underlying space remains `PrimeSpectrum A`; AAT-specific readings are
recorded in the decoration fields instead of replacing the spectrum theory.
-/
structure SpecAAT (A : Type v) [CommRing A] [Algebra k A] where
  Decoration : Type w
  decoration : Decoration
  obstructionIdeal : Ideal A

namespace SpecAAT

/-- III.定義8.1: the underlying ordinary affine spectrum. -/
abbrev pointSpace {A : Type v} [CommRing A] [Algebra k A] (_X : SpecAAT k A) :=
  PrimeSpectrum A

/-- III.定義8.5: local lawful chart `V(I_Ob^U(W)) ⊆ Spec_AAT`. -/
def localLawfulChart {A : Type v} [CommRing A] [Algebra k A] (X : SpecAAT k A) :
    Set (PrimeSpectrum A) :=
  PrimeSpectrum.zeroLocus X.obstructionIdeal

end SpecAAT

/-- III.定義8.2: an affine AAT chart with its chosen coordinate algebra. -/
structure AffineAATChart where
  AlgebraCarrier : Type v
  commRing : CommRing AlgebraCarrier
  algebra : Algebra k AlgebraCarrier
  spec : SpecAAT k AlgebraCarrier

attribute [instance] AffineAATChart.commRing AffineAATChart.algebra

namespace AffineAATChart

/-- III.定義8.2: `R`-valued local configuration functor `h_W^U(R)`. -/
def hWU (C : AffineAATChart k) (R : Type w) [CommRing R] [Algebra k R] :=
  C.AlgebraCarrier →ₐ[k] R

/--
III.定理8.3: selected raw algebra hom surface.

This keeps the older chart API available: for an arbitrary selected affine
chart, `h_W^U(R)` is the chosen `k`-algebra hom surface from the chart algebra.
The coordinate-assignment / structural-relation quotient theorem is
`rawQuotientRepresentability`.
-/
def rawAffineChartRepresentability (C : AffineAATChart k)
    (R : Type w) [CommRing R] [Algebra k R] :
    hWU k C R ≃ (C.AlgebraCarrier →ₐ[k] R) :=
  Equiv.refl _

/--
III.定義8.2 / 定理8.3: a raw affine presentation by typed coordinates and
structural relations.

The selected chart algebra is related to the structural quotient
`FreeTypedCommAlg F k ⧸ J_struct(W)`. This package is intentionally explicit:
it does not assert any scheme-level gluing or sheafification theorem.
-/
structure RawAffinePresentation (k : Type u) [CommRing k]
    {U : AtomCarrier.{v}} {A : ArchitectureObject U}
    {W : Site.ArchitectureContext A} (F : CoordinateFamily W)
    (C : AffineAATChart k) where
  relations : StructuralRelationFamily F k
  rawComparison : C.AlgebraCarrier ≃ₐ[k] relations.RawAmbientLawAlgebra

namespace RawAffinePresentation

variable {k : Type u} [CommRing k]
variable {U : AtomCarrier.{v}} {A : ArchitectureObject U}
variable {W : Site.ArchitectureContext A} {F : CoordinateFamily W}
variable {C : AffineAATChart k}

/-- III.定義8.2: typed coordinate assignment into a coefficient algebra. -/
abbrev CoordinateAssignment (_P : RawAffinePresentation k F C)
    (R : Type w) [CommRing R] [Algebra k R] :=
  F.CoordX -> R

/-- III.定義8.2: evaluation hom induced by an assignment of coordinates. -/
def assignmentAlgHom (P : RawAffinePresentation k F C)
    {R : Type w} [CommRing R] [Algebra k R]
    (a : P.CoordinateAssignment R) :
    FreeTypedCommAlg F k →ₐ[k] R :=
  MvPolynomial.aeval a

/-- III.定義8.2: coordinate variables evaluate to their assigned values. -/
theorem assignmentAlgHom_X (P : RawAffinePresentation k F C)
    {R : Type w} [CommRing R] [Algebra k R]
    (a : P.CoordinateAssignment R) (c : F.CoordX) :
    P.assignmentAlgHom a (MvPolynomial.X c) = a c := by
  simp [assignmentAlgHom]

/--
III.定義8.2: an `R`-valued configuration satisfies all structural relations
when each selected relation polynomial evaluates to zero.
-/
def SatisfiesStructuralRelations (P : RawAffinePresentation k F C)
    {R : Type w} [CommRing R] [Algebra k R]
    (a : P.CoordinateAssignment R) : Prop :=
  ∀ r : P.relations.Relation, P.assignmentAlgHom a (P.relations.polynomial r) = 0

/--
III.定義8.2: `h_W^U(R)` as typed coordinate assignments satisfying structural
relations.
-/
def hWUConfiguration (P : RawAffinePresentation k F C)
    (R : Type w) [CommRing R] [Algebra k R] :=
  P.relations.Configuration R

/-- III.定理8.3: relation satisfaction kills the whole structural ideal. -/
theorem assignmentAlgHom_eq_zero_of_mem_JStruct (P : RawAffinePresentation k F C)
    {R : Type w} [CommRing R] [Algebra k R]
    {a : P.CoordinateAssignment R} (ha : P.SatisfiesStructuralRelations a)
    {p : FreeTypedCommAlg F k} (hp : p ∈ P.relations.JStruct) :
    P.assignmentAlgHom a p = 0 := by
  exact P.relations.configurationAlgHom_eq_zero_of_mem_JStruct ⟨a, ha⟩ hp

/--
III.定理8.3: a structural-relation-satisfying assignment descends to the raw
quotient algebra by `Ideal.Quotient.liftₐ`.
-/
def quotientAlgHomOfConfiguration (P : RawAffinePresentation k F C)
    {R : Type w} [CommRing R] [Algebra k R]
    (a : P.hWUConfiguration R) :
    P.relations.RawAmbientLawAlgebra →ₐ[k] R :=
  P.relations.quotientAlgHomOfConfiguration a

/-- III.定理8.3: the descended quotient hom agrees with polynomial evaluation. -/
theorem quotientAlgHomOfConfiguration_mk (P : RawAffinePresentation k F C)
    {R : Type w} [CommRing R] [Algebra k R]
    (a : P.hWUConfiguration R) (p : FreeTypedCommAlg F k) :
    P.quotientAlgHomOfConfiguration a (P.relations.quotientMap p) =
      P.assignmentAlgHom a.1 p := by
  exact P.relations.quotientAlgHomOfConfiguration_mk a p

/-- III.定理8.3: recover a coordinate assignment from a raw quotient hom. -/
def configurationOfQuotientAlgHom (P : RawAffinePresentation k F C)
    {R : Type w} [CommRing R] [Algebra k R]
    (f : P.relations.RawAmbientLawAlgebra →ₐ[k] R) :
    P.hWUConfiguration R :=
  P.relations.configurationOfQuotientAlgHom f

/--
III.定理8.3: raw quotient representability.

Typed coordinate assignments satisfying structural relations are equivalent to
`k`-algebra homomorphisms out of the raw structural quotient.
-/
def rawQuotientRepresentability (P : RawAffinePresentation k F C)
    (R : Type w) [CommRing R] [Algebra k R] :
    P.hWUConfiguration R ≃ (P.relations.RawAmbientLawAlgebra →ₐ[k] R) :=
  P.relations.configurationRepresentability R

/-- SD7 contract: the legacy raw quotient API is definitionally the generic core. -/
theorem rawQuotientRepresentability_eq_generic (P : RawAffinePresentation k F C)
    (R : Type w) [CommRing R] [Algebra k R] :
    P.rawQuotientRepresentability R =
      P.relations.configurationRepresentability R :=
  rfl

/--
III.定理8.3: comparison with the older selected chart hom surface.

Under a selected comparison between the chart algebra and the raw quotient,
the typed-configuration representability reads as `h_W^U(R)`.
-/
def hWUConfigurationRepresentability (P : RawAffinePresentation k F C)
    (R : Type w) [CommRing R] [Algebra k R] :
    P.hWUConfiguration R ≃ hWU k C R :=
  (P.rawQuotientRepresentability R).trans
    { toFun := fun f => f.comp P.rawComparison.toAlgHom
      invFun := fun f => f.comp P.rawComparison.symm.toAlgHom
      left_inv := by
        intro f
        apply AlgHom.ext
        intro x
        simp
      right_inv := by
        intro f
        apply AlgHom.ext
        intro x
        simp }

end RawAffinePresentation

/-! ### SD7 canonical sheafification-unit representability -/

/--
SD7 / Assumption 8.4: the strong case in which the canonical sheafification unit at `W` is an
isomorphism. This proposition contains no independently selected algebra comparison or free
decoration / obstruction condition.
-/
structure SheafifiedChartPresentation
    {U : AtomCarrier.{u}} {A : ArchitectureObject U}
    {S : Site.AATSite A} {k : Type v} [CommRing k]
    (raw : RawAmbientRestrictionSystem S k)
    [CategoryTheory.HasSheafify S.topology (AATCommAlgCat k)]
    (W : S.category) : Prop where
  canonical_isIso :
    CategoryTheory.IsIso (raw.toRingedSite.canonical.app (op W))

/--
SD7 canonical comparison from sheafified sections back to the raw quotient. It is obtained by
turning the canonical unit itself into an algebra equivalence and taking its inverse.
-/
noncomputable def SheafifiedChartPresentation.comparison
    {U : AtomCarrier.{u}} {A : ArchitectureObject U}
    {S : Site.AATSite A} {k : Type v} [CommRing k]
    {raw : RawAmbientRestrictionSystem S k}
    [CategoryTheory.HasSheafify S.topology (AATCommAlgCat k)]
    {W : S.category} (P : SheafifiedChartPresentation raw W) :
    SheafifiedSectionRing raw W ≃ₐ[k] raw.rawAlgebra W := by
  let unit := raw.toRingedSite.canonical.app (op W)
  letI : CategoryTheory.IsIso unit := P.canonical_isIso
  exact (AlgEquiv.ofBijective (sheafificationUnitAlgHom raw W) (by
    change Function.Bijective unit.right
    exact CategoryTheory.ConcreteCategory.bijective_of_isIso unit.right)).symm

/-- SD7 provenance equation: the inverse comparison is exactly the canonical unit. -/
@[simp] theorem SheafifiedChartPresentation.comparison_symm_toAlgHom
    {U : AtomCarrier.{u}} {A : ArchitectureObject U}
    {S : Site.AATSite A} {k : Type v} [CommRing k]
    {raw : RawAmbientRestrictionSystem S k}
    [CategoryTheory.HasSheafify S.topology (AATCommAlgCat k)]
    {W : S.category} (P : SheafifiedChartPresentation raw W) :
    P.comparison.symm.toAlgHom = sheafificationUnitAlgHom raw W := by
  simp [SheafifiedChartPresentation.comparison]

/--
SD7 / Theorem 8.3 under Assumption 8.4: representability by the actual sheafified section ring.
The construction composes the generic local equivalence with the canonical-unit comparison.
-/
noncomputable def sheafifiedChartRepresentability
    {U : AtomCarrier.{u}} {A : ArchitectureObject U}
    {S : Site.AATSite A} {k : Type v} [CommRing k]
    {raw : RawAmbientRestrictionSystem S k}
    [CategoryTheory.HasSheafify S.topology (AATCommAlgCat k)]
    {W : S.category} (P : SheafifiedChartPresentation raw W)
    (R : Type w) [CommRing R] [Algebra k R] :
    raw.LocalConfiguration W R ≃
      (SheafifiedSectionRing raw W →ₐ[k] R) :=
  (raw.localConfigurationRepresentability W R).trans {
    toFun := fun f => f.comp P.comparison.toAlgHom
    invFun := fun f => f.comp P.comparison.symm.toAlgHom
    left_inv := by
      intro f
      apply AlgHom.ext
      intro x
      simp
    right_inv := by
      intro f
      apply AlgHom.ext
      intro x
      simp }

/-- SD7 forward computation rule for sheafified chart representability. -/
@[simp] theorem sheafifiedChartRepresentability_apply
    {U : AtomCarrier.{u}} {A : ArchitectureObject U}
    {S : Site.AATSite A} {k : Type v} [CommRing k]
    {raw : RawAmbientRestrictionSystem S k}
    [CategoryTheory.HasSheafify S.topology (AATCommAlgCat k)]
    {W : S.category} (P : SheafifiedChartPresentation raw W)
    (R : Type w) [CommRing R] [Algebra k R]
    (a : raw.LocalConfiguration W R) :
    sheafifiedChartRepresentability P R a =
      (raw.localConfigurationRepresentability W R a).comp
        P.comparison.toAlgHom :=
  rfl

/-- SD7 inverse computation rule for sheafified chart representability. -/
@[simp] theorem sheafifiedChartRepresentability_symm_apply
    {U : AtomCarrier.{u}} {A : ArchitectureObject U}
    {S : Site.AATSite A} {k : Type v} [CommRing k]
    {raw : RawAmbientRestrictionSystem S k}
    [CategoryTheory.HasSheafify S.topology (AATCommAlgCat k)]
    {W : S.category} (P : SheafifiedChartPresentation raw W)
    (R : Type w) [CommRing R] [Algebra k R]
    (f : SheafifiedSectionRing raw W →ₐ[k] R) :
    (sheafifiedChartRepresentability P R).symm f =
      (raw.localConfigurationRepresentability W R).symm
        (f.comp P.comparison.symm.toAlgHom) :=
  rfl

/-- SD7 naturality of sheafified chart representability in the target algebra. -/
theorem sheafifiedChartRepresentability_natural
    {U : AtomCarrier.{u}} {A : ArchitectureObject U}
    {S : Site.AATSite A} {k : Type v} [CommRing k]
    {raw : RawAmbientRestrictionSystem S k}
    [CategoryTheory.HasSheafify S.topology (AATCommAlgCat k)]
    {W : S.category} (P : SheafifiedChartPresentation raw W)
    {R : Type w} {T : Type x} [CommRing R] [Algebra k R]
    [CommRing T] [Algebra k T]
    (g : R →ₐ[k] T) (a : raw.LocalConfiguration W R) :
    sheafifiedChartRepresentability P T (a.map g) =
      g.comp (sheafifiedChartRepresentability P R a) := by
  rw [sheafifiedChartRepresentability_apply,
    RawAmbientRestrictionSystem.localConfigurationRepresentability_natural,
    sheafifiedChartRepresentability_apply, AlgHom.comp_assoc]

end AffineAATChart

end AffineChart

end LawAlgebra
end AAT.AG
