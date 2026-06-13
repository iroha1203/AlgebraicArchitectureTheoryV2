import Formal.AG.LawAlgebra.Nullstellensatz
import Formal.AG.LawAlgebra.StructuralRelation

noncomputable section

namespace AAT.AG
namespace LawAlgebra

universe u v w

open MvPolynomial

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
  { a : P.CoordinateAssignment R // P.SatisfiesStructuralRelations a }

/-- III.定理8.3: relation satisfaction kills the whole structural ideal. -/
theorem assignmentAlgHom_eq_zero_of_mem_JStruct (P : RawAffinePresentation k F C)
    {R : Type w} [CommRing R] [Algebra k R]
    {a : P.CoordinateAssignment R} (ha : P.SatisfiesStructuralRelations a)
    {p : FreeTypedCommAlg F k} (hp : p ∈ P.relations.JStruct) :
    P.assignmentAlgHom a p = 0 := by
  refine Submodule.span_induction ?hset ?hzero ?hadd ?hsmul hp
  · rintro p ⟨r, rfl⟩
    exact ha r
  · simp
  · intro p q _ _ hp hq
    simp [map_add, hp, hq]
  · intro c p _ hp
    simp [hp]

/--
III.定理8.3: a structural-relation-satisfying assignment descends to the raw
quotient algebra by `Ideal.Quotient.liftₐ`.
-/
def quotientAlgHomOfConfiguration (P : RawAffinePresentation k F C)
    {R : Type w} [CommRing R] [Algebra k R]
    (a : P.hWUConfiguration R) :
    P.relations.RawAmbientLawAlgebra →ₐ[k] R :=
  Ideal.Quotient.liftₐ P.relations.JStruct (P.assignmentAlgHom a.1)
    (fun _p hp => P.assignmentAlgHom_eq_zero_of_mem_JStruct a.2 hp)

/-- III.定理8.3: the descended quotient hom agrees with polynomial evaluation. -/
theorem quotientAlgHomOfConfiguration_mk (P : RawAffinePresentation k F C)
    {R : Type w} [CommRing R] [Algebra k R]
    (a : P.hWUConfiguration R) (p : FreeTypedCommAlg F k) :
    P.quotientAlgHomOfConfiguration a (P.relations.quotientMap p) =
      P.assignmentAlgHom a.1 p := by
  rfl

/-- III.定理8.3: recover a coordinate assignment from a raw quotient hom. -/
def configurationOfQuotientAlgHom (P : RawAffinePresentation k F C)
    {R : Type w} [CommRing R] [Algebra k R]
    (f : P.relations.RawAmbientLawAlgebra →ₐ[k] R) :
    P.hWUConfiguration R where
  val c := f (P.relations.quotientMap (MvPolynomial.X c))
  property r := by
    have h :
        P.assignmentAlgHom
            (fun c => f (P.relations.quotientMap (MvPolynomial.X c))) =
          f.comp (Ideal.Quotient.mkₐ k P.relations.JStruct) := by
      apply MvPolynomial.algHom_ext
      intro c
      simp [assignmentAlgHom, StructuralRelationFamily.quotientMap]
    rw [AlgHom.congr_fun h (P.relations.polynomial r)]
    change f (P.relations.quotientMap (P.relations.polynomial r)) = 0
    rw [StructuralRelationFamily.quotientMap_polynomial_eq_zero]
    simp

/--
III.定理8.3: raw quotient representability.

Typed coordinate assignments satisfying structural relations are equivalent to
`k`-algebra homomorphisms out of the raw structural quotient.
-/
def rawQuotientRepresentability (P : RawAffinePresentation k F C)
    (R : Type w) [CommRing R] [Algebra k R] :
    P.hWUConfiguration R ≃ (P.relations.RawAmbientLawAlgebra →ₐ[k] R) where
  toFun := P.quotientAlgHomOfConfiguration
  invFun := P.configurationOfQuotientAlgHom
  left_inv a := by
    apply Subtype.ext
    funext c
    change P.quotientAlgHomOfConfiguration a (P.relations.quotientMap (MvPolynomial.X c)) =
      a.1 c
    rw [P.quotientAlgHomOfConfiguration_mk a (MvPolynomial.X c)]
    simp [assignmentAlgHom]
  right_inv f := by
    apply AlgHom.ext
    intro q
    refine Quotient.inductionOn' q ?_
    intro p
    have h :
        P.assignmentAlgHom (P.configurationOfQuotientAlgHom f).1 =
          f.comp (Ideal.Quotient.mkₐ k P.relations.JStruct) := by
      apply MvPolynomial.algHom_ext
      intro c
      simp [configurationOfQuotientAlgHom, assignmentAlgHom,
        StructuralRelationFamily.quotientMap]
    change P.quotientAlgHomOfConfiguration (P.configurationOfQuotientAlgHom f)
        (P.relations.quotientMap p) = f (P.relations.quotientMap p)
    rw [P.quotientAlgHomOfConfiguration_mk (P.configurationOfQuotientAlgHom f) p]
    exact AlgHom.congr_fun h p

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

/-- III.仮定8.4: selected presentation for a sheafified affine chart. -/
structure SheafifiedChartPresentation (raw sheafified : AffineAATChart k) where
  comparison : sheafified.AlgebraCarrier ≃ₐ[k] raw.AlgebraCarrier
  preservesDecoration : Prop
  preservesObstructionIdeal : Prop

/--
III.定理8.3 / 仮定8.4: representability for the sheafified chart under the
selected presentation package.
-/
def sheafifiedChartRepresentability {raw sheafified : AffineAATChart k}
    (_P : SheafifiedChartPresentation k raw sheafified)
    (R : Type w) [CommRing R] [Algebra k R] :
    hWU k sheafified R ≃ (sheafified.AlgebraCarrier →ₐ[k] R) :=
  Equiv.refl _

end AffineAATChart

end AffineChart

end LawAlgebra
end AAT.AG
