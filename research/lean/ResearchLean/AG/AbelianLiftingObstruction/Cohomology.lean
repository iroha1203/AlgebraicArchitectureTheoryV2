import ResearchLean.AG.AbelianLiftingObstruction.Cochains
import Mathlib.Algebra.Homology.ShortComplex.Ab
import Mathlib.Algebra.Homology.HomologicalComplex

/-!
# Cohomology of the same finite presentation

G-129 A3: the first and second cohomology groups are quotients of the kernels
of the differentials by the images of their predecessors. The quotient maps
give the zero-class criterion used by the obstruction and solution theorems.

## Implementation notes

The quotient is formed inside the actual cycle subgroup, so a class cannot be
created from a non-cocycle. The adjacent three-term complexes connect these
explicit quotients to mathlib's homology API.
-/

namespace AAT.AG.AbelianLiftingObstruction

open CategoryTheory

universe uG uA

variable {K : TransportCoherence.FiniteTransportPresentation.{uG}}
variable (M : LocalCoefficients.{uG,uA} K)

/-- G-129 A3: first cocycles of the same face differential. -/
abbrev Z1 : AddSubgroup (C1 M) := (d1Hom M).ker

/-- G-129 A3: second cocycles of the same 3-cell differential. -/
abbrev Z2 : AddSubgroup (C2 M) := (d2Hom M).ker

/-- G-129 A3: the vertex differential lands in first cocycles. -/
def d0ToZ1 : C0 M →+ Z1 M where
  toFun b := ⟨d0Hom M b, d1_d0 M b⟩
  map_zero' := Subtype.ext (map_zero (d0Hom M))
  map_add' b c := Subtype.ext (map_add (d0Hom M) b c)

/-- G-129 A3: the face differential lands in second cocycles. -/
def d1ToZ2 : C1 M →+ Z2 M where
  toFun h := ⟨d1Hom M h, d2_d1 M h⟩
  map_zero' := Subtype.ext (map_zero (d1Hom M))
  map_add' h k := Subtype.ext (map_add (d1Hom M) h k)

/-- G-129 A3: first cohomology, with no finiteness assumption on coefficients. -/
abbrev H1 := (Z1 M) ⧸ (d0ToZ1 M).range

/-- G-129 A3: second cohomology, with no finiteness assumption on coefficients. -/
abbrev H2 := (Z2 M) ⧸ (d1ToZ2 M).range

/-- API: a first cocycle is zero in H1 exactly when it is a vertex coboundary. -/
theorem h1_eq_zero_iff (z : Z1 M) :
    (QuotientAddGroup.mk z : H1 M) = 0 ↔ ∃ b : C0 M, d0ToZ1 M b = z := by
  rw [QuotientAddGroup.eq_zero_iff, AddMonoidHom.mem_range]

/-- API: a second cocycle is zero in H2 exactly when it is a face coboundary. -/
theorem h2_eq_zero_iff (z : Z2 M) :
    (QuotientAddGroup.mk z : H2 M) = 0 ↔ ∃ h : C1 M, d1ToZ2 M h = z := by
  rw [QuotientAddGroup.eq_zero_iff, AddMonoidHom.mem_range]

/-- G-129 A3: the degree-one segment as a native short complex of abelian groups. -/
def firstShortComplex : ShortComplex Ab where
  X₁ := AddCommGrpCat.of (C0 M)
  X₂ := AddCommGrpCat.of (C1 M)
  X₃ := AddCommGrpCat.of (C2 M)
  f := AddCommGrpCat.ofHom (d0Hom M)
  g := AddCommGrpCat.ofHom (d1Hom M)
  zero := by
    apply AddCommGrpCat.hom_ext
    apply AddMonoidHom.ext
    intro b
    exact d1_d0 M b

/-- G-129 A3: the degree-two segment as a native short complex of abelian groups. -/
def secondShortComplex : ShortComplex Ab where
  X₁ := AddCommGrpCat.of (C1 M)
  X₂ := AddCommGrpCat.of (C2 M)
  X₃ := AddCommGrpCat.of (C3 M)
  f := AddCommGrpCat.ofHom (d1Hom M)
  g := AddCommGrpCat.ofHom (d2Hom M)
  zero := by
    apply AddCommGrpCat.hom_ext
    apply AddMonoidHom.ext
    intro h
    exact d2_d1 M h

/-- G-129 A3: the same four cochain groups as objects of `Ab`, zero above degree three. -/
def cochainObject : ℕ → Ab
  | 0 => AddCommGrpCat.of (C0 M)
  | 1 => AddCommGrpCat.of (C1 M)
  | 2 => AddCommGrpCat.of (C2 M)
  | 3 => AddCommGrpCat.of (C3 M)
  | _ => AddCommGrpCat.of PUnit

/-- G-129 A3: the three constructed differentials, zero above degree two. -/
def cochainDifferential : ∀ n : ℕ, cochainObject M n ⟶ cochainObject M (n + 1)
  | 0 => AddCommGrpCat.ofHom (d0Hom M)
  | 1 => AddCommGrpCat.ofHom (d1Hom M)
  | 2 => AddCommGrpCat.ofHom (d2Hom M)
  | _ + 3 => 0

/-- G-129 A3: the four-term complex is native mathlib `CochainComplex`. -/
def cochainComplex : CochainComplex Ab ℕ :=
  CochainComplex.of (cochainObject M) (cochainDifferential M) (by
    intro n
    cases n with
    | zero =>
        change AddCommGrpCat.ofHom (d0Hom M) ≫ AddCommGrpCat.ofHom (d1Hom M) = 0
        exact (firstShortComplex M).zero
    | succ n =>
        cases n with
        | zero =>
            change AddCommGrpCat.ofHom (d1Hom M) ≫
              AddCommGrpCat.ofHom (d2Hom M) = 0
            exact (secondShortComplex M).zero
        | succ n =>
            cases n with
            | zero => rfl
            | succ n => rfl)

/-- G-129 A3: explicit H1 is the native homology of the same differential segment. -/
noncomputable def firstHomologyIso :
    (firstShortComplex M).homology ≅ AddCommGrpCat.of (H1 M) := by
  exact (firstShortComplex M).abHomologyIso

/-- G-129 A3: explicit H2 is the native homology of the same differential segment. -/
noncomputable def secondHomologyIso :
    (secondShortComplex M).homology ≅ AddCommGrpCat.of (H2 M) := by
  exact (secondShortComplex M).abHomologyIso

end AAT.AG.AbelianLiftingObstruction

#assert_standard_axioms_only AAT.AG.AbelianLiftingObstruction
