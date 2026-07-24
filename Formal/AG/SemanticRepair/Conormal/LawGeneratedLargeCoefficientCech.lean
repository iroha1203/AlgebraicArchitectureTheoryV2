import Formal.AG.Cohomology.CochainComparison
import Formal.AG.Site.FinitePosetGeometry
import Formal.Util.AssertStandardAxioms
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic

/-!
# Large-coefficient canonical-tuple Cech complex

This file separates the universe of an AAT site from the universe of its
additive coefficients.  From coefficient-free finite-poset cover geometry and
an `AddCommGrpCat`-valued presheaf, it generates the canonical tuple cochains in
degrees zero, one, and two, their alternating differentials, and the proof that
the two displayed differentials compose to zero.

The resulting data is packaged in the repository
`Cohomology.AdditiveThreeTermComplex` and therefore exposes its additive `H¹`.
No cocycle, differential-composition, cohomology class, or vanishing witness is
accepted as a field.
-/

noncomputable section

namespace AAT.AG.SemanticRepair.Conormal
namespace LawGeneratedLargeCoefficientCech

universe u v

open CategoryTheory Opposite
open AAT.AG

variable {U : AtomCarrier.{u}} {A : ArchitectureObject U}
variable {S : Site.AATSite A}
variable (geometry : Site.FinitePosetCoverGeometry S)

/-- Ordered canonical cover-index tuples in the selected degree. -/
abbrev Tuple (n : Nat) :=
  Site.FinitePosetCechCanonicalTupleSimplex geometry.cover.Index n

/-- The overlap-generated coefficient-free canonical tuple geometry. -/
abbrev tupleGeometry := geometry.canonicalTupleCoverGeometryFromOverlap

/-- The site object represented by a canonical tuple overlap. -/
def overlapObject (n : Nat) (simplex : Tuple geometry n) : S.category :=
  Site.ContextCategoryObject.of S.contextPreorder
    ((tupleGeometry geometry).tupleOverlap n simplex)

/-- Delete one entry of a canonical tuple by the standard coface map. -/
def face (n : Nat) (simplex : Tuple geometry (n + 1)) (i : Fin (n + 2)) :
    Tuple geometry n :=
  Site.FinitePosetCechCanonicalTupleSimplex.simplexMap
    (SimplexCategory.δ i) simplex

/-- The generated restriction morphism from a tuple overlap to one of its faces. -/
def faceHom (n : Nat) (simplex : Tuple geometry (n + 1)) (i : Fin (n + 2)) :
    overlapObject geometry (n + 1) simplex ⟶
      overlapObject geometry n (face geometry n simplex i) :=
  homOfLE
    ((tupleGeometry geometry).tupleOverlap_le_tupleMap
      (SimplexCategory.δ i) simplex)

variable (F : S.categoryᵒᵖ ⥤ AddCommGrpCat.{v})

/-- Degree-`n` cochains for a large additive coefficient presheaf. -/
abbrev Cochain (n : Nat) :=
  (simplex : Tuple geometry n) →
    F.obj (op (overlapObject geometry n simplex))

/-- Restrict a cochain value along one generated tuple face. -/
def faceRestriction (n : Nat) (c : Cochain geometry F n)
    (simplex : Tuple geometry (n + 1)) (i : Fin (n + 2)) :
    F.obj (op (overlapObject geometry (n + 1) simplex)) :=
  F.map (faceHom geometry n simplex i).op (c (face geometry n simplex i))

/-- The finite alternating face-restriction differential. -/
def differential (n : Nat) : Cochain geometry F n →+ Cochain geometry F (n + 1) where
  toFun c simplex :=
    Finset.univ.sum (fun i : Fin (n + 2) =>
      if Even i.val then faceRestriction geometry F n c simplex i
      else -faceRestriction geometry F n c simplex i)
  map_zero' := by
    funext simplex
    simp [faceRestriction]
  map_add' x y := by
    funext simplex
    change
      (Finset.univ.sum (fun i : Fin (n + 2) =>
        if Even i.val then faceRestriction geometry F n (x + y) simplex i
        else -faceRestriction geometry F n (x + y) simplex i)) =
      (Finset.univ.sum (fun i : Fin (n + 2) =>
        if Even i.val then faceRestriction geometry F n x simplex i
        else -faceRestriction geometry F n x simplex i)) +
      (Finset.univ.sum (fun i : Fin (n + 2) =>
        if Even i.val then faceRestriction geometry F n y simplex i
        else -faceRestriction geometry F n y simplex i))
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _hi
    by_cases h : Even i.val
    · simp [h, faceRestriction]
    · simp [h, faceRestriction]
      abel

/-- The degree-zero differential. -/
def d0 := differential geometry F 0

/-- The degree-one differential. -/
def d1 := differential geometry F 1

/-- One iterated restriction along two tuple faces. -/
def doubleFaceRestriction (c : Cochain geometry F 0) (simplex : Tuple geometry 2)
    (outer : Fin 3) (inner : Fin 2) :
    F.obj (op (overlapObject geometry 2 simplex)) :=
  F.map (faceHom geometry 1 simplex outer).op
    (F.map (faceHom geometry 0 (face geometry 1 simplex outer) inner).op
      (c (face geometry 0 (face geometry 1 simplex outer) inner)))

/-- The direct composite restriction map underlying one double-face term. -/
def doubleFaceRestrictionMap (simplex : Tuple geometry 2)
    (outer : Fin 3) (inner : Fin 2) :
    F.obj (op (overlapObject geometry 0
      (face geometry 0 (face geometry 1 simplex outer) inner))) →
      F.obj (op (overlapObject geometry 2 simplex)) :=
  F.map (homOfLE
    (S.contextPreorder.trans
      ((tupleGeometry geometry).tupleOverlap_le_tupleMap
        (SimplexCategory.δ outer) simplex)
      ((tupleGeometry geometry).tupleOverlap_le_tupleMap
        (SimplexCategory.δ inner) (face geometry 1 simplex outer)))).op

/-- Iterated restriction agrees with the direct composite restriction. -/
theorem doubleFaceRestriction_eq_map (c : Cochain geometry F 0)
    (simplex : Tuple geometry 2) (outer : Fin 3) (inner : Fin 2) :
    doubleFaceRestriction geometry F c simplex outer inner =
      doubleFaceRestrictionMap geometry F simplex outer inner
        (c (face geometry 0 (face geometry 1 simplex outer) inner)) := by
  dsimp [doubleFaceRestriction, doubleFaceRestrictionMap, faceHom]
  change
    (F ⋙ forget AddCommGrpCat).map _
        ((F ⋙ forget AddCommGrpCat).map _
          (c (face geometry 0 (face geometry 1 simplex outer) inner))) =
      (F ⋙ forget AddCommGrpCat).map _
        (c (face geometry 0 (face geometry 1 simplex outer) inner))
  rw [← FunctorToTypes.map_comp_apply]
  congr

/-- Composite restriction is invariant under transport of equal lower simplices. -/
theorem compositeRestriction_eq_of_low_eq (c : Cochain geometry F 0)
    (simplex : Tuple geometry 2) (lowLeft lowRight : Tuple geometry 0)
    (h : lowLeft = lowRight)
    (hleLeft : S.contextPreorder.le
      ((tupleGeometry geometry).tupleOverlap 2 simplex)
      ((tupleGeometry geometry).tupleOverlap 0 lowLeft))
    (hleRight : S.contextPreorder.le
      ((tupleGeometry geometry).tupleOverlap 2 simplex)
      ((tupleGeometry geometry).tupleOverlap 0 lowRight)) :
    F.map (homOfLE hleLeft).op (c lowLeft) =
      F.map (homOfLE hleRight).op (c lowRight) := by
  cases h
  congr

/-- Equal lower faces generate equal double-face restriction terms. -/
theorem doubleFaceRestriction_eq_of_face_eq (c : Cochain geometry F 0)
    (simplex : Tuple geometry 2) (outer outer' : Fin 3) (inner inner' : Fin 2)
    (hface : face geometry 0 (face geometry 1 simplex outer) inner =
      face geometry 0 (face geometry 1 simplex outer') inner') :
    doubleFaceRestriction geometry F c simplex outer inner =
      doubleFaceRestriction geometry F c simplex outer' inner' := by
  rw [doubleFaceRestriction_eq_map, doubleFaceRestriction_eq_map]
  exact compositeRestriction_eq_of_low_eq geometry F c simplex _ _ hface _ _

/-- The generated degree-one differential kills every degree-zero differential. -/
theorem d1_d0 (c : Cochain geometry F 0) :
    d1 geometry F (d0 geometry F c) = 0 := by
  funext simplex
  have h00 :
      face geometry 0 (face geometry 1 simplex (1 : Fin 3)) (0 : Fin 2) =
        face geometry 0 (face geometry 1 simplex (0 : Fin 3)) (0 : Fin 2) := by
    exact Site.FinitePosetCechCanonicalTupleSimplex.twoFace_simplex_eq
      0 simplex (0 : Fin 2) (0 : Fin 2) (le_refl _)
  have h01 :
      face geometry 0 (face geometry 1 simplex (2 : Fin 3)) (0 : Fin 2) =
        face geometry 0 (face geometry 1 simplex (0 : Fin 3)) (1 : Fin 2) := by
    exact Site.FinitePosetCechCanonicalTupleSimplex.twoFace_simplex_eq
      0 simplex (0 : Fin 2) (1 : Fin 2) (by decide)
  have h11 :
      face geometry 0 (face geometry 1 simplex (2 : Fin 3)) (1 : Fin 2) =
        face geometry 0 (face geometry 1 simplex (1 : Fin 3)) (1 : Fin 2) := by
    exact Site.FinitePosetCechCanonicalTupleSimplex.twoFace_simplex_eq
      0 simplex (1 : Fin 2) (1 : Fin 2) (le_refl _)
  have e00 := doubleFaceRestriction_eq_of_face_eq geometry F c simplex
    (1 : Fin 3) (0 : Fin 3) (0 : Fin 2) (0 : Fin 2) h00
  have e01 := doubleFaceRestriction_eq_of_face_eq geometry F c simplex
    (2 : Fin 3) (0 : Fin 3) (0 : Fin 2) (1 : Fin 2) h01
  have e11 := doubleFaceRestriction_eq_of_face_eq geometry F c simplex
    (2 : Fin 3) (1 : Fin 3) (1 : Fin 2) (1 : Fin 2) h11
  dsimp [d1, d0, differential]
  simp [Fin.sum_univ_succ, faceRestriction]
  change
    doubleFaceRestriction geometry F c simplex (0 : Fin 3) (0 : Fin 2) +
      -doubleFaceRestriction geometry F c simplex (0 : Fin 3) (1 : Fin 2) +
    (doubleFaceRestriction geometry F c simplex (1 : Fin 3) (1 : Fin 2) +
      -doubleFaceRestriction geometry F c simplex (1 : Fin 3) (0 : Fin 2) +
    (doubleFaceRestriction geometry F c simplex (2 : Fin 3) (0 : Fin 2) +
      -doubleFaceRestriction geometry F c simplex (2 : Fin 3) (1 : Fin 2))) = 0
  rw [e00, e01, e11]
  abel

/-- The generated large-coefficient degree-zero-to-two additive complex. -/
def threeTermComplex : Cohomology.AdditiveThreeTermComplex
    (Cochain geometry F 0) (Cochain geometry F 1) (Cochain geometry F 2) where
  d0 := d0 geometry F
  d1 := d1 geometry F
  d_comp := d1_d0 geometry F

/-- Repository additive `H¹` of the generated large-coefficient three-term complex. -/
abbrev H1 := (threeTermComplex geometry F).H1

/-- The cohomology class represented by a generated degree-one cocycle. -/
def h1Class (c : (threeTermComplex geometry F).H1Cocycle) : H1 geometry F :=
  Quotient.mk (threeTermComplex geometry F).H1CoboundarySetoid c

/-- A generated additive `H¹` class is zero exactly when it is a degree-zero coboundary. -/
theorem h1Class_isZero_iff (c : (threeTermComplex geometry F).H1Cocycle) :
    (threeTermComplex geometry F).H1IsZero (h1Class geometry F c) ↔
      ∃ b : Cochain geometry F 0, c.1 = d0 geometry F b := by
  change Quotient.mk _ c = Quotient.mk _ ⟨0, by simp⟩ ↔ _
  rw [Quotient.eq_iff_equiv]
  change (∃ b : Cochain geometry F 0, c.1 - 0 = d0 geometry F b) ↔ _
  simp

/-- The same generated three-term complex for a bundled large additive sheaf. -/
noncomputable abbrev sheafThreeTermComplex
    (𝓕 : Sheaf S.topology AddCommGrpCat.{v}) :=
  threeTermComplex geometry 𝓕.val

/-- Additive `H¹` of a bundled large additive sheaf on the canonical tuple cover. -/
abbrev SheafH1 (𝓕 : Sheaf S.topology AddCommGrpCat.{v}) :=
  (sheafThreeTermComplex geometry 𝓕).H1

end LawGeneratedLargeCoefficientCech
end AAT.AG.SemanticRepair.Conormal

#assert_standard_axioms_only AAT.AG.SemanticRepair.Conormal.LawGeneratedLargeCoefficientCech
