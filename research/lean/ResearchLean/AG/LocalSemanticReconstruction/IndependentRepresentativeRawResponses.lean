import ResearchLean.AG.LocalSemanticReconstruction.IndependentRepresentativeHomReadings
import ResearchLean.AG.LocalSemanticReconstruction.IndependentRawCandidatePoints
import Formal.Util.AssertStandardAxioms

/-!
# Representative raw response comparisons

Implementation notes: these basic reader lemmas connect arbitrary candidate
carrier responses to the existing native raw comparison. Polynomial and image
responses apply coefficient change to the source optional value, preserving
inactive cells. This exposes an API for primitive Hom laws without storing
the complete raw equality or unfolding the reader downstream.
-/

namespace AAT.AG.LocalSemanticReconstruction.IndependentRepresentativeHom

noncomputable section

universe u v

open Site CategoryTheory AtomFoundation GeometryTransport LawAlgebra

variable {U : AtomCarrier.{u}} {A : ArchitectureObject U}

/-- At the declared coefficient reference, every candidate polynomial response is its native local reading. -/
theorem polynomial_candidate_read (S : AATSite A) (k : Type v) [CommRing k]
    (R : RawAmbientRestrictionSystem S k) (W : ArchCtx A) (C I : Type u) (i : I) :
    (IndependentRawCandidate.read S k R (.polynomial W C I (IndependentRawCandidate.coefficientRef k) i)).down =
      (IndependentRawLocal.read R (.polynomial ⟨W⟩ C I i)).down := by
  classical
  simp [IndependentRawCandidate.read, IndependentRawCandidate.raise, IndependentRawCandidate.transportPolynomial]

/-- A readable context pair has the same candidate image value as its actual native arrow. -/
theorem image_candidate_read (S : AATSite A) (k : Type v) [CommRing k]
    (R : RawAmbientRestrictionSystem S k) {W X : S.category} (g : W ⟶ X) (C D : Type u) (d : D) :
    (IndependentRawCandidate.read S k R (.image W.ctx X.ctx C D (IndependentRawCandidate.coefficientRef k) d)).down =
      (IndependentRawLocal.read R (.image g C D d)).down := by
  classical
  have hg : S.contextPreorder.le W.ctx X.ctx := leOfHom g
  simp [IndependentRawCandidate.read, IndependentRawCandidate.raise, IndependentRawCandidate.transportPolynomial, hg]
  rfl

variable {G H : GeometryPackage.{u, v} U}
variable (f : PackageTotalHom G.core H.core) (a : G.Coefficient →+* H.Coefficient)

/-- Every transported relation response is coefficient change of one source candidate response. -/
theorem transport_polynomial_from_candidate (V : H.site.category) (C I : Type u) (i : I) :
    (transportTable f a (.polynomial V C I i)).down =
      Option.map (MvPolynomial.map a)
        (IndependentRawCandidate.read G.site G.Coefficient G.raw
          (.polynomial ((coreContextInverse f).obj V).ctx C I
            (IndependentRawCandidate.coefficientRef G.Coefficient) i)).down := by
  classical
  rw [polynomial_candidate_read]
  change (transportTable f a (.polynomial V C I i)).down =
    Option.map (MvPolynomial.map a)
      (IndependentRawLocal.read G.raw (.polynomial ((coreContextInverse f).obj V) C I i)).down
  by_cases hc : C = (G.raw.coordFamily ((coreContextInverse f).obj V)).Coord
  · subst C
    by_cases hi : I = (G.raw.relationFamily ((coreContextInverse f).obj V)).Relation
    · subst I
      simp [transportTable, IndependentRawLocal.read]
    · simp [transportTable, IndependentRawLocal.read, hi]
  · simp [transportTable, IndependentRawLocal.read, hc]

/-- Every transported variable image is coefficient change of its source candidate image response. -/
theorem transport_image_from_candidate {V Y : H.site.category} (g : V ⟶ Y) (C D : Type u) (d : D) :
    (transportTable f a (.image g C D d)).down =
      Option.map (MvPolynomial.map a)
        (IndependentRawCandidate.read G.site G.Coefficient G.raw
          (.image ((coreContextInverse f).obj V).ctx ((coreContextInverse f).obj Y).ctx C D
            (IndependentRawCandidate.coefficientRef G.Coefficient) d)).down := by
  classical
  rw [image_candidate_read G.site G.Coefficient G.raw ((coreContextInverse f).map g)]
  by_cases hc : C = (G.raw.coordFamily ((coreContextInverse f).obj V)).Coord
  · subst C
    by_cases hd : D = (G.raw.coordFamily ((coreContextInverse f).obj Y)).Coord
    · subst D
      simp [transportTable, IndependentRawLocal.read]
    · simp [transportTable, IndependentRawLocal.read, hd]
  · simp [transportTable, IndependentRawLocal.read, hc]

end

end AAT.AG.LocalSemanticReconstruction.IndependentRepresentativeHom

#assert_standard_axioms_only AAT.AG.LocalSemanticReconstruction.IndependentRepresentativeHom
