import Formal.AG.Cohomology.FinitePosetStandardComplex
import Formal.AG.Measurement.Verdict

noncomputable section

namespace AAT.AG
namespace Measurement

open CategoryTheory
open Opposite

universe u v

/-!
Part VIII definition 4.1: finite measurement geometry and effective
coefficient procedures.

The selected site, adequate cover, module-valued obstruction sheaf, restriction
maps, and Čech differential are connected by the existing canonical
finite-poset construction.  No completed cochain complex or kernel/image/
quotient comparison is accepted from the caller.
-/

/-- VIII.Definition 4.1: geometric input for a finite measurement regime. -/
structure FiniteMeasurementGeometry (M : MeasurementProfile.{u, v}) where
  /-- Atom carrier supporting the selected AAT site. -/
  U : AtomCarrier.{u}
  /-- Architecture object supporting the selected AAT site. -/
  A : ArchitectureObject U
  /-- Selected AAT site. -/
  site : Site.AATSite A
  /-- Finite-poset site and adequate cover data. -/
  coverGeometry : Site.FinitePosetCoverGeometry site
  /-- Canonical tuple nerve generated from the selected cover. -/
  tupleGeometry : Site.FinitePosetCanonicalTupleCoverGeometry coverGeometry
  /-- Module-valued coefficient ring. -/
  [coeffCommRing : CommRing M.Coeff]
  /-- Selected obstruction coefficient sheaf. -/
  obstructionSheaf : Cohomology.ObstructionSheaf site
  /-- Every selected obstruction section is a module over the profile ring. -/
  sectionModule :
    ∀ (n : Nat)
      (simplex : Site.FinitePosetCechSimplex
        (tupleGeometry.toCoverGeometry.toObstructionCoefficientRegime
          obstructionSheaf) n),
      Module M.Coeff
        (Site.FinitePosetCechSection
          (tupleGeometry.toCoverGeometry.toObstructionCoefficientRegime
            obstructionSheaf) n simplex)
  /-- Every selected obstruction section has a finite carrier. -/
  sectionFintype :
    ∀ (n : Nat)
      (simplex : Site.FinitePosetCechSimplex
        (tupleGeometry.toCoverGeometry.toObstructionCoefficientRegime
          obstructionSheaf) n),
      Fintype
        (Site.FinitePosetCechSection
          (tupleGeometry.toCoverGeometry.toObstructionCoefficientRegime
            obstructionSheaf) n simplex)
  /-- Profile site objects identify with the selected finite context index. -/
  siteObjEquiv : M.SiteObj ≃ coverGeometry.ContextIndex
  /-- Profile cover indices identify with the selected adequate cover. -/
  coverEquiv : M.Cover ≃ coverGeometry.cover.Index

namespace FiniteMeasurementGeometry

variable {M : MeasurementProfile.{u, v}}

/-- Coefficient regime generated from the selected cover and obstruction sheaf. -/
abbrev coefficientRegime (G : FiniteMeasurementGeometry M) :=
  G.tupleGeometry.toCoverGeometry.toObstructionCoefficientRegime G.obstructionSheaf

/-- Degree-`n` cochains of the generated finite-poset Čech complex. -/
abbrev CechCochain (G : FiniteMeasurementGeometry M) (n : Nat) :=
  Site.FinitePosetCechCochain G.coefficientRegime n

/-- Canonical Čech complex generated from the cover nerve and restriction maps. -/
def cechComplex (G : FiniteMeasurementGeometry M) :=
  Cohomology.StandardFinitePosetCech.canonicalTupleStandardFinitePosetCechComplex
    G.tupleGeometry G.obstructionSheaf

/-- The profile site-object type is concretely finite. -/
noncomputable def siteObjFintype (G : FiniteMeasurementGeometry M) :
    Fintype M.SiteObj := by
  letI : Finite G.coverGeometry.ContextIndex := G.coverGeometry.finiteContextIndex
  letI : Finite M.SiteObj :=
    Finite.of_injective G.siteObjEquiv G.siteObjEquiv.injective
  exact Fintype.ofFinite M.SiteObj

/-- The profile cover-index type is concretely finite. -/
noncomputable def coverFintype (G : FiniteMeasurementGeometry M) :
    Fintype M.Cover := by
  letI : Finite G.coverGeometry.cover.Index := G.coverGeometry.finiteCoverIndex
  letI : Finite M.Cover :=
    Finite.of_injective G.coverEquiv G.coverEquiv.injective
  exact Fintype.ofFinite M.Cover

/-- Generated degree-`n` cochains have a finite carrier. -/
noncomputable def cochainFintype (G : FiniteMeasurementGeometry M) (n : Nat) :
    Fintype (G.CechCochain n) := by
  classical
  letI : Finite (Site.FinitePosetCechSimplex G.coefficientRegime n) :=
    G.coefficientRegime.finiteNerveSimplex n
  letI : Fintype (Site.FinitePosetCechSimplex G.coefficientRegime n) :=
    Fintype.ofFinite _
  letI (simplex : Site.FinitePosetCechSimplex G.coefficientRegime n) :
      Fintype (Site.FinitePosetCechSection G.coefficientRegime n simplex) :=
    G.sectionFintype n simplex
  infer_instance

/-- Generated degree-`n` cochains inherit their pointwise abelian group. -/
noncomputable def cochainAddCommGroup (G : FiniteMeasurementGeometry M) (n : Nat) :
    AddCommGroup (G.CechCochain n) := by
  letI (simplex : Site.FinitePosetCechSimplex G.coefficientRegime n) :
      AddCommGroup (Site.FinitePosetCechSection G.coefficientRegime n simplex) :=
    G.obstructionSheaf.addCommGroup _
  infer_instance

/-- Generated degree-`n` cochains inherit the pointwise coefficient module. -/
noncomputable def cochainModule (G : FiniteMeasurementGeometry M) (n : Nat) :
    letI := G.coeffCommRing
    letI := G.cochainAddCommGroup n
    Module M.Coeff (G.CechCochain n) := by
  letI := G.coeffCommRing
  letI := G.cochainAddCommGroup n
  letI (simplex : Site.FinitePosetCechSimplex G.coefficientRegime n) :
      Module M.Coeff (Site.FinitePosetCechSection G.coefficientRegime n simplex) :=
    G.sectionModule n simplex
  infer_instance

/-- The generated standard differential preserves addition. -/
theorem differential_add (G : FiniteMeasurementGeometry M) (n : Nat)
    (x y : G.CechCochain n) :
    G.cechComplex.differential n (x + y) =
      G.cechComplex.differential n x + G.cechComplex.differential n y := by
  classical
  funext simplex
  letI : AddCommGroup
      (Site.FinitePosetCechSection
        (G.tupleGeometry.toCoverGeometry.toRegime
          G.obstructionSheaf.carrier.toPresheaf) (n + 1) simplex) :=
    G.obstructionSheaf.addCommGroup
      (Site.FinitePosetCechOverlapObject G.coefficientRegime (n + 1) simplex)
  dsimp only [cechComplex,
    Cohomology.StandardFinitePosetCech.canonicalTupleStandardFinitePosetCechComplex,
    Cohomology.StandardFinitePosetCech.standardFinitePosetCechComplex,
    Cohomology.StandardFinitePosetCech.standardDifferential,
    Cohomology.StandardFinitePosetCech.standardAdditiveData,
    Cohomology.StandardFinitePosetCech.obstructionSheafStandardAlternatingCombination]
  let signedTerm (c : G.CechCochain n) (i : Fin (n + 2)) :
      Site.FinitePosetCechSection G.coefficientRegime (n + 1) simplex :=
    if Even i.val then
      Site.FinitePosetCechFaceRestriction
        (G.tupleGeometry.toSimplicialFaceAction
          G.obstructionSheaf.carrier.toPresheaf).toFaceData c simplex i
    else
      -Site.FinitePosetCechFaceRestriction
        (G.tupleGeometry.toSimplicialFaceAction
          G.obstructionSheaf.carrier.toPresheaf).toFaceData c simplex i
  change (∑ i, signedTerm (x + y) i) =
    (∑ i, signedTerm x i) + ∑ i, signedTerm y i
  have hfun : (fun i : Fin (n + 2) => signedTerm (x + y) i) =
      (fun i : Fin (n + 2) => signedTerm x i + signedTerm y i) := by
    funext i
    have hmap := G.obstructionSheaf.map_add
      (CategoryTheory.homOfLE
        ((G.tupleGeometry.toSimplicialFaceAction
          G.obstructionSheaf.carrier.toPresheaf).toFaceData.faceOverlap_le
            n simplex i))
      (x ((G.tupleGeometry.toSimplicialFaceAction
        G.obstructionSheaf.carrier.toPresheaf).toFaceData.face n simplex i))
      (y ((G.tupleGeometry.toSimplicialFaceAction
        G.obstructionSheaf.carrier.toPresheaf).toFaceData.face n simplex i))
    change
      Site.FinitePosetCechFaceRestriction
          (G.tupleGeometry.toSimplicialFaceAction
            G.obstructionSheaf.carrier.toPresheaf).toFaceData
          (x + y) simplex i = _ at hmap
    by_cases hi : Even i.val
    · simp only [signedTerm, hi, if_true]
      exact hmap
    · simp only [signedTerm, hi, if_false]
      rw [hmap, neg_add_rev]
      exact add_comm _ _
  rw [hfun, Finset.sum_add_distrib]

/-- The generated restriction differential as an additive homomorphism. -/
noncomputable def differentialHom (G : FiniteMeasurementGeometry M) (n : Nat) :
    letI := G.cochainAddCommGroup n
    letI := G.cochainAddCommGroup (n + 1)
    G.CechCochain n →+ G.CechCochain (n + 1) := by
  letI := G.cochainAddCommGroup n
  letI := G.cochainAddCommGroup (n + 1)
  exact {
    toFun := G.cechComplex.differential n
    map_zero' := G.cechComplex.differential_zero n
    map_add' := G.differential_add n
  }

/-- Degree-`n` cocycles computed as the actual differential kernel. -/
noncomputable def CechCocycle (G : FiniteMeasurementGeometry M) (n : Nat) : Type u :=
  letI := G.cochainAddCommGroup n
  letI := G.cochainAddCommGroup (n + 1)
  { c : G.CechCochain n // G.differentialHom n c = 0 }

/-- Positive-degree coboundary equivalence generated by the previous differential. -/
noncomputable def coboundarySetoidSucc (G : FiniteMeasurementGeometry M) (n : Nat) :
    Setoid (G.CechCocycle (n + 1)) := by
  letI := G.cochainAddCommGroup n
  letI := G.cochainAddCommGroup (n + 1)
  letI := G.cochainAddCommGroup (n + 2)
  exact {
    r x y := ∃ b : G.CechCochain n, x.1 - y.1 = G.differentialHom n b
    iseqv := by
      refine ⟨?_, ?_, ?_⟩
      · intro x
        exact ⟨0, by simp⟩
      · rintro x y ⟨b, hb⟩
        refine ⟨-b, ?_⟩
        calc
          y.1 - x.1 = -(x.1 - y.1) := by abel
          _ = -(G.differentialHom n b) := by rw [hb]
          _ = G.differentialHom n (-b) := by simp
      · rintro x y z ⟨bxy, hxy⟩ ⟨byz, hyz⟩
        refine ⟨bxy + byz, ?_⟩
        rw [map_add, ← hxy, ← hyz]
        abel
  }

/-- Generated finite-poset Čech `H^n` in every selected degree. -/
noncomputable def CechHn (G : FiniteMeasurementGeometry M) : Nat → Type u
  | 0 => G.CechCocycle 0
  | n + 1 => Quotient (G.coboundarySetoidSucc n)

/-- Zero class in the generated finite-poset Čech `H^n`. -/
noncomputable def zeroClass (G : FiniteMeasurementGeometry M) :
    (n : Nat) → G.CechHn n
  | 0 => by
      letI := G.cochainAddCommGroup 0
      letI := G.cochainAddCommGroup 1
      exact ⟨0, (G.differentialHom 0).map_zero⟩
  | n + 1 => by
      letI := G.cochainAddCommGroup n
      letI := G.cochainAddCommGroup (n + 1)
      letI := G.cochainAddCommGroup (n + 2)
      exact Quotient.mk (G.coboundarySetoidSucc n)
        ⟨0, (G.differentialHom (n + 1)).map_zero⟩

/-- Generated cocycles have a concrete finite enumeration. -/
noncomputable def cocycleFintype (G : FiniteMeasurementGeometry M) (n : Nat) :
    Fintype (G.CechCocycle n) := by
  classical
  letI := G.cochainAddCommGroup n
  letI := G.cochainAddCommGroup (n + 1)
  letI := G.cochainFintype n
  letI : Finite (G.CechCocycle n) :=
    Finite.of_injective (fun c : G.CechCocycle n => c.1) Subtype.val_injective
  exact Fintype.ofFinite _

/-- Generated Čech `H^n` has a concrete finite enumeration in every degree. -/
noncomputable def hFintype (G : FiniteMeasurementGeometry M) (n : Nat) :
    Fintype (G.CechHn n) := by
  classical
  cases n with
  | zero => exact G.cocycleFintype 0
  | succ n =>
      letI := G.cochainAddCommGroup n
      letI := G.cochainAddCommGroup (n + 1)
      letI := G.cochainAddCommGroup (n + 2)
      letI := G.cochainFintype (n + 1)
      letI : Fintype (G.CechCocycle (n + 1)) := G.cocycleFintype (n + 1)
      letI : Finite (G.CechCocycle (n + 1)) :=
        Finite.of_injective (fun c : G.CechCocycle (n + 1) => c.1)
          Subtype.val_injective
      letI : Finite (G.CechHn (n + 1)) := by
        change Finite (Quotient (G.coboundarySetoidSucc n))
        infer_instance
      exact Fintype.ofFinite _

/-- Finite kernel enumeration for the selected degree-`n` differential. -/
noncomputable def kernelFinset (G : FiniteMeasurementGeometry M) (n : Nat) :
    Finset (G.CechCochain n) := by
  classical
  letI := G.cochainAddCommGroup n
  letI := G.cochainAddCommGroup (n + 1)
  letI := G.cochainFintype n
  exact Finset.univ.filter fun c => G.differentialHom n c = 0

/-- Kernel enumeration is exact. -/
theorem mem_kernelFinset_iff (G : FiniteMeasurementGeometry M) (n : Nat)
    (c : G.CechCochain n) :
    c ∈ G.kernelFinset n ↔ G.differentialHom n c = 0 := by
  classical
  letI := G.cochainAddCommGroup n
  letI := G.cochainAddCommGroup (n + 1)
  letI := G.cochainFintype n
  simp [kernelFinset]

/-- Finite image enumeration for the selected degree-`n` differential. -/
noncomputable def imageFinset (G : FiniteMeasurementGeometry M) (n : Nat) :
    Finset (G.CechCochain (n + 1)) := by
  classical
  letI := G.cochainAddCommGroup n
  letI := G.cochainAddCommGroup (n + 1)
  letI := G.cochainFintype n
  exact Finset.univ.image (G.differentialHom n)

/-- Image enumeration is exact. -/
theorem mem_imageFinset_iff (G : FiniteMeasurementGeometry M) (n : Nat)
    (c : G.CechCochain (n + 1)) :
    c ∈ G.imageFinset n ↔
      ∃ b : G.CechCochain n, G.differentialHom n b = c := by
  classical
  letI := G.cochainAddCommGroup n
  letI := G.cochainAddCommGroup (n + 1)
  letI := G.cochainFintype n
  simp [imageFinset]

/-- Complete finite list of generated degree-`n` cocycle representatives. -/
noncomputable def cocycleFinset (G : FiniteMeasurementGeometry M) (n : Nat) :
    Finset (G.CechCocycle n) := by
  classical
  letI := G.cochainAddCommGroup n
  letI := G.cochainAddCommGroup (n + 1)
  letI := G.cocycleFintype n
  exact Finset.univ

/-- Complete finite list of generated Čech `H^n` classes. -/
noncomputable def cohomologyFinset (G : FiniteMeasurementGeometry M) (n : Nat) :
    Finset (G.CechHn n) := by
  classical
  letI := G.hFintype n
  exact Finset.univ

end FiniteMeasurementGeometry

/--
VIII.Definition 4.1: effective verdict interface for the generated Čech
cohomology.  The verdict is constructed below from zero/nonzero decisions; a
completed `MeasurementVerdict` is not a field.
-/
structure EffCoeff (M : MeasurementProfile.{u, v})
    (G : FiniteMeasurementGeometry M) where
  /-- Profile-owned effective interface token. -/
  profileInterface : M.EffCoeff
  /-- Selected cohomological degree measured by the profile domain. -/
  selectedDegree : Nat
  /-- Profile-domain classes identify with generated Čech classes. -/
  domainEquiv : M.Domain ≃ G.CechHn selectedDegree
  /-- The profile zero predicate is the generated zero-class predicate. -/
  zero_iff :
    ∀ alpha, M.Zero alpha ↔ domainEquiv alpha = G.zeroClass selectedDegree
  /-- The profile nonzero predicate is complement of the generated zero class. -/
  nonzero_iff :
    ∀ alpha, M.NonZero alpha ↔ domainEquiv alpha ≠ G.zeroClass selectedDegree
  /-- Every selected class is in the finite measurement scope. -/
  inScope : ∀ alpha, M.InScope alpha
  /-- Selected computation method for every profile-domain class. -/
  method : ∀ alpha, M.SelectedMethod alpha
  /-- Certificate reference produced for every profile-domain class. -/
  certificate : ∀ alpha, M.CertRef alpha

namespace EffCoeff

/-- Compute a certified zero/nonzero verdict from the generated Čech class. -/
noncomputable def verdict {M : MeasurementProfile.{u, v}}
    {G : FiniteMeasurementGeometry M} (E : EffCoeff M G) (alpha : M.Domain) :
    MeasurementVerdict M alpha := by
  classical
  by_cases hzero : E.domainEquiv alpha = G.zeroClass E.selectedDegree
  · exact MeasurementVerdict.measured_zero (E.inScope alpha)
      ((E.zero_iff alpha).mpr hzero) (E.certificate alpha)
  · exact MeasurementVerdict.measured_nonzero (E.inScope alpha)
      ((E.nonzero_iff alpha).mpr hzero) (E.certificate alpha)

end EffCoeff

/-- VIII.Definition 4.1: finite measurement regime with generated computations. -/
structure FiniteMeasurementRegime (M : MeasurementProfile.{u, v}) where
  /-- Selected finite geometry and module-valued coefficient sheaf. -/
  geometry : FiniteMeasurementGeometry M
  /-- Effective verdict interface tied to the generated Čech cohomology. -/
  effCoeff : EffCoeff M geometry
  /-- Finite witness-variable carrier used by square-free readings. -/
  witnessFintype : Fintype M.WitnessVariables
  /-- Decidable equality for finite witness computations. -/
  witnessDecidableEq : DecidableEq M.WitnessVariables

namespace FiniteMeasurementRegime

/-- Compute the selected profile verdict from actual generated cohomology. -/
noncomputable def verdict {M : MeasurementProfile.{u, v}}
    (R : FiniteMeasurementRegime M) (alpha : M.Domain) :
    MeasurementVerdict M alpha :=
  R.effCoeff.verdict alpha

end FiniteMeasurementRegime

end Measurement
end AAT.AG
