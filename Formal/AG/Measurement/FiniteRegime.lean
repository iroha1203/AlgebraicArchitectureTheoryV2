import Formal.AG.Cohomology.FinitePosetStandardComplex
import Formal.AG.Measurement.Verdict
import Mathlib.LinearAlgebra.Matrix.Basis
import Mathlib.LinearAlgebra.Dimension.Finite
import Mathlib.LinearAlgebra.Quotient.Basic

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
  /-- Finite-poset site and adequate cover data. -/
  coverGeometry :
    Site.FinitePosetCoverGeometry M.equationGeometry.site
  /-- Canonical tuple nerve generated from the selected cover. -/
  tupleGeometry : Site.FinitePosetCanonicalTupleCoverGeometry coverGeometry
  /-- Module-valued coefficient ring. -/
  [coeffCommRing : CommRing M.Coeff]
  /-- Selected obstruction coefficient sheaf. -/
  obstructionSheaf :
    Cohomology.ObstructionSheaf M.equationGeometry.site
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
  /-- Every selected face restriction is a bundled coefficient-linear map. -/
  faceRestrictionLinear :
    ∀ (n : Nat)
      (simplex : Site.FinitePosetCechSimplex
        (tupleGeometry.toCoverGeometry.toObstructionCoefficientRegime
          obstructionSheaf) (n + 1))
      (i : Fin (n + 2)),
      let face :=
        (tupleGeometry.toSimplicialFaceAction
          obstructionSheaf.carrier.toPresheaf).toFaceData.face n simplex i
      letI := coeffCommRing
      letI : AddCommGroup
          (Site.FinitePosetCechSection
            (tupleGeometry.toCoverGeometry.toObstructionCoefficientRegime
              obstructionSheaf) n face) :=
        obstructionSheaf.addCommGroup
          (Site.FinitePosetCechOverlapObject
            (tupleGeometry.toCoverGeometry.toObstructionCoefficientRegime
              obstructionSheaf) n face)
      letI := sectionModule n face
      letI : AddCommGroup
          (Site.FinitePosetCechSection
            (tupleGeometry.toCoverGeometry.toObstructionCoefficientRegime
              obstructionSheaf) (n + 1) simplex) :=
        obstructionSheaf.addCommGroup
          (Site.FinitePosetCechOverlapObject
            (tupleGeometry.toCoverGeometry.toObstructionCoefficientRegime
              obstructionSheaf) (n + 1) simplex)
      letI := sectionModule (n + 1) simplex
      Site.FinitePosetCechSection
          (tupleGeometry.toCoverGeometry.toObstructionCoefficientRegime
            obstructionSheaf) n face →ₗ[M.Coeff]
        Site.FinitePosetCechSection
          (tupleGeometry.toCoverGeometry.toObstructionCoefficientRegime
            obstructionSheaf) (n + 1) simplex
  /-- The bundled linear map is the actual obstruction-sheaf restriction. -/
  faceRestrictionLinear_apply :
    ∀ (n : Nat)
      (simplex : Site.FinitePosetCechSimplex
        (tupleGeometry.toCoverGeometry.toObstructionCoefficientRegime
          obstructionSheaf) (n + 1))
      (i : Fin (n + 2))
      (x : Site.FinitePosetCechSection
        (tupleGeometry.toCoverGeometry.toObstructionCoefficientRegime
          obstructionSheaf) n
        ((tupleGeometry.toSimplicialFaceAction
          obstructionSheaf.carrier.toPresheaf).toFaceData.face n simplex i)),
      faceRestrictionLinear n simplex i x =
        obstructionSheaf.carrier.toPresheaf.map
          (CategoryTheory.homOfLE
            ((tupleGeometry.toSimplicialFaceAction
              obstructionSheaf.carrier.toPresheaf).toFaceData.faceOverlap_le
                n simplex i)).op x
  /-- Profile site objects identify with the selected finite context index. -/
  siteObjEquiv : M.SiteObj ≃ coverGeometry.ContextIndex
  /-- Profile cover indices identify with the selected adequate cover. -/
  coverEquiv : M.Cover ≃ coverGeometry.cover.Index

namespace FiniteMeasurementGeometry

variable {M : MeasurementProfile.{u, v}}

/-- Atom carrier fixed by the measurement profile. -/
abbrev U (_G : FiniteMeasurementGeometry M) : AtomCarrier.{u} :=
  M.equationGeometry.U

/-- Architecture object fixed by the measurement profile. -/
abbrev A (_G : FiniteMeasurementGeometry M) :
    ArchitectureObject M.equationGeometry.U :=
  M.equationGeometry.A

/-- Equation-generated AAT site fixed by the measurement profile. -/
abbrev site (_G : FiniteMeasurementGeometry M) :
    Site.AATSite M.equationGeometry.A :=
  M.equationGeometry.site

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

/-- The generated standard differential preserves coefficient scalar multiplication. -/
theorem differential_smul (G : FiniteMeasurementGeometry M) (n : Nat)
    (r : M.Coeff) (c : G.CechCochain n) :
    letI := G.coeffCommRing
    letI := G.cochainAddCommGroup n
    letI := G.cochainAddCommGroup (n + 1)
    letI := G.cochainModule n
    letI := G.cochainModule (n + 1)
    G.cechComplex.differential n (r • c) =
      r • G.cechComplex.differential n c := by
  classical
  funext simplex
  letI := G.coeffCommRing
  letI := G.cochainAddCommGroup n
  letI := G.cochainAddCommGroup (n + 1)
  letI := G.cochainModule n
  letI := G.cochainModule (n + 1)
  letI : AddCommGroup
      (Site.FinitePosetCechSection
        (G.tupleGeometry.toCoverGeometry.toRegime
          G.obstructionSheaf.carrier.toPresheaf) (n + 1) simplex) :=
    G.obstructionSheaf.addCommGroup
      (Site.FinitePosetCechOverlapObject G.coefficientRegime (n + 1) simplex)
  letI : Module M.Coeff
      (Site.FinitePosetCechSection
        (G.tupleGeometry.toCoverGeometry.toRegime
          G.obstructionSheaf.carrier.toPresheaf) (n + 1) simplex) :=
    G.sectionModule (n + 1) simplex
  letI : AddCommGroup
      (Site.FinitePosetCechSection G.coefficientRegime (n + 1) simplex) :=
    G.obstructionSheaf.addCommGroup
      (Site.FinitePosetCechOverlapObject G.coefficientRegime (n + 1) simplex)
  letI : Module M.Coeff
      (Site.FinitePosetCechSection G.coefficientRegime (n + 1) simplex) :=
    G.sectionModule (n + 1) simplex
  dsimp only [cechComplex,
    Cohomology.StandardFinitePosetCech.canonicalTupleStandardFinitePosetCechComplex,
    Cohomology.StandardFinitePosetCech.standardFinitePosetCechComplex,
    Cohomology.StandardFinitePosetCech.standardDifferential,
    Cohomology.StandardFinitePosetCech.standardAdditiveData,
    Cohomology.StandardFinitePosetCech.obstructionSheafStandardAlternatingCombination]
  let signedTerm (cochain : G.CechCochain n) (i : Fin (n + 2)) :
      Site.FinitePosetCechSection
        (G.tupleGeometry.toCoverGeometry.toRegime
          G.obstructionSheaf.carrier.toPresheaf) (n + 1) simplex :=
    if Even i.val then
      Site.FinitePosetCechFaceRestriction
        (G.tupleGeometry.toSimplicialFaceAction
          G.obstructionSheaf.carrier.toPresheaf).toFaceData cochain simplex i
    else
      -Site.FinitePosetCechFaceRestriction
        (G.tupleGeometry.toSimplicialFaceAction
          G.obstructionSheaf.carrier.toPresheaf).toFaceData cochain simplex i
  simp only [Pi.smul_apply]
  dsimp only [Cohomology.StandardFinitePosetCech.standardDifferential,
    Cohomology.StandardFinitePosetCech.standardAdditiveData,
    Cohomology.StandardFinitePosetCech.obstructionSheafStandardAlternatingCombination]
  change (∑ i, signedTerm (r • c) i) = r • ∑ i, signedTerm c i
  have hfun : (fun i : Fin (n + 2) => signedTerm (r • c) i) =
      (fun i : Fin (n + 2) => r • signedTerm c i) := by
    funext i
    let face := (G.tupleGeometry.toSimplicialFaceAction
      G.obstructionSheaf.carrier.toPresheaf).toFaceData.face n simplex i
    letI : AddCommGroup
        (Site.FinitePosetCechSection G.coefficientRegime n face) :=
      G.obstructionSheaf.addCommGroup
        (Site.FinitePosetCechOverlapObject G.coefficientRegime n face)
    letI : Module M.Coeff
        (Site.FinitePosetCechSection G.coefficientRegime n face) :=
      G.sectionModule n face
    have hmap := (G.faceRestrictionLinear n simplex i).map_smul r
      (c ((G.tupleGeometry.toSimplicialFaceAction
        G.obstructionSheaf.carrier.toPresheaf).toFaceData.face n simplex i))
    simp only [G.faceRestrictionLinear_apply] at hmap
    change
      Site.FinitePosetCechFaceRestriction
          (G.tupleGeometry.toSimplicialFaceAction
            G.obstructionSheaf.carrier.toPresheaf).toFaceData
          (r • c) simplex i =
        r • Site.FinitePosetCechFaceRestriction
          (G.tupleGeometry.toSimplicialFaceAction
            G.obstructionSheaf.carrier.toPresheaf).toFaceData
          c simplex i at hmap
    by_cases hi : Even i.val
    · simpa only [signedTerm, hi, if_true] using hmap
    · simp only [signedTerm, hi, if_false]
      rw [hmap, smul_neg]
  rw [hfun, Finset.smul_sum]

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

/-- The generated restriction differential as a coefficient-linear map. -/
noncomputable def differentialLinear (G : FiniteMeasurementGeometry M) (n : Nat) :
    letI := G.coeffCommRing
    letI := G.cochainAddCommGroup n
    letI := G.cochainAddCommGroup (n + 1)
    letI := G.cochainModule n
    letI := G.cochainModule (n + 1)
    G.CechCochain n →ₗ[M.Coeff] G.CechCochain (n + 1) := by
  letI := G.coeffCommRing
  letI := G.cochainAddCommGroup n
  letI := G.cochainAddCommGroup (n + 1)
  letI := G.cochainModule n
  letI := G.cochainModule (n + 1)
  exact {
    toFun := G.cechComplex.differential n
    map_add' := G.differential_add n
    map_smul' := G.differential_smul n
  }

/-- Degree-`n` cocycles use the existing finite-poset Čech kernel API. -/
abbrev CechCocycle (G : FiniteMeasurementGeometry M) (n : Nat) :=
  Site.FinitePosetCechCocycle G.cechComplex n

/-- Existing finite-poset image-killing relation generated by the actual differential. -/
noncomputable def coboundaryRelation (G : FiniteMeasurementGeometry M) :
    (n : Nat) -> Site.FinitePosetCechCoboundaryRelation G.cechComplex n
  | 0 => {
      related := fun x y => x = y
      refl := fun _ => rfl
      symm := fun h => h.symm
      trans := fun h₁ h₂ => h₁.trans h₂
      kills_image := by
        intro _ himage
        exact False.elim himage
    }
  | n + 1 => by
      letI := G.cochainAddCommGroup n
      letI := G.cochainAddCommGroup (n + 1)
      letI := G.cochainAddCommGroup (n + 2)
      exact {
        related := fun x y =>
          ∃ b : G.CechCochain n, x.1 - y.1 = G.differentialHom n b
        refl := by
          intro x
          exact ⟨0, by simp⟩
        symm := by
          rintro x y ⟨b, hb⟩
          refine ⟨-b, ?_⟩
          calc
            y.1 - x.1 = -(x.1 - y.1) := by abel
            _ = -(G.differentialHom n b) := by rw [hb]
            _ = G.differentialHom n (-b) := by simp
        trans := by
          rintro x y z ⟨bxy, hxy⟩ ⟨byz, hyz⟩
          refine ⟨bxy + byz, ?_⟩
          rw [map_add, ← hxy, ← hyz]
          abel
        kills_image := by
          rintro cocycle ⟨b, hb⟩
          refine ⟨-b, ?_⟩
          have hzero :
              Site.FinitePosetCechZeroCochain G.cechComplex.additive (n + 1) =
                (0 : G.CechCochain (n + 1)) := by
            funext simplex
            rfl
          calc
            (Site.FinitePosetCechZeroCocycle G.cechComplex (n + 1)).1 -
                cocycle.1 = -cocycle.1 := by
                  rw [show
                    (Site.FinitePosetCechZeroCocycle
                      G.cechComplex (n + 1)).1 =
                        Site.FinitePosetCechZeroCochain
                          G.cechComplex.additive (n + 1) from rfl,
                    hzero]
                  simp
            _ = -(G.cechComplex.differential n b) := by rw [hb]
            _ = G.differentialHom n (-b) := by
              simpa [differentialHom] using
                ((G.differentialHom n).map_neg b).symm
      }

/-- Generated Čech `H^n` is the existing finite-poset kernel/image quotient. -/
abbrev CechHn (G : FiniteMeasurementGeometry M) (n : Nat) :=
  Site.FinitePosetCechCohomology G.cechComplex n (G.coboundaryRelation n)

/-- Zero class in the generated finite-poset Čech `H^n`. -/
noncomputable def zeroClass (G : FiniteMeasurementGeometry M) (n : Nat) :
    G.CechHn n :=
  Quotient.mk (Site.FinitePosetCechCoboundarySetoid (G.coboundaryRelation n))
    (Site.FinitePosetCechZeroCocycle G.cechComplex n)

/-- Send an actual cocycle representative to its generated cohomology class. -/
noncomputable def classOfCocycle (G : FiniteMeasurementGeometry M) (n : Nat) :
    G.CechCocycle n -> G.CechHn n :=
  Quotient.mk (Site.FinitePosetCechCoboundarySetoid (G.coboundaryRelation n))

end FiniteMeasurementGeometry

/-! ### Explicit finite-dimensional coefficient branch -/

/--
Part VIII definition 4.1, finite-dimensional branch.  This surface does not
require the section carriers to be finite: it records finite bases and the
actual canonical restriction differential as a finite matrix.
-/
structure FiniteDimensionalCechModel (M : MeasurementProfile.{u, v})
    (G : FiniteMeasurementGeometry M) [Field M.Coeff] where
  /-- Selected finite-dimensional cochain space in each degree. -/
  CochainSpace : Nat -> Type u
  /-- Finite basis index for each selected cochain space. -/
  CochainIndex : Nat -> Type u
  [cochainIndexFintype : (n : Nat) -> Fintype (CochainIndex n)]
  [cochainIndexDecidableEq : (n : Nat) -> DecidableEq (CochainIndex n)]
  [cochainAddCommGroup : (n : Nat) -> AddCommGroup (CochainSpace n)]
  [cochainModule : (n : Nat) -> Module M.Coeff (CochainSpace n)]
  /-- Explicit finite basis for each selected cochain space. -/
  cochainBasis :
    (n : Nat) -> Module.Basis (CochainIndex n) M.Coeff
      (CochainSpace n)
  /-- Additive identification with the canonical cover-generated cochains. -/
  cochainEquivCanonical :
    (n : Nat) ->
      CochainSpace n ≃+
        Site.FinitePosetCechCochain
          G.coefficientRegime n
  /-- The cochain identification respects the selected coefficient action. -/
  cochainEquivCanonical_smul :
    ∀ (n : Nat) (r : M.Coeff) (c : CochainSpace n),
      letI := G.coeffCommRing
      letI := G.cochainAddCommGroup n
      letI := G.cochainModule n
      cochainEquivCanonical n (r • c) =
        r • cochainEquivCanonical n c
  /-- Selected coefficient-linear differential. -/
  differentialLinear :
    (n : Nat) ->
      CochainSpace n →ₗ[M.Coeff] CochainSpace (n + 1)
  differential_eq_canonical :
    ∀ n c, cochainEquivCanonical (n + 1) (differentialLinear n c) =
      G.cechComplex.differential n (cochainEquivCanonical n c)
  differential_comp :
    ∀ n c, differentialLinear (n + 1) (differentialLinear n c) = 0
  /-- Matrix of the selected differential in the explicit bases. -/
  differentialMatrix :
    (n : Nat) -> Matrix (CochainIndex (n + 1)) (CochainIndex n) M.Coeff
  differentialMatrix_correct :
    ∀ n,
      LinearMap.toMatrix (cochainBasis n) (cochainBasis (n + 1))
        (differentialLinear n) = differentialMatrix n

attribute [instance] FiniteDimensionalCechModel.cochainIndexFintype
attribute [instance] FiniteDimensionalCechModel.cochainIndexDecidableEq
attribute [instance] FiniteDimensionalCechModel.cochainAddCommGroup
attribute [instance] FiniteDimensionalCechModel.cochainModule

namespace FiniteDimensionalCechModel

variable {M : MeasurementProfile.{u, v}} {G : FiniteMeasurementGeometry M}
  [Field M.Coeff]

/-- Actual cochain module of the explicit finite-dimensional model. -/
abbrev Cochain (F : FiniteDimensionalCechModel M G) (n : Nat) :=
  F.CochainSpace n

/-- Actual kernel of the selected finite differential matrix. -/
abbrev Kernel (F : FiniteDimensionalCechModel M G) (n : Nat) :=
  LinearMap.ker (F.differentialLinear n)

/-- Actual image of the selected finite differential matrix. -/
abbrev Image (F : FiniteDimensionalCechModel M G) (n : Nat) :=
  LinearMap.range (F.differentialLinear n)

/-- Previous differential, corestricted to the next cocycle kernel. -/
noncomputable def boundaryLinear (F : FiniteDimensionalCechModel M G) (n : Nat) :
    F.Cochain n →ₗ[M.Coeff] F.Kernel (n + 1) :=
  (F.differentialLinear n).codRestrict (LinearMap.ker (F.differentialLinear (n + 1)))
    fun c => F.differential_comp n c

/-- Actual boundary submodule, with no incoming differential in degree zero. -/
noncomputable def Boundaries (F : FiniteDimensionalCechModel M G) :
    (n : Nat) -> Submodule M.Coeff (F.Kernel n)
  | 0 => ⊥
  | n + 1 => LinearMap.range (F.boundaryLinear n)

/-- Finite-dimensional Čech cohomology as the actual kernel/image quotient. -/
noncomputable def Cohomology (F : FiniteDimensionalCechModel M G) (n : Nat) : Type u :=
  F.Kernel n ⧸ F.Boundaries n

noncomputable instance cohomologyAddCommGroup
    (F : FiniteDimensionalCechModel M G) (n : Nat) : AddCommGroup (F.Cohomology n) := by
  unfold Cohomology
  infer_instance

noncomputable instance cohomologyModule
    (F : FiniteDimensionalCechModel M G) (n : Nat) : Module M.Coeff (F.Cohomology n) := by
  unfold Cohomology
  infer_instance

/-- Every cochain module is finite-dimensional, even when its carrier is infinite. -/
theorem cochain_moduleFinite (F : FiniteDimensionalCechModel M G) (n : Nat) :
    Module.Finite M.Coeff (F.Cochain n) :=
  Module.Finite.of_basis (F.cochainBasis n)

/-- Kernel computation is a finite-dimensional linear-algebra object. -/
theorem kernel_moduleFinite (F : FiniteDimensionalCechModel M G) (n : Nat) :
    Module.Finite M.Coeff (F.Kernel n) := by
  letI : Module.Finite M.Coeff (F.Cochain n) := F.cochain_moduleFinite n
  exact FiniteDimensional.of_injective (F.Kernel n).subtype Subtype.val_injective

/-- Image computation is a finite-dimensional linear-algebra object. -/
theorem image_moduleFinite (F : FiniteDimensionalCechModel M G) (n : Nat) :
    Module.Finite M.Coeff (F.Image n) := by
  letI : Module.Finite M.Coeff (F.Cochain (n + 1)) :=
    F.cochain_moduleFinite (n + 1)
  exact FiniteDimensional.of_injective (F.Image n).subtype Subtype.val_injective

/-- Kernel/image quotient is finite-dimensional in every selected degree. -/
theorem cohomology_moduleFinite (F : FiniteDimensionalCechModel M G) (n : Nat) :
    Module.Finite M.Coeff (F.Cohomology n) := by
  letI : Module.Finite M.Coeff (F.Kernel n) := F.kernel_moduleFinite n
  exact Module.Finite.quotient M.Coeff _

/--
The finite-dimensional cocycle kernel is the kernel of the actual canonical
Čech differential, transported along the selected cochain equivalence.
-/
noncomputable def cocycleEquivCanonical
    (F : FiniteDimensionalCechModel M G) (n : Nat) :
    F.Kernel n ≃ G.CechCocycle n where
  toFun z := ⟨F.cochainEquivCanonical n z.1, by
    have hzero :
        Site.FinitePosetCechZeroCochain G.cechComplex.additive (n + 1) =
          (0 : Site.FinitePosetCechCochain G.coefficientRegime (n + 1)) := by
      funext simplex
      rfl
    rw [← F.differential_eq_canonical]
    rw [hzero]
    exact ((map_eq_zero_iff (F.cochainEquivCanonical (n + 1))
      (F.cochainEquivCanonical (n + 1)).injective).mpr z.2)⟩
  invFun z := ⟨(F.cochainEquivCanonical n).symm z.1, by
    have hzero :
        Site.FinitePosetCechZeroCochain G.cechComplex.additive (n + 1) =
          (0 : Site.FinitePosetCechCochain G.coefficientRegime (n + 1)) := by
      funext simplex
      rfl
    apply (F.cochainEquivCanonical (n + 1)).injective
    rw [F.differential_eq_canonical]
    rw [map_zero, ← hzero]
    simpa using z.2⟩
  left_inv z := by
    apply Subtype.ext
    simp
  right_inv z := by
    apply Subtype.ext
    simp

/--
The model quotient relation is exactly the generated finite-poset Čech
coboundary relation.  This is derived from differential compatibility rather
than accepted as a comparison certificate.
-/
theorem quotient_relation_iff_canonical
    (F : FiniteDimensionalCechModel M G) (n : Nat)
    (x y : F.Kernel n) :
    (Submodule.quotientRel (F.Boundaries n)).r x y ↔
      (Site.FinitePosetCechCoboundarySetoid (G.coboundaryRelation n)).r
        (F.cocycleEquivCanonical n x) (F.cocycleEquivCanonical n y) := by
  cases n with
  | zero =>
      rw [Submodule.quotientRel_def]
      change x - y ∈ (⊥ : Submodule M.Coeff (F.Kernel 0)) ↔
        F.cocycleEquivCanonical 0 x = F.cocycleEquivCanonical 0 y
      rw [Submodule.mem_bot]
      constructor
      · intro h
        apply Subtype.ext
        simpa [cocycleEquivCanonical] using
          congrArg Subtype.val (sub_eq_zero.mp h)
      · intro h
        apply sub_eq_zero.mpr
        apply Subtype.ext
        apply (F.cochainEquivCanonical 0).injective
        exact congrArg Subtype.val h
  | succ n =>
      constructor
      · intro h
        rw [Submodule.quotientRel_def] at h
        change x - y ∈ LinearMap.range (F.boundaryLinear n) at h
        rcases h with ⟨b, hb⟩
        refine ⟨F.cochainEquivCanonical n b, ?_⟩
        change F.cochainEquivCanonical (n + 1) x.1 -
            F.cochainEquivCanonical (n + 1) y.1 =
          G.cechComplex.differential n (F.cochainEquivCanonical n b)
        have hbval : F.differentialLinear n b = x.1 - y.1 := by
          exact congrArg Subtype.val hb
        rw [← map_sub, ← hbval, F.differential_eq_canonical]
      · rintro ⟨b, hb⟩
        rw [Submodule.quotientRel_def]
        change x - y ∈ LinearMap.range (F.boundaryLinear n)
        refine ⟨(F.cochainEquivCanonical n).symm b, ?_⟩
        apply Subtype.ext
        change F.differentialLinear n ((F.cochainEquivCanonical n).symm b) =
          x.1 - y.1
        apply (F.cochainEquivCanonical (n + 1)).injective
        rw [F.differential_eq_canonical, map_sub]
        change F.cochainEquivCanonical (n + 1) x.1 -
            F.cochainEquivCanonical (n + 1) y.1 =
          G.cechComplex.differential n b at hb
        simpa using hb.symm

/--
The finite-dimensional kernel/image quotient computes the canonical generated
Čech cohomology in every degree.
-/
noncomputable def cohomologyEquivCanonical
    (F : FiniteDimensionalCechModel M G) (n : Nat) :
    F.Cohomology n ≃ G.CechHn n :=
  @Quotient.congr _ _
    (Submodule.quotientRel (F.Boundaries n))
    (Site.FinitePosetCechCoboundarySetoid (G.coboundaryRelation n))
    (F.cocycleEquivCanonical n)
    (F.quotient_relation_iff_canonical n)

end FiniteDimensionalCechModel

/--
Certified procedures acting on the actual generated Čech differential and
quotient.  Correctness is stated on each procedure input; no final reduction
equivalence is accepted as an input.
-/
structure EffectiveFinitelyPresentedCechProcedure (M : MeasurementProfile.{u, v})
    (G : FiniteMeasurementGeometry M) where
  /-- Selected kernel decision procedure. -/
  kernel : ∀ n, G.CechCochain n -> Bool
  kernel_correct :
    ∀ n c, kernel n c = true ↔ G.differentialHom n c = 0
  /-- Selected image decision procedure. -/
  image : ∀ n, G.CechCochain (n + 1) -> Bool
  image_correct :
    ∀ n c, image n c = true ↔
      ∃ b : G.CechCochain n, G.differentialHom n b = c
  /-- Selected representative procedure for the generated quotient. -/
  quotientRepresentative : ∀ n, G.CechHn n -> G.CechCocycle n
  quotientRepresentative_correct :
    ∀ n h, G.classOfCocycle n (quotientRepresentative n h) = h
  /-- Selected zero-class decision on the generated quotient. -/
  zeroDecision : ∀ n, G.CechHn n -> Bool
  zeroDecision_correct :
    ∀ n h, zeroDecision n h = true ↔ h = G.zeroClass n

/--
Explicit finite-carrier presentation used to construct, rather than assume,
kernel, image, quotient-representative, and zero-class algorithms.  It is the
finite module subcase of the selected effective coefficient route.
-/
structure FiniteCarrierCechPresentation (M : MeasurementProfile.{u, v})
    (G : FiniteMeasurementGeometry M) where
  /-- Explicit finite carrier for every generated Čech cochain degree. -/
  cochainFintype : ∀ n, Fintype (G.CechCochain n)
  /-- Executable equality on every generated Čech cochain degree. -/
  cochainDecidableEq : ∀ n, DecidableEq (G.CechCochain n)
  /-- Explicit finite carrier for every generated cocycle kernel. -/
  cocycleFintype : ∀ n, Fintype (G.CechCocycle n)
  /-- Executable equality on every generated canonical cohomology quotient. -/
  cohomologyDecidableEq : ∀ n, DecidableEq (G.CechHn n)

namespace FiniteCarrierCechPresentation

variable {M : MeasurementProfile.{u, v}} {G : FiniteMeasurementGeometry M}

/-- Search the finite cocycle list and retain the class-equality certificate. -/
def quotientRepresentativeCertified (P : FiniteCarrierCechPresentation M G)
    (n : Nat) (h : G.CechHn n) :
    { c : G.CechCocycle n // G.classOfCocycle n c = h } := by
  letI := P.cocycleFintype n
  letI := P.cohomologyDecidableEq n
  let candidates := (Finset.univ : Finset (G.CechCocycle n)).toList
  let found := candidates.find? fun c => decide (G.classOfCocycle n c = h)
  have hfound : found.isSome = true := by
    rw [List.find?_isSome]
    rcases Quotient.exists_rep h with ⟨c, hc⟩
    exact ⟨c, by simp [candidates], by
      simpa [FiniteMeasurementGeometry.classOfCocycle] using hc⟩
  refine ⟨found.get hfound, ?_⟩
  have hs := List.find?_some (Option.some_get hfound).symm
  simpa [found, candidates] using hs

/-- Representative returned by the explicit finite search. -/
def quotientRepresentative (P : FiniteCarrierCechPresentation M G)
    (n : Nat) (h : G.CechHn n) : G.CechCocycle n :=
  (P.quotientRepresentativeCertified n h).1

/-- The searched representative maps back to the requested canonical class. -/
theorem quotientRepresentative_correct (P : FiniteCarrierCechPresentation M G)
    (n : Nat) (h : G.CechHn n) :
    G.classOfCocycle n (P.quotientRepresentative n h) = h :=
  (P.quotientRepresentativeCertified n h).2

/--
Construct all effective Čech procedures by finite enumeration and decidable
equality.  No kernel/image/quotient correctness field is supplied by the caller.
-/
def toEffectiveProcedure (P : FiniteCarrierCechPresentation M G) :
    EffectiveFinitelyPresentedCechProcedure M G where
  kernel := fun n c => by
    letI := P.cochainDecidableEq (n + 1)
    exact decide (G.differentialHom n c = 0)
  kernel_correct := by
    intro n c
    letI := P.cochainDecidableEq (n + 1)
    simp
  image := fun n c => by
    letI := P.cochainFintype n
    letI := P.cochainDecidableEq (n + 1)
    exact decide (∃ b : G.CechCochain n, G.differentialHom n b = c)
  image_correct := by
    intro n c
    letI := P.cochainFintype n
    letI := P.cochainDecidableEq (n + 1)
    simp
  quotientRepresentative := P.quotientRepresentative
  quotientRepresentative_correct := P.quotientRepresentative_correct
  zeroDecision := fun n h => by
    letI := P.cohomologyDecidableEq n
    exact decide (h = G.zeroClass n)
  zeroDecision_correct := by
    intro n h
    letI := P.cohomologyDecidableEq n
    simp

end FiniteCarrierCechPresentation

/--
An executable solver for finite linear systems over an explicitly presented
commutative semiring. The correctness law is uniform in the matrix and
right-hand side: it is coefficient infrastructure, not a zero-decision
certificate for one selected cohomology class.
-/
structure FiniteLinearSystemSolver (k : Type v) [CommSemiring k] where
  /-- Return a solution of the finite matrix equation when one exists. -/
  solve :
    {m n : Type u} ->
      [Fintype m] -> [DecidableEq m] ->
      [Fintype n] -> [DecidableEq n] ->
      Matrix m n k -> (m -> k) -> Option (n -> k)
  solve_isSome_iff :
    ∀ {m n : Type u}
      [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]
      (A : Matrix m n k) (b : m -> k),
      (solve A b).isSome = true ↔ ∃ x : n -> k, Matrix.mulVec A x = b

namespace FiniteLinearSystemSolver

/--
Executable linear-system solver over a finite commutative semiring, obtained by
enumerating all coordinate vectors. This is deliberately simple but it is a
real search whose correctness is proved for every finite matrix.
-/
def ofFiniteSemiring (k : Type v) [CommSemiring k] [Fintype k] [DecidableEq k] :
    FiniteLinearSystemSolver.{u, v} k where
  solve := fun A b =>
    ((Finset.univ : Finset (_ -> k)).toList.find? fun x =>
      decide (Matrix.mulVec A x = b))
  solve_isSome_iff := by
    intro m n _ _ _ _ A b
    rw [List.find?_isSome]
    simp

/-- Finite-field specialization of the exhaustive matrix solver. -/
abbrev ofFiniteField (k : Type v) [Field k] [Fintype k] [DecidableEq k] :
    FiniteLinearSystemSolver.{u, v} k :=
  ofFiniteSemiring k

end FiniteLinearSystemSolver

/--
Uniform canonical representative procedure for finite linear cosets.  The
laws quantify over every finite matrix and right-hand side, so this is
coefficient infrastructure rather than a certificate for one selected Čech
class.
-/
structure FiniteLinearCosetNormalizer (k : Type v) [Field k] where
  /-- Canonical representative modulo the column space of a finite matrix. -/
  normalize :
    {m n : Type u} ->
      [Fintype m] -> [DecidableEq m] ->
      [Fintype n] -> [DecidableEq n] ->
      Matrix m n k -> (m -> k) -> (m -> k)
  /-- The normalized vector lies in the same matrix coset. -/
  sameCoset :
    ∀ {m n : Type u}
      [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]
      (A : Matrix m n k) (b : m -> k),
      ∃ x : n -> k, Matrix.mulVec A x = b - normalize A b
  /-- Vectors in the same matrix coset receive the same representative. -/
  canonical :
    ∀ {m n : Type u}
      [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]
      (A : Matrix m n k) (b₁ b₂ : m -> k),
      (∃ x : n -> k, Matrix.mulVec A x = b₁ - b₂) ->
      normalize A b₁ = normalize A b₂

namespace FiniteLinearCosetNormalizer

/-- Finite search returning a representative together with its matrix-coset
certificate. -/
def finiteRepresentativeCertified
    (k : Type v) [Field k] [Fintype k] [DecidableEq k]
    {m n : Type u}
    [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]
    (A : Matrix m n k) (b : m -> k) :
    { representative : m -> k //
      ∃ x : n -> k, Matrix.mulVec A x = b - representative } := by
  let solver := FiniteLinearSystemSolver.ofFiniteField k
  let candidates := (Finset.univ : Finset (m -> k)).toList
  let found := candidates.find? fun representative =>
    (solver.solve A (b - representative)).isSome
  have hfound : found.isSome = true := by
    rw [List.find?_isSome]
    refine ⟨b, by simp [candidates], ?_⟩
    rw [solver.solve_isSome_iff]
    refine ⟨0, ?_⟩
    simp
  refine ⟨found.get hfound, ?_⟩
  have hs := List.find?_some (Option.some_get hfound).symm
  exact (solver.solve_isSome_iff A
    (b - found.get hfound)).mp (by simpa [found, candidates] using hs)

/-- Canonical finite-search representative modulo a matrix column space. -/
def finiteRepresentative
    (k : Type v) [Field k] [Fintype k] [DecidableEq k]
    {m n : Type u}
    [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]
    (A : Matrix m n k) (b : m -> k) : m -> k :=
  (finiteRepresentativeCertified k A b).1

/-- Finite search is invariant under changing the input by a matrix-column
vector. -/
theorem finiteRepresentative_eq_of_sub_mem
    (k : Type v) [Field k] [Fintype k] [DecidableEq k]
    {m n : Type u}
    [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]
    (A : Matrix m n k) (b₁ b₂ : m -> k)
    (hcoset : ∃ x : n -> k, Matrix.mulVec A x = b₁ - b₂) :
    finiteRepresentative k A b₁ = finiteRepresentative k A b₂ := by
  let solver := FiniteLinearSystemSolver.ofFiniteField k
  have hpredicate :
      (fun representative : m -> k =>
        (solver.solve A (b₁ - representative)).isSome) =
      (fun representative : m -> k =>
        (solver.solve A (b₂ - representative)).isSome) := by
    funext representative
    apply Bool.eq_iff_iff.mpr
    rw [solver.solve_isSome_iff, solver.solve_isSome_iff]
    rcases hcoset with ⟨offset, hoffset⟩
    constructor
    · rintro ⟨x, hx⟩
      refine ⟨x - offset, ?_⟩
      rw [Matrix.mulVec_sub, hx, hoffset]
      funext i
      simp only [Pi.sub_apply]
      ring
    · rintro ⟨x, hx⟩
      refine ⟨x + offset, ?_⟩
      rw [Matrix.mulVec_add, hx, hoffset]
      funext i
      simp only [Pi.add_apply, Pi.sub_apply]
      ring
  unfold finiteRepresentative finiteRepresentativeCertified
  simp only
  apply Option.some.inj
  rw [Option.some_get, Option.some_get]
  exact congrArg (fun predicate =>
    List.find? predicate (Finset.univ : Finset (m -> k)).toList) hpredicate

/-- Executable canonical coset normalization over a finite field. -/
def ofFiniteField
    (k : Type v) [Field k] [Fintype k] [DecidableEq k] :
    FiniteLinearCosetNormalizer.{u, v} k where
  normalize := finiteRepresentative k
  sameCoset := fun A b => (finiteRepresentativeCertified k A b).2
  canonical := fun A b₁ b₂ hcoset =>
    finiteRepresentative_eq_of_sub_mem k A b₁ b₂ hcoset

end FiniteLinearCosetNormalizer

/-- Finite-dimensional reduction data, including the explicitly presented field. -/
structure FiniteDimensionalCechProcedure (M : MeasurementProfile.{u, v})
    (G : FiniteMeasurementGeometry M) : Type (max (u + 1) v) where
  /-- Explicitly presented coefficient-field structure. -/
  [coeffField : Field M.Coeff]
  /-- Executable equality in the explicitly presented coefficient field. -/
  [coeffDecidableEq : DecidableEq M.Coeff]
  /-- Matrix solver supplied by the explicitly presented coefficient field. -/
  linearSystemSolver :
    letI : Field M.Coeff := coeffField
    FiniteLinearSystemSolver.{u, v} M.Coeff
  /-- Uniform canonical matrix-coset normalizer supplied by the selected
  coefficient field implementation. -/
  cosetNormalizer :
    letI : Field M.Coeff := coeffField
    FiniteLinearCosetNormalizer.{u, v} M.Coeff
  /-- Finite-dimensional matrix model connected to the canonical Čech complex. -/
  model : @FiniteDimensionalCechModel M G coeffField

namespace FiniteDimensionalCechProcedure

/--
The selected finite-dimensional branch computes the canonical Čech quotient,
not a parallel model-only cohomology carrier.
-/
noncomputable def cohomologyEquivCanonical
    {M : MeasurementProfile.{u, v}} {G : FiniteMeasurementGeometry M}
    (P : FiniteDimensionalCechProcedure M G) (n : Nat) :
    @FiniteDimensionalCechModel.Cohomology M G P.coeffField P.model n ≃
      G.CechHn n :=
  @FiniteDimensionalCechModel.cohomologyEquivCanonical M G P.coeffField P.model n

/-- Coordinates of a model cochain in its explicit basis. -/
def cochainCoordinates
    {M : MeasurementProfile.{u, v}} {G : FiniteMeasurementGeometry M}
    (P : FiniteDimensionalCechProcedure M G) (n : Nat)
    (c : @FiniteDimensionalCechModel.Cochain M G P.coeffField P.model n) :
    @FiniteDimensionalCechModel.CochainIndex M G P.coeffField P.model n -> M.Coeff := by
  letI : Field M.Coeff := P.coeffField
  exact fun i => (P.model.cochainBasis n).repr c i

/-- Decidable equality on cochains obtained from the explicit selected basis. -/
def modelCochainDecidableEq
    {M : MeasurementProfile.{u, v}} {G : FiniteMeasurementGeometry M}
    (P : FiniteDimensionalCechProcedure M G) (n : Nat) :
    DecidableEq (@FiniteDimensionalCechModel.Cochain M G P.coeffField P.model n) := by
  letI : Field M.Coeff := P.coeffField
  letI : DecidableEq M.Coeff := P.coeffDecidableEq
  exact (P.model.cochainBasis n).repr.toEquiv.decidableEq

/--
Decide whether a difference of cocycles is a boundary by solving the actual
previous-differential matrix. Degree zero has no incoming differential.
-/
def quotientRelationDecision
    {M : MeasurementProfile.{u, v}} {G : FiniteMeasurementGeometry M}
    (P : FiniteDimensionalCechProcedure M G) :
    (n : Nat) ->
      @FiniteDimensionalCechModel.Kernel M G P.coeffField P.model n ->
      @FiniteDimensionalCechModel.Kernel M G P.coeffField P.model n -> Bool
  | 0, x, y => by
      letI : Field M.Coeff := P.coeffField
      letI : DecidableEq M.Coeff := P.coeffDecidableEq
      letI : DecidableEq (P.model.Cochain 0) := P.modelCochainDecidableEq 0
      letI : DecidableEq (P.model.Kernel 0) := inferInstance
      exact decide (x = y)
  | n + 1, x, y => by
      letI : Field M.Coeff := P.coeffField
      letI : DecidableEq M.Coeff := P.coeffDecidableEq
      exact (P.linearSystemSolver.solve
        (P.model.differentialMatrix n)
        (P.cochainCoordinates (n + 1) (x.1 - y.1))).isSome

@[simp] theorem quotientRelationDecision_zero_true_iff
    {M : MeasurementProfile.{u, v}} {G : FiniteMeasurementGeometry M}
    (P : FiniteDimensionalCechProcedure M G)
    (x y : @FiniteDimensionalCechModel.Kernel M G P.coeffField P.model 0) :
    P.quotientRelationDecision 0 x y = true ↔ x = y := by
  letI : Field M.Coeff := P.coeffField
  letI : DecidableEq M.Coeff := P.coeffDecidableEq
  letI : DecidableEq (P.model.Cochain 0) := P.modelCochainDecidableEq 0
  letI : DecidableEq (P.model.Kernel 0) := inferInstance
  simp [quotientRelationDecision]

@[simp] theorem quotientRelationDecision_succ
    {M : MeasurementProfile.{u, v}} {G : FiniteMeasurementGeometry M}
    (P : FiniteDimensionalCechProcedure M G) (n : Nat)
    (x y : @FiniteDimensionalCechModel.Kernel M G P.coeffField P.model (n + 1)) :
    letI : Field M.Coeff := P.coeffField
    P.quotientRelationDecision (n + 1) x y =
      (P.linearSystemSolver.solve
        (P.model.differentialMatrix n)
        (P.cochainCoordinates (n + 1) (x.1 - y.1))).isSome := by
  rfl

/-- Decidable quotient equality obtained from the actual matrix relation. -/
def modelCohomologyDecidableEq
    {M : MeasurementProfile.{u, v}} {G : FiniteMeasurementGeometry M}
    (P : FiniteDimensionalCechProcedure M G) (n : Nat) :
    DecidableEq
      (@FiniteDimensionalCechModel.Cohomology M G P.coeffField P.model n) := by
  letI : Field M.Coeff := P.coeffField
  letI : DecidableEq M.Coeff := P.coeffDecidableEq
  let relationDecision : DecidableRel
      (Submodule.quotientRel (P.model.Boundaries n)) :=
    fun x y => decidable_of_iff
      (P.quotientRelationDecision n x y = true)
      (by
        cases n with
        | zero =>
            rw [quotientRelationDecision_zero_true_iff]
            rw [Submodule.quotientRel_def]
            change x = y ↔ x - y = 0
            exact ⟨fun h => sub_eq_zero.mpr h, fun h => sub_eq_zero.mp h⟩
        | succ n =>
            rw [quotientRelationDecision_succ]
            rw [P.linearSystemSolver.solve_isSome_iff
              (P.model.differentialMatrix n)
              (P.cochainCoordinates (n + 1) (x.1 - y.1))]
            rw [Submodule.quotientRel_def]
            change
              (∃ coordinates : P.model.CochainIndex n -> M.Coeff,
                Matrix.mulVec (P.model.differentialMatrix n) coordinates =
                  P.cochainCoordinates (n + 1) (x.1 - y.1)) ↔
                x - y ∈ LinearMap.range (P.model.boundaryLinear n)
            constructor
            · rintro ⟨coordinates, hcoordinates⟩
              let b : P.model.Cochain n :=
                (P.model.cochainBasis n).repr.symm
                  (Finsupp.equivFunOnFinite.symm coordinates)
              refine ⟨b, ?_⟩
              apply Subtype.ext
              apply (P.model.cochainBasis (n + 1)).repr.injective
              have hmatrix := LinearMap.toMatrix_mulVec_repr
                (P.model.cochainBasis n) (P.model.cochainBasis (n + 1))
                (P.model.differentialLinear n) b
              rw [P.model.differentialMatrix_correct] at hmatrix
              have hbcoords : (P.model.cochainBasis n).repr b =
                  Finsupp.equivFunOnFinite.symm coordinates := by
                simp [b]
              rw [hbcoords] at hmatrix
              change (P.model.cochainBasis (n + 1)).repr
                  (P.model.differentialLinear n b) =
                (P.model.cochainBasis (n + 1)).repr (x.1 - y.1)
              apply Finsupp.ext
              intro i
              exact congrFun (hmatrix.symm.trans hcoordinates) i
            · rintro ⟨b, hb⟩
              refine ⟨P.cochainCoordinates n b, ?_⟩
              have hmatrix := LinearMap.toMatrix_mulVec_repr
                (P.model.cochainBasis n) (P.model.cochainBasis (n + 1))
                (P.model.differentialLinear n) b
              rw [P.model.differentialMatrix_correct] at hmatrix
              have hbval : P.model.differentialLinear n b = x.1 - y.1 :=
                congrArg Subtype.val hb
              have hbcoords := congrArg (fun c =>
                ((P.model.cochainBasis (n + 1)).repr c :
                  P.model.CochainIndex (n + 1) -> M.Coeff)) hbval
              change Matrix.mulVec (P.model.differentialMatrix n)
                  (fun i => (P.model.cochainBasis n).repr b i) =
                (fun i => (P.model.cochainBasis (n + 1)).repr (x.1 - y.1) i)
              exact hmatrix.trans hbcoords)
  exact @Quotient.decidableEq _ _ relationDecision

/-- Reconstruct a model cochain from its finite coordinate vector. -/
def cochainOfCoordinates
    {M : MeasurementProfile.{u, v}} {G : FiniteMeasurementGeometry M}
    (P : FiniteDimensionalCechProcedure M G) (n : Nat)
    (coordinates :
      @FiniteDimensionalCechModel.CochainIndex M G P.coeffField P.model n ->
        M.Coeff) :
    @FiniteDimensionalCechModel.Cochain M G P.coeffField P.model n := by
  letI : Field M.Coeff := P.coeffField
  exact (P.model.cochainBasis n).repr.symm
    (Finsupp.equivFunOnFinite.symm coordinates)

/-- Coordinate reconstruction is inverse to the selected finite basis. -/
theorem cochainCoordinates_cochainOfCoordinates
    {M : MeasurementProfile.{u, v}} {G : FiniteMeasurementGeometry M}
    (P : FiniteDimensionalCechProcedure M G) (n : Nat)
    (coordinates :
      @FiniteDimensionalCechModel.CochainIndex M G P.coeffField P.model n ->
        M.Coeff) :
    P.cochainCoordinates n (P.cochainOfCoordinates n coordinates) = coordinates := by
  letI : Field M.Coeff := P.coeffField
  funext i
  simp [cochainOfCoordinates, cochainCoordinates]

/-- Coordinates preserve subtraction in the selected finite basis. -/
@[simp] theorem cochainCoordinates_sub
    {M : MeasurementProfile.{u, v}} {G : FiniteMeasurementGeometry M}
    (P : FiniteDimensionalCechProcedure M G) (n : Nat)
    (c d : @FiniteDimensionalCechModel.Cochain M G P.coeffField P.model n) :
    let _ : Field M.Coeff := P.coeffField
    P.cochainCoordinates n (c - d) =
      P.cochainCoordinates n c - P.cochainCoordinates n d := by
  letI : Field M.Coeff := P.coeffField
  funext i
  simp [cochainCoordinates]

/-- The actual differential in coordinates is multiplication by the selected
finite differential matrix. -/
theorem cochainCoordinates_differential
    {M : MeasurementProfile.{u, v}} {G : FiniteMeasurementGeometry M}
    (P : FiniteDimensionalCechProcedure M G) (n : Nat)
    (c : @FiniteDimensionalCechModel.Cochain M G P.coeffField P.model n) :
    let _ : Field M.Coeff := P.coeffField
    P.cochainCoordinates (n + 1)
        (@FiniteDimensionalCechModel.differentialLinear M G P.coeffField
          P.model n c) =
      Matrix.mulVec
        (@FiniteDimensionalCechModel.differentialMatrix M G P.coeffField
          P.model n)
        (P.cochainCoordinates n c) := by
  letI : Field M.Coeff := P.coeffField
  have hmatrix := LinearMap.toMatrix_mulVec_repr
    (P.model.cochainBasis n) (P.model.cochainBasis (n + 1))
    (P.model.differentialLinear n) c
  rw [P.model.differentialMatrix_correct] at hmatrix
  funext i
  exact congrFun hmatrix.symm i

/-- Underlying normalized cochain of a positive-degree model cocycle. -/
def normalizedCochainSucc
    {M : MeasurementProfile.{u, v}} {G : FiniteMeasurementGeometry M}
    (P : FiniteDimensionalCechProcedure M G) (n : Nat)
    (z : @FiniteDimensionalCechModel.Kernel M G P.coeffField P.model (n + 1)) :
    @FiniteDimensionalCechModel.Cochain M G P.coeffField P.model (n + 1) := by
  letI : Field M.Coeff := P.coeffField
  let coordinates := P.cochainCoordinates (n + 1) z.1
  let normalizedCoordinates :=
    P.cosetNormalizer.normalize (P.model.differentialMatrix n) coordinates
  exact P.cochainOfCoordinates (n + 1) normalizedCoordinates

/-- The normalized cochain has exactly the coordinates selected by the
uniform coset normalizer. -/
@[simp] theorem cochainCoordinates_normalizedCochainSucc
    {M : MeasurementProfile.{u, v}} {G : FiniteMeasurementGeometry M}
    (P : FiniteDimensionalCechProcedure M G) (n : Nat)
    (z : @FiniteDimensionalCechModel.Kernel M G P.coeffField P.model (n + 1)) :
    let _ : Field M.Coeff := P.coeffField
    P.cochainCoordinates (n + 1) (P.normalizedCochainSucc n z) =
      P.cosetNormalizer.normalize (P.model.differentialMatrix n)
        (P.cochainCoordinates (n + 1) z.1) := by
  letI : Field M.Coeff := P.coeffField
  simp [normalizedCochainSucc, cochainCoordinates_cochainOfCoordinates]

/-- Matrix-coset normalization preserves the cocycle kernel because
consecutive selected differentials compose to zero. -/
theorem normalizedCochainSucc_mem_kernel
    {M : MeasurementProfile.{u, v}} {G : FiniteMeasurementGeometry M}
    (P : FiniteDimensionalCechProcedure M G) (n : Nat)
    (z : @FiniteDimensionalCechModel.Kernel M G P.coeffField P.model (n + 1)) :
    @FiniteDimensionalCechModel.differentialLinear M G P.coeffField P.model
      (n + 1) (P.normalizedCochainSucc n z) = 0 := by
  letI : Field M.Coeff := P.coeffField
  let coordinates := P.cochainCoordinates (n + 1) z.1
  let normalizedCoordinates :=
    P.cosetNormalizer.normalize (P.model.differentialMatrix n) coordinates
  let normalized := P.normalizedCochainSucc n z
  obtain ⟨x, hx⟩ := P.cosetNormalizer.sameCoset
    (P.model.differentialMatrix n) coordinates
  let b := P.cochainOfCoordinates n x
  have hboundary : P.model.differentialLinear n b = z.1 - normalized := by
    apply (P.model.cochainBasis (n + 1)).repr.injective
    apply Finsupp.ext
    intro i
    have hcoordinates : P.cochainCoordinates (n + 1)
          (P.model.differentialLinear n b) =
        P.cochainCoordinates (n + 1) (z.1 - normalized) := by
      rw [P.cochainCoordinates_differential, P.cochainCoordinates_sub,
        P.cochainCoordinates_cochainOfCoordinates]
      simpa [coordinates, normalizedCoordinates, normalized,
        cochainCoordinates_normalizedCochainSucc] using hx
    simpa [cochainCoordinates] using congrFun hcoordinates i
  have hnormalized : normalized = z.1 - P.model.differentialLinear n b := by
    rw [hboundary]
    abel
  change P.model.differentialLinear (n + 1) normalized = 0
  rw [hnormalized, map_sub, z.2, P.model.differential_comp]
  simp

/-- Canonical normalized representative of a positive-degree model cocycle. -/
def normalizedCocycleSucc
    {M : MeasurementProfile.{u, v}} {G : FiniteMeasurementGeometry M}
    (P : FiniteDimensionalCechProcedure M G) (n : Nat)
    (z : @FiniteDimensionalCechModel.Kernel M G P.coeffField P.model (n + 1)) :
    @FiniteDimensionalCechModel.Kernel M G P.coeffField P.model (n + 1) :=
  ⟨P.normalizedCochainSucc n z, P.normalizedCochainSucc_mem_kernel n z⟩

/-- The normalized positive-degree cocycle represents the same model
cohomology class as the input cocycle. -/
theorem normalizedCocycleSucc_sameClass
    {M : MeasurementProfile.{u, v}} {G : FiniteMeasurementGeometry M}
    (P : FiniteDimensionalCechProcedure M G) (n : Nat)
    (z : @FiniteDimensionalCechModel.Kernel M G P.coeffField P.model (n + 1)) :
    let _ : Field M.Coeff := P.coeffField
    (Submodule.quotientRel
      (@FiniteDimensionalCechModel.Boundaries M G P.coeffField P.model
        (n + 1))).r z
      (P.normalizedCocycleSucc n z) := by
  letI : Field M.Coeff := P.coeffField
  rw [Submodule.quotientRel_def]
  change z - P.normalizedCocycleSucc n z ∈
    LinearMap.range (P.model.boundaryLinear n)
  let coordinates := P.cochainCoordinates (n + 1) z.1
  obtain ⟨x, hx⟩ := P.cosetNormalizer.sameCoset
    (P.model.differentialMatrix n) coordinates
  let b := P.cochainOfCoordinates n x
  refine ⟨b, ?_⟩
  apply Subtype.ext
  apply (P.model.cochainBasis (n + 1)).repr.injective
  apply Finsupp.ext
  intro i
  have hcoordinates : P.cochainCoordinates (n + 1)
        (P.model.differentialLinear n b) =
      P.cochainCoordinates (n + 1)
        (z.1 - (P.normalizedCocycleSucc n z).1) := by
    rw [P.cochainCoordinates_differential, P.cochainCoordinates_sub,
      P.cochainCoordinates_cochainOfCoordinates]
    simpa [coordinates, normalizedCocycleSucc,
      cochainCoordinates_normalizedCochainSucc] using hx
  simpa [FiniteDimensionalCechModel.boundaryLinear,
    cochainCoordinates] using congrFun hcoordinates i

/-- The uniform normalizer assigns equal positive-degree cocycles to related
model cocycles. -/
theorem normalizedCocycleSucc_eq_of_rel
    {M : MeasurementProfile.{u, v}} {G : FiniteMeasurementGeometry M}
    (P : FiniteDimensionalCechProcedure M G) (n : Nat)
    (z w : @FiniteDimensionalCechModel.Kernel M G P.coeffField P.model (n + 1))
    (hrel : let _ : Field M.Coeff := P.coeffField
      (Submodule.quotientRel
        (@FiniteDimensionalCechModel.Boundaries M G P.coeffField P.model
          (n + 1))).r z w) :
    let _ : Field M.Coeff := P.coeffField
    P.normalizedCocycleSucc n z = P.normalizedCocycleSucc n w := by
  letI : Field M.Coeff := P.coeffField
  rw [Submodule.quotientRel_def] at hrel
  change z - w ∈ LinearMap.range (P.model.boundaryLinear n) at hrel
  rcases hrel with ⟨b, hb⟩
  have hcoordinates :
      ∃ x : P.model.CochainIndex n -> M.Coeff,
        Matrix.mulVec (P.model.differentialMatrix n) x =
          P.cochainCoordinates (n + 1) z.1 -
            P.cochainCoordinates (n + 1) w.1 := by
    refine ⟨P.cochainCoordinates n b, ?_⟩
    rw [← P.cochainCoordinates_differential n b]
    have hbval : P.model.differentialLinear n b = z.1 - w.1 :=
      congrArg Subtype.val hb
    rw [hbval, P.cochainCoordinates_sub]
  apply Subtype.ext
  apply (P.model.cochainBasis (n + 1)).repr.injective
  have hnormalized := P.cosetNormalizer.canonical
    (P.model.differentialMatrix n)
    (P.cochainCoordinates (n + 1) z.1)
    (P.cochainCoordinates (n + 1) w.1) hcoordinates
  apply Finsupp.ext
  intro i
  have hcoordinates : P.cochainCoordinates (n + 1)
        (P.normalizedCocycleSucc n z).1 =
      P.cochainCoordinates (n + 1)
        (P.normalizedCocycleSucc n w).1 := by
    simpa [normalizedCocycleSucc,
      cochainCoordinates_normalizedCochainSucc] using hnormalized
  simpa [cochainCoordinates] using congrFun hcoordinates i

/-- Canonical representative of a finite-dimensional model cohomology class.
Degree zero uses the trivial incoming-image quotient; positive degrees use the
uniform matrix-coset normalizer. -/
noncomputable def modelQuotientRepresentative
    {M : MeasurementProfile.{u, v}} {G : FiniteMeasurementGeometry M}
    (P : FiniteDimensionalCechProcedure M G) :
    (n : Nat) ->
      @FiniteDimensionalCechModel.Cohomology M G P.coeffField P.model n ->
      @FiniteDimensionalCechModel.Kernel M G P.coeffField P.model n
  | 0 => by
      letI : Field M.Coeff := P.coeffField
      exact @Quotient.lift _ _
        (Submodule.quotientRel (P.model.Boundaries 0)) id
        (fun z w hrel => by
          have hmem : z - w ∈ P.model.Boundaries 0 :=
            (Submodule.quotientRel_def (P.model.Boundaries 0)).mp hrel
          have hzero : z - w = 0 := by
            simpa [FiniteDimensionalCechModel.Boundaries] using hmem
          exact sub_eq_zero.mp hzero)
  | n + 1 => by
      letI : Field M.Coeff := P.coeffField
      exact Quotient.lift (P.normalizedCocycleSucc n) fun z w hrel =>
        P.normalizedCocycleSucc_eq_of_rel n z w hrel

/-- The model representative maps back to the requested kernel/image class. -/
theorem modelQuotientRepresentative_correct
    {M : MeasurementProfile.{u, v}} {G : FiniteMeasurementGeometry M}
    (P : FiniteDimensionalCechProcedure M G) (n : Nat)
    (h : @FiniteDimensionalCechModel.Cohomology M G P.coeffField P.model n) :
    let _ : Field M.Coeff := P.coeffField
    Quotient.mk (Submodule.quotientRel (P.model.Boundaries n))
        (P.modelQuotientRepresentative n h) = h := by
  letI : Field M.Coeff := P.coeffField
  dsimp only
  induction h using Quotient.inductionOn with
  | _ z =>
      cases n with
      | zero => rfl
      | succ n =>
          symm
          apply Quotient.sound
          exact P.normalizedCocycleSucc_sameClass n z

/-- Canonical generated Čech cocycle selected from a finite-dimensional
cohomology class. -/
noncomputable def quotientRepresentative
    {M : MeasurementProfile.{u, v}} {G : FiniteMeasurementGeometry M}
    (P : FiniteDimensionalCechProcedure M G) (n : Nat) (h : G.CechHn n) :
    G.CechCocycle n := by
  letI : Field M.Coeff := P.coeffField
  exact P.model.cocycleEquivCanonical n
    (P.modelQuotientRepresentative n ((P.cohomologyEquivCanonical n).symm h))

/-- The finite-dimensional representative maps back to the requested
canonical generated Čech class. -/
theorem quotientRepresentative_correct
    {M : MeasurementProfile.{u, v}} {G : FiniteMeasurementGeometry M}
    (P : FiniteDimensionalCechProcedure M G) (n : Nat) (h : G.CechHn n) :
    G.classOfCocycle n (P.quotientRepresentative n h) = h := by
  letI : Field M.Coeff := P.coeffField
  have hmodel := congrArg (P.cohomologyEquivCanonical n)
    (P.modelQuotientRepresentative_correct n
      ((P.cohomologyEquivCanonical n).symm h))
  simpa [quotientRepresentative, cohomologyEquivCanonical,
    FiniteDimensionalCechModel.cohomologyEquivCanonical,
    FiniteMeasurementGeometry.classOfCocycle] using hmodel

/-- Equality on canonical Čech cohomology is transported from model coordinates. -/
noncomputable def canonicalCohomologyDecidableEq
    {M : MeasurementProfile.{u, v}} {G : FiniteMeasurementGeometry M}
    (P : FiniteDimensionalCechProcedure M G) (n : Nat) :
    DecidableEq (G.CechHn n) := by
  letI := P.modelCohomologyDecidableEq n
  exact (P.cohomologyEquivCanonical n).symm.decidableEq

/-- Decide the canonical zero class through finite-dimensional coordinates. -/
noncomputable def zeroDecision
    {M : MeasurementProfile.{u, v}} {G : FiniteMeasurementGeometry M}
    (P : FiniteDimensionalCechProcedure M G) (n : Nat) (h : G.CechHn n) : Bool := by
  letI := P.canonicalCohomologyDecidableEq n
  exact decide (h = G.zeroClass n)

/-- The coordinate decision is correct for the canonical zero class. -/
theorem zeroDecision_correct
    {M : MeasurementProfile.{u, v}} {G : FiniteMeasurementGeometry M}
    (P : FiniteDimensionalCechProcedure M G) (n : Nat) (h : G.CechHn n) :
    P.zeroDecision n h = true ↔ h = G.zeroClass n := by
  letI := P.canonicalCohomologyDecidableEq n
  simp [zeroDecision]

end FiniteDimensionalCechProcedure

/-- The two coefficient-computation branches selected by definition 4.1. -/
inductive CechComputationProcedure (M : MeasurementProfile.{u, v})
    (G : FiniteMeasurementGeometry M) where
  | finiteDimensional (procedure : FiniteDimensionalCechProcedure M G)
  | effectiveFinitelyPresented
      (procedure : EffectiveFinitelyPresentedCechProcedure M G)

/-- Selected coefficient-computation route from Part VIII definition 4.1. -/
inductive CoefficientComputationRoute where
  | finiteDimensionalLinearAlgebra
  | effectiveFinitelyPresented
  deriving DecidableEq

namespace CechComputationProcedure

/-- Expose which of the two definition 4.1 branches was selected. -/
def route {M : MeasurementProfile.{u, v}} {G : FiniteMeasurementGeometry M} :
    CechComputationProcedure M G -> CoefficientComputationRoute
  | .finiteDimensional _ => .finiteDimensionalLinearAlgebra
  | .effectiveFinitelyPresented _ => .effectiveFinitelyPresented

/-- Run the zero-class decision belonging to the selected coefficient route. -/
def zeroDecision {M : MeasurementProfile.{u, v}}
    {G : FiniteMeasurementGeometry M}
    (P : CechComputationProcedure M G) (n : Nat) : G.CechHn n -> Bool :=
  match P with
  | .finiteDimensional procedure => procedure.zeroDecision n
  | .effectiveFinitelyPresented procedure => procedure.zeroDecision n

/-- Select a canonical generated Čech cocycle through either computation
route. -/
noncomputable def quotientRepresentative {M : MeasurementProfile.{u, v}}
    {G : FiniteMeasurementGeometry M}
    (P : CechComputationProcedure M G) (n : Nat) :
    G.CechHn n -> G.CechCocycle n :=
  match P with
  | .finiteDimensional procedure => procedure.quotientRepresentative n
  | .effectiveFinitelyPresented procedure => procedure.quotientRepresentative n

/-- Either selected coefficient route returns a representative of the input
canonical class. -/
theorem quotientRepresentative_correct {M : MeasurementProfile.{u, v}}
    {G : FiniteMeasurementGeometry M}
    (P : CechComputationProcedure M G) (n : Nat) (h : G.CechHn n) :
    G.classOfCocycle n (P.quotientRepresentative n h) = h := by
  cases P with
  | finiteDimensional procedure =>
      exact procedure.quotientRepresentative_correct n h
  | effectiveFinitelyPresented procedure =>
      exact procedure.quotientRepresentative_correct n h

/-- The selected route decides equality with the canonical zero class. -/
theorem zeroDecision_correct {M : MeasurementProfile.{u, v}}
    {G : FiniteMeasurementGeometry M}
    (P : CechComputationProcedure M G) (n : Nat) (h : G.CechHn n) :
    P.zeroDecision n h = true ↔ h = G.zeroClass n := by
  cases P with
  | finiteDimensional procedure => exact procedure.zeroDecision_correct n h
  | effectiveFinitelyPresented procedure => exact procedure.zeroDecision_correct n h

end CechComputationProcedure

/-- Availability state selected before running the structural zero decision. -/
inductive VerdictAvailability where
  | measured
  | unmeasured
  | unknown
  | notComputed
  deriving DecidableEq

/--
Selected verdict availability algorithm and its soundness against profile
predicates.  In the measured branch, zero/nonzero is decided by the selected
Čech coefficient procedure, so a caller cannot replace both outcomes by a
constant unavailable result.
-/
structure VerdictProcedure (M : MeasurementProfile.{u, v})
    (G : FiniteMeasurementGeometry M) (selectedDegree : Nat)
    (domainClass : M.Domain -> G.CechHn selectedDegree)
    (cechProcedure : CechComputationProcedure M G) where
  /-- Decide whether the selected class is measured or has another status. -/
  availability : M.Domain -> VerdictAvailability
  measured_zero_sound :
    ∀ alpha, availability alpha = .measured ->
      cechProcedure.zeroDecision selectedDegree (domainClass alpha) = true ->
      M.InScope alpha ∧ M.Zero alpha
  measured_nonzero_sound :
    ∀ alpha, availability alpha = .measured ->
      cechProcedure.zeroDecision selectedDegree (domainClass alpha) = false ->
      M.InScope alpha ∧ M.NonZero alpha
  unmeasured_sound :
    ∀ alpha, availability alpha = .unmeasured -> M.OutOfScope alpha
  unknown_sound :
    ∀ alpha, availability alpha = .unknown ->
      M.InScope alpha ∧ M.Undecided alpha
  notComputed_sound :
    ∀ alpha, availability alpha = .notComputed ->
      M.NotRunOrUnavailable alpha
  /-- Record the selected method for each profile-domain input. -/
  method : ∀ alpha, M.SelectedMethod alpha
  /-- Record the selected certificate channel for each profile-domain input. -/
  certificate : ∀ alpha, M.CertRef alpha

/--
VIII.Definition 4.1: effective verdict interface for the generated Čech
cohomology.  The verdict is constructed below from the selected five-state
classifier; a completed `MeasurementVerdict` is not a field.
-/
structure EffCoeff (M : MeasurementProfile.{u, v})
    (G : FiniteMeasurementGeometry M) where
  /-- Profile-owned effective interface token. -/
  profileInterface : M.EffCoeff
  /-- Selected cohomological degree measured by the profile domain. -/
  selectedDegree : Nat
  /-- Send each selected profile-domain class to its generated Čech class. -/
  domainClass : M.Domain -> G.CechHn selectedDegree
  /-- Selected certified kernel/image/quotient procedures. -/
  cechProcedure : CechComputationProcedure M G
  /-- Selected five-state verdict procedure using that coefficient route. -/
  verdictProcedure :
    VerdictProcedure M G selectedDegree domainClass cechProcedure

namespace EffCoeff

/-- Compute a structural verdict by running the selected classifier. -/
def verdict {M : MeasurementProfile.{u, v}}
    {G : FiniteMeasurementGeometry M} (E : EffCoeff M G) (alpha : M.Domain) :
    MeasurementVerdict M alpha := by
  generalize havailability : E.verdictProcedure.availability alpha = availability
  cases availability with
  | measured =>
      generalize hzero : E.cechProcedure.zeroDecision E.selectedDegree
        (E.domainClass alpha) = zeroResult
      cases zeroResult with
      | false =>
          exact MeasurementVerdict.measured_nonzero
            (E.verdictProcedure.measured_nonzero_sound alpha havailability hzero).1
            (E.verdictProcedure.measured_nonzero_sound alpha havailability hzero).2
            (E.verdictProcedure.certificate alpha)
      | true =>
          exact MeasurementVerdict.measured_zero
            (E.verdictProcedure.measured_zero_sound alpha havailability hzero).1
            (E.verdictProcedure.measured_zero_sound alpha havailability hzero).2
            (E.verdictProcedure.certificate alpha)
  | unmeasured =>
      exact MeasurementVerdict.unmeasured
        (E.verdictProcedure.unmeasured_sound alpha havailability)
  | unknown =>
      exact MeasurementVerdict.unknown
        (E.verdictProcedure.unknown_sound alpha havailability).1
        (E.verdictProcedure.unknown_sound alpha havailability).2
  | notComputed =>
      exact MeasurementVerdict.not_computed
        (E.verdictProcedure.notComputed_sound alpha havailability)

/-- Verdict data records the selected method and computed certificate channel. -/
def verdictData {M : MeasurementProfile.{u, v}}
    {G : FiniteMeasurementGeometry M} (E : EffCoeff M G) (alpha : M.Domain) :
    VerdictData M alpha where
  verdict := E.verdict alpha
  method? := some (E.verdictProcedure.method alpha)
  cert? := some (E.verdictProcedure.certificate alpha)

end EffCoeff

/-- VIII.Definition 4.1: finite measurement regime with generated computations. -/
structure FiniteMeasurementRegime (M : MeasurementProfile.{u, v}) where
  /-- Selected finite geometry and module-valued coefficient sheaf. -/
  geometry : FiniteMeasurementGeometry M
  /-- Equality in the selected coefficient presentation is decidable. -/
  coeffDecidableEq : DecidableEq M.Coeff
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

/-- Run the selected procedure and retain its method/certificate channels. -/
noncomputable def verdictData {M : MeasurementProfile.{u, v}}
    (R : FiniteMeasurementRegime M) (alpha : M.Domain) :
    VerdictData M alpha :=
  R.effCoeff.verdictData alpha

end FiniteMeasurementRegime

end Measurement
end AAT.AG
