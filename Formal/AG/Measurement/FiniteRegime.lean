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

/-- Finite-dimensional reduction data, including the explicitly presented field. -/
structure FiniteDimensionalCechProcedure (M : MeasurementProfile.{u, v})
    (G : FiniteMeasurementGeometry M) where
  /-- Explicitly presented coefficient-field structure. -/
  coeffField : Field M.Coeff
  /-- Finite-dimensional matrix model connected to the canonical Čech complex. -/
  model : @FiniteDimensionalCechModel M G coeffField

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

end CechComputationProcedure

/-- Result of running a selected structural-verdict procedure. -/
inductive VerdictProcedureResult where
  | zero
  | nonzero
  | unmeasured
  | unknown
  | notComputed
  deriving DecidableEq

/--
Selected verdict algorithm and its soundness against profile predicates.
All five verdict states remain available; zero and nonzero are not assumed to
be logical complements.
-/
structure VerdictProcedure (M : MeasurementProfile.{u, v})
    (G : FiniteMeasurementGeometry M) (selectedDegree : Nat)
    (domainEquiv : M.Domain ≃ G.CechHn selectedDegree) where
  /-- Run the selected five-state classifier. -/
  classify : G.CechHn selectedDegree -> VerdictProcedureResult
  zero_sound :
    ∀ alpha, classify (domainEquiv alpha) = .zero ->
      M.InScope alpha ∧ M.Zero alpha
  nonzero_sound :
    ∀ alpha, classify (domainEquiv alpha) = .nonzero ->
      M.InScope alpha ∧ M.NonZero alpha
  unmeasured_sound :
    ∀ alpha, classify (domainEquiv alpha) = .unmeasured -> M.OutOfScope alpha
  unknown_sound :
    ∀ alpha, classify (domainEquiv alpha) = .unknown ->
      M.InScope alpha ∧ M.Undecided alpha
  notComputed_sound :
    ∀ alpha, classify (domainEquiv alpha) = .notComputed ->
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
  /-- Profile-domain classes identify with generated Čech classes. -/
  domainEquiv : M.Domain ≃ G.CechHn selectedDegree
  /-- Selected certified kernel/image/quotient procedures. -/
  cechProcedure : CechComputationProcedure M G
  /-- Selected five-state verdict procedure on generated Čech classes. -/
  verdictProcedure : VerdictProcedure M G selectedDegree domainEquiv

namespace EffCoeff

/-- Compute a structural verdict by running the selected classifier. -/
def verdict {M : MeasurementProfile.{u, v}}
    {G : FiniteMeasurementGeometry M} (E : EffCoeff M G) (alpha : M.Domain) :
    MeasurementVerdict M alpha := by
  generalize hresult : E.verdictProcedure.classify (E.domainEquiv alpha) = result
  cases result with
  | zero =>
      exact MeasurementVerdict.measured_zero
        (E.verdictProcedure.zero_sound alpha hresult).1
        (E.verdictProcedure.zero_sound alpha hresult).2
        (E.verdictProcedure.certificate alpha)
  | nonzero =>
      exact MeasurementVerdict.measured_nonzero
        (E.verdictProcedure.nonzero_sound alpha hresult).1
        (E.verdictProcedure.nonzero_sound alpha hresult).2
        (E.verdictProcedure.certificate alpha)
  | unmeasured =>
      exact MeasurementVerdict.unmeasured
        (E.verdictProcedure.unmeasured_sound alpha hresult)
  | unknown =>
      exact MeasurementVerdict.unknown
        (E.verdictProcedure.unknown_sound alpha hresult).1
        (E.verdictProcedure.unknown_sound alpha hresult).2
  | notComputed =>
      exact MeasurementVerdict.not_computed
        (E.verdictProcedure.notComputed_sound alpha hresult)

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
