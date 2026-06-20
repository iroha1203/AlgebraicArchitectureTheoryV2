import Formal.AG.Research.QualitySurface.ScalarCollapse

/-!
Cycle 3 evidence for `G-aat-quality-surface-01`.

The file fixes a finite profile-square witness: two path-ordered certificate
transports agree on scalar reading and verdict while disagreeing on selected
support antichain and repair hitting requirement. The discrepancy is recorded
as failure of full-certificate square coherence.
-/

namespace Formal.AG.Research
namespace QualitySurface
namespace ProfileCurvature

/-! ## Finite profile square and certificate tuple -/

/-- The four vertices of a finite two-dimensional profile square. -/
inductive SquareProfile where
  | lowerLeft
  | lowerRight
  | upperLeft
  | upperRight
  deriving DecidableEq, Fintype

/-- A finite atom vocabulary for the profile-curvature witness. -/
inductive CurvatureAtom where
  | a
  | b
  | c
  deriving DecidableEq, Fintype

/-- The selected verdict is intentionally unchanged along both paths. -/
inductive CurvatureVerdict where
  | acceptable
  deriving DecidableEq

/--
Certificates appearing along the profile square.

`lawThenCoverResult` and `coverThenLawResult` live in the same upper-right
certificate space but arise from different path-ordered comparison maps.
-/
inductive SquareCertificate where
  | seed
  | lawStage
  | coverStage
  | lawThenCoverResult
  | coverThenLawResult
  deriving DecidableEq, Fintype

open CurvatureVerdict SquareCertificate

/-- The first selected support branch. -/
def supportA : Set CurvatureAtom :=
  fun x => x = CurvatureAtom.a

/-- The first branch of the split selected support family. -/
def supportB : Set CurvatureAtom :=
  fun x => x = CurvatureAtom.b

/-- The second branch of the split selected support family. -/
def supportC : Set CurvatureAtom :=
  fun x => x = CurvatureAtom.c

/--
A finite certificate tuple over a profile vertex.

The scalar and verdict components are the visible reading. The support family
and repair hitting requirement are the certificate geometry carried underneath.
-/
structure SquareCertificateTuple where
  selectedScalarReading : Nat
  selectedVerdict : CurvatureVerdict
  selectedSupportFamily : Set (Set CurvatureAtom)
  repairHittingRequirement : Nat

/-- A one-branch support family. -/
def oneSupportFamily : Set (Set CurvatureAtom) :=
  fun M => M = supportA

/-- A two-branch support family. -/
def splitSupportFamily : Set (Set CurvatureAtom) :=
  fun M => M = supportB ∨ M = supportC

/-- The initial certificate before either profile change. -/
def seedTuple : SquareCertificateTuple where
  selectedScalarReading := 0
  selectedVerdict := acceptable
  selectedSupportFamily := oneSupportFamily
  repairHittingRequirement := 1

/-- The bottom-edge intermediate certificate after law strengthening. -/
def lawStageTuple : SquareCertificateTuple where
  selectedScalarReading := 1
  selectedVerdict := acceptable
  selectedSupportFamily := oneSupportFamily
  repairHittingRequirement := 1

/-- The left-edge intermediate certificate after cover refinement. -/
def coverStageTuple : SquareCertificateTuple where
  selectedScalarReading := 1
  selectedVerdict := acceptable
  selectedSupportFamily := oneSupportFamily
  repairHittingRequirement := 1

/-- The upper-right certificate reached by law strengthening then cover refinement. -/
def lawThenCoverTuple : SquareCertificateTuple where
  selectedScalarReading := 1
  selectedVerdict := acceptable
  selectedSupportFamily := oneSupportFamily
  repairHittingRequirement := 1

/-- The upper-right certificate reached by cover refinement then law strengthening. -/
def coverThenLawTuple : SquareCertificateTuple where
  selectedScalarReading := 1
  selectedVerdict := acceptable
  selectedSupportFamily := splitSupportFamily
  repairHittingRequirement := 2

/-- Read the tuple carried by a named certificate. -/
def certificateTuple : SquareCertificate -> SquareCertificateTuple
  | seed => seedTuple
  | lawStage => lawStageTuple
  | coverStage => coverStageTuple
  | lawThenCoverResult => lawThenCoverTuple
  | coverThenLawResult => coverThenLawTuple

/-- The profile vertex where a named certificate lives. -/
def profileOf : SquareCertificate -> SquareProfile
  | seed => SquareProfile.lowerLeft
  | lawStage => SquareProfile.lowerRight
  | coverStage => SquareProfile.upperLeft
  | lawThenCoverResult => SquareProfile.upperRight
  | coverThenLawResult => SquareProfile.upperRight

/-- Certificates typed by the profile vertex where they live. -/
def CertificateAt (p : SquareProfile) : Type :=
  { c : SquareCertificate // profileOf c = p }

/-- The selected seed certificate at the lower-left vertex. -/
def seedAt : CertificateAt SquareProfile.lowerLeft :=
  ⟨seed, rfl⟩

/-- The visible scalar reading selected from the certificate tuple. -/
def scalarReading (c : SquareCertificate) : Nat :=
  (certificateTuple c).selectedScalarReading

/-- The selected verdict component. -/
def verdict (c : SquareCertificate) : CurvatureVerdict :=
  (certificateTuple c).selectedVerdict

/-- The selected minimal support family carried by a certificate. -/
def supportFamily (c : SquareCertificate) : Set (Set CurvatureAtom) :=
  (certificateTuple c).selectedSupportFamily

/-- The repair hitting requirement carried by a certificate. -/
def repairHittingNumber (c : SquareCertificate) : Nat :=
  (certificateTuple c).repairHittingRequirement

/-! ## Four typed edge transports and the two path composites -/

/-- A comparison map along one profile-square edge. -/
structure EdgeTransport (source target : SquareProfile) where
  map : CertificateAt source -> CertificateAt target

/-- Bottom edge: strengthen the law universe. -/
def transportLawBottom :
    EdgeTransport SquareProfile.lowerLeft SquareProfile.lowerRight where
  map := fun _ => ⟨lawStage, rfl⟩

/-- Right edge: refine the cover after law strengthening. -/
def transportCoverRight :
    EdgeTransport SquareProfile.lowerRight SquareProfile.upperRight where
  map := fun _ => ⟨lawThenCoverResult, rfl⟩

/-- Left edge: refine the cover first. -/
def transportCoverLeft :
    EdgeTransport SquareProfile.lowerLeft SquareProfile.upperLeft where
  map := fun _ => ⟨coverStage, rfl⟩

/-- Top edge: strengthen the law universe after cover refinement. -/
def transportLawTop :
    EdgeTransport SquareProfile.upperLeft SquareProfile.upperRight where
  map := fun _ => ⟨coverThenLawResult, rfl⟩

/-- The path that strengthens law first and refines cover second. -/
def lawThenCover
    (c : CertificateAt SquareProfile.lowerLeft) :
    CertificateAt SquareProfile.upperRight :=
  transportCoverRight.map (transportLawBottom.map c)

/-- The path that refines cover first and strengthens law second. -/
def coverThenLaw
    (c : CertificateAt SquareProfile.lowerLeft) :
    CertificateAt SquareProfile.upperRight :=
  transportLawTop.map (transportCoverLeft.map c)

/-- The bottom edge sends the seed certificate to the law stage. -/
theorem transportLawBottom_seed :
    (transportLawBottom.map seedAt).val = lawStage :=
  rfl

/-- The right edge sends the law stage to the first upper-right certificate. -/
theorem transportCoverRight_lawStage :
    (transportCoverRight.map (transportLawBottom.map seedAt)).val =
      lawThenCoverResult :=
  rfl

/-- The left edge sends the seed certificate to the cover stage. -/
theorem transportCoverLeft_seed :
    (transportCoverLeft.map seedAt).val = coverStage :=
  rfl

/-- The top edge sends the cover stage to the second upper-right certificate. -/
theorem transportLawTop_coverStage :
    (transportLawTop.map (transportCoverLeft.map seedAt)).val =
      coverThenLawResult :=
  rfl

/-- The law-then-cover path reaches its named upper-right certificate. -/
theorem lawThenCover_seed :
    (lawThenCover seedAt).val = lawThenCoverResult :=
  rfl

/-- The cover-then-law path reaches its named upper-right certificate. -/
theorem coverThenLaw_seed :
    (coverThenLaw seedAt).val = coverThenLawResult :=
  rfl

/-! ## Support antichains along the transported certificates -/

/-- A selected support family is populated by at least one branch. -/
def SupportFamilyNonempty (F : Set (Set CurvatureAtom)) : Prop :=
  ∃ M : Set CurvatureAtom, F M

/-- Selected support branches form an antichain under inclusion. -/
def SupportFamilyAntichain (F : Set (Set CurvatureAtom)) : Prop :=
  ∀ {M N : Set CurvatureAtom},
    F M -> F N -> (∀ x, x ∈ M -> x ∈ N) -> M = N

/-- The law-then-cover transported support family is nonempty. -/
theorem lawThenCover_supportFamily_nonempty :
    SupportFamilyNonempty (supportFamily (lawThenCover seedAt).val) :=
  Exists.intro supportA rfl

/-- The cover-then-law transported support family is nonempty. -/
theorem coverThenLaw_supportFamily_nonempty :
    SupportFamilyNonempty (supportFamily (coverThenLaw seedAt).val) :=
  Exists.intro supportB (Or.inl rfl)

/-- The law-then-cover transported support family is an antichain. -/
theorem lawThenCover_supportFamily_antichain :
    SupportFamilyAntichain (supportFamily (lawThenCover seedAt).val) := by
  intro M N hM hN _hsub
  rw [hM, hN]

/-- The support branches `b` and `a` are distinct. -/
theorem supportB_ne_supportA : supportB ≠ supportA := by
  intro h
  have hbA : CurvatureAtom.b ∈ supportA := by
    rw [← h]
    rfl
  cases hbA

/-- The support branches `b` and `c` are distinct. -/
theorem supportB_ne_supportC : supportB ≠ supportC := by
  intro h
  have hbC : CurvatureAtom.b ∈ supportC := by
    rw [← h]
    rfl
  cases hbC

/-- The cover-then-law transported support family is an antichain. -/
theorem coverThenLaw_supportFamily_antichain :
    SupportFamilyAntichain (supportFamily (coverThenLaw seedAt).val) := by
  intro M N hM hN hsub
  cases hM with
  | inl hMB =>
      cases hN with
      | inl hNB =>
          rw [hMB, hNB]
      | inr hNC =>
          have hbM : CurvatureAtom.b ∈ M := by
            rw [hMB]
            rfl
          have hbN : CurvatureAtom.b ∈ N := hsub CurvatureAtom.b hbM
          rw [hNC] at hbN
          cases hbN
  | inr hMC =>
      cases hN with
      | inl hNB =>
          have hcM : CurvatureAtom.c ∈ M := by
            rw [hMC]
            rfl
          have hcN : CurvatureAtom.c ∈ N := hsub CurvatureAtom.c hcM
          rw [hNB] at hcN
          cases hcN
      | inr hNC =>
          rw [hMC, hNC]

/-! ## Regularity and curvature for the square -/

/-- Full-certificate path coherence for a transported certificate. -/
def FullCertificateAgreement (c₁ c₂ : SquareCertificate) : Prop :=
  scalarReading c₁ = scalarReading c₂ ∧
    verdict c₁ = verdict c₂ ∧
      supportFamily c₁ = supportFamily c₂ ∧
        repairHittingNumber c₁ = repairHittingNumber c₂

/-- Full-certificate path coherence for two typed upper-right certificates. -/
def FullCertificateAgreementAt
    (c₁ c₂ : CertificateAt SquareProfile.upperRight) : Prop :=
  FullCertificateAgreement c₁.val c₂.val

/-- A regular square keeps the full certificate geometry coherent along paths. -/
def RegularSquareCell (c : CertificateAt SquareProfile.lowerLeft) : Prop :=
  FullCertificateAgreementAt (lawThenCover c) (coverThenLaw c)

/-- A curvature cell is a square where full-certificate path coherence fails. -/
def CurvatureCell (c : CertificateAt SquareProfile.lowerLeft) : Prop :=
  ¬ RegularSquareCell c

/-- The two paths agree on the selected scalar reading. -/
theorem same_scalarReading_after_paths :
    scalarReading (lawThenCover seedAt).val =
      scalarReading (coverThenLaw seedAt).val :=
  rfl

/-- The two paths agree on the selected verdict. -/
theorem same_verdict_after_paths :
    verdict (lawThenCover seedAt).val = verdict (coverThenLaw seedAt).val :=
  rfl

/-- The two paths disagree on selected support family. -/
theorem supportFamily_path_ne :
    supportFamily (lawThenCover seedAt).val ≠
      supportFamily (coverThenLaw seedAt).val := by
  intro h
  have hbRight : supportFamily (coverThenLaw seedAt).val supportB := Or.inl rfl
  have hbLeft : supportFamily (lawThenCover seedAt).val supportB := by
    rw [h]
    exact hbRight
  exact supportB_ne_supportA hbLeft

/-- The two paths disagree on repair hitting requirement. -/
theorem repairHittingNumber_path_ne :
    repairHittingNumber (lawThenCover seedAt).val ≠
      repairHittingNumber (coverThenLaw seedAt).val := by
  decide

/-- Support / repair discrepancy after the two path-ordered transports. -/
def SupportRepairPathDiscrepancy
    (c : CertificateAt SquareProfile.lowerLeft) : Prop :=
  supportFamily (lawThenCover c).val ≠ supportFamily (coverThenLaw c).val ∨
    repairHittingNumber (lawThenCover c).val ≠
      repairHittingNumber (coverThenLaw c).val

/-- The seed square has both support and repair discrepancies after transport. -/
theorem supportAndRepairPathDiscrepancy_seed :
    supportFamily (lawThenCover seedAt).val ≠
        supportFamily (coverThenLaw seedAt).val ∧
      repairHittingNumber (lawThenCover seedAt).val ≠
        repairHittingNumber (coverThenLaw seedAt).val :=
  And.intro supportFamily_path_ne repairHittingNumber_path_ne

/-- The seed square has a support / repair discrepancy after transport. -/
theorem supportRepairPathDiscrepancy_seed :
    SupportRepairPathDiscrepancy seedAt :=
  Or.inl supportFamily_path_ne

/-- A support / repair discrepancy violates full-certificate regularity. -/
theorem curvatureCell_of_supportRepair_path_discrepancy
    {c : CertificateAt SquareProfile.lowerLeft}
    (h : SupportRepairPathDiscrepancy c) :
    CurvatureCell c := by
  intro hregular
  cases h with
  | inl hsupport =>
      exact hsupport hregular.2.2.1
  | inr hrepair =>
      exact hrepair hregular.2.2.2

/-- The finite profile square is a curvature cell. -/
theorem seed_curvatureCell : CurvatureCell seedAt :=
  curvatureCell_of_supportRepair_path_discrepancy supportRepairPathDiscrepancy_seed

/--
The finite profile-curvature witness: the scalar reading and verdict are flat
across the two paths, while the full certificate geometry is curved.
-/
theorem same_scalar_verdict_but_curved_square :
    scalarReading (lawThenCover seedAt).val =
        scalarReading (coverThenLaw seedAt).val ∧
      verdict (lawThenCover seedAt).val = verdict (coverThenLaw seedAt).val ∧
        CurvatureCell seedAt := by
  exact And.intro same_scalarReading_after_paths
    (And.intro same_verdict_after_paths seed_curvatureCell)

end ProfileCurvature
end QualitySurface
end Formal.AG.Research
