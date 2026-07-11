import ResearchLean.AG.QualitySurface.SupportHitting

/-!
Cycle 2 evidence for `G-aat-quality-surface-01`.

The file fixes a finite reading-fold witness: two certificates have the same
scalar reading and verdict, while their selected support families and repair
hitting requirements differ.
-/

namespace ResearchLean.AG
namespace QualitySurface
namespace ScalarCollapse

/-- A finite atom vocabulary for the scalar-collapse witness. -/
inductive FoldAtom where
  | a
  | b
  | c
  deriving DecidableEq, Fintype

/-- Two certificates in the same scalar fiber. -/
inductive FoldCertificate where
  | singleSupport
  | splitSupport
  deriving DecidableEq

/-- A deliberately small verdict type: both certificates receive the same verdict. -/
inductive FoldVerdict where
  | acceptable
  deriving DecidableEq

open FoldAtom FoldCertificate FoldVerdict

/-- The first certificate is supported on one atom. -/
def supportA : Set FoldAtom :=
  fun x => x = a

/-- The second certificate has one selected support branch at `b`. -/
def supportB : Set FoldAtom :=
  fun x => x = b

/-- The second certificate has another selected support branch at `c`. -/
def supportC : Set FoldAtom :=
  fun x => x = c

/--
A finite certificate tuple for the scalar-collapse witness.

`selectedViolationCount` is the selected scalar projection used by the reading.
It records a count-like scalar while leaving support and repair-frontier data in
the full certificate tuple.
-/
structure FoldCertificateTuple where
  selectedViolationCount : Nat
  verdict : FoldVerdict
  selectedSupportFamily : Set (Set FoldAtom)
  repairHittingRequirement : Nat

/-- The certificate whose repair frontier has one selected support branch. -/
def singleSupportTuple : FoldCertificateTuple where
  selectedViolationCount := 1
  verdict := acceptable
  selectedSupportFamily := fun M => M = supportA
  repairHittingRequirement := 1

/-- The certificate whose repair frontier has two selected support branches. -/
def splitSupportTuple : FoldCertificateTuple where
  selectedViolationCount := 1
  verdict := acceptable
  selectedSupportFamily := fun M => M = supportB ∨ M = supportC
  repairHittingRequirement := 2

/-- Map certificate names to their full finite tuple. -/
def certificateTuple : FoldCertificate -> FoldCertificateTuple
  | singleSupport => singleSupportTuple
  | splitSupport => splitSupportTuple

/-- The selected scalar reading: project to the selected violation count. -/
def scalarReading (c : FoldCertificate) : Nat :=
  (certificateTuple c).selectedViolationCount

/-- The selected verdict is also unchanged by the fold. -/
def certificateVerdict (c : FoldCertificate) : FoldVerdict :=
  (certificateTuple c).verdict

/-- Selected minimal support family for each certificate. -/
def supportFamily (c : FoldCertificate) : Set (Set FoldAtom) :=
  (certificateTuple c).selectedSupportFamily

/-- Minimal number of support branches a repair must hit in this finite witness. -/
def repairHittingNumber (c : FoldCertificate) : Nat :=
  (certificateTuple c).repairHittingRequirement

/-- A selected support family is populated by at least one support branch. -/
def SupportFamilyNonempty (F : Set (Set FoldAtom)) : Prop :=
  ∃ M : Set FoldAtom, F M

/-- Selected minimal support branches form an antichain under inclusion. -/
def SupportFamilyAntichain (F : Set (Set FoldAtom)) : Prop :=
  ∀ {M N : Set FoldAtom},
    F M -> F N -> (∀ x, x ∈ M -> x ∈ N) -> M = N

/-- A support family with exactly one selected branch. -/
def HasOneSupportBranch (F : Set (Set FoldAtom)) (M : Set FoldAtom) : Prop :=
  F M ∧ ∀ N : Set FoldAtom, F N -> N = M

/-- A support family with exactly two selected branches. -/
def HasTwoSupportBranches (F : Set (Set FoldAtom)) (M N : Set FoldAtom) : Prop :=
  F M ∧ F N ∧ M ≠ N ∧
    ∀ K : Set FoldAtom, F K -> K = M ∨ K = N

/-- The repair hitting requirement agrees with the selected support-family shape. -/
def RepairRequirementMatchesSupportFamily : FoldCertificate -> Prop
  | singleSupport =>
      repairHittingNumber singleSupport = 1 ∧
        HasOneSupportBranch (supportFamily singleSupport) supportA
  | splitSupport =>
      repairHittingNumber splitSupport = 2 ∧
        HasTwoSupportBranches (supportFamily splitSupport) supportB supportC

/-- The scalar reading is the selected violation-count projection. -/
theorem scalarReading_eq_selectedViolationCount (c : FoldCertificate) :
    scalarReading c = (certificateTuple c).selectedViolationCount :=
  rfl

/-- The two certificates have the same scalar reading. -/
theorem same_scalarReading :
    scalarReading singleSupport = scalarReading splitSupport :=
  rfl

/-- The two certificates have the same verdict. -/
theorem same_verdict :
    certificateVerdict singleSupport = certificateVerdict splitSupport :=
  rfl

/-- The support branches `a` and `b` are distinct. -/
theorem supportB_ne_supportA : supportB ≠ supportA := by
  intro h
  have hbA : FoldAtom.b ∈ supportA := by
    rw [← h]
    rfl
  cases hbA

/-- The support branches `b` and `c` are distinct. -/
theorem supportB_ne_supportC : supportB ≠ supportC := by
  intro h
  have hbC : FoldAtom.b ∈ supportC := by
    rw [← h]
    rfl
  cases hbC

/-- The two certificates have different selected support families. -/
theorem supportFamily_ne :
    supportFamily singleSupport ≠ supportFamily splitSupport := by
  intro h
  have hbSplit : supportFamily splitSupport supportB := Or.inl rfl
  have hbSingle : supportFamily singleSupport supportB := by
    rw [h]
    exact hbSplit
  exact supportB_ne_supportA hbSingle

/-- The single-support certificate has hitting requirement one. -/
theorem singleSupport_repairHittingNumber_eq :
    repairHittingNumber singleSupport = 1 :=
  rfl

/-- The split-support certificate has hitting requirement two. -/
theorem splitSupport_repairHittingNumber_eq :
    repairHittingNumber splitSupport = 2 :=
  rfl

/-- Every selected support family in the witness is nonempty. -/
theorem supportFamily_nonempty (c : FoldCertificate) :
    SupportFamilyNonempty (supportFamily c) := by
  cases c with
  | singleSupport =>
      exact Exists.intro supportA rfl
  | splitSupport =>
      exact Exists.intro supportB (Or.inl rfl)

/-- The single-support certificate has exactly one selected support branch. -/
theorem singleSupport_hasOneSupportBranch :
    HasOneSupportBranch (supportFamily singleSupport) supportA := by
  constructor
  · rfl
  · intro N hN
    exact hN

/-- The split-support certificate has exactly two selected support branches. -/
theorem splitSupport_hasTwoSupportBranches :
    HasTwoSupportBranches (supportFamily splitSupport) supportB supportC := by
  constructor
  · exact Or.inl rfl
  · constructor
    · exact Or.inr rfl
    · constructor
      · exact supportB_ne_supportC
      · intro K hK
        exact hK

/-- The selected support branches are antichains for both certificates. -/
theorem supportFamily_antichain (c : FoldCertificate) :
    SupportFamilyAntichain (supportFamily c) := by
  cases c with
  | singleSupport =>
      intro M N hM hN _hsub
      rw [hM, hN]
  | splitSupport =>
      intro M N hM hN hsub
      cases hM with
      | inl hMB =>
          cases hN with
          | inl hNB =>
              rw [hMB, hNB]
          | inr hNC =>
              have hbM : FoldAtom.b ∈ M := by
                rw [hMB]
                rfl
              have hbN : FoldAtom.b ∈ N := hsub FoldAtom.b hbM
              rw [hNC] at hbN
              cases hbN
      | inr hMC =>
          cases hN with
          | inl hNB =>
              have hcM : FoldAtom.c ∈ M := by
                rw [hMC]
                rfl
              have hcN : FoldAtom.c ∈ N := hsub FoldAtom.c hcM
              rw [hNB] at hcN
              cases hcN
          | inr hNC =>
              rw [hMC, hNC]

/-- The named repair hitting requirement matches the selected support family. -/
theorem repairRequirement_matches_supportFamily (c : FoldCertificate) :
    RepairRequirementMatchesSupportFamily c := by
  cases c with
  | singleSupport =>
      exact And.intro singleSupport_repairHittingNumber_eq singleSupport_hasOneSupportBranch
  | splitSupport =>
      exact And.intro splitSupport_repairHittingNumber_eq splitSupport_hasTwoSupportBranches

/-- The two certificates have different repair hitting requirements. -/
theorem repairHittingNumber_ne :
    repairHittingNumber singleSupport ≠ repairHittingNumber splitSupport := by
  decide

/--
The finite reading fold: scalar reading and verdict agree, but support geometry
and repair frontier differ.
-/
theorem same_scalar_and_verdict_but_supportRepair_diff :
    scalarReading singleSupport = scalarReading splitSupport ∧
      certificateVerdict singleSupport = certificateVerdict splitSupport ∧
        supportFamily singleSupport ≠ supportFamily splitSupport ∧
          repairHittingNumber singleSupport ≠ repairHittingNumber splitSupport := by
  exact And.intro same_scalarReading
    (And.intro same_verdict (And.intro supportFamily_ne repairHittingNumber_ne))

/-- Faithfulness of a scalar reading to support and repair data. -/
def ScalarReadingFaithfulToSupportRepair
    (r : FoldCertificate -> Nat) : Prop :=
  ∀ c1 c2 : FoldCertificate,
    r c1 = r c2 ->
      certificateVerdict c1 = certificateVerdict c2 ->
        supportFamily c1 = supportFamily c2 ∧
          repairHittingNumber c1 = repairHittingNumber c2

/-- The selected scalar reading is not faithful to support and repair data. -/
theorem scalarReading_not_faithful_to_supportRepair :
    ¬ ScalarReadingFaithfulToSupportRepair scalarReading := by
  intro hfaithful
  have hsame :=
    hfaithful singleSupport splitSupport same_scalarReading same_verdict
  exact supportFamily_ne hsame.1

end ScalarCollapse
end QualitySurface
end ResearchLean.AG
