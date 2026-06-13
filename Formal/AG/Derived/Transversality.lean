import Formal.AG.Derived.TaylorResolution

noncomputable section

namespace AAT.AG
namespace Derived

universe u v

namespace Transversality

variable (A : Type v) [CommRing A]
variable {I_U I_V : Ideal A}

/-- V.定義7.1: selected vanishing of a law-conflict object in one degree. -/
def LawConflictVanishes (P : Intersection.LawConflictPackage.{u, v} A I_U I_V)
    (i : Nat) : Prop :=
  ∀ x : P.LawConflict i, x = 0

/-- V.定義7.2: selected positive-degree derived transversality. -/
def PositiveLawConflictVanishing
    (P : Intersection.LawConflictPackage.{u, v} A I_U I_V) : Prop :=
  ∀ i, 0 < i -> LawConflictVanishes A P i

/-- V.定義7.4: selected nonzero law-conflict object in one degree. -/
def LawConflictNonzero (P : Intersection.LawConflictPackage.{u, v} A I_U I_V)
    (i : Nat) : Prop :=
  ∃ x : P.LawConflict i, x ≠ 0

/-- V.定理6.1: first law conflict nonvanishing. -/
abbrev FirstLawConflictNonzero
    (P : Intersection.LawConflictPackage.{u, v} A I_U I_V) : Prop :=
  LawConflictNonzero A P 1

/-- V.定義7.4: selected derived non-transversality. -/
def DerivedNonTransverse
    (P : Intersection.LawConflictPackage.{u, v} A I_U I_V) : Prop :=
  ∃ i, 0 < i ∧ LawConflictNonzero A P i

/-- V.R5: Mathlib Tor vanishing in one degree. -/
def MathlibTorVanishes (i : Nat) : Prop :=
  ∀ x : Intersection.mathlibTor A I_U I_V i, x = 0

/-- V.R5: positive-degree Mathlib Tor vanishing. -/
def PositiveMathlibTorVanishing : Prop :=
  ∀ i, 0 < i -> MathlibTorVanishes A (I_U := I_U) (I_V := I_V) i

namespace LawConflictPackage

variable {A}
variable (P : Intersection.LawConflictPackage.{u, v} A I_U I_V)

/-- V.定理6.1: nonzero `LawConflict_1` gives selected derived non-transversality. -/
theorem derivedNonTransverse_of_firstLawConflictNonzero
    (h : FirstLawConflictNonzero A P) :
    DerivedNonTransverse A P :=
  ⟨1, Nat.zero_lt_one, h⟩

/--
V.定理6.1: a first nonzero law conflict rules out positive-degree
law-conflict vanishing.
-/
theorem not_positiveLawConflictVanishing_of_firstLawConflictNonzero
    (h : FirstLawConflictNonzero A P) :
    ¬ PositiveLawConflictVanishing A P := by
  intro hvanish
  rcases h with ⟨x, hx⟩
  exact hx (hvanish 1 Nat.zero_lt_one x)

/-- V.R5: selected `LawConflict_i` vanishes iff the bridged Mathlib `Tor_i` vanishes. -/
theorem lawConflictVanishes_iff_mathlibTorVanishes (i : Nat) :
    LawConflictVanishes A P i ↔
      MathlibTorVanishes A (I_U := I_U) (I_V := I_V) i := by
  constructor
  · intro h y
    let e := P.lawConflictLinearEquivMathlibTor i
    have hy : e.symm y = 0 := h (e.symm y)
    have hmap := congrArg e hy
    simpa using hmap
  · intro h x
    let e := P.lawConflictLinearEquivMathlibTor i
    have hx : e x = 0 := h (e x)
    have hmap := congrArg e.symm hx
    simpa using hmap

/--
V.R5: positive-degree selected law-conflict vanishing is equivalent to
positive-degree Mathlib Tor vanishing.
-/
theorem positiveLawConflictVanishing_iff_mathlibTorVanishing :
    PositiveLawConflictVanishing A P ↔
      PositiveMathlibTorVanishing A (I_U := I_U) (I_V := I_V) := by
  constructor
  · intro h i hi
    exact (lawConflictVanishes_iff_mathlibTorVanishes P i).1 (h i hi)
  · intro h i hi
    exact (lawConflictVanishes_iff_mathlibTorVanishes P i).2 (h i hi)

/--
V.定理6.1: a first nonzero law conflict also rules out positive Mathlib Tor
vanishing through the selected bridge.
-/
theorem not_positiveMathlibTorVanishing_of_firstLawConflictNonzero
    (h : FirstLawConflictNonzero A P) :
    ¬ PositiveMathlibTorVanishing A (I_U := I_U) (I_V := I_V) := by
  intro htor
  exact not_positiveLawConflictVanishing_of_firstLawConflictNonzero P h
    ((positiveLawConflictVanishing_iff_mathlibTorVanishing P).2 htor)

end LawConflictPackage

/--
V.定理7.3: selected derived transversality criterion.

`classicalAgreement` is the chosen statement that the selected derived tensor
surface has no higher residue and agrees with the classical degree-zero reading.
The equivalence is explicit data, avoiding a global derived-category claim.
-/
structure DerivedTransversalityCriterion
    (P : Intersection.LawConflictPackage.{u, v} A I_U I_V) where
  classicalAgreement : Prop
  positiveTorVanishing_iff_classicalAgreement :
    PositiveMathlibTorVanishing A (I_U := I_U) (I_V := I_V) ↔ classicalAgreement

/--
V.定理7.3: selected classical-agreement data stated directly in terms of
LawConflict vanishing.

The derived transversality criterion below reconstructs the Mathlib Tor
criterion from this data using the selected `LawConflict_i = Tor_i` bridge.
-/
structure SelectedClassicalAgreementData
    (P : Intersection.LawConflictPackage.{u, v} A I_U I_V) where
  classicalAgreement : Prop
  positiveLawConflictVanishing_iff_classicalAgreement :
    PositiveLawConflictVanishing A P ↔ classicalAgreement

/--
V.定理7.3: concrete selected classical-agreement reading attached to the
chosen derived tensor surface.

The first component says all positive Mathlib Tor residues vanish.  The second
component records that the selected degree-zero homology of the chosen derived
tensor complex is the classical joint quotient.  This is still a selected
chart-level surface, not a global derived-category theorem.
-/
def SelectedDerivedTensorClassicalAgreement
    (P : Intersection.LawConflictPackage.{u, v} A I_U I_V) : Prop :=
  PositiveMathlibTorVanishing A (I_U := I_U) (I_V := I_V) ∧
    Nonempty
      (P.intersection.structureSheafComplex.homology0 ≃ₗ[A]
        Intersection.classicalJointQuotient A I_U I_V)

namespace SelectedDerivedTensorClassicalAgreement

variable {A}
variable {P : Intersection.LawConflictPackage.{u, v} A I_U I_V}

/--
V.定理7.3: Mathlib positive Tor vanishing is exactly the higher-residue part
of the concrete selected derived-tensor agreement reading.
-/
theorem iff_positiveMathlibTorVanishing :
    SelectedDerivedTensorClassicalAgreement A P ↔
      PositiveMathlibTorVanishing A (I_U := I_U) (I_V := I_V) := by
  constructor
  · intro h
    exact h.1
  · intro h
    exact
      ⟨h,
        ⟨P.intersection.homology0LinearEquivClassicalJoint⟩⟩

/--
V.定理7.3: selected LawConflict vanishing is equivalent to the concrete
selected derived-tensor classical-agreement reading.
-/
theorem iff_positiveLawConflictVanishing :
    SelectedDerivedTensorClassicalAgreement A P ↔
      PositiveLawConflictVanishing A P :=
  iff_positiveMathlibTorVanishing (A := A) (P := P) |>.trans
    (LawConflictPackage.positiveLawConflictVanishing_iff_mathlibTorVanishing P).symm

/--
V.定理7.3: selected LawConflict vanishing gives the concrete selected
derived-tensor classical-agreement reading.
-/
theorem of_positiveLawConflictVanishing
    (h : PositiveLawConflictVanishing A P) :
    SelectedDerivedTensorClassicalAgreement A P :=
  (iff_positiveLawConflictVanishing (A := A) (P := P)).2 h

/--
V.定理7.3: concrete selected derived-tensor agreement gives selected
LawConflict vanishing.
-/
theorem positiveLawConflictVanishing
    (h : SelectedDerivedTensorClassicalAgreement A P) :
    PositiveLawConflictVanishing A P :=
  (iff_positiveLawConflictVanishing (A := A) (P := P)).1 h

/--
V.定理7.3: Mathlib Tor vanishing gives the concrete selected derived-tensor
agreement reading without a separate selected equivalence field.
-/
theorem of_positiveMathlibTorVanishing
    (h : PositiveMathlibTorVanishing A (I_U := I_U) (I_V := I_V)) :
    SelectedDerivedTensorClassicalAgreement A P :=
  (iff_positiveMathlibTorVanishing (A := A) (P := P)).2 h

/--
V.定理7.3: build the usual criterion package from the concrete selected
derived-tensor agreement reading.
-/
def toDerivedTransversalityCriterion :
    DerivedTransversalityCriterion A P where
  classicalAgreement := SelectedDerivedTensorClassicalAgreement A P
  positiveTorVanishing_iff_classicalAgreement :=
    (iff_positiveMathlibTorVanishing (A := A) (P := P)).symm

/--
V.定理7.3: build the law-conflict agreement-data package from the concrete
selected derived-tensor agreement reading.
-/
def toSelectedClassicalAgreementData :
    SelectedClassicalAgreementData A P where
  classicalAgreement := SelectedDerivedTensorClassicalAgreement A P
  positiveLawConflictVanishing_iff_classicalAgreement :=
    (iff_positiveLawConflictVanishing (A := A) (P := P)).symm

end SelectedDerivedTensorClassicalAgreement

namespace SelectedClassicalAgreementData

variable {A}
variable {P : Intersection.LawConflictPackage.{u, v} A I_U I_V}

/--
V.定理7.3: build the Mathlib Tor criterion from selected law-conflict
vanishing data.
-/
def toDerivedTransversalityCriterion
    (D : SelectedClassicalAgreementData A P) :
    DerivedTransversalityCriterion A P where
  classicalAgreement := D.classicalAgreement
  positiveTorVanishing_iff_classicalAgreement :=
    (LawConflictPackage.positiveLawConflictVanishing_iff_mathlibTorVanishing P).symm.trans
      D.positiveLawConflictVanishing_iff_classicalAgreement

/-- V.定理7.3: selected law-conflict vanishing gives selected classical agreement. -/
theorem classicalAgreement_of_positiveLawConflictVanishing
    (D : SelectedClassicalAgreementData A P)
    (h : PositiveLawConflictVanishing A P) :
    D.classicalAgreement :=
  D.positiveLawConflictVanishing_iff_classicalAgreement.1 h

/-- V.定理7.3: selected classical agreement gives law-conflict vanishing. -/
theorem positiveLawConflictVanishing_of_classicalAgreement
    (D : SelectedClassicalAgreementData A P)
    (h : D.classicalAgreement) :
    PositiveLawConflictVanishing A P :=
  D.positiveLawConflictVanishing_iff_classicalAgreement.2 h

end SelectedClassicalAgreementData

namespace DerivedTransversalityCriterion

variable {A}
variable {P : Intersection.LawConflictPackage.{u, v} A I_U I_V}

/-- V.定理7.3: Mathlib positive Tor vanishing iff selected classical agreement. -/
theorem criterion_positiveTorVanishing_iff_classicalAgreement
    (C : DerivedTransversalityCriterion A P) :
    PositiveMathlibTorVanishing A (I_U := I_U) (I_V := I_V) ↔ C.classicalAgreement :=
  C.positiveTorVanishing_iff_classicalAgreement

/-- V.定理7.3: selected law-conflict vanishing iff selected classical agreement. -/
theorem positiveLawConflictVanishing_iff_classicalAgreement
    (C : DerivedTransversalityCriterion A P) :
    PositiveLawConflictVanishing A P ↔ C.classicalAgreement :=
  (LawConflictPackage.positiveLawConflictVanishing_iff_mathlibTorVanishing P).trans
    C.positiveTorVanishing_iff_classicalAgreement

end DerivedTransversalityCriterion

end Transversality

end Derived
end AAT.AG
