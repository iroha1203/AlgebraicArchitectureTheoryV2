import Formal.AG.Atom.Obstruction

namespace AAT.AG

universe u

/-- I.命題9.1: obstruction soundness for a selected law valuation. -/
def ObstructionSound {U : AtomCarrier.{u}} {Value : Type u}
    (valuation : ObstructionValuation U Value) (L : Law U) : Prop :=
  ∀ A : ArchitectureObject U, L.holds A ->
    valuation.omega L A = valuation.domain.zero

/-- I.命題9.2: obstruction completeness for a selected law valuation. -/
def ObstructionComplete {U : AtomCarrier.{u}} {Value : Type u}
    (valuation : ObstructionValuation U Value) (L : Law U) : Prop :=
  ∀ A : ArchitectureObject U, ¬ L.holds A ->
    valuation.domain.positive (valuation.omega L A)

/--
I.命題9.1 / 9.2: soundness and completeness make a selected law equivalent to
zero obstruction valuation.
-/
theorem law_holds_iff_omega_zero {U : AtomCarrier.{u}} {Value : Type u}
    (valuation : ObstructionValuation U Value) (L : Law U)
    (hsound : ObstructionSound valuation L)
    (hcomplete : ObstructionComplete valuation L)
    (A : ArchitectureObject U) :
    L.holds A ↔ valuation.omega L A = valuation.domain.zero := by
  constructor
  · intro hlaw
    exact hsound A hlaw
  · intro hzero
    by_cases hlaw : L.holds A
    · exact hlaw
    · exact False.elim
        ((valuation.domain.noCancellationAtZero (hcomplete A hlaw)) hzero)

/--
I.定理9.3: Lawfulness-Zero Obstruction for a selected law universe, required
laws, and zero-reflecting aggregate valuation.
-/
theorem lawfulness_iff_omegaU_zero {U : AtomCarrier.{u}} {Value : Type u}
    (valuation : ObstructionValuation U Value) (LU : LawUniverse U)
    (aggregation :
      ZeroReflectingAggregation Value valuation.domain LU.RequiredIndex)
    (hsound :
      ∀ index : LU.RequiredIndex, ObstructionSound valuation (LU.law index.1))
    (hcomplete :
      ∀ index : LU.RequiredIndex, ObstructionComplete valuation (LU.law index.1))
    (A : ArchitectureObject U) :
    Lawfulness A LU ↔ omegaU valuation LU aggregation A = valuation.domain.zero := by
  constructor
  · intro hlawful
    apply (omegaU_zero_iff_required valuation LU aggregation A).mpr
    intro index
    exact hsound index A (hlawful index.1 index.2)
  · intro hzero index hrequired
    let requiredIndex : LU.RequiredIndex := ⟨index, hrequired⟩
    have hvalue :
        valuation.omega (LU.law index) A = valuation.domain.zero :=
      (omegaU_zero_iff_required valuation LU aggregation A).mp hzero requiredIndex
    exact (law_holds_iff_omega_zero valuation (LU.law index)
      (hsound requiredIndex) (hcomplete requiredIndex) A).mpr hvalue

end AAT.AG
