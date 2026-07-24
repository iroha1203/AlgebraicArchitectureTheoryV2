import Formal.AG.Examples.FiniteModel
import Formal.AG.Atom.LawfulnessZeroLegacy
import Formal.Util.AssertStandardAxioms

namespace AAT.AG

namespace FiniteModel

/-- Compatibility universe obtained from the generated finite equation system. -/
noncomputable def lawUniverse : LawUniverse carrier :=
  site.equationSystem.toLegacyLawUniverse

/--
Compatibility display name for the generated finite NoCycle equation.
Standard finite consumers use `equationSystem`.
-/
noncomputable def noCycleLaw : Law carrier :=
  lawUniverse.law PUnit.unit

/-- Every compatibility law in the singleton universe is required. -/
theorem lawUniverse_required (index : lawUniverse.Index) :
    lawUniverse.Required index := by
  cases index
  rfl

/-- The one-way legacy law generated from the finite equation is the NoCycle predicate. -/
theorem equationSystem_legacy_law_eq_noCycleLaw
    (C : Site.ContextPreorderCategory object) :
    (equationSystem C).toLegacyLawUniverse.law PUnit.unit = noCycleLaw := by
  apply Law.ext
  funext A
  apply propext
  change
    (equationSystem C).EquationHolds PUnit.unit A ↔
      site.equationSystem.EquationHolds PUnit.unit A
  exact (equationHolds_iff_noCycle C A).trans
    (site_equationHolds_iff_noCycle A).symm

/-- The generated compatibility display holds exactly on NoCycle objects. -/
@[simp] theorem noCycleLaw_holds_iff
    (A : ArchitectureObject carrier) :
    noCycleLaw.holds A ↔ ¬ hasDependencyCycle A := by
  change site.equationSystem.EquationHolds PUnit.unit A ↔
    ¬ hasDependencyCycle A
  exact site_equationHolds_iff_noCycle A

/-- The generated site legacy display is exactly the finite NoCycle equation. -/
@[simp] theorem site_law_holds_iff_noCycleLaw
    (A : ArchitectureObject carrier) :
    (site.equationSystem.toLegacyLawUniverse.law PUnit.unit).holds A ↔
      noCycleLaw.holds A := by
  rfl

/-- SD2: the finite site retains the generated core law universe. -/
theorem site_lawUniverse_eq_core :
    site.equationSystem.toLegacyLawUniverse =
      siteCorePackage.equationSystem.toLegacyLawUniverse :=
  rfl

/-- Compatibility count-valued obstruction reading for the NoCycle display. -/
noncomputable def noCycleOmega (_law : Law carrier)
    (A : ArchitectureObject carrier) : Nat := by
  classical
  exact if hasCycleWitness A then 1 else 0

/-- Compatibility obstruction valuation for the NoCycle display. -/
noncomputable def noCycleValuation : ObstructionValuation carrier Nat where
  domain := ObstructionValueDomain.nat
  omega := noCycleOmega

/-- Compatibility zero-reflecting aggregation for the singleton universe. -/
def singletonRequiredAggregation :
    ZeroReflectingAggregation Nat noCycleValuation.domain
      lawUniverse.RequiredIndex where
  aggregate values := values ⟨PUnit.unit, rfl⟩
  zero_reflecting values := by
    constructor
    · intro h index
      cases index with
      | mk index hrequired =>
          cases index
          exact h
    · intro h
      exact h ⟨PUnit.unit, rfl⟩

/-- Compatibility soundness theorem for the NoCycle display. -/
theorem noCycleSound :
    ObstructionSound noCycleValuation noCycleLaw := by
  intro A h
  classical
  have hnot : ¬ hasCycleWitness A := by
    simpa [hasCycleWitness, hasDependencyCycle] using
      (noCycleLaw_holds_iff A).mp h
  simp [noCycleValuation, noCycleOmega, ObstructionValueDomain.nat, hnot]

/-- Compatibility completeness theorem for the NoCycle display. -/
theorem noCycleComplete :
    ObstructionComplete noCycleValuation noCycleLaw := by
  intro A hfailure
  classical
  have hcycle : hasCycleWitness A := by
    exact Classical.byContradiction (fun hnot =>
      hfailure (by
        apply (noCycleLaw_holds_iff A).mpr
        simpa [hasCycleWitness, hasDependencyCycle] using hnot))
  simp [noCycleValuation, noCycleOmega, ObstructionValueDomain.nat, hcycle]

end FiniteModel

end AAT.AG

#assert_standard_axioms_only AAT.AG.FiniteModel
