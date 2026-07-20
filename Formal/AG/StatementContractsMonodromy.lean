import Formal.AG.SingularityMonodromyStack.Monodromy

noncomputable section

/-!
Fixed statement contracts for the Part VI presented monodromy connection.
-/

namespace AAT.AG
namespace SingularityMonodromyStack

universe u v w x y z

variable {U : AtomCarrier.{u}} {A : ArchitectureObject U}
variable {S : Site.AATSite A} {P : StratumReadingParameter S}
variable {k : Type v} [CommRing k]
variable {X : ArchitectureStratum.{u, v, w, x, y} P k}
variable {G : OperationCategoryData.{u, v, w, x, y, z} X}
variable {R : RefactorEndpointReading.{u, v, w, x, y, z} G}
variable {H : HomotopyGeneratorFamily.{u, v, w, x, y, z} R}
variable {base : G.State}

/-- Fixed contract: free edge words are composable loops at the selected base. -/
example (word : FreeEdgeWord.{u, v, w, x, y, z} G base) :
    FormalEdgeStepsStartAt base word.steps ∧
      FormalEdgeStepsComposable word.steps ∧
      FormalEdgeStepsEndAt base word.steps :=
  ⟨word.startsAtBase, word.composable, word.endsAtBase⟩

/-- Fixed contract: every backward step is inverse to its matching forward step. -/
example
    (Pi : PresentedArchitectureFundamentalGroup.{u, v, w, x, y, z} H base)
    {a b : G.State} (op : SelectedOperation G a b) :
    FreeGroup.of (FormalEdgeStep.backward op) *
        FreeGroup.of (FormalEdgeStep.forward op) ∈ Pi.presentedRelators :=
  Or.inr ⟨a, b, op, rfl⟩

/-- Fixed contract: coefficient automorphisms form the target automorphism group. -/
example (C : MonodromyCoefficientObject.{z}) :
    Group (CoefficientAutomorphism C) :=
  inferInstance

/-- Fixed contract: multiplication follows the standard automorphism composition order. -/
example (C : MonodromyCoefficientObject.{z})
    (f g : CoefficientAutomorphism C)
    (xOb : C.Ob) (xSem : C.Sem) (xEff : C.Eff) :
    (f * g).obAut xOb = f.obAut (g.obAut xOb) ∧
      (f * g).semAut xSem = f.semAut (g.semAut xSem) ∧
      (f * g).effAut xEff = f.effAut (g.effAut xEff) :=
  ⟨rfl, rfl, rfl⟩

/-- Fixed contract: monodromy acts directly on the Mathlib presented group. -/
example
    (Pi : PresentedArchitectureFundamentalGroup.{u, v, w, x, y, z} H base)
    (M : MonodromyAction.{u, v, w, x, y, z} Pi) :
    Pi.pi1AAT →* CoefficientAutomorphism M.coefficient :=
  M.rho

/-- Fixed contract: generator actions killing all relators construct monodromy. -/
example
    (Pi : PresentedArchitectureFundamentalGroup.{u, v, w, x, y, z} H base)
    (coefficient : MonodromyCoefficientObject.{z})
    (generatorAction :
      FormalEdgeStep.{u, v, w, x, y, z} G -> CoefficientAutomorphism coefficient)
    (relators_map_to_one :
      ∀ r ∈ Pi.presentedRelators, FreeGroup.lift generatorAction r = 1) :
    MonodromyAction.{u, v, w, x, y, z} Pi :=
  MonodromyAction.ofPresentedGenerators
    Pi coefficient generatorAction relators_map_to_one

/-- Fixed contract: presented monodromy evaluates to the selected generator action. -/
example
    (Pi : PresentedArchitectureFundamentalGroup.{u, v, w, x, y, z} H base)
    (coefficient : MonodromyCoefficientObject.{z})
    (generatorAction :
      FormalEdgeStep.{u, v, w, x, y, z} G -> CoefficientAutomorphism coefficient)
    (relators_map_to_one :
      ∀ r ∈ Pi.presentedRelators, FreeGroup.lift generatorAction r = 1)
    (step : FormalEdgeStep.{u, v, w, x, y, z} G) :
    (MonodromyAction.ofPresentedGenerators
      Pi coefficient generatorAction relators_map_to_one).Mon_gamma
        (PresentedGroup.of step) = generatorAction step :=
  MonodromyAction.mon_gamma_presented_generator
    Pi coefficient generatorAction relators_map_to_one step

/-- Fixed contract: every selected relator has identity monodromy. -/
example
    {Pi : PresentedArchitectureFundamentalGroup.{u, v, w, x, y, z} H base}
    (M : MonodromyAction.{u, v, w, x, y, z} Pi)
    {word : Pi.FreeWord} (hword : Pi.Relator word) :
    M.Mon_gamma (Pi.presentedQuotientMap word) = 1 :=
  M.mon_gamma_presented_relator hword

end SingularityMonodromyStack
end AAT.AG
