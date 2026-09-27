import ResearchLean.AG.OperationRepair.FiniteConstruction

/-!
# Explicit enumeration of a finite operation system

The two supplied equivalences number states and operation names. The three
tables are constructed from the raw maps; their value equations are the
interface to the general operation system and request relation.
-/

namespace AAT.AG.OperationRepair

namespace FiniteEnumeration

universe u v w

/-- Explicit numberings are input data. Neither repairability nor a quotient
is part of this input. -/
structure Input (S : Type u) (E : Type v) (O : Type w) (n m : Nat) where
  states : S ≃ Fin n
  operations : E ≃ Fin m
  system : OperationSystem S E
  observe : S → O
  request : S → S → Bool

variable {S : Type u} {E : Type v} {O : Type w} {n m : Nat}

/-- Materialize precisely the table input used by the finite procedure. -/
def Input.toTables (a : Input S E O n m) : FiniteRepairInput n m O where
  transition := FiniteTable.ofFn fun e => FiniteTable.ofFn fun x =>
    a.states (a.system.step (a.operations.symm e) (a.states.symm x))
  observation := FiniteTable.ofFn fun x => a.observe (a.states.symm x)
  request := FiniteTable.ofFn fun x => FiniteTable.ofFn fun y =>
    a.request (a.states.symm x) (a.states.symm y)

@[simp] theorem Input.toTables_step (a : Input S E O n m) (e : E) (x : S) :
    (a.toTables.step (a.operations e)) (a.states x) =
      a.states (a.system.step e x) := by
  simp [Input.toTables, FiniteRepairInput.step]

@[simp] theorem Input.toTables_observe (a : Input S E O n m) (x : S) :
    a.toTables.observe (a.states x) = a.observe x := by
  simp [Input.toTables, FiniteRepairInput.observe]

@[simp] theorem Input.toTables_wants (a : Input S E O n m) (x y : S) :
    a.toTables.wants (a.states x) (a.states y) = a.request x y := by
  simp [Input.toTables, FiniteRepairInput.wants, RelationTable.get]

theorem Input.toTables_requestRel (a : Input S E O n m) (x y : S) :
    a.toTables.requestRel (a.states x) (a.states y) ↔
      a.request x y = true := by
  simp [FiniteRepairInput.requestRel]

/-- The finite decision is invoked on the tables built from the supplied
numberings. In particular, an empty source requires no default state. -/
def Input.run [DecidableEq O] (a : Input S E O n m) :
    FiniteConstruction.RunOutput n m O :=
  FiniteConstruction.runRepair a.toTables

end FiniteEnumeration

end AAT.AG.OperationRepair

#assert_standard_axioms_only AAT.AG.OperationRepair
