import ResearchLean.AG.OperationRepair.LawBridge
import ResearchLean.AG.OperationRepair.InputMaps
import ResearchLean.AG.OperationRepair.FiniteConstruction

/-!
# Finite path-pair requests

A finite list of pairs of operation words generates requests at every source
state. Identifying those requests is equivalent, for every repair quotient, to
the corresponding equations of operations on its entire target.
-/

namespace AAT.AG.OperationRepair

universe u u' v w

variable {S : Type u} {S' : Type u'} {E : Type v} {O : Type w}

/-- The relation generated directly by the given finite list of path pairs. -/
def pathRequest (T : OperationSystem S E)
    (paths : List (List E × List E)) (x y : S) : Prop :=
  ∃ pair ∈ paths, ∃ source : S,
    x = T.eval source pair.1 ∧ y = T.eval source pair.2

/-- The descended operations of a repair quotient form an operation system. -/
def RepairQuotient.targetSystem {T : OperationSystem S E}
    {observe : S → O} {R : S → S → Prop}
    (q : RepairQuotient T observe R) : OperationSystem q.Target E where
  step := q.step

/-- Reading a source after a word equals executing its descended word. -/
theorem RepairQuotient.eval_comm {T : OperationSystem S E}
    {observe : S → O} {R : S → S → Prop}
    (q : RepairQuotient T observe R) (x : S) (word : List E) :
    q.read (T.eval x word) = q.targetSystem.eval (q.read x) word := by
  induction word generalizing x with
  | nil => rfl
  | cons e rest ih =>
      rw [OperationSystem.eval_cons, OperationSystem.eval_cons,
        ih, q.step_comm]
      rfl

/-- A finite set of path equations on every target state. -/
def RepairQuotient.PathEquations {T : OperationSystem S E}
    {observe : S → O} {R : S → S → Prop}
    (q : RepairQuotient T observe R)
    (paths : List (List E × List E)) : Prop :=
  ∀ pair ∈ paths, ∀ z : q.Target,
    q.targetSystem.eval z pair.1 = q.targetSystem.eval z pair.2

/-- For any surjective operation-preserving map, identification of the
generated source requests is equivalent to all target path equations. -/
theorem RepairQuotient.pathRequest_identified_iff
    {T : OperationSystem S E} {observe : S → O}
    {R : S → S → Prop} (q : RepairQuotient T observe R)
    (paths : List (List E × List E)) :
    (∀ x y, pathRequest T paths x y → q.read x = q.read y) ↔
      q.PathEquations paths := by
  constructor
  · intro h pair hp z
    obtain ⟨source, rfl⟩ := q.surjective z
    rw [← q.eval_comm source pair.1, ← q.eval_comm source pair.2]
    exact h _ _ ⟨pair, hp, source, rfl, rfl⟩
  · intro h x y hxy
    obtain ⟨pair, hp, source, rfl, rfl⟩ := hxy
    rw [q.eval_comm source pair.1, q.eval_comm source pair.2]
    exact h pair hp (q.read source)

/-- Every repair quotient for the path-generated relation satisfies all
specified equations, including at target points outside a chosen source list. -/
theorem RepairQuotient.path_equations
    {T : OperationSystem S E} {observe : S → O}
    {paths : List (List E × List E)}
    (q : RepairQuotient T observe (pathRequest T paths)) :
    q.PathEquations paths :=
  (q.pathRequest_identified_iff paths).mp q.identifies

/-- Conversely, a surjective operation/observation preserving quotient with
the target path equations is a repair for exactly the generated requests. -/
def RepairQuotient.withPathEquations
    {T : OperationSystem S E} {observe : S → O}
    (q : RepairQuotient T observe (fun _ _ => False))
    (paths : List (List E × List E)) (h : q.PathEquations paths) :
    RepairQuotient T observe (pathRequest T paths) where
  Target := q.Target
  read := q.read
  surjective := q.surjective
  step := q.step
  observation := q.observation
  step_comm := q.step_comm
  observation_comm := q.observation_comm
  identifies := (q.pathRequest_identified_iff paths).mpr h

/-- Forgetting the path requests retains the same quotient data. -/
def RepairQuotient.forgetPathRequests
    {T : OperationSystem S E} {observe : S → O}
    {paths : List (List E × List E)}
    (q : RepairQuotient T observe (pathRequest T paths)) :
    RepairQuotient T observe (fun _ _ => False) where
  Target := q.Target
  read := q.read
  surjective := q.surjective
  step := q.step
  observation := q.observation
  step_comm := q.step_comm
  observation_comm := q.observation_comm
  identifies := by intro x y h; exact False.elim h

theorem RepairQuotient.path_roundtrip_read
    {T : OperationSystem S E} {observe : S → O}
    {paths : List (List E × List E)}
    (q : RepairQuotient T observe (pathRequest T paths)) (x : S) :
    (q.forgetPathRequests.withPathEquations paths
      q.path_equations).read x = q.read x := rfl

/-- Feasibility of the finite path request is precisely behavioral agreement
of each listed pair of words at every source state. -/
theorem pathRepair_exists_iff (T : OperationSystem S E)
    (observe : S → O) (paths : List (List E × List E)) :
    Nonempty (RepairQuotient.{u, v, w, u} T observe (pathRequest T paths)) ↔
      ∀ pair ∈ paths, ∀ source : S,
        (behavior T observe).setoid.r
          (T.eval source pair.1) (T.eval source pair.2) := by
  rw [repair_exists_iff_request_behavior]
  constructor
  · intro h pair hp source
    exact h _ _ ⟨pair, hp, source, rfl, rfl⟩
  · intro h x y hxy
    obtain ⟨pair, hp, source, rfl, rfl⟩ := hxy
    exact h pair hp source

/-- For Law observation, every path repair descends all original Law values
through its existing Reading. -/
theorem pathLawRepair_adequate
    (laws : CanonicalResolution.FiniteLawFamily S)
    (T : OperationSystem S E) (paths : List (List E × List E))
    (q : RepairQuotient.{u, v, u, u} T (lawObserve laws)
      (pathRequest T paths)) :
    laws.Adequate q.toReading :=
  (repair_to_lawReadingConditions laws T (pathRequest T paths) q).2.1

/-- A map commuting with operations transports the generated path relation
without assuming that the map is injective or surjective. -/
theorem pathRequest_map (T : OperationSystem S E)
    (T' : OperationSystem S' E) (paths : List (List E × List E))
    (map : S → S')
    (hstep : ∀ e x, map (T.step e x) = T'.step e (map x))
    {x y : S} (hxy : pathRequest T paths x y) :
    pathRequest T' paths (map x) (map y) := by
  have heval (source : S) (word : List E) :
      map (T.eval source word) = T'.eval (map source) word := by
    induction word generalizing source with
    | nil => rfl
    | cons e rest ih =>
        rw [OperationSystem.eval_cons, OperationSystem.eval_cons,
          ih, hstep]
  obtain ⟨pair, hp, source, rfl, rfl⟩ := hxy
  exact ⟨pair, hp, map source,
    heval source pair.1, heval source pair.2⟩

/-- Operation, observation and path data supply an ordinary C input map. -/
def pathInputHom
    (T : OperationSystem S E) (T' : OperationSystem S' E)
    (observe : S → O) (observe' : S' → O)
    (paths : List (List E × List E))
    (map : S → S')
    (hstep : ∀ e x, map (T.step e x) = T'.step e (map x))
    (hobserve : ∀ x, observe' (map x) = observe x)
    : InputHom T observe (pathRequest T paths)
        T' observe' (pathRequest T' paths) where
  map := map
  step_comm := hstep
  observe_comm := hobserve
  request_preserve := by
    intro x y hxy
    exact pathRequest_map T T' paths map hstep hxy

/-- Pull back the same Law indices, values, and evaluations along a source map. -/
def pullbackLaws {S₂ : Type u}
    (laws₂ : CanonicalResolution.FiniteLawFamily S₂) (map : S → S₂) :
    CanonicalResolution.FiniteLawFamily S where
  Law := laws₂.Law
  lawFintype := laws₂.lawFintype
  Value := laws₂.Value
  valueDecidableEq := laws₂.valueDecidableEq
  eval := fun law x => laws₂.eval law (map x)

/-- A path input map with pulled-back Laws preserves each Law evaluation,
so C's endpoint maps and commuting square apply to the Law/path inputs. -/
def pathLawInputHom {S₂ : Type u}
    (laws₂ : CanonicalResolution.FiniteLawFamily S₂)
    (T : OperationSystem S E) (T₂ : OperationSystem S₂ E)
    (paths : List (List E × List E)) (map : S → S₂)
    (hstep : ∀ e x, map (T.step e x) = T₂.step e (map x)) :
    InputHom T (lawObserve (pullbackLaws laws₂ map)) (pathRequest T paths)
      T₂ (lawObserve laws₂) (pathRequest T₂ paths) :=
  pathInputHom T T₂ (lawObserve (pullbackLaws laws₂ map))
    (lawObserve laws₂) paths map hstep (by intro x; rfl)

namespace FiniteRepairInput

variable {n m : Nat} {O : Type w}

def pathRequestBool (input : FiniteRepairInput n m O)
    (paths : List (List (Fin m) × List (Fin m))) (x y : Fin n) : Bool :=
  paths.any fun pair =>
    (List.finRange n).any fun source =>
      decide (x = input.system.eval source pair.1) &&
        decide (y = input.system.eval source pair.2)

theorem pathRequestBool_eq_true_iff (input : FiniteRepairInput n m O)
    (paths : List (List (Fin m) × List (Fin m))) (x y : Fin n) :
    input.pathRequestBool paths x y = true ↔
      pathRequest input.system paths x y := by
  simp [pathRequestBool, pathRequest, List.any_eq_true,
    Bool.and_eq_true, List.mem_finRange]

/-- Enumerate the path relation on the numbered source, using the original
transition table and the finite list of path pairs. -/
def withPathRequest (input : FiniteRepairInput n m O)
    (paths : List (List (Fin m) × List (Fin m))) :
    FiniteRepairInput n m O where
  transition := input.transition
  observation := input.observation
  request := FiniteTable.ofFn fun x =>
    FiniteTable.ofFn fun y => input.pathRequestBool paths x y

@[simp] theorem withPathRequest_system (input : FiniteRepairInput n m O)
    (paths : List (List (Fin m) × List (Fin m))) :
    (input.withPathRequest paths).system = input.system := rfl

@[simp] theorem withPathRequest_observe (input : FiniteRepairInput n m O)
    (paths : List (List (Fin m) × List (Fin m))) :
    (input.withPathRequest paths).observe = input.observe := rfl

theorem withPathRequest_requestRel (input : FiniteRepairInput n m O)
    (paths : List (List (Fin m) × List (Fin m))) (x y : Fin n) :
    (input.withPathRequest paths).requestRel x y ↔
      pathRequest input.system paths x y := by
  simpa [requestRel, wants, withPathRequest, RelationTable.get] using
    input.pathRequestBool_eq_true_iff paths x y

/-- Run the same D procedure on the table generated from path pairs. -/
def runPathRepair [DecidableEq O] (input : FiniteRepairInput n m O)
    (paths : List (List (Fin m) × List (Fin m))) :
    FiniteConstruction.RunOutput n m O :=
  FiniteConstruction.runRepair (input.withPathRequest paths)

/-- D's success branch decides precisely whether every requested path pair
remains behaviorally equivalent at every source state. -/
theorem runPathRepair_success_iff [DecidableEq O]
    (input : FiniteRepairInput n m O)
    (paths : List (List (Fin m) × List (Fin m))) :
    (∃ tables : FiniteConstruction.SuccessTables n m O,
      (input.runPathRepair paths).outcome = Sum.inr tables) ↔
      ∀ pair ∈ paths, ∀ source : Fin n,
        (behavior input.system input.observe).setoid.r
          (input.system.eval source pair.1)
          (input.system.eval source pair.2) := by
  rw [runPathRepair, FiniteConstruction.runRepair_success_iff]
  simp only [withPathRequest_system, withPathRequest_observe,
    withPathRequest_requestRel]
  constructor
  · intro h pair hp source
    exact h _ _ ⟨pair, hp, source, rfl, rfl⟩
  · intro h x y hxy
    obtain ⟨pair, hp, source, rfl, rfl⟩ := hxy
    exact h pair hp source

/-- A successful table run returns an upper repair satisfying every listed
path equation on all quotient states. -/
theorem runPathRepair_upper_equations [DecidableEq O]
    (input : FiniteRepairInput n m O)
    (paths : List (List (Fin m) × List (Fin m)))
    (tables : FiniteConstruction.SuccessTables n m O)
    (h : (input.runPathRepair paths).outcome = Sum.inr tables) :
    (FiniteConstruction.successUpperRepair
      (input.withPathRequest paths) tables h).PathEquations paths := by
  let q := FiniteConstruction.successUpperRepair
    (input.withPathRequest paths) tables h
  apply (q.pathRequest_identified_iff paths).mp
  intro x y hxy
  exact q.identifies x y
    ((input.withPathRequest_requestRel paths x y).mpr hxy)

/-- A failure from the same D run contains a pair generated by one listed
path pair and a short separating operation word. -/
theorem runPathRepair_failure [DecidableEq O]
    (input : FiniteRepairInput n m O)
    (paths : List (List (Fin m) × List (Fin m)))
    (x y : Fin n) (word : List (Fin m))
    (h : (input.runPathRepair paths).outcome = Sum.inl (x, y, word)) :
    pathRequest input.system paths x y ∧ word.length < n * n ∧
      FiniteBehavior.separates (input.withPathRequest paths) x y word := by
  obtain ⟨hr, hlen, hsep⟩ :=
    FiniteConstruction.runRepair_failure (input.withPathRequest paths) x y word h
  exact ⟨(input.withPathRequest_requestRel paths x y).mp hr, hlen, hsep⟩

end FiniteRepairInput

end AAT.AG.OperationRepair

#assert_standard_axioms_only AAT.AG.OperationRepair
