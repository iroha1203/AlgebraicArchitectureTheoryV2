import ResearchLean.AG.RepairObservationDuality.W1GeneratedNumericalPlan
import ResearchLean.AG.RelativeRepairComposition.W1SymbolicPublicMatrices

/-!
# G-131 E: receiving the generated full local relations discloses both values

## Implementation notes

The public indices are the complete original named coordinates, independent
of x and y. The relations are G-130's generated actual relations. Each is
nonempty, and its original face expression is constant on the entire relation.
Hence the received sets themselves determine the corresponding input value;
no successful global repair or alleged disclosure certificate is supplied.
-/
namespace AAT.AG.RepairObservationDuality.W1ReceivedRelations
open RelativeRepairComposition W1AffineInput W1Regions W1IndexedCover
open W1LocalPublicValues W1GeneratedRelations W1SymbolicPublicMatrices W1PhysicalInputs
set_option autoImplicit false
attribute [local instance] Classical.propDecidable

/-- The received relation is the entire original generated local relation on common named public coordinates. -/
noncomputable def received (v : Values) (j : Bool) : Set (publicIndex j → ZMod 3) :=
  W1LocalInterfaces.relation (v false) (v true) j

/-- The received U relation reads its original full e,b values and is constant at x. -/
theorem left_iff (v : Values) (z : publicIndex false → ZMod 3) :
    z ∈ received v false ↔ z (structuralE false) + z (structuralB false) = v false := by
  change z ∈ W1LocalInterfaces.relation (v false) (v true) false ↔ _
  rw [left_relation]
  have he := public_value (v false) (v true) false z ⟨name edgeE,Or.inl rfl⟩
    (by simp [fixedRegion,geometry,name,edgeE,edgeRx,edgeRy]) (shared_e_public false)
  have hb := public_value (v false) (v true) false z ⟨name edgeB,Or.inr (Or.inl rfl)⟩
    (by simp [fixedRegion,geometry,name,edgeB,edgeRx,edgeRy])
    (candidates_public false ⟨name edgeB,Or.inl rfl⟩)
  change W1LocalDifferentials.value (v false) (v true) leftRegion
    (publicCochain (v false) (v true) false z) ⟨name edgeE,Or.inl rfl⟩ = z (structuralE false) at he
  change W1LocalDifferentials.value (v false) (v true) leftRegion
    (publicCochain (v false) (v true) false z) ⟨name edgeB,Or.inr (Or.inl rfl)⟩ = z (structuralB false) at hb
  rw [he,hb]

/-- The received V relation reads its original full e,b,c values and is constant at y. -/
theorem right_iff (v : Values) (z : publicIndex true → ZMod 3) :
    z ∈ received v true ↔ z (structuralE true) - z (structuralB true) + z structuralC = v true := by
  change z ∈ W1LocalInterfaces.relation (v false) (v true) true ↔ _
  rw [right_relation]
  have he := public_value (v false) (v true) true z ⟨name edgeE,Or.inl rfl⟩
    (by simp [fixedRegion,geometry,name,edgeE,edgeRx,edgeRy]) (shared_e_public true)
  have hb := public_value (v false) (v true) true z ⟨name edgeB,Or.inr (Or.inr (Or.inl rfl))⟩
    (by simp [fixedRegion,geometry,name,edgeB,edgeRx,edgeRy])
    (candidates_public true ⟨name edgeB,Or.inl rfl⟩)
  have hc := public_value (v false) (v true) true z ⟨name edgeC,Or.inr (Or.inr (Or.inr (Or.inl rfl)))⟩
    (by simp [fixedRegion,geometry,name,edgeC,edgeRx,edgeRy])
    (candidates_public true ⟨name edgeC,Or.inr rfl⟩)
  change W1LocalDifferentials.value (v false) (v true) rightRegion
    (publicCochain (v false) (v true) true z) ⟨name edgeE,Or.inl rfl⟩ = z (structuralE true) at he
  change W1LocalDifferentials.value (v false) (v true) rightRegion
    (publicCochain (v false) (v true) true z) ⟨name edgeB,Or.inr (Or.inr (Or.inl rfl))⟩ = z (structuralB true) at hb
  change W1LocalDifferentials.value (v false) (v true) rightRegion
    (publicCochain (v false) (v true) true z) ⟨name edgeC,Or.inr (Or.inr (Or.inr (Or.inl rfl)))⟩ = z structuralC at hc
  rw [he,hb,hc]

/-- Distinct original e,b names remain distinct full public coordinates. -/
theorem e_ne_b (j : Bool) : structuralE j ≠ structuralB j := by
  intro h
  have he := congrArg (fun e : publicIndex j => e.1.1.1.2.2) h
  exact (by decide : (0 : Fin 6) ≠ 2) he

/-- Original e,c names remain distinct in the full V public coordinates. -/
theorem e_ne_c : structuralE true ≠ structuralC := by
  intro h
  have he := congrArg (fun e : publicIndex true => e.1.1.1.2.2) h
  exact (by decide : (0 : Fin 6) ≠ 3) he

/-- Every actual generated U/V relation has a point on its full public coordinate space. -/
theorem nonempty (v : Values) (j : Bool) : (received v j).Nonempty := by
  cases j
  · refine ⟨Pi.single (structuralE false) (v false),(left_iff v _).mpr ?_⟩
    simp [Ne.symm (e_ne_b false)]
  · refine ⟨Pi.single (structuralE true) (v true),(right_iff v _).mpr ?_⟩
    simp [Ne.symm (e_ne_b true),Ne.symm e_ne_c]

/-- Equality of an actually received local relation forces equality of its unique original input value. -/
theorem value_eq_of_received_eq (v w : Values) (j : Bool) (h : received v j = received w j) :
    v j = w j := by
  obtain ⟨z,hz⟩ := nonempty v j
  have hw : z ∈ received w j := h ▸ hz
  cases j
  · exact ((left_iff v z).mp hz).symm.trans ((left_iff w z).mp hw)
  · exact ((right_iff v z).mp hz).symm.trans ((right_iff w z).mp hw)

/-- Receiving both complete generated relations has precisely the both-values-known information fiber. -/
theorem both_fiber_iff (v w : Values) :
    (received v false = received w false ∧ received v true = received w true) ↔ v = w := by
  constructor
  · rintro ⟨hl,hr⟩
    funext j
    cases j
    · exact value_eq_of_received_eq v w false hl
    · exact value_eq_of_received_eq v w true hr
  · rintro rfl
    exact ⟨rfl,rfl⟩

/-- The actual both-relations information fiber is exactly the both-values known fiber used by the finite optimal controller. -/
theorem physical_fiber (w : Values) :
    {X : Inputs | received (values X) false = received w false ∧ received (values X) true = received w true} =
      values ⁻¹' informationFiber (W1ObservationCosts.known 2) (W1ObservationCosts.known 2 w) := by
  ext X
  rw [Set.mem_setOf_eq,both_fiber_iff]
  change values X = w ↔ W1ObservationCosts.known 2 (values X) = W1ObservationCosts.known 2 w
  simp [W1ObservationCosts.known_apply]

/-- The full generated numerical controller, after receipt of both original local relations, is correct and has exactly zero additional primitive cost. -/
theorem received_numerical (p : W1NumericalEquation.Permissions) (w : Values) :
    PrimitiveQueries.Correct evaluate
      {X : Inputs | received (values X) false = received w false ∧ received (values X) true = received w true}
      (fun X out => ValidOutput (W1NumericalEquation.differential p)
        (affineRhs W1NumericalEquation.rhsLinear 0) (values X) out)
      (W1GeneratedNumericalPlan.procedure p 2 (W1ObservationCosts.known 2 w)) ∧
    PrimitiveQueries.worst evaluate
      {X : Inputs | received (values X) false = received w false ∧ received (values X) true = received w true}
      (W1GeneratedNumericalPlan.procedure p 2 (W1ObservationCosts.known 2 w)) = 0 := by
  rw [physical_fiber]
  exact ⟨W1GeneratedNumericalPlan.correct p 2 w,(W1GeneratedNumericalPlan.optimal p 2 w).2⟩

end AAT.AG.RepairObservationDuality.W1ReceivedRelations
#assert_standard_axioms_only AAT.AG.RepairObservationDuality.W1ReceivedRelations
