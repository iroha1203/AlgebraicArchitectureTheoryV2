import ResearchLean.AG.OperationRepair.LawBridge

/-!
# Existing Readings for repair targets in arbitrary universes

The existing `Reading S` has its target in the source universe. Every repair
quotient, including one with a target in another universe, has a canonical
Reading obtained from the standard quotient by its kernel. Its recovered
repair is uniquely isomorphic to the original repair as a quotient of `S`.
-/

namespace AAT.AG.OperationRepair

open AAT.AG.CanonicalResolution

universe u v z

variable {S : Type u} {E : Type v}
variable {T : OperationSystem S E}
variable {laws : FiniteLawFamily S} {R : S → S → Prop}

/-- Normalize a repair with any target universe into the existing Reading
universe by quotienting the original source by its actual kernel. -/
def RepairQuotient.standardReading
    (q : RepairQuotient.{u, v, u, z} T (lawObserve laws) R) : Reading S where
  Target := Quotient q.kernel.setoid
  read := Quotient.mk q.kernel.setoid
  surjective := Quotient.mk_surjective

theorem RepairQuotient.standardReading_kernel_iff
    (q : RepairQuotient.{u, v, u, z} T (lawObserve laws) R) (x y : S) :
    q.standardReading.Kernel x y ↔ q.kernel.setoid.r x y :=
  Quotient.eq

/-- The normalized Reading has precisely the three E conditions; no
operation or Law descent is assumed beyond the original repair equations. -/
theorem RepairQuotient.standardReading_conditions
    (q : RepairQuotient.{u, v, u, z} T (lawObserve laws) R) :
    LawReadingConditions laws T R q.standardReading := by
  refine ⟨?_, ?_, ?_⟩
  · intro e
    apply (q.standardReading.factors_iff_kernel
      (fun x => q.standardReading.read (T.step e x))).mpr
    intro x y hxy
    apply (q.standardReading_kernel_iff _ _).mpr
    exact q.kernel.stable e x y
      ((q.standardReading_kernel_iff _ _).mp hxy)
  · apply (laws.adequate_iff_kernel q.standardReading).mpr
    intro x y hxy
    apply (lawObserve_eq_iff laws x y).mp
    exact (behavior_le_kernel T (lawObserve laws))
      (q.kernel_le_behavior ((q.standardReading_kernel_iff _ _).mp hxy))
  · intro x y hxy
    exact (q.standardReading_kernel_iff _ _).mpr (q.identifies x y hxy)

/-- Recover a repair in the source universe from the normalized Reading. -/
noncomputable def RepairQuotient.standardReadingRepair
    (q : RepairQuotient.{u, v, u, z} T (lawObserve laws) R) :
    RepairQuotient.{u, v, u, u} T (lawObserve laws) R :=
  lawReadingToRepair laws T R q.standardReading q.standardReading_conditions

theorem RepairQuotient.standardReadingRepair_kernel
    (q : RepairQuotient.{u, v, u, z} T (lawObserve laws) R) :
    q.standardReadingRepair.kernel.setoid = q.kernel.setoid := by
  apply Setoid.ext
  intro x y
  change (Quotient.mk q.kernel.setoid x = Quotient.mk q.kernel.setoid y) ↔
    q.kernel.setoid.r x y
  exact Quotient.eq

/-- The canonical quotient maps to the original target by a morphism that
preserves all operations and the full Law observation. -/
noncomputable def RepairQuotient.standardReadingHomTo
    (q : RepairQuotient.{u, v, u, z} T (lawObserve laws) R) :
    RepairHom T (lawObserve laws) R q.standardReadingRepair q := by
  apply Classical.choice
  apply RepairHom.nonempty_iff_kernel_le.mpr
  change q.standardReadingRepair.kernel.setoid ≤ q.kernel.setoid
  rw [q.standardReadingRepair_kernel]

/-- The original repair maps back to its normalized Reading repair. -/
noncomputable def RepairQuotient.standardReadingHomFrom
    (q : RepairQuotient.{u, v, u, z} T (lawObserve laws) R) :
    RepairHom T (lawObserve laws) R q q.standardReadingRepair := by
  apply Classical.choice
  apply RepairHom.nonempty_iff_kernel_le.mpr
  change q.kernel.setoid ≤ q.standardReadingRepair.kernel.setoid
  rw [q.standardReadingRepair_kernel]

/-- Both source-commuting morphism compositions are the identities, by the
uniqueness theorem for morphisms of surjective repair quotients. -/
theorem RepairQuotient.standardReadingHom_left_inv
    (q : RepairQuotient.{u, v, u, z} T (lawObserve laws) R) :
    (q.standardReadingHomTo.toFun ∘ q.standardReadingHomFrom.toFun) = id := by
  exact RepairHom.unique
    (RepairHom.comp q.standardReadingHomFrom q.standardReadingHomTo)
    (RepairHom.id q)

theorem RepairQuotient.standardReadingHom_right_inv
    (q : RepairQuotient.{u, v, u, z} T (lawObserve laws) R) :
    (q.standardReadingHomFrom.toFun ∘ q.standardReadingHomTo.toFun) = id := by
  exact RepairHom.unique
    (RepairHom.comp q.standardReadingHomTo q.standardReadingHomFrom)
    (RepairHom.id q.standardReadingRepair)

/-- The morphism in the preceding isomorphism is the standard quotient
equivalence of B, not an arbitrary replacement of the source map. -/
theorem RepairQuotient.standardReadingHomTo_eq_standardEquiv
    (q : RepairQuotient.{u, v, u, z} T (lawObserve laws) R) :
    q.standardReadingHomTo.toFun = q.standardEquiv := by
  funext target
  obtain ⟨x, rfl⟩ := q.standardReadingRepair.surjective target
  exact q.standardReadingHomTo.source_comm x

end AAT.AG.OperationRepair

#assert_standard_axioms_only AAT.AG.OperationRepair
