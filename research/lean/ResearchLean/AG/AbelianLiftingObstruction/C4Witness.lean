import ResearchLean.AG.AbelianLiftingObstruction.ProtocolExtension
import ResearchLean.AG.AbelianLiftingObstruction.SquarePresentation
import ResearchLean.AG.ProtocolHolonomy.TwoVertexNoSection
import ResearchLean.AG.ProtocolHolonomy.TwoVertexQuotient

/-!
# The same G-127 non-split C₄ extension on the three-cell square

G-129 completion criterion 2: both original visible-swap lifts are evaluated
in the actual change group and projectionToLiftable. Their generated local
coefficients have rho = id, d1 = 2 = 0 and d2 = rho - 1 = 0. The original
defect maps to 1 in the actual H2 quotient, so B3 excludes original square
lifts and therefore sections of the same original visible projection.

## Implementation notes

A Bool indexes the two already constructed original state changes; it does
not replace their source group with an abstract cyclic group. The existing
C4/C2 equivalences identify the full actual group and kernel, and the kernel
generator is evaluated back to the original vertical change.

The H2 coordinate factors through the actual cycle subgroup and its actual
boundary range. Defining H2 directly as ZMod 2 would omit the required native
cohomology computation. Here zero differentials prove that range is bottom,
and the canonical quotient equivalence gives the coordinate.

A hypothetical original group section is converted to an independently
defined GroupSolution before applying B3. The accepted no-section theorem is
also recorded on that identical source proposition, while the new proof uses
the computed nonzero obstruction.
-/

namespace AAT.AG.AbelianLiftingObstruction.C4Witness
open AAT.AG.ProtocolHolonomy AAT.AG.RealizationReconstruction TransportCoherence
open GroupExtension
/-- G-129 completion criterion 2: The original operation-preserving change group of the fixed two-vertex example. -/
abbrev E := twoVertexData.ChangeGroup twoVertexInput.H
/-- G-129 completion criterion 2: The original liftable visible subgroup; it is the whole selected visible C2. -/
abbrev H := twoVertexData.LiftableVisible twoVertexInput.H
/-- G-129 completion criterion 2: The same original projection to liftable visible changes. -/
abbrev π : E →* H := twoVertexData.projectionToLiftable twoVertexInput.H

/-- G-129 completion criterion 2: The full original change group is commutative via its accepted C4 presentation. -/
theorem ambient_comm (a b : E) : a * b = b * a := by
  apply twoVertexC4.symm.injective
  simp only [map_mul]
  exact mul_comm _ _

/-- G-129 completion criterion 2: A condition 1: the entire actual projection kernel is commutative. -/
theorem kernel_comm (a b : π.ker) : a * b = b * a := by
  apply Subtype.ext
  exact ambient_comm a b

/-- G-129 completion criterion 2: The full original identity-visible lift group is cyclic two. -/
noncomputable def verticalC2 :
    Multiplicative (ZMod 2) ≃* twoVertexData.Lift (1 : FixedFGraphAutomorphism twoVertexGraph) := by
  rw [← twoVertex_vertical_card_two]
  exact zmodCyclicMulEquiv twoVertex_vertical_isCyclic

/-- G-129 completion criterion 2: The full actual kernel is C2 through the original vertical inclusion. -/
noncomputable def kernelC2 : Multiplicative (ZMod 2) ≃* π.ker :=
  verticalC2.trans
    (twoVertexData.verticalLiftEquivLiftableKernel twoVertexInput.H)

/-- G-129 completion criterion 2: The two original swap lifts, indexed by false (first) and true (second). -/
def reference (choice : Bool) : ∀ {i j : squarePresentation.Vertex}, squarePresentation.Edge i j → E :=
  fun {_ _} _ => if choice then twoVertexSecondCycleChange else twoVertexCycleChange

/-- G-129 completion criterion 2: The same nonidentity visible change is the fixed core value. -/
def core : ∀ {i j : squarePresentation.Vertex}, squarePresentation.Edge i j → H :=
  fun {_ _} _ => π twoVertexCycleChange

/-- G-129 completion criterion 2: Both original lifts project to that identical fixed core value. -/
theorem projects (choice : Bool) {i j : squarePresentation.Vertex} (e : squarePresentation.Edge i j) :
    π (reference choice e) = core e := by
  cases choice
  · rfl
  · apply Subtype.ext
    apply Subtype.ext
    rfl

/-- G-129 completion criterion 2: The original visible core has square one. -/
theorem core_sq : (@core () () ()) ^ 2 = 1 := by
  apply Subtype.ext
  apply Subtype.ext
  change twoVertexSwap ^ 2 = 1
  exact congrArg Subtype.val twoVertexVisibleSwap_sq

/-- G-129 completion criterion 2: The fixed core satisfies the shared square word relation. -/
theorem relations (f : squarePresentation.TwoCell) :
    pathValue squarePresentation core (squarePresentation.twoLeft f) =
      pathValue squarePresentation core (squarePresentation.twoRight f) := by
  cases f
  simpa [pathValue, squarePresentation, squareTwoPresentation, squareTwo,
    squareEdge, pow_two] using core_sq

/-- G-129 completion criterion 2: D applied to the same original group projection, for either reference lift.
Strongness, A2, transport bijectivity and comparison centralization are generated. -/
noncomputable abbrev input (choice : Bool) := GroupExtension.input squarePresentation π kernel_comm
  core (reference choice) (projects choice) relations

/-- G-129 completion criterion 2: Remove the multiplicative and additive type tags, preserving all group values. -/
noncomputable def tagEquiv : Additive (Multiplicative (ZMod 2)) ≃+ ZMod 2 where
  toFun x := Multiplicative.toAdd (Additive.toMul x)
  invFun x := Additive.ofMul (Multiplicative.ofAdd x)
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl

/-- G-129 completion criterion 2: A1: every coefficient is the full actual kernel, identified additively with C2. -/
noncomputable def coefficient (choice : Bool) :
    (input choice).toTower.localCoefficients.A () ≃+ ZMod 2 :=
  ((GroupExtension.coefficientEquiv squarePresentation π kernel_comm core
    (reference choice) (projects choice) relations ()).trans
    kernelC2.symm.toAdditive).trans tagEquiv

/-- G-129 completion criterion 2: Both original lifts square to the same nonidentity vertical change. -/
theorem reference_sq (choice : Bool) :
    (reference choice (i := ()) (j := ()) ()) ^ 2 = twoVertexVerticalChange := by
  cases choice
  · exact twoVertexCycleChange_sq
  · exact twoVertexSecondCycleChange_sq

/-- G-129 completion criterion 2: The local coefficients generated from the same input and reference lift. -/
noncomputable abbrev M (choice : Bool) := (input choice).toTower.localCoefficients

/-- G-129 completion criterion 2: A2 evaluation: the generated edge transport is identity on the full actual kernel. -/
theorem edge_identity (choice : Bool) (a : (M choice).A ()) :
    (M choice).edge (() : squarePresentation.Edge () ()) a = a := by
  obtain ⟨k, hk⟩ := (GroupExtension.kernelEquiv π).surjective (Additive.toMul a)
  change Additive.ofMul _ = a
  have h := GroupExtension.transport_kernelEquiv π (reference choice (i := ()) (j := ()) ()) k
  have hcon : GroupExtension.conjugation π (reference choice (i := ()) (j := ()) ()) k = k := by
    apply Subtype.ext
    change reference choice () * k.1 * (reference choice ())⁻¹ = k.1
    rw [ambient_comm (reference choice ()) k.1]
    group
  rw [hcon] at h
  simpa only [GroupExtension.input_edge_value, hk] using congrArg Additive.ofMul h

/-- G-129 completion criterion 2: Every actual coefficient doubles to zero, through its full C2 equivalence. -/
theorem coefficient_double (choice : Bool) (a : (M choice).A ()) : a + a = 0 := by
  apply (coefficient choice).injective
  rw [map_add, map_zero]
  have h (x : ZMod 2) : x + x = 0 := by fin_cases x <;> decide
  exact h _

/-- G-129 completion criterion 2: A3 evaluation: the generated vertex differential is 1 - rho = 0. -/
theorem d0_zero (choice : Bool) (b : C0 (M choice)) : d0 (M choice) b = 0 := by
  funext ⟨i,j,e⟩
  cases i; cases j; cases e
  rw [square_d0, edge_identity, sub_self]
  rfl

/-- G-129 completion criterion 2: A3 evaluation: the generated face differential is rho + 1 = 2 = 0. -/
theorem d1_zero (choice : Bool) (h : C1 (M choice)) : d1 (M choice) h = 0 := by
  funext f
  cases f
  rw [square_d1, edge_identity, coefficient_double]
  rfl

/-- G-129 completion criterion 2: A3 evaluation: the specified three-cell differential is rho - 1 = 0. -/
theorem d2_zero (choice : Bool) (c : C2 (M choice)) : d2 (M choice) c = 0 := by
  funext cell
  cases cell
  rw [square_d2]
  change (M choice).edge (() : squarePresentation.Edge () ()) (c ()) - c () = 0
  exact sub_eq_zero.mpr (edge_identity choice (c ()))

/-- G-129 completion criterion 2: A4: the two specified authored pastings are equal for either original lift. -/
theorem syzygy (choice : Bool) : ∀ cell : squarePresentation.ThreeCell,
    TransportCoherence.Arbitrary.AuthoredSyzygy (input choice).toTower.toTransportData 1
      (squarePresentation.threeLeft cell) (squarePresentation.threeRight cell) :=
  GroupExtension.syzygy squarePresentation π kernel_comm core
    (reference choice) (projects choice) relations

/-- G-129 completion criterion 2: B1 evaluation: the actual defect is the original nonidentity vertical change. -/
theorem defect_value (choice : Bool) :
    (Additive.toMul (GroupExtension.coefficientEquiv squarePresentation π kernel_comm
      core (reference choice) (projects choice) relations () ((input choice).toTower.defect ()))).1 =
      twoVertexVerticalChange := by
  have hd := GroupExtension.coefficientEquiv_defect squarePresentation π kernel_comm
    core (reference choice) (projects choice) relations ()
  exact hd.trans (by
    simpa [pathValue, squarePresentation, squareTwoPresentation, squareTwo, squareEdge,
      pow_two] using reference_sq choice)

/-- G-129 completion criterion 2: The actual defect is nonzero for either original reference lift. -/
theorem defect_nonzero (choice : Bool) : (input choice).toTower.defect () ≠ 0 := by
  intro h
  have hd := defect_value choice
  rw [h, map_zero] at hd
  exact twoVertexVerticalChange_ne_one hd.symm

/-- G-129 completion criterion 2: B1 evaluation: the actual defect has coordinate 1 in the full C2 kernel. -/
theorem defect_coordinate (choice : Bool) :
    coefficient choice ((input choice).toTower.defect ()) = 1 := by
  have hn : coefficient choice ((input choice).toTower.defect ()) ≠ 0 := by
    intro h
    exact defect_nonzero choice ((coefficient choice).injective (h.trans (map_zero _).symm))
  have hc (x : ZMod 2) : x = 0 ∨ x = 1 := by
    fin_cases x <;> first | exact Or.inl rfl | exact Or.inr rfl
  exact (hc _).resolve_left hn

/-- G-129 completion criterion 2: B1 evaluation: the same three-cell differential kills the actual defect. -/
theorem defect_cocycle (choice : Bool) :
    d2 (M choice) (input choice).toTower.defect = 0 := d2_zero choice _


/-- G-129 completion criterion 2: Every degree-two cochain is a cycle; evaluation at the sole face is an additive equivalence. -/
noncomputable def cycleCoordinate (choice : Bool) : Z2 (M choice) ≃+ (M choice).A () where
  toFun z := z.1 ()
  invFun a := ⟨fun _ => a, d2_zero choice _⟩
  left_inv z := by apply Subtype.ext; funext f; cases f; rfl
  right_inv _ := rfl
  map_add' _ _ := rfl

/-- G-129 completion criterion 2: The actual face coboundary range in the actual cycle subgroup is bottom. -/
theorem boundary_bot (choice : Bool) : (d1ToZ2 (M choice)).range = ⊥ := by
  apply AddSubgroup.ext
  intro z
  constructor
  · rintro ⟨h, rfl⟩
    apply AddSubgroup.mem_bot.mpr
    apply Subtype.ext
    exact d1_zero choice h
  · intro hz
    rw [AddSubgroup.mem_bot] at hz
    subst z
    exact ⟨0, map_zero _⟩

/-- G-129 completion criterion 2: The native H2 quotient of the generated complex is additively C2. -/
noncomputable def h2Coordinate (choice : Bool) : H2 (M choice) ≃+ ZMod 2 :=
  (((QuotientAddGroup.quotientAddEquivOfEq (boundary_bot choice)).trans
    QuotientAddGroup.quotientBot).trans (cycleCoordinate choice)).trans (coefficient choice)

/-- G-129 completion criterion 2: The native quotient equivalence evaluates each original cycle at the sole face. -/
theorem h2Coordinate_mk (choice : Bool) (z : Z2 (M choice)) :
    h2Coordinate choice (QuotientAddGroup.mk z) = coefficient choice (z.1 ()) := rfl

/-- G-129 completion criterion 2: The actual obstruction class has coordinate 1 in the native H2 quotient. -/
theorem obstruction_coordinate (choice : Bool) :
    h2Coordinate choice ((input choice).toTower.obstructionClass (syzygy choice)) = 1 :=
  defect_coordinate choice

/-- G-129 completion criterion 2: The computed original obstruction is nonzero for either reference lift. -/
theorem obstruction_nonzero (choice : Bool) :
    (input choice).toTower.obstructionClass (syzygy choice) ≠ 0 := by
  intro h
  have hv := obstruction_coordinate choice
  rw [h, map_zero] at hv
  exact (by decide : (0 : ZMod 2) ≠ 1) hv

/-- G-129 completion criterion 2: B3 excludes all original coherent lifts over this same fixed core. -/
theorem no_solution (choice : Bool) : ¬ Nonempty (Solution (input choice)) := by
  intro h
  exact obstruction_nonzero choice
    (((input choice).obstructionClass_eq_zero_iff_solution (syzygy choice)).mpr h)

/-- G-129 completion criterion 2: D/B3 excludes all original E-valued lifts preserving the square relation. -/
theorem no_group_solution : ¬ Nonempty (GroupSolution squarePresentation π core) := by
  intro h
  exact obstruction_nonzero false ((GroupExtension.obstruction_zero_iff squarePresentation
    π kernel_comm core (reference false) (projects false) relations).mpr h)

/-- G-129 completion criterion 2: Every section of the original visible projection supplies an original square lift. -/
noncomputable def solutionOfSection
    (s : twoVertexInput.H →* E)
    (hs : Function.RightInverse s twoVertexActualProjection) :
    GroupSolution squarePresentation π core where
  edge _ := s twoVertexVisibleSwap
  projects _ := by
    apply Subtype.ext
    exact hs twoVertexVisibleSwap
  face f := by
    cases f
    change s twoVertexVisibleSwap * s twoVertexVisibleSwap * 1 = 1
    rw [mul_one, ← map_mul, ← pow_two, twoVertexVisibleSwap_sq, map_one]

/-- G-129 completion criterion 2: The computed nonzero H2 obstruction excludes a section of the original visible projection. -/
theorem no_group_section_from_obstruction :
    ¬ ∃ s : twoVertexInput.H →* E, Function.RightInverse s twoVertexActualProjection := by
  rintro ⟨s, hs⟩
  exact no_group_solution ⟨solutionOfSection s hs⟩

/-- G-129 completion criterion 2: The new obstruction proof and accepted G-127 result have the identical source proposition. -/
theorem agrees_with_original_no_section :
    (¬ ∃ s : twoVertexInput.H →* E, Function.RightInverse s twoVertexActualProjection) ∧
    (¬ ∃ s : twoVertexInput.H →* E, Function.RightInverse s
      (ReversibleData.ChangeGroup.projection (D := twoVertexData) (H := twoVertexInput.H))) :=
  ⟨no_group_section_from_obstruction, twoVertex_no_group_section⟩


/-- G-129 completion criterion 2: For every original change, the liftable projection keeps the original visible projection value. -/
theorem same_projection (a : E) : (π a).1 = twoVertexActualProjection a := rfl

/-- G-129 completion criterion 2: The specified core exchanges the original graph vertices and edges. -/
theorem core_nonidentity : @core () () () ≠ 1 := by
  intro h
  have hv := congrArg (fun g : H => g.1.1.edge false) h
  change true = false at hv
  cases hv

/-- G-129 completion criterion 2: The two fixed original lifts exhaust the fiber over that same visible exchange. -/
theorem reference_exhaustive (a : E) (h : π a = @core () () ()) :
    a = reference false (i := ()) (j := ()) () ∨
      a = reference true (i := ()) (j := ()) () := by
  apply twoVertex_swap_change_cases a
  exact congrArg (fun g : H => g.1.1) h

/-- G-129 completion criterion 2: A4 evaluation: deleting the first e2 in e3 gives the identity authored comparator. -/
theorem first_pasting_value (choice : Bool) :
    TransportCoherence.Arbitrary.authoredPastingComparator
      (input choice).toTower.toTransportData 1 (squarePresentation.threeLeft ()) = 1 :=
  GroupExtension.authored_pasting_one squarePresentation π kernel_comm core
    (reference choice) (projects choice) relations _

/-- G-129 completion criterion 2: A4 evaluation: deleting the last e2 in e3 gives the identity authored comparator. -/
theorem last_pasting_value (choice : Bool) :
    TransportCoherence.Arbitrary.authoredPastingComparator
      (input choice).toTower.toTransportData 1 (squarePresentation.threeRight ()) = 1 :=
  GroupExtension.authored_pasting_one squarePresentation π kernel_comm core
    (reference choice) (projects choice) relations _

/-- G-129 completion criterion 2: The two native H2 quotients are identified by their evaluated kernel coordinates. -/
noncomputable def referenceH2Equiv : H2 (M false) ≃+ H2 (M true) :=
  (h2Coordinate false).trans (h2Coordinate true).symm

/-- G-129 completion criterion 2: The two original reference lifts give the same nonzero obstruction under this identification. -/
theorem reference_obstruction_same :
    referenceH2Equiv ((input false).toTower.obstructionClass (syzygy false)) =
      (input true).toTower.obstructionClass (syzygy true) := by
  apply (h2Coordinate true).injective
  change h2Coordinate true ((h2Coordinate true).symm
    (h2Coordinate false ((input false).toTower.obstructionClass (syzygy false)))) = _
  rw [AddEquiv.apply_symm_apply, obstruction_coordinate, obstruction_coordinate]


/-- G-129 completion criterion 2: The same original projection is reduction C4 to C2 under the accepted presentations. -/
theorem original_projection_mod_two (z : Multiplicative (ZMod 4)) :
    twoVertexC2.symm ((π (twoVertexC4 z)).1) = twoVertexModTwo z :=
  twoVertex_projection_is_mod_two z

/-- G-129 completion criterion 2: Every element of the original selected visible C2 lifts in the original operation graph. -/
theorem liftable_visible_full : twoVertexData.LiftableVisible twoVertexInput.H = ⊤ :=
  twoVertex_liftableVisible_eq_top

/-- G-129 completion criterion 2: The two reference lifts differ on the original state above vertex false. -/
theorem reference_distinct : reference false (i := ()) (j := ()) () ≠
    reference true (i := ()) (j := ()) () := by
  intro h
  have hs := congrArg (fun c : E => (c.1.state ⟨false, false⟩).2) h
  change false = true at hs
  cases hs

/-- G-129 completion criterion 2: The C2 generator includes as the original nonidentity vertical change. -/
theorem kernel_generator_value : (kernelC2 (Multiplicative.ofAdd 1)).1 =
    twoVertexVerticalChange := by
  let a := Additive.toMul (GroupExtension.coefficientEquiv squarePresentation π kernel_comm
    core (reference false) (projects false) relations () ((input false).toTower.defect ()))
  have ha : kernelC2.symm a = Multiplicative.ofAdd 1 := by
    apply Multiplicative.toAdd.injective
    exact defect_coordinate false
  have hk : kernelC2 (Multiplicative.ofAdd 1) = a := by
    rw [← ha, MulEquiv.apply_symm_apply]
  exact (congrArg Subtype.val hk).trans (defect_value false)

end AAT.AG.AbelianLiftingObstruction.C4Witness
#assert_standard_axioms_only AAT.AG.AbelianLiftingObstruction.C4Witness
