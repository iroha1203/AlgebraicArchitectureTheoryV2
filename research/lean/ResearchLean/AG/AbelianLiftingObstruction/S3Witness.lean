import ResearchLean.AG.AbelianLiftingObstruction.GroupExtension
import ResearchLean.AG.AbelianLiftingObstruction.SquarePresentation
import Mathlib.GroupTheory.Perm.Sign
import Mathlib.GroupTheory.SpecificGroups.Cyclic
import Mathlib.Tactic.FinCases
import Mathlib.Data.Fintype.Units

/-!
# The actual S₃ sign extension with nontrivial local coefficients

G-129 completion criterion 3 applies D to Sym(Fin 3) and its original sign
homomorphism. The full sign kernel is C3 with generator (012). The reference
lift (01) induces rho = -1 on the generated coefficients. The same square
has d0 = 2, d1 = 0, d2 = -2 = id and defect zero. The native H1 and H2
quotients are zero; the actual three transpositions form a first-cocycle
torsor and one class under original kernel vertex conjugation.

## Implementation notes

The kernel coordinate is constructed by the three actual even permutations.
Using an unspecified cyclic equivalence would not fix its generator to (012).
`kernel_cases` follows from the six original permutations and sign membership,
and both maps of `kernelC3` retain all original kernel elements.

The differentials and defect are evaluated after the group adapter generates
them. H1 and H2 remain the native cycle/boundary quotients; replacing their
definitions by a trivial group would omit the required calculation. Their
trivialization follows from d0 surjectivity and d2 injectivity.

`originalSolutionTorsor` exposes the native first-cocycle structure as an
explicit value, while `c3Action` exposes its C3 coordinates. A second global
instance under the coordinate group would compete for the same solution
carrier and the AddTorsor action-group out-parameter. The explicit coordinate
value formulas and free-transitive theorem provide this second reading
without making typeclass selection choose between these groups.

All solution and vertex-class calculations use the adapter's edge-preserving
full equivalence. Creating another orbit quotient would duplicate that
relation. `vertexConjugation_value` and `vertex_transitive` identify the same
native H1 quotient with original S3 kernel conjugation.
-/

namespace AAT.AG.AbelianLiftingObstruction.S3Witness
open GroupExtension TransportCoherence

/-- G-129 completion criterion 3: The original full permutation group Sym(Fin 3). -/
abbrev E := Equiv.Perm (Fin 3)
/-- G-129 completion criterion 3: The full sign codomain, the two integer units. -/
abbrev H := ℤˣ
/-- G-129 completion criterion 3: The original sign homomorphism on all six permutations. -/
abbrev π : E →* H := Equiv.Perm.sign

/-- G-129 completion criterion 3: The specified kernel generator (012), with the usual composition order. -/
def cycle : E := Equiv.swap 0 1 * Equiv.swap 1 2

/-- G-129 completion criterion 3: The specified reference lift (01). -/
def reference : E := Equiv.swap 0 1

/-- G-129 completion criterion 3: The generator maps 0 to 1, 1 to 2 and 2 to 0. -/
theorem cycle_value (x : Fin 3) : cycle x = x + 1 := by
  fin_cases x <;> decide

/-- G-129 completion criterion 3: The original generator lies in the actual sign kernel. -/
theorem cycle_sign : π cycle = 1 := by
  simp [cycle, Equiv.Perm.sign_swap (by decide : (0 : Fin 3) ≠ 1),
    Equiv.Perm.sign_swap (by decide : (1 : Fin 3) ≠ 2)]

/-- G-129 completion criterion 3: The reference lift projects to the nonidentity visible value. -/
theorem reference_sign : π reference = -1 :=
  Equiv.Perm.sign_swap (by decide : (0 : Fin 3) ≠ 1)

/-- G-129 completion criterion 3: The six original permutations exhaust the full S3 group. -/
theorem permutations (p : E) : p = 1 ∨ p = cycle ∨ p = cycle ^ 2 ∨
    p = Equiv.swap 0 1 ∨ p = Equiv.swap 0 2 ∨ p = Equiv.swap 1 2 := by
  fin_cases p <;> decide


/-- G-129 completion criterion 3: The original sign map is onto its full C2 codomain. -/
theorem π_surjective : Function.Surjective π := Equiv.Perm.sign_surjective (Fin 3)

/-- G-129 completion criterion 3: The original three-cycle has cube one. -/
theorem cycle_cube : cycle ^ 3 = 1 := by decide

/-- G-129 completion criterion 3: The specified original three-cycle as an actual sign-kernel element. -/
def kernelGenerator : π.ker := ⟨cycle, cycle_sign⟩

/-- G-129 completion criterion 3: The actual full sign kernel consists of 1, (012), and its square. -/
theorem kernel_cases (a : π.ker) : a = 1 ∨ a = kernelGenerator ∨ a = kernelGenerator ^ 2 := by
  have ha : π a.1 = 1 := a.2
  rcases permutations a.1 with h | h | h | h | h | h
  · exact Or.inl (Subtype.ext h)
  · exact Or.inr (Or.inl (Subtype.ext h))
  · exact Or.inr (Or.inr (Subtype.ext h))
  · rw [h, Equiv.Perm.sign_swap (by decide : (0 : Fin 3) ≠ 1)] at ha
    norm_num at ha
  · rw [h, Equiv.Perm.sign_swap (by decide : (0 : Fin 3) ≠ 2)] at ha
    norm_num at ha
  · rw [h, Equiv.Perm.sign_swap (by decide : (1 : Fin 3) ≠ 2)] at ha
    norm_num at ha

/-- G-129 completion criterion 3: A condition 1: the full original sign kernel is commutative. -/
theorem kernel_comm (a b : π.ker) : a * b = b * a := by
  rcases kernel_cases a with rfl | rfl | rfl <;>
    rcases kernel_cases b with rfl | rfl | rfl <;> group

/-- G-129 completion criterion 3: The three C3 coordinates as original actual kernel elements. -/
def c3Value (x : Multiplicative (ZMod 3)) : π.ker :=
  if Multiplicative.toAdd x = 0 then 1 else
    if Multiplicative.toAdd x = 1 then kernelGenerator else kernelGenerator ^ 2

/-- G-129 completion criterion 3: The inverse coordinate reads each actual kernel permutation. -/
def c3Index (a : π.ker) : Multiplicative (ZMod 3) :=
  if a = 1 then Multiplicative.ofAdd 0 else
    if a = kernelGenerator then Multiplicative.ofAdd 1 else Multiplicative.ofAdd 2

/-- G-129 completion criterion 3: The full actual sign kernel is C3, with both maps and multiplication preserved. -/
def kernelC3 : Multiplicative (ZMod 3) ≃* π.ker where
  toFun := c3Value
  invFun := c3Index
  left_inv x := by fin_cases x <;> decide
  right_inv a := by rcases kernel_cases a with rfl | rfl | rfl <;> decide
  map_mul' x y := by fin_cases x <;> fin_cases y <;> decide

/-- G-129 completion criterion 3: The coordinate 1 is the specified actual kernel generator. -/
theorem kernelC3_generator : kernelC3 (Multiplicative.ofAdd 1) = kernelGenerator := by decide

/-- G-129 completion criterion 3: Conjugation by the reference lift inverts every actual kernel element. -/
theorem conjugation_inverts (a : π.ker) : GroupExtension.conjugation π reference a = a⁻¹ := by
  rcases kernel_cases a with rfl | rfl | rfl <;> decide

/-- G-129 completion criterion 3: The same nonidentity C2 value is fixed on the shared square edge. -/
def core : ∀ {i j : squarePresentation.Vertex}, squarePresentation.Edge i j → H :=
  fun {_ _} _ => -1

/-- G-129 completion criterion 3: The reference transposition is the chosen original E lift on that edge. -/
def lifts : ∀ {i j : squarePresentation.Vertex}, squarePresentation.Edge i j → E :=
  fun {_ _} _ => reference

/-- G-129 completion criterion 3: The original edge lift projects to the specified fixed core. -/
theorem projects {i j : squarePresentation.Vertex} (e : squarePresentation.Edge i j) :
    π (lifts e) = core e := reference_sign

/-- G-129 completion criterion 3: The same core satisfies the square word relation. -/
theorem relations (f : squarePresentation.TwoCell) :
    pathValue squarePresentation core (squarePresentation.twoLeft f) =
      pathValue squarePresentation core (squarePresentation.twoRight f) := by
  cases f
  simp [pathValue, squarePresentation, squareTwoPresentation, squareTwo, squareEdge, core]

/-- G-129 completion criterion 3: D constructs the same original sign tower and all concrete A conditions. -/
noncomputable abbrev input :=
  GroupExtension.input squarePresentation π kernel_comm core lifts projects relations
/-- G-129 completion criterion 3: The local coefficients generated from that original tower input. -/
noncomputable abbrev M := input.toTower.localCoefficients


/-- G-129 completion criterion 3: Remove the additive and multiplicative tags, preserving every C3 value. -/
def tagEquiv : Additive (Multiplicative (ZMod 3)) ≃+ ZMod 3 where
  toFun x := Multiplicative.toAdd (Additive.toMul x)
  invFun x := Additive.ofMul (Multiplicative.ofAdd x)
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl

/-- G-129 completion criterion 3: A1: the full generated actual coefficient group is additively C3. -/
noncomputable def coefficient : M.A () ≃+ ZMod 3 :=
  ((GroupExtension.coefficientEquiv squarePresentation π kernel_comm core lifts projects relations ()).trans
    kernelC3.symm.toAdditive).trans tagEquiv

/-- G-129 completion criterion 3: A2 evaluation: the generated coefficient edge map is rho = -1. -/
theorem edge_neg (a : M.A ()) : M.edge (() : squarePresentation.Edge () ()) a = -a := by
  obtain ⟨k, hk⟩ := (GroupExtension.kernelEquiv π).surjective (Additive.toMul a)
  have h := GroupExtension.transport_kernelEquiv π reference k
  rw [conjugation_inverts] at h
  have hn : Additive.ofMul (GroupExtension.kernelEquiv π (k⁻¹)) = -a := by
    rw [map_inv, hk]
    rfl
  change Additive.ofMul _ = -a
  simpa only [GroupExtension.input_edge_value, lifts, hk] using (congrArg Additive.ofMul h).trans hn

/-- G-129 completion criterion 3: On this entire actual kernel, -2 is the identity map. -/
theorem negative_double (a : M.A ()) : -a - a = a := by
  apply coefficient.injective
  rw [map_sub, map_neg]
  have h (x : ZMod 3) : -x - x = x := by fin_cases x <;> decide
  exact h _

/-- G-129 completion criterion 3: A3 evaluation: the generated vertex differential is 1 - rho = 2. -/
theorem d0_value (b : C0 M) : d0 M b ⟨(), (), ()⟩ = 2 • b () := by
  rw [square_d0, edge_neg]
  simp [two_nsmul]

/-- G-129 completion criterion 3: A3 evaluation: the generated face differential is 1 + rho = 0. -/
theorem d1_zero (h : C1 M) : d1 M h = 0 := by
  funext f
  cases f
  rw [square_d1, edge_neg, neg_add_cancel]
  rfl

/-- G-129 completion criterion 3: A3 evaluation: the same specified three-cell differential is rho - 1 = -2 = id. -/
theorem d2_value (c : C2 M) : d2 M c () = c () := by
  rw [square_d2]
  change M.edge (() : squarePresentation.Edge () ()) (c ()) - c () = c ()
  exact (congrArg (fun a => a - c ()) (edge_neg (c ()))).trans (negative_double (c ()))

/-- G-129 completion criterion 3: The original reference transposition squares to one. -/
theorem reference_sq : reference ^ 2 = 1 := by decide

/-- G-129 completion criterion 3: B1 evaluation: the generated original defect is zero, from the original square word. -/
theorem defect_zero : input.toTower.defect = 0 := by
  funext f
  cases f
  apply (GroupExtension.coefficientEquiv squarePresentation π kernel_comm core lifts projects relations ()).injective
  apply Additive.toMul.injective
  apply Subtype.ext
  have hd := GroupExtension.coefficientEquiv_defect squarePresentation π kernel_comm core lifts projects relations ()
  exact hd.trans (by simpa [pathValue, squarePresentation, squareTwoPresentation,
    squareTwo, squareEdge, lifts, pow_two] using reference_sq)

/-- G-129 completion criterion 3: A4: the two specified authored square deletions have equal comparisons. -/
theorem syzygy : ∀ cell : squarePresentation.ThreeCell,
    TransportCoherence.Arbitrary.AuthoredSyzygy input.toTower.toTransportData 1
      (squarePresentation.threeLeft cell) (squarePresentation.threeRight cell) :=
  GroupExtension.syzygy squarePresentation π kernel_comm core lifts projects relations

/-- G-129 completion criterion 3: B1 evaluation: the same generated three-cell differential kills the original defect. -/
theorem defect_cocycle : d2 M input.toTower.defect = 0 := by
  rw [defect_zero]
  exact map_zero (d2Hom M)

/-- G-129 completion criterion 3: The actual second cycle subgroup is zero, since its generated differential is injective. -/
theorem z2_zero (z : Z2 M) : z = 0 := by
  apply Subtype.ext
  funext f
  cases f
  have h := congrFun z.2 ()
  exact (d2_value z.1).symm.trans h

/-- G-129 completion criterion 3: Every class in the actual native H2 quotient is zero. -/
theorem h2_zero (x : H2 M) : x = 0 := by
  induction x using Quotient.inductionOn with | h z =>
    rw [z2_zero z]
    rfl

/-- G-129 completion criterion 3: Every class in the actual native H1 quotient is zero, using the generated vertex differential. -/
theorem h1_zero (x : H1 M) : x = 0 := by
  induction x using Quotient.inductionOn with | h z =>
    apply (h1_eq_zero_iff M z).mpr
    refine ⟨fun _ => -z.1 ⟨(), (), ()⟩, ?_⟩
    apply Subtype.ext
    funext ⟨i, j, e⟩
    cases i; cases j; cases e
    change d0 M (fun _ => -z.1 ⟨(), (), ()⟩) ⟨(), (), ()⟩ = z.1 ⟨(), (), ()⟩
    rw [square_d0, edge_neg, neg_neg]
    exact negative_double _


/-- G-129 completion criterion 3: The actual first cocycles are all C3 edge values, with an additive equivalence. -/
noncomputable def z1Coordinate : Z1 M ≃+ ZMod 3 where
  toFun z := coefficient (z.1 ⟨(), (), ()⟩)
  invFun a := ⟨fun _ => coefficient.symm a, d1_zero _⟩
  left_inv z := by
    apply Subtype.ext
    funext ⟨i, j, e⟩
    cases i; cases j; cases e
    exact coefficient.symm_apply_apply _
  right_inv a := coefficient.apply_symm_apply a
  map_add' z w := map_add coefficient _ _

/-- G-129 completion criterion 3: All original S3 square lifts over the fixed core, independently of the cochain equation. -/
abbrev GroupSolutions := GroupSolution squarePresentation π core

/-- G-129 completion criterion 3: The sole original edge value determines all data in an original square solution. -/
theorem solution_ext {S R : GroupSolutions} (h : S.edge (i := ()) (j := ()) () =
    R.edge (i := ()) (j := ()) ()) : S = R := by
  cases S with | mk eS pS fS =>
    cases R with | mk eR pR fR =>
      have he : @eS = @eR := by
        funext i j e
        cases i; cases j; cases e
        exact h
      subst eR
      rfl

/-- G-129 completion criterion 3: Each original transposition gives a relation-preserving S3 lift of the fixed core. -/
def transpositionSolution (i j : Fin 3) (hne : i ≠ j) : GroupSolutions where
  edge _ := Equiv.swap i j
  projects _ := Equiv.Perm.sign_swap hne
  face f := by
    cases f
    change Equiv.swap i j * Equiv.swap i j * 1 = 1
    simp

/-- G-129 completion criterion 3: The specified reference transposition as an actual solution. -/
def origin : GroupSolutions := transpositionSolution 0 1 (by decide)

/-- G-129 completion criterion 3: The original solution carrier is inhabited by that transposition. -/
instance solutions_nonempty : Nonempty GroupSolutions := ⟨origin⟩

/-- G-129 completion criterion 3: All original solutions are precisely the three original transpositions. -/
theorem solution_cases (S : GroupSolutions) :
    S = origin ∨ S = transpositionSolution 0 2 (by decide) ∨
      S = transpositionSolution 1 2 (by decide) := by
  have hs : π (S.edge (i := ()) (j := ()) ()) = -1 := S.projects ()
  rcases permutations (S.edge (i := ()) (j := ()) ()) with h | h | h | h | h | h
  · rw [h, map_one] at hs
    norm_num at hs
  · rw [h, cycle_sign] at hs
    norm_num at hs
  · rw [h, map_pow, cycle_sign] at hs
    norm_num at hs
  · exact Or.inl (solution_ext h)
  · exact Or.inr (Or.inl (solution_ext h))
  · exact Or.inr (Or.inr (solution_ext h))

/-- G-129 completion criterion 3: Those three solutions differ on the original permutation values. -/
theorem solutions_distinct : origin ≠ transpositionSolution 0 2 (by decide) ∧
    origin ≠ transpositionSolution 1 2 (by decide) ∧
    transpositionSolution 0 2 (by decide) ≠ transpositionSolution 1 2 (by decide) := by
  constructor
  · intro h
    have he := congrArg (fun S : GroupSolutions => S.edge (i := ()) (j := ()) () 0) h
    change (1 : Fin 3) = 2 at he
    omega
  · constructor
    · intro h
      have he := congrArg (fun S : GroupSolutions => S.edge (i := ()) (j := ()) () 0) h
      change (1 : Fin 3) = 0 at he
      omega
    · intro h
      have he := congrArg (fun S : GroupSolutions => S.edge (i := ()) (j := ()) () 0) h
      change (2 : Fin 3) = 0 at he
      omega

/-- G-129 completion criterion 3: The full original solution carrier has its native AddTorsor structure under the same Z1. -/
noncomputable def originalSolutionTorsor : AddTorsor (Z1 M) GroupSolutions :=
  GroupExtension.groupAddTorsor squarePresentation π kernel_comm core lifts projects relations

/-- G-129 completion criterion 3: The same first-cocycle action expressed in the evaluated C3 coordinates. -/
noncomputable def c3Action (a : ZMod 3) (S : GroupSolutions) : GroupSolutions :=
  GroupExtension.groupAction squarePresentation π kernel_comm core lifts projects relations
    (z1Coordinate.symm a) S

/-- G-129 completion criterion 3: The evaluated C3 action on all original solutions is free and transitive. -/
theorem c3Action_free_transitive (S R : GroupSolutions) : ∃! a : ZMod 3, c3Action a R = S := by
  obtain ⟨z, hz, hu⟩ := GroupExtension.groupAction_existsUnique squarePresentation π kernel_comm
    core lifts projects relations R S
  refine ⟨z1Coordinate z, ?_, ?_⟩
  · change GroupExtension.groupAction squarePresentation π kernel_comm core lifts projects relations (z1Coordinate.symm (z1Coordinate z)) R = S
    rw [AddEquiv.symm_apply_apply]
    exact hz
  · intro a ha
    have hu' := hu (z1Coordinate.symm a) ha
    exact (z1Coordinate.apply_symm_apply a).symm.trans (congrArg z1Coordinate hu')

/-- G-129 completion criterion 3: The action multiplies the original S3 edge by exactly its original kernel element. -/
theorem c3Action_value (a : ZMod 3) (S : GroupSolutions) :
    (c3Action a S).edge (i := ()) (j := ()) () =
      (kernelC3 (Multiplicative.ofAdd a)).1 * S.edge (i := ()) (j := ()) () := by
  rw [c3Action, GroupExtension.groupAction_edge]
  rfl

/-- G-129 completion criterion 3: The same generated vertex action on all original S3 solutions. -/
noncomputable def vertexConjugation (b : C0 M) (S : GroupSolutions) : GroupSolutions :=
  GroupExtension.groupVertex squarePresentation π kernel_comm core lifts projects relations b S

/-- G-129 completion criterion 3: C1 evaluation: the original edge is conjugated by the actual kernel at the sole vertex. -/
theorem vertexConjugation_value (b : C0 M) (S : GroupSolutions) :
    (vertexConjugation b S).edge (i := ()) (j := ()) () =
      ((kernelEquiv π).symm (Additive.toMul (b ()))).1 * S.edge (i := ()) (j := ()) () *
        (((kernelEquiv π).symm (Additive.toMul (b ()))).1)⁻¹ :=
  GroupExtension.groupVertex_edge squarePresentation π kernel_comm core lifts projects relations b S ()

/-- G-129 completion criterion 3: H1 = 0 gives one original solution class under actual kernel vertex conjugation. -/
theorem vertex_transitive (S R : GroupSolutions) : ∃ b : C0 M, vertexConjugation b R = S := by
  let e := GroupExtension.solutionEquiv squarePresentation π kernel_comm core lifts projects relations
  let q := GroupExtension.groupOrbitEquivH1 squarePresentation π kernel_comm core lifts projects relations origin
  have heq : (⟦e.symm S⟧ : input.SolutionOrbit) = (⟦e.symm R⟧ : input.SolutionOrbit) := by
    apply q.symm.injective
    exact (h1_zero _).trans (h1_zero _).symm
  exact (GroupExtension.orbit_eq_iff_groupVertex squarePresentation π kernel_comm core lifts projects relations S R).mp heq


/-- G-129 completion criterion 3: All original solutions are bijective with C3 through the evaluated action. -/
noncomputable def solutionEquivC3 : ZMod 3 ≃ GroupSolutions :=
  Equiv.ofBijective (fun a => c3Action a origin) (by
    constructor
    · intro a b h
      obtain ⟨c, hc, hu⟩ := c3Action_free_transitive (c3Action a origin) origin
      exact (hu a rfl).trans (hu b h.symm).symm
    · intro S
      obtain ⟨a, ha, _⟩ := c3Action_free_transitive S origin
      exact ⟨a, ha⟩)

/-- G-129 completion criterion 3: The full original solution carrier contains exactly three elements. -/
theorem solution_card_three : Nat.card GroupSolutions = 3 := by
  rw [← Nat.card_congr solutionEquivC3, Nat.card_eq_fintype_card, ZMod.card]

/-- G-129 completion criterion 3: The original obstruction class is zero in its actual native H2. -/
theorem obstruction_zero : input.toTower.obstructionClass syzygy = 0 := h2_zero _

/-- G-129 completion criterion 3: B3 supplies a coherent lift of the same original input. -/
theorem b3_nonempty : Nonempty (Solution input) :=
  (input.obstructionClass_eq_zero_iff_solution syzygy).mp obstruction_zero

/-- G-129 completion criterion 3: A4 evaluation: deleting the first e2 gives the identity authored comparison. -/
theorem first_pasting_value :
    TransportCoherence.Arbitrary.authoredPastingComparator input.toTower.toTransportData 1
      (squarePresentation.threeLeft ()) = 1 :=
  GroupExtension.authored_pasting_one squarePresentation π kernel_comm core lifts projects relations _

/-- G-129 completion criterion 3: A4 evaluation: deleting the last e2 gives the identity authored comparison. -/
theorem last_pasting_value :
    TransportCoherence.Arbitrary.authoredPastingComparator input.toTower.toTransportData 1
      (squarePresentation.threeRight ()) = 1 :=
  GroupExtension.authored_pasting_one squarePresentation π kernel_comm core lifts projects relations _


/-- G-129 completion criterion 3: The full original sign codomain is cyclic two. -/
noncomputable def visibleC2 : Multiplicative (ZMod 2) ≃* H := by
  have hcard : Nat.card H = 2 := by rw [Nat.card_eq_fintype_card, Fintype.card_units_int]
  rw [← hcard]
  exact zmodCyclicMulEquiv (isCyclic_of_prime_card hcard)

/-- G-129 completion criterion 3: Its nonidentity coordinate is exactly the original sign value -1. -/
theorem visibleC2_generator : visibleC2 (Multiplicative.ofAdd 1) = (-1 : H) := by
  have hn : visibleC2 (Multiplicative.ofAdd 1) ≠ 1 := by
    intro h
    have hx : (Multiplicative.ofAdd 1 : Multiplicative (ZMod 2)) = 1 :=
      visibleC2.injective (h.trans (map_one visibleC2).symm)
    exact (by decide : (Multiplicative.ofAdd 1 : Multiplicative (ZMod 2)) ≠ 1) hx
  exact (Int.units_eq_one_or _).resolve_left hn

/-- G-129 completion criterion 3: The specified fixed core is nonidentity in the full original sign codomain. -/
theorem core_nonidentity : @core () () () ≠ 1 := by
  change (-1 : H) ≠ 1
  norm_num

/-- G-129 completion criterion 3: All kernel coordinates evaluate as powers of the specified original (012). -/
theorem kernelC3_inclusion (z : ZMod 3) :
    (kernelC3 (Multiplicative.ofAdd z)).1 = cycle ^ z.val := by
  fin_cases z <;> decide

/-- G-129 completion criterion 3: The same native H1 is additively equivalent to the trivial group. -/
noncomputable def h1Trivial : H1 M ≃+ PUnit where
  toFun _ := PUnit.unit
  invFun _ := 0
  left_inv x := (h1_zero x).symm
  right_inv x := by cases x; rfl
  map_add' _ _ := rfl

/-- G-129 completion criterion 3: The same native H2 is additively equivalent to the trivial group. -/
noncomputable def h2Trivial : H2 M ≃+ PUnit where
  toFun _ := PUnit.unit
  invFun _ := 0
  left_inv x := (h2_zero x).symm
  right_inv x := by cases x; rfl
  map_add' _ _ := rfl


/-- G-129 completion criterion 3: The fixed core has the same nonidentity C2 coordinate as in the square requirement. -/
theorem core_c2_coordinate : visibleC2.symm (@core () () ()) = Multiplicative.ofAdd 1 := by
  change visibleC2.symm (-1) = _
  rw [← visibleC2_generator, MulEquiv.symm_apply_apply]

end AAT.AG.AbelianLiftingObstruction.S3Witness
#assert_standard_axioms_only AAT.AG.AbelianLiftingObstruction.S3Witness
