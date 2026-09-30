import ResearchLean.AG.AbelianLiftingObstruction.H1Classification
import Mathlib.CategoryTheory.SingleObj

/-! # The actual single-object tower of an arbitrary group projection

G-129 D: every arrow and coefficient is induced by the given group homomorphism.
The API below preserves the elements of E, H and the actual kernel.
-/
namespace AAT.AG.AbelianLiftingObstruction.GroupExtension
open CategoryTheory TransportCoherence TransportCoherence.Arbitrary
universe u v
variable {E : Type u} {H : Type v} [Group E] [Group H]

/-- G-129 D input: the original group homomorphism acts on the same arrows. -/
abbrev projection (π : E →* H) : SingleObj E ⥤ SingleObj H := SingleObj.mapHom E H π
/-- G-129 D input: the bottom category has one object and one arrow. -/
def terminal (H : Type v) [Group H] : SingleObj H ⥤ SingleObj PUnit.{1} :=
  SingleObj.mapHom H PUnit.{1} 1

/-- G-129 D API: all composite-fiber automorphisms are the original group E.
The terminal functor imposes no extra verticality premise. -/
noncomputable def upperEquiv (π : E →* H) :
    E ≃* FiberAut (projection π ⋙ terminal H) (SingleObj.star E) where
  toFun e := ⟨((toUnits (G := E)).trans (Units.toAut E)) e, rfl⟩
  invFun a := a.1.hom
  left_inv _ := rfl
  right_inv a := by apply Subtype.ext; apply Iso.ext; rfl
  map_mul' _ _ := by apply Subtype.ext; apply Iso.ext; rfl

/-- G-129 D API: upperEquiv retains the same forward group element. -/
@[simp] theorem upperEquiv_hom (π : E →* H) (e : E) :
    FiberAut.hom (upperEquiv π e) = e := rfl

/-- G-129 D API: all core-fiber automorphisms are the original group H. -/
noncomputable def lowerEquiv : H ≃* FiberAut (terminal H) (SingleObj.star H) where
  toFun h := ⟨((toUnits (G := H)).trans (Units.toAut H)) h, rfl⟩
  invFun a := a.1.hom
  left_inv _ := rfl
  right_inv a := by apply Subtype.ext; apply Iso.ext; rfl
  map_mul' _ _ := by apply Subtype.ext; apply Iso.ext; rfl

/-- G-129 D API: the categorical projection is the given π on every E element. -/
theorem pushforward_eq (π : E →* H) (e : E) :
    fiberPushforward (projection π) (terminal H) _ (upperEquiv π e) =
      lowerEquiv (π e) := by
  apply Subtype.ext; apply Iso.ext; rfl

/-- G-129 D API: the actual categorical kernel equals π.ker, preserving inclusion.
Its membership is proved by the original π equation. -/
noncomputable def kernelEquiv (π : E →* H) :
    π.ker ≃* Kernel (projection π) (terminal H) (SingleObj.star E) where
  toFun a := ⟨upperEquiv π a.1, by
    change fiberPushforward (projection π) (terminal H) _ (upperEquiv π a.1) = 1
    rw [pushforward_eq]
    have ha : π a.1 = 1 := a.2
    rw [ha, map_one]⟩
  invFun a := ⟨a.1.1.hom, by
    have h := congrArg FiberAut.hom a.2
    exact h⟩
  left_inv _ := rfl
  right_inv a := by apply Subtype.ext; apply Subtype.ext; apply Iso.ext; rfl
  map_mul' _ _ := by apply Subtype.ext; apply Subtype.ext; apply Iso.ext; rfl

/-- G-129 D API: the kernel comparison keeps each original included E element. -/
@[simp] theorem kernelEquiv_hom (π : E →* H) (a : π.ker) :
    FiberAut.hom (kernelInclusion _ _ _ (kernelEquiv π a)) = a.1 := rfl

/-- G-129 A1 discharge API: commutativity is exactly that of the actual π kernel. -/
theorem kernel_comm (π : E →* H) (hc : ∀ a b : π.ker, a * b = b * a)
    (a b : Kernel (projection π) (terminal H) (SingleObj.star E)) : a * b = b * a := by
  obtain ⟨a, rfl⟩ := (kernelEquiv π).surjective a
  obtain ⟨b, rfl⟩ := (kernelEquiv π).surjective b
  rw [← map_mul, hc, map_mul]

/-- G-129 A input: every original edge is identity in the same E category. -/
noncomputable def original (K : FiniteTransportPresentation) (π : E →* H) :
    LiftData K.toFiniteTransportTwoPresentation (projection π ⋙ terminal H) where
  object _ := SingleObj.star E
  edgeBase _ := 𝟙 _
  edgeLift _ := 𝟙 _
  edgeStrong _ := identityStrong _ _

/-- G-129 D API: original path arrows are identities, by the path constructors. -/
theorem original_path (K : FiniteTransportPresentation) (π : E →* H)
    {i j : K.Vertex} (w : K.Path i j) : (original K π).pathLift w = 𝟙 _ := by
  induction w with
  | nil _ => rfl
  | cons e w ih =>
    change (𝟙 (SingleObj.star E)) ≫ (original K π).pathLift w = _
    rw [ih, Category.id_comp]
    rfl

/-- G-129 A input API: the selected original group arrows remain strong, since
all group-category arrows are invertible and lie over the terminal identity. -/
theorem selectedStrong (π : E →* H) (e : E) :
    (projection π ⋙ terminal H).IsStronglyCocartesian
      (a := SingleObj.star E) (b := SingleObj.star E) (𝟙 ((projection π ⋙ terminal H).obj (SingleObj.star E)))
      (e : SingleObj.star E ⟶ SingleObj.star E) := by
  letI : (projection π ⋙ terminal H).IsHomLift
      (𝟙 ((projection π ⋙ terminal H).obj (SingleObj.star E)))
      (a := SingleObj.star E) (b := SingleObj.star E) (upperEquiv π e).1.hom :=
    Functor.IsHomLift.map (p := projection π ⋙ terminal H)
      (a := SingleObj.star E) (b := SingleObj.star E) e
  exact Functor.IsStronglyCocartesian.of_iso (projection π ⋙ terminal H)
    (𝟙 ((projection π ⋙ terminal H).obj (SingleObj.star E))) (upperEquiv π e).1

/-- G-129 A2 strong input API: the same projected E arrow is strong for q. -/
theorem selectedLowerStrong (π : E →* H) (e : E) :
    (terminal H).IsStronglyCocartesian (a := SingleObj.star H) (b := SingleObj.star H) (𝟙 ((terminal H).obj (SingleObj.star H)))
      (π e : SingleObj.star H ⟶ SingleObj.star H) := by
  letI : (terminal H).IsHomLift (𝟙 ((terminal H).obj (SingleObj.star H)))
      (a := SingleObj.star H) (b := SingleObj.star H) (lowerEquiv (π e)).1.hom :=
    Functor.IsHomLift.map (p := terminal H) (a := SingleObj.star H) (b := SingleObj.star H) (π e)
  exact Functor.IsStronglyCocartesian.of_iso (terminal H)
    (𝟙 ((terminal H).obj (SingleObj.star H))) (lowerEquiv (π e)).1

/-- G-129 A2 discharge API: generated kernel transport is conjugation by the
same chosen E lift. The formula follows from the original factorization. -/
theorem transport_hom (π : E →* H) (e : E)
    (a : Kernel (projection π) (terminal H) (SingleObj.star E)) :
    FiberAut.hom (kernelInclusion _ _ _
      (kernelTransportHom (projection π) (terminal H) e
        (selectedStrong π e) (selectedLowerStrong π e) a)) =
      e * FiberAut.hom (kernelInclusion _ _ _ a) * e⁻¹ := by
  have hf := kernelTransportHom_fac (projection π) (terminal H) e
    (selectedStrong π e) (selectedLowerStrong π e) a
  change _ * e = e * _ at hf
  exact (eq_mul_inv_iff_mul_eq).mpr hf

/-- G-129 A2 discharge API: conjugation by an E element preserves the actual
π kernel. Its inverse is conjugation by the inverse original element. -/
def conjugation (π : E →* H) (e : E) : π.ker ≃* π.ker where
  toFun a := ⟨e * a.1 * e⁻¹, by
    change π (e * a.1 * e⁻¹) = 1
    rw [map_mul, map_mul, map_inv, a.2, mul_one, mul_inv_cancel]⟩
  invFun a := ⟨e⁻¹ * a.1 * e, by
    change π (e⁻¹ * a.1 * e) = 1
    rw [map_mul, map_mul, map_inv, a.2, mul_one, inv_mul_cancel]⟩
  left_inv a := by apply Subtype.ext; simp [mul_assoc]
  right_inv a := by apply Subtype.ext; simp [mul_assoc]
  map_mul' a b := by apply Subtype.ext; simp [mul_assoc]

/-- G-129 D transport API: same actual kernel elements and same E conjugation,
proved from the generated transport factorization rather than stored as a field. -/
theorem transport_kernelEquiv (π : E →* H) (e : E) (a : π.ker) :
    kernelTransportHom (projection π) (terminal H) e
      (selectedStrong π e) (selectedLowerStrong π e) (kernelEquiv π a) =
    kernelEquiv π (conjugation π e a) := by
  apply Subtype.ext
  apply Subtype.ext
  apply Iso.ext
  exact transport_hom π e (kernelEquiv π a)

/-- G-129 A2 discharge: bijectivity of the same generated kernel transport
follows from its comparison with an explicit conjugation equivalence. -/
theorem transport_bijective (π : E →* H) (e : E) :
    Function.Bijective (kernelTransportHom (projection π) (terminal H)
      (X := SingleObj.star E) (Y := SingleObj.star E) e
      (selectedStrong π e) (selectedLowerStrong π e)) := by
  let eqv := (kernelEquiv π).symm.trans ((conjugation π e).trans (kernelEquiv π))
  have hh : (fun a => kernelTransportHom (projection π) (terminal H) e
      (selectedStrong π e) (selectedLowerStrong π e) a) = eqv := by
    funext a
    obtain ⟨x, rfl⟩ := (kernelEquiv π).surjective a
    simpa only [MulEquiv.trans_apply, MulEquiv.symm_apply_apply] using
      transport_kernelEquiv π e x
  change Function.Bijective (fun a => kernelTransportHom (projection π) (terminal H) e
    (selectedStrong π e) (selectedLowerStrong π e) a)
  rw [hh]
  exact eqv.bijective

/-- G-129 D API: two lifts of the same visible H value have the same kernel
conjugation. This uses commutativity of the entire original π kernel. -/
theorem conjugation_independent (π : E →* H)
    (hc : ∀ a b : π.ker, a * b = b * a) (e e' : E) (hp : π e = π e') :
    conjugation π e = conjugation π e' := by
  apply MulEquiv.ext
  intro a
  apply Subtype.ext
  let k : π.ker := ⟨e'⁻¹ * e, by
    change π (e'⁻¹ * e) = 1
    rw [map_mul, map_inv, hp, inv_mul_cancel]⟩
  have hk := congrArg Subtype.val (hc k a)
  have hv := congrArg (fun x : E => e' * x * e⁻¹) hk
  change e * a.1 * e⁻¹ = e' * a.1 * e'⁻¹
  change e' * ((e'⁻¹ * e) * a.1) * e⁻¹ = e' * (a.1 * (e'⁻¹ * e)) * e⁻¹ at hv
  simpa [mul_assoc] using hv

/-- G-129 D API: conjugation of the actual kernel is an E group action. -/
def conjugationAction (π : E →* H) : E →* MulAut π.ker where
  toFun := conjugation π
  map_one' := by apply MulEquiv.ext; intro a; apply Subtype.ext; simp [conjugation]
  map_mul' e f := by
    apply MulEquiv.ext; intro a; apply Subtype.ext
    simp [conjugation, mul_assoc]

/-- G-129 D construction: surjectivity of the original π selects one E lift
for each H value; subsequent action independence removes this choice. -/
noncomputable def visibleLift (π : E →* H) (hs : Function.Surjective π) (h : H) : E :=
  Classical.choose (hs h)

/-- G-129 D API: the selected E lift projects to exactly the original H value. -/
theorem visibleLift_projects (π : E →* H) (hs : Function.Surjective π) (h : H) :
    π (visibleLift π hs h) = h := Classical.choose_spec (hs h)

/-- G-129 D construction: the H action descends from the original E conjugation,
using π surjectivity and the whole actual kernel's commutativity. -/
noncomputable def visibleAction (π : E →* H) (hs : Function.Surjective π)
    (hc : ∀ a b : π.ker, a * b = b * a) : H →* MulAut π.ker where
  toFun h := conjugation π (visibleLift π hs h)
  map_one' := by
    have hh := conjugation_independent π hc (visibleLift π hs 1) 1
      (by rw [visibleLift_projects, map_one])
    exact hh.trans (map_one (conjugationAction π))
  map_mul' h k := by
    have hh := conjugation_independent π hc (visibleLift π hs (h * k))
      (visibleLift π hs h * visibleLift π hs k)
      (by rw [visibleLift_projects, map_mul, visibleLift_projects, visibleLift_projects])
    exact hh.trans (map_mul (conjugationAction π) _ _)

/-- G-129 D action API: evaluating the descended H action at π(e) recovers
conjugation by that same original E lift, for every lift e. -/
theorem visibleAction_at_projection (π : E →* H) (hs : Function.Surjective π)
    (hc : ∀ a b : π.ker, a * b = b * a) (e : E) :
    visibleAction π hs hc (π e) = conjugation π e :=
  conjugation_independent π hc _ e (visibleLift_projects π hs _)

/-- G-129 D primitive API: evaluate the same temporal edge word in any group.
Composition y∘x is y*x, retaining all repeated and empty occurrences. -/
def pathValue {G : Type*} [Group G] (K : FiniteTransportPresentation)
    (edge : ∀ {i j : K.Vertex}, K.Edge i j → G) :
    ∀ {i j : K.Vertex}, K.Path i j → G
  | _, _, .nil _ => 1
  | _, _, .cons e w => pathValue K edge w * edge e

/-- G-129 D path API: the original homomorphism evaluates the same word. -/
theorem pathValue_map (K : FiniteTransportPresentation) (π : E →* H)
    (edge : ∀ {i j : K.Vertex}, K.Edge i j → E)
    {i j : K.Vertex} (w : K.Path i j) :
    π (pathValue K edge w) = pathValue K (fun e => π (edge e)) w := by
  induction w with
  | nil _ => exact map_one π
  | cons _ _ ih => exact (map_mul π _ _).trans (congrArg (fun x => x * _) ih)

/-- G-129 D path API: the same selected E lift evaluates the original group word.
It uses the identity original edges and retains every chosen fiber element. -/
theorem selected_path_value (K : FiniteTransportPresentation) (π : E →* H)
    (edge : ∀ {i j : K.Vertex}, K.Edge i j → E)
    {i j : K.Vertex} (w : K.Path i j) :
    (selectedUpper K (projection π) (terminal H) (original K π)
      (fun e => upperEquiv π (edge e))).pathLift w = pathValue K edge w := by
  induction w with
  | nil _ => rfl
  | cons e w ih =>
    change (edge e * 1) ≫ (selectedUpper K _ _ (original K π)
      (fun e => upperEquiv π (edge e))).pathLift w = _
    change (selectedUpper K _ _ (original K π)
      (fun e => upperEquiv π (edge e))).pathLift w * (edge e * 1) = _
    rw [ih, mul_one]
    rfl

/-- G-129 D construction: the primitive group extension input, with original
identity arrows/comparisons, fixed H edge values and chosen E lifts. All A
conditions except the whole actual kernel's abelianness are derived. -/
noncomputable abbrev input (K : FiniteTransportPresentation) (π : E →* H)
    (hc : ∀ a b : π.ker, a * b = b * a)
    (core : ∀ {i j : K.Vertex}, K.Edge i j → H)
    (reference : ∀ {i j : K.Vertex}, K.Edge i j → E)
    (projects : ∀ {i j : K.Vertex} (e : K.Edge i j), π (reference e) = core e)
    (relations : ∀ f : K.TwoCell,
      pathValue K core (K.twoLeft f) = pathValue K core (K.twoRight f)) :
    OriginalTowerPresentation K (projection π) (terminal H) where
  original := original K π
  originalLowerStrong _ := by
    change (terminal H).IsStronglyCocartesian (a := SingleObj.star H) (b := SingleObj.star H)
      (𝟙 ((terminal H).obj (SingleObj.star H))) (π 1)
    rw [map_one]
    exact identityStrong (terminal H) (SingleObj.star H)
  core e := lowerEquiv (core e)
  lift e := upperEquiv π (reference e)
  lift_core e := by
    change fiberPushforward (projection π) (terminal H) (SingleObj.star E)
      (upperEquiv π (reference e)) = lowerEquiv (core e)
    rw [pushforward_eq, projects]
  faceBase _ := by
    change (_ : PUnit.{1}) = _
    exact Subsingleton.elim _ _
  comparator _ := 1
  coreAlignment f := by
    rw [selected_path_value, selected_path_value]
    have hone : (1 : Aut (SingleObj.star E)).hom = 𝟙 (SingleObj.star E) := rfl
    simp only [FiberAut.hom, Subgroup.coe_one, hone]
    change π 1 * π (pathValue K reference (K.twoLeft f)) = π (pathValue K reference (K.twoRight f))
    rw [map_one, one_mul]
    rw [pathValue_map, pathValue_map]
    have hh : (fun {i j} (e : K.Edge i j) => π (reference e)) = @core := by
      funext i j e; exact projects e
    rw [hh]
    exact relations f
  kernelComm _ := kernel_comm π hc
  edgeBijective e := by
    simpa only [selectedUpper, Arbitrary.reselectedEdgeLift, original, upperEquiv_hom,
      SingleObj.comp_as_mul, SingleObj.id_as_one, mul_one] using transport_bijective π (reference e)
  comparatorCentralizes _ _ := by rw [one_mul, mul_one]

variable (K : FiniteTransportPresentation) (π : E →* H)
variable (hc : ∀ a b : π.ker, a * b = b * a)
variable (core : ∀ {i j : K.Vertex}, K.Edge i j → H)
variable (reference : ∀ {i j : K.Vertex}, K.Edge i j → E)
variable (projects : ∀ {i j : K.Vertex} (e : K.Edge i j), π (reference e) = core e)
variable (relations : ∀ f : K.TwoCell,
  pathValue K core (K.twoLeft f) = pathValue K core (K.twoRight f))
local notation "T" => input K π hc core reference projects relations

/-- G-129 D API: every actual fiber choice evaluates the same original E word,
without requiring that it satisfy the face relations. -/
theorem selected_choice_path
    (choice : ∀ {i j : K.Vertex}, K.Edge i j →
      FiberAut (projection π ⋙ terminal H) (SingleObj.star E))
    {i j : K.Vertex} (w : K.Path i j) :
    (selectedUpper K (projection π) (terminal H) (original K π) choice).pathLift w =
      pathValue K (fun e => FiberAut.hom (choice e)) w := by
  induction w with
  | nil _ => rfl
  | cons e w ih =>
    change (selectedUpper K _ _ (original K π) choice).pathLift w *
      (FiberAut.hom (choice e) * 1) = _
    rw [ih, mul_one]
    rfl

/-- G-129 D construction: the independently defined original E-valued lifts
of the fixed H data satisfying every original word relation. -/
structure GroupSolution (K : FiniteTransportPresentation) (π : E →* H)
    (core : ∀ {i j : K.Vertex}, K.Edge i j → H) where
  /-- Original full E values at each edge. -/
  edge : ∀ {i j : K.Vertex}, K.Edge i j → E
  /-- The fixed H value is recovered on every original edge. -/
  projects : ∀ {i j : K.Vertex} (e : K.Edge i j), π (edge e) = core e
  /-- Every original temporal word relation is preserved. -/
  face : ∀ f : K.TwoCell, pathValue K edge (K.twoLeft f) = pathValue K edge (K.twoRight f)

/-- G-129 D main correspondence: all categorical solutions are precisely all
relation-preserving E lifts of the same H edge values, keeping each E element. -/
noncomputable def solutionEquiv : Solution (T) ≃ GroupSolution K π core where
  toFun S := {
    edge e := FiberAut.hom (S.choice e)
    projects e := congrArg FiberAut.hom (S.choice_core e)
    face f := by
      have hh := S.face f
      rw [selected_choice_path, selected_choice_path] at hh
      change 1 * pathValue K (fun {i j} (e : K.Edge i j) => FiberAut.hom (S.choice (i := i) (j := j) e)) (K.twoLeft f) = _ at hh
      simpa only [one_mul] using hh }
  invFun S := {
    choice e := upperEquiv π (S.edge e)
    choice_core e := by
      change fiberPushforward (projection π) (terminal H) (SingleObj.star E)
        (upperEquiv π (S.edge e)) = lowerEquiv (core e)
      rw [pushforward_eq, S.projects]
    face f := by
      rw [selected_path_value, selected_path_value]
      change 1 * pathValue K S.edge (K.twoLeft f) = pathValue K S.edge (K.twoRight f)
      rw [one_mul]
      exact S.face f }
  left_inv S := by
    apply Solution.ext
    intro i j e
    apply Subtype.ext
    apply Iso.ext
    rfl
  right_inv S := by cases S; rfl

/-- G-129 D API: the group correspondence preserves the original E edge value. -/
theorem solutionEquiv_edge (S : Solution (T)) {i j : K.Vertex} (e : K.Edge i j) :
    (solutionEquiv K π hc core reference projects relations S).edge e =
      FiberAut.hom (S.choice e) := rfl

/-- G-129 A4 discharge API: identity original comparisons remain identity
through every oriented face, using the generated strong transport. -/
theorem authored_face_one {i j : K.Vertex} (f : WhiskeredFace K.toFiniteTransportTwoPresentation i j) :
    orientedFaceAuthoredComparator (T).toTower.toTransportData 1 f = 1 := by
  unfold Arbitrary.orientedFaceAuthoredComparator Arbitrary.orientedFaceComparator Arbitrary.authoredComparatorFamily
  change Arbitrary.whiskerFiberAut (T).toTower.upper 1
    (match f.orientation with | .forward => 1 | .backward => (1 : FiberAut _ _)⁻¹) f.outgoing = 1
  cases f.orientation <;> simp only [inv_one, whiskerFiberAut_one]

/-- G-129 A4 discharge API: every original authored pasting is identity,
including inverse faces and arbitrary prefixes/suffixes and repetitions. -/
theorem authored_pasting_one {i j : K.Vertex} {w z : K.Path i j}
    (P : RewritePasting K.toFiniteTransportTwoPresentation w z) :
    authoredPastingComparator (T).toTower.toTransportData 1 P = 1 := by
  induction P with
  | nil => rfl
  | cons step tail ih =>
    change authoredPastingComparator (T).toTower.toTransportData 1 tail *
      orientedFaceAuthoredComparator (T).toTower.toTransportData 1 step.face = 1
    rw [ih, authored_face_one, one_mul]

/-- G-129 A4 discharge: the same identity original comparison gives all
specified 3-cell equalities without assuming a coherent E lift. -/
theorem syzygy : ∀ cell : K.ThreeCell, AuthoredSyzygy (T).toTower.toTransportData 1
    (K.threeLeft cell) (K.threeRight cell) := by
  intro cell
  unfold AuthoredSyzygy
  rw [authored_pasting_one, authored_pasting_one]

/-- G-129 D main existence criterion: B3 tests precisely the original
relation-preserving E lift of these same H values, using the constructed A4. -/
theorem obstruction_zero_iff :
    (T).toTower.obstructionClass (syzygy K π hc core reference projects relations) = 0 ↔
      Nonempty (GroupSolution K π core) := by
  rw [(T).obstructionClass_eq_zero_iff_solution]
  exact (solutionEquiv K π hc core reference projects relations).nonempty_congr

/-- G-129 C/D action on the original group lifts, transported through the
proved edge-preserving full-solution equivalence. -/
noncomputable def groupAction (z : Z1 (T).toTower.localCoefficients)
    (S : GroupSolution K π core) : GroupSolution K π core :=
  solutionEquiv K π hc core reference projects relations
    ((T).solutionAction z ((solutionEquiv K π hc core reference projects relations).symm S))

/-- G-129 C/D API: the action multiplies every original E edge by exactly
its actual kernel coefficient, so the transported action has the required meaning. -/
theorem groupAction_edge (z : Z1 (T).toTower.localCoefficients)
    (S : GroupSolution K π core) {i j : K.Vertex} (e : K.Edge i j) :
    (groupAction K π hc core reference projects relations z S).edge e =
      ((kernelEquiv π).symm (Additive.toMul (z.1 ⟨i, j, e⟩))).1 * S.edge e := by
  have hh := (T).solutionAction_edge z
    ((solutionEquiv K π hc core reference projects relations).symm S) e
  exact congrArg FiberAut.hom hh

/-- G-129 C/D vertex action on all original E lifts, using the same C0 kernel
coordinates and the proved full-solution correspondence. -/
noncomputable def groupVertex (b : C0 (T).toTower.localCoefficients)
    (S : GroupSolution K π core) : GroupSolution K π core :=
  solutionEquiv K π hc core reference projects relations
    ((T).vertexGauge b ((solutionEquiv K π hc core reference projects relations).symm S))

/-- G-129 C1/D API: the same original E edge is conjugated at its two endpoints
by the whole actual π kernel; source is inverted and target is not. -/
theorem groupVertex_edge (b : C0 (T).toTower.localCoefficients)
    (S : GroupSolution K π core) {i j : K.Vertex} (e : K.Edge i j) :
    (groupVertex K π hc core reference projects relations b S).edge e =
      ((kernelEquiv π).symm (Additive.toMul (b j))).1 * S.edge e *
        (((kernelEquiv π).symm (Additive.toMul (b i))).1)⁻¹ := by
  have hh := (T).vertexGauge_edge_arrow b
    ((solutionEquiv K π hc core reference projects relations).symm S) e
  have hinv : FiberAut.hom (kernelInclusion (projection π) (terminal H) (SingleObj.star E)
      (Additive.toMul (-b i))) =
      (FiberAut.hom (kernelInclusion (projection π) (terminal H) (SingleObj.star E)
        (Additive.toMul (b i))))⁻¹ := by
    change FiberAut.hom (kernelInclusion _ _ _ ((Additive.toMul (b i))⁻¹)) = _
    rw [map_inv]
    exact map_inv (upperEquiv π).symm _
  change FiberAut.hom (((T).vertexGauge b
    ((solutionEquiv K π hc core reference projects relations).symm S)).choice e) =
    FiberAut.hom (kernelInclusion _ _ (SingleObj.star E) (Additive.toMul (b j))) *
    FiberAut.hom (((solutionEquiv K π hc core reference projects relations).symm S).choice e) *
    (FiberAut.hom (kernelInclusion _ _ (SingleObj.star E) (Additive.toMul (b i))))⁻¹
  rw [← hinv]
  simpa only [selectedUpper, Arbitrary.reselectedEdgeLift, original, SingleObj.comp_as_mul,
    SingleObj.id_as_one, mul_one, mul_assoc] using hh

/-- G-129 C/D classification API: every pair of original group lifts is joined
by exactly one first cocycle in this same local coefficient complex. -/
theorem groupAction_existsUnique (S R : GroupSolution K π core) :
    ∃! z : Z1 (T).toTower.localCoefficients,
      groupAction K π hc core reference projects relations z S = R := by
  let eqv := solutionEquiv K π hc core reference projects relations
  rcases (T).solutionAction_existsUnique (eqv.symm S) (eqv.symm R) with ⟨z, hz, hu⟩
  refine ⟨z, ?_, ?_⟩
  · change eqv ((T).solutionAction z (eqv.symm S)) = R
    rw [hz, eqv.apply_symm_apply]
  · intro w hw
    apply hu
    exact eqv.injective (hw.trans (eqv.apply_symm_apply R).symm)

/-- G-129 C/D classification API: equality in the native H1 orbit torsor is
exactly an original kernel change at vertices, transported by the full edge equivalence. -/
theorem orbit_eq_iff_groupVertex (S R : GroupSolution K π core) :
    (⟦(solutionEquiv K π hc core reference projects relations).symm S⟧ : (T).SolutionOrbit) =
      ⟦(solutionEquiv K π hc core reference projects relations).symm R⟧ ↔
    ∃ b : C0 (T).toTower.localCoefficients,
      groupVertex K π hc core reference projects relations b R = S := by
  rw [(T).solutionOrbit_mk_eq_iff]
  apply exists_congr
  intro b
  exact ((solutionEquiv K π hc core reference projects relations).apply_eq_iff_eq_symm_apply).symm

/-- G-129 C/D native torsor: when original E lifts exist, all of them form
an AddTorsor under the same first cocycles. Action values are groupAction_edge. -/
noncomputable def groupAddTorsor [Nonempty (GroupSolution K π core)] :
    AddTorsor (Z1 (T).toTower.localCoefficients) (GroupSolution K π core) where
  vadd := groupAction K π hc core reference projects relations
  zero_vadd S := by
    change (solutionEquiv K π hc core reference projects relations)
      ((T).solutionAction 0 ((solutionEquiv K π hc core reference projects relations).symm S)) = S
    rw [(T).solutionAction_zero, Equiv.apply_symm_apply]
  add_vadd z w S := by
    change (solutionEquiv K π hc core reference projects relations)
      ((T).solutionAction (z + w) ((solutionEquiv K π hc core reference projects relations).symm S)) = _
    rw [(T).solutionAction_add]
    change (solutionEquiv K π hc core reference projects relations)
      ((T).solutionAction z ((T).solutionAction w
        ((solutionEquiv K π hc core reference projects relations).symm S))) =
      (solutionEquiv K π hc core reference projects relations)
      ((T).solutionAction z ((solutionEquiv K π hc core reference projects relations).symm
        ((solutionEquiv K π hc core reference projects relations)
          ((T).solutionAction w ((solutionEquiv K π hc core reference projects relations).symm S)))))
    rw [Equiv.symm_apply_apply]
  nonempty := inferInstance
  vsub S R := (T).solutionDifference
    ((solutionEquiv K π hc core reference projects relations).symm S)
    ((solutionEquiv K π hc core reference projects relations).symm R)
  vsub_vadd' S R := by
    change (solutionEquiv K π hc core reference projects relations)
      ((T).solutionAction ((T).solutionDifference _ _)
        ((solutionEquiv K π hc core reference projects relations).symm R)) = S
    rw [(T).solutionDifference_action, Equiv.apply_symm_apply]
  vadd_vsub' z S := by
    change (T).solutionDifference
      ((solutionEquiv K π hc core reference projects relations).symm
        ((solutionEquiv K π hc core reference projects relations)
          ((T).solutionAction z ((solutionEquiv K π hc core reference projects relations).symm S))))
      ((solutionEquiv K π hc core reference projects relations).symm S) = z
    rw [Equiv.symm_apply_apply, (T).solutionDifference_solutionAction]

/-- G-129 C/D H1 classification: a chosen original E solution identifies the
same H1 with all vertex classes. orbit_eq_iff_groupVertex and groupVertex_edge
identify this native orbit torsor with original kernel conjugation classes. -/
noncomputable def groupOrbitEquivH1 (origin : GroupSolution K π core) :
    H1 (T).toTower.localCoefficients ≃ (T).SolutionOrbit :=
  (T).solutionOrbitEquivH1
    ((solutionEquiv K π hc core reference projects relations).symm origin)

/-- G-129 D path API: the concrete input evaluates the same reference word;
this exposes the input construction for subsequent B1 computation. -/
theorem input_path_value {i j : K.Vertex} (w : K.Path i j) :
    (T).toTower.upper.pathLift w = pathValue K reference w :=
  selected_path_value K π reference w

/-- G-129 B1/D API: the generated standard comparator is the same original
right word times inverse left word, derived from its strong factorization. -/
theorem canonical_hom (f : K.TwoCell) :
    FiberAut.hom ((T).toTower.canonicalFace f) =
      pathValue K reference (K.twoRight f) * (pathValue K reference (K.twoLeft f))⁻¹ := by
  have hh := Arbitrary.canonicalFiberComparator_fac (projection π ⋙ terminal H)
    ((T).toTower.upper.pathBase (K.twoLeft f))
    ((T).toTower.upper.pathLift (K.twoLeft f))
    ((T).toTower.upper.pathLift (K.twoRight f))
    ((T).toTower.upper.pathLift_isStronglyCocartesian (K.twoLeft f))
    (by rw [(T).toTower.faceBase f]; exact (T).toTower.upper.pathLift_isStronglyCocartesian (K.twoRight f))
  change (T).toTower.upper.pathLift (K.twoLeft f) ≫
    FiberAut.hom ((T).toTower.canonicalFace f) = (T).toTower.upper.pathLift (K.twoRight f) at hh
  rw [input_path_value, input_path_value] at hh
  change FiberAut.hom ((T).toTower.canonicalFace f) *
    pathValue K reference (K.twoLeft f) = pathValue K reference (K.twoRight f) at hh
  exact (eq_mul_inv_iff_mul_eq).mpr hh

/-- G-129 B1/D API: the actual kernel defect is exactly the original left
word times inverse right word, without defining defect from this output equation. -/
theorem defect_hom (f : K.TwoCell) :
    ((kernelEquiv π).symm ((T).toTower.faceDefect f)).1 =
      pathValue K reference (K.twoLeft f) * (pathValue K reference (K.twoRight f))⁻¹ := by
  have hi := (T).toTower.faceDefect_inclusion f
  change kernelInclusion _ _ _ ((T).toTower.faceDefect f) = 1 * ((T).toTower.canonicalFace f)⁻¹ at hi
  have hh := congrArg (upperEquiv π).symm hi
  rw [map_mul, map_inv, map_one, one_mul] at hh
  change FiberAut.hom (kernelInclusion _ _ _ ((T).toTower.faceDefect f)) =
    (FiberAut.hom ((T).toTower.canonicalFace f))⁻¹ at hh
  rw [canonical_hom] at hh
  simpa only [mul_inv_rev, inv_inv] using hh

/-- G-129 D edge API: the original identity arrow followed by its reference
lift is the same reference E element, exposing the concrete input to transport. -/
theorem input_edge_value {i j : K.Vertex} (e : K.Edge i j) :
    (T).toTower.upper.edgeLift e = reference e := by
  change reference e * 1 = reference e
  exact mul_one _

/-- G-129 A/D action API: the same generated coefficient edge map is the
H action at the fixed core value, for every original kernel coefficient. -/
theorem edge_transport (hs : Function.Surjective π)
    {i j : K.Vertex} (e : K.Edge i j) (a : π.ker) :
    (T).toTower.localCoefficients.edge e (Additive.ofMul (kernelEquiv π a)) =
      Additive.ofMul (kernelEquiv π (visibleAction π hs hc (core e) a)) := by
  have hv := visibleAction_at_projection π hs hc (reference e)
  rw [projects] at hv
  rw [hv]
  change Additive.ofMul (kernelTransportHom (projection π) (terminal H)
    ((T).toTower.upper.edgeLift e) ((T).toTower.upper.edgeStrong e)
    ((T).toTower.lowerStrong e) (kernelEquiv π a)) = _
  simpa only [input_edge_value] using
      congrArg Additive.ofMul (transport_kernelEquiv π (reference e) a)

/-- G-129 A1/D coefficient API: additivization keeps the whole original π
kernel at each vertex, with inverse maps and unchanged original E values. -/
noncomputable def coefficientEquiv (v : K.Vertex) :
    (T).toTower.localCoefficients.A v ≃+ Additive π.ker :=
  (kernelEquiv π).symm.toAdditive

/-- G-129 B1/D coefficient API: the additive defect recovers the original
kernel group word under the same coefficient equivalence. -/
theorem coefficientEquiv_defect (f : K.TwoCell) :
    (Additive.toMul (coefficientEquiv K π hc core reference projects relations
      (K.twoTarget f) ((T).toTower.defect f))).1 =
    pathValue K reference (K.twoLeft f) * (pathValue K reference (K.twoRight f))⁻¹ :=
  defect_hom K π hc core reference projects relations f

end AAT.AG.AbelianLiftingObstruction.GroupExtension
#assert_standard_axioms_only AAT.AG.AbelianLiftingObstruction.GroupExtension
