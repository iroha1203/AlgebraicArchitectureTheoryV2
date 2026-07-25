import Formal.AG.SemanticRepair.Saga.KappaComparison
import Formal.AG.Examples.FiniteModel
import Formal.Util.AssertStandardAxioms
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Fintype.Powerset

/-!
# Part X 例10.2 / 付録B.9: independently generated circle comparison witness

This file constructs the monomorphic 4-cycle circle cover of Appendix B.9 and
instantiates the `SagaEquationPacket` on it: the semantic coefficient
`M_sem(V) = ℤ[σ_V]/(2σ_V)` is generated as a presentation quotient, the
equation coefficient `Q_E(V) = ℤ/(2)` is generated as the obstruction-ideal
quotient of the equation system, and the two carriers are built by distinct
type formers (`QuotientAddGroup` of a `Finsupp` presentation vs
`Ideal.Quotient`), so `AddEquiv.refl` does not typecheck between them.  This
carrier-level non-identity of `Φ` is a meta-level design condition (type
inequality is not statable inside Lean); it is how this file receives the
#3718 negative condition (no same-carrier rename).

The local state systems realize `P_sem = P_E = F₂` with the twisted
restriction system `t = (1,0,0,0)` of B.9.4, the base context carries an
empty state (there is no global repair, consistently with `[r_sem] ≠ 0`),
and contexts outside the intersection diagram carry a singleton state.

The X.§1 empty-pullback convention ("omit empty intersections from the
diagram") is implemented non-uniformly across the three layers: coefficients
vanish off the diagram because `relSet` adds the relation `σ_V = 0` there
(semantic side) and because the observable ring is `ZMod 1 = 0` there
(equation side, via `modulus`), while states collapse to a singleton; B.9.2's
uniform relation `2σ_V = 0` is kept verbatim on the diagram and base.
Exactness soundness is discharged through the Lemma 6.2A route
(`equationRelationSound` from `β` and the atlases); the direct B.9.3
computation `χ(2σ) = [2] = 0` appears as the evenness computation inside
`repairSystem.relation_sound`.  The two completeness conditions are
discharged by direct finite computation (`relationComplete` /
`generatorComplete`).

Claim boundary: this witness fires the comparison core (Theorems 6.3, 7.2,
7.4-7.6 through `sagaCentralTheorem_comparison` and the named instance
statements below); it does not construct a `TopologicalMonomorphicCover`
(`circleRequirements` is trivial) and does not fire Theorem 8.2 / Corollary
8.3 true sheaf descent, which is C5's separate surface.
-/

noncomputable section

namespace AAT.AG
namespace SemanticRepair
namespace Saga
namespace CircleWitness

open CategoryTheory
open AAT.AG

/-! ## B.9.1: the circle context lattice -/

/-- Finite Boolean-lattice indices for the four-chart circle site. -/
abbrev ContextIndex := Finset (Fin 4)

/-- A selected architecture context carrying one Boolean-lattice index. -/
def context (s : ContextIndex) : Site.ArchCtx FiniteModel.object where
  minimal := {
    Support := PUnit
    Axis := PUnit
    Observable := PUnit
    supportReads := fun _ atom =>
      FiniteModel.object.configuration.family.mem atom
    supportReads_objectFamily := fun h => h
    axisReads := fun _ => True
    observableReads := fun _ => True
  }
  Extension := ContextIndex
  extension := s

theorem context_injective : Function.Injective context := by
  intro s t h
  cases h
  rfl

/-- Recognition predicate for the selected Boolean-lattice contexts. -/
def Recognized (W : Site.ArchCtx FiniteModel.object) : Prop :=
  ∃ s, W = context s

/-- Recover the unique selected index, with the empty index off the family. -/
noncomputable def indexOf
    (W : Site.ArchCtx FiniteModel.object) : ContextIndex := by
  classical
  exact if h : Recognized W then Classical.choose h else ∅

theorem context_indexOf {W : Site.ArchCtx FiniteModel.object}
    (h : Recognized W) : W = context (indexOf W) := by
  simp only [indexOf, dif_pos h]
  exact Classical.choose_spec h

theorem recognized_context (s : ContextIndex) : Recognized (context s) :=
  ⟨s, rfl⟩

@[simp] theorem indexOf_context (s : ContextIndex) : indexOf (context s) = s := by
  apply context_injective
  exact (context_indexOf (recognized_context s)).symm

/-- Reverse inclusion on selected contexts, identity only off the family. -/
def contextLe (W V : Site.ArchCtx FiniteModel.object) : Prop :=
  W = V ∨ ∃ s t, W = context s ∧ V = context t ∧ t ⊆ s

theorem contextLe_refl (W : Site.ArchCtx FiniteModel.object) :
    contextLe W W :=
  Or.inl rfl

theorem contextLe_trans {W V X : Site.ArchCtx FiniteModel.object}
    (hWV : contextLe W V) (hVX : contextLe V X) : contextLe W X := by
  rcases hWV with rfl | ⟨s, t, rfl, ht, hts⟩
  · exact hVX
  rcases hVX with rfl | ⟨t', u, ht', rfl, hut'⟩
  · exact Or.inr ⟨s, t, rfl, ht, hts⟩
  have htt' : t = t' := context_injective (ht.symm.trans ht')
  subst t'
  exact Or.inr ⟨s, u, rfl, rfl, hut'.trans hts⟩

theorem contextLe_recognized_of_ne
    {W V : Site.ArchCtx FiniteModel.object}
    (h : contextLe W V) (hne : W ≠ V) : Recognized W ∧ Recognized V := by
  rcases h with h | ⟨s, t, hs, ht, _⟩
  · exact False.elim (hne h)
  · exact ⟨⟨s, hs⟩, ⟨t, ht⟩⟩

/-- Any context below a recognized context is recognized. -/
theorem recognized_of_le_recognized
    {W V : Site.ArchCtx FiniteModel.object}
    (h : contextLe W V) (hV : Recognized V) : Recognized W := by
  rcases h with rfl | ⟨s, t, hs, _, _⟩
  · exact hV
  · exact ⟨s, hs⟩

/-- An unrecognized source forces the relation to be an equality. -/
theorem eq_of_le_of_not_recognized
    {W V : Site.ArchCtx FiniteModel.object}
    (h : contextLe W V) (hW : ¬ Recognized W) : W = V := by
  rcases h with rfl | ⟨s, _, hs, _, _⟩
  · rfl
  · exact False.elim (hW ⟨s, hs⟩)

theorem le_iff_indexOf_subset {W V : Site.ArchCtx FiniteModel.object}
    (hW : Recognized W) (hV : Recognized V) :
    contextLe W V ↔ indexOf V ⊆ indexOf W := by
  constructor
  · intro h
    rcases h with rfl | ⟨s, t, hs, ht, hts⟩
    · exact Finset.Subset.rfl
    · have hs' : s = indexOf W :=
        context_injective (hs.symm.trans (context_indexOf hW))
      have ht' : t = indexOf V :=
        context_injective (ht.symm.trans (context_indexOf hV))
      simpa [hs', ht'] using hts
  · intro h
    exact Or.inr ⟨indexOf W, indexOf V, context_indexOf hW,
      context_indexOf hV, h⟩

/-- The readable morphism carried by a selected reverse-inclusion relation. -/
def contextMorphism (s t : ContextIndex) :
    Site.ContextMorphism (context s) (context t) where
  supportMap := id
  axisMap := id
  observableRestrict := id

theorem contextMorphism_isRestriction (s t : ContextIndex) :
    (contextMorphism s t).IsRestriction :=
  ⟨fun h => h, fun h => h, fun h => h,
    fun h => (context t).supportReads_objectFamily h⟩

theorem exists_readableMorphism
    (source target : Site.ArchCtx FiniteModel.object)
    (h : contextLe source target) :
    ∃ f : Site.ContextMorphism source target, f.IsRestriction := by
  rcases h with rfl | ⟨s, t, rfl, rfl, _⟩
  · exact ⟨Site.identityContextMorphism source,
      ⟨fun x => x, fun x => x, fun x => x,
        fun x => source.supportReads_objectFamily x⟩⟩
  · exact ⟨contextMorphism s t, contextMorphism_isRestriction s t⟩

noncomputable def readableMorphism
    (source target : Site.ArchCtx FiniteModel.object)
    (h : contextLe source target) :
    Site.ContextMorphism source target :=
  Classical.choose (exists_readableMorphism source target h)

theorem readableMorphism_isRestriction
    (source target : Site.ArchCtx FiniteModel.object)
    (h : contextLe source target) :
    (readableMorphism source target h).IsRestriction :=
  Classical.choose_spec (exists_readableMorphism source target h)

/-- The context preorder used by the circle site. -/
noncomputable def contextPreorder :
    Site.ContextPreorderCategory FiniteModel.object where
  le := contextLe
  refl := contextLe_refl
  trans := fun h h' => contextLe_trans h h'
  readableMorphism := fun h => readableMorphism _ _ h
  readableMorphism_isRestriction := fun h => readableMorphism_isRestriction _ _ h

theorem recognized_pair_of_common_base
    {base left right : Site.ArchCtx FiniteModel.object}
    (hl : contextPreorder.le left base) (hr : contextPreorder.le right base)
    (hne : left ≠ right) : Recognized left ∧ Recognized right := by
  by_cases hlb : left = base
  · subst base
    have h := contextLe_recognized_of_ne hr (Ne.symm hne)
    exact ⟨h.2, h.1⟩
  · have hleft := (contextLe_recognized_of_ne hl hlb).1
    by_cases hrb : right = base
    · subst base
      exact ⟨hleft, (contextLe_recognized_of_ne hl hlb).2⟩
    · exact ⟨hleft, (contextLe_recognized_of_ne hr hrb).1⟩

/-- Union of selected indices realizes overlap. -/
def overlapContext (_base left right : Site.ArchCtx FiniteModel.object) :
    Site.ArchCtx FiniteModel.object := by
  classical
  exact if hl : Recognized left then
    if hr : Recognized right then context (indexOf left ∪ indexOf right) else left
  else left

/-- Pullback-style overlap generated by union in the selected lattice. -/
noncomputable def contextOverlap : Site.ContextOverlapPullback contextPreorder where
  overlap := overlapContext
  overlap_le_left := by
    intro base left right hl hr
    by_cases heq : left = right
    · subst right
      by_cases hleft : Recognized left
      · rw [overlapContext, dif_pos hleft, dif_pos hleft, Finset.union_self,
          context_indexOf hleft]
        simp only [indexOf_context]
        exact Or.inl rfl
      · rw [overlapContext, dif_neg hleft]
        exact Or.inl rfl
    · obtain ⟨hleft, hright⟩ := recognized_pair_of_common_base hl hr heq
      rw [overlapContext, dif_pos hleft, dif_pos hright]
      apply (le_iff_indexOf_subset (recognized_context _) hleft).2
      simpa only [indexOf_context] using
        (Finset.subset_union_left :
          indexOf left ⊆ indexOf left ∪ indexOf right)
  overlap_le_right := by
    intro base left right hl hr
    by_cases heq : left = right
    · subst right
      by_cases hleft : Recognized left
      · rw [overlapContext, dif_pos hleft, dif_pos hleft, Finset.union_self,
          context_indexOf hleft]
        simp only [indexOf_context]
        exact Or.inl rfl
      · rw [overlapContext, dif_neg hleft]
        exact contextPreorder.refl left
    · obtain ⟨hleft, hright⟩ := recognized_pair_of_common_base hl hr heq
      rw [overlapContext, dif_pos hleft, dif_pos hright]
      apply (le_iff_indexOf_subset (recognized_context _) hright).2
      simpa only [indexOf_context] using
        (Finset.subset_union_right :
          indexOf right ⊆ indexOf left ∪ indexOf right)
  overlap_le_base := by
    intro base left right hl hr
    by_cases heq : left = right
    · subst right
      by_cases hleft : Recognized left
      · rw [overlapContext, dif_pos hleft, dif_pos hleft, Finset.union_self,
            context_indexOf hleft]
        simp only [indexOf_context]
        rw [← context_indexOf hleft]
        exact hl
      · rw [overlapContext, dif_neg hleft]
        exact hl
    · obtain ⟨hleft, hright⟩ := recognized_pair_of_common_base hl hr heq
      rw [overlapContext, dif_pos hleft, dif_pos hright]
      exact contextPreorder.trans
        ((le_iff_indexOf_subset (recognized_context _) hleft).2 (by simp)) hl
  overlap_lift := by
    intro base left right X hl hr hXl hXr
    by_cases heq : left = right
    · subst right
      by_cases hleft : Recognized left
      · rw [overlapContext, dif_pos hleft, dif_pos hleft, Finset.union_self,
          context_indexOf hleft]
        simp only [indexOf_context]
        rw [← context_indexOf hleft]
        exact hXl
      · rw [overlapContext, dif_neg hleft]
        exact hXl
    · obtain ⟨hleft, hright⟩ := recognized_pair_of_common_base hl hr heq
      have hX : Recognized X := by
        by_cases hEq : X = left
        · simpa [hEq] using hleft
        · exact (contextLe_recognized_of_ne hXl hEq).1
      rw [overlapContext, dif_pos hleft, dif_pos hright]
      apply (le_iff_indexOf_subset hX (recognized_context _)).2
      simp only [indexOf_context]
      exact Finset.union_subset
        ((le_iff_indexOf_subset hX hleft).1 hXl)
        ((le_iff_indexOf_subset hX hright).1 hXr)

/-! ## B.9.1/B.9.3: kept contexts and the circle equation system -/

/-- The nine kept intersection-diagram indices (base, charts, adjacent pairs). -/
def keptSets : Finset ContextIndex :=
  {∅, {0}, {1}, {2}, {3}, {0, 1}, {1, 2}, {2, 3}, {0, 3}}

/-- Kept sets are downward closed under inclusion. -/
theorem keptSets_downward_closed :
    ∀ s ∈ keptSets, ∀ t : ContextIndex, t ⊆ s → t ∈ keptSets := by
  decide

/-- Contexts on which the circle observable ring is `ℤ`. -/
def KeptCtx (W : Site.ArchCtx FiniteModel.object) : Prop :=
  Recognized W ∧ indexOf W ∈ keptSets

/-- The observable modulus: `0` (giving `ℤ`) on kept contexts, else `1`. -/
noncomputable def modulus
    (W : Site.ArchCtx FiniteModel.object) : ℕ := by
  classical
  exact if KeptCtx W then 0 else 1

theorem modulus_eq_zero {W : Site.ArchCtx FiniteModel.object}
    (h : KeptCtx W) : modulus W = 0 := by
  simp [modulus, h]

theorem modulus_eq_one {W : Site.ArchCtx FiniteModel.object}
    (h : ¬ KeptCtx W) : modulus W = 1 := by
  simp [modulus, h]

/-- Keptness is inherited upward along the reverse-inclusion order. -/
theorem keptCtx_of_le {W V : Site.ArchCtx FiniteModel.object}
    (hle : contextLe W V) (hW : KeptCtx W) : KeptCtx V := by
  rcases hle with rfl | ⟨s, t, hs, ht, hts⟩
  · exact hW
  · refine ⟨⟨t, ht⟩, ?_⟩
    have hsW : indexOf W = s := by rw [hs, indexOf_context]
    have htV : indexOf V = t := by rw [ht, indexOf_context]
    rw [htV]
    exact keptSets_downward_closed s (hsW ▸ hW.2) t hts

/-- The divisibility discharging restriction between context moduli. -/
theorem modulus_dvd {W V : Site.ArchCtx FiniteModel.object}
    (hle : contextLe W V) : modulus W ∣ modulus V := by
  by_cases hV : KeptCtx V
  · rw [modulus_eq_zero hV]
    exact dvd_zero _
  · have hW : ¬ KeptCtx W := fun h => hV (keptCtx_of_le hle h)
    rw [modulus_eq_one hW, modulus_eq_one hV]

/-- Ring homomorphisms out of `ZMod n` into a fixed target are unique. -/
theorem zmod_ringHom_subsingleton (n : ℕ) (R : Type) [Semiring R] :
    Subsingleton (ZMod n →+* R) :=
  ZMod.subsingleton_ringHom

/--
B.9.3: the circle equation system.  One required equation index, observable
ring `ZMod (modulus V)` (`ℤ` on the intersection diagram and base, the zero
ring elsewhere), symbolic violation coordinate `2`, and residual `1`.
-/
noncomputable def circleEquationSystem :
    ArchitecturalEquationSystem contextPreorder where
  Index := PUnit
  role _ := EquationRole.required
  Observable W := ZMod (modulus W.ctx)
  observableCommRing _ := inferInstance
  restrict {source target} f :=
    ZMod.castHom (modulus_dvd (leOfHom f)) (ZMod (modulus source.ctx))
  restrict_id W x := by
    have h := (zmod_ringHom_subsingleton (modulus W.ctx) _).elim
      (ZMod.castHom (modulus_dvd (leOfHom (𝟙 W))) (ZMod (modulus W.ctx)))
      (RingHom.id _)
    rw [h]
    rfl
  restrict_comp {W₀ W₁ W₂} f g x := by
    have h := (zmod_ringHom_subsingleton (modulus W₂.ctx) _).elim
      (ZMod.castHom (modulus_dvd (leOfHom (f ≫ g)))
        (ZMod (modulus W₀.ctx)))
      ((ZMod.castHom (modulus_dvd (leOfHom f))
        (ZMod (modulus W₀.ctx))).comp
        (ZMod.castHom (modulus_dvd (leOfHom g)) (ZMod (modulus W₁.ctx))))
    rw [h]
    rfl
  violationCoordinate _ _ _ := 2
  violationCoordinate_restrict {source target} f index atom :=
    map_ofNat (ZMod.castHom (modulus_dvd (leOfHom f))
      (ZMod (modulus source.ctx))) 2
  equationResidual _ _ _ _ := 1
  equationResidual_restrict {source target} f object index atom :=
    map_one (ZMod.castHom (modulus_dvd (leOfHom f))
      (ZMod (modulus source.ctx)))

/-! ## B.9.1: the circle AAT site and the monomorphic 4-cycle cover -/

/-- Trivial coverage requirements: the witness never consumes the topology. -/
def circleRequirements :
    Site.CoverageRequirements FiniteModel.object circleEquationSystem
      FiniteModel.signature where
  requiredSupport _ := False
  requiredEquationCoordinate _ := False
  selectedViolationWitness _ := False
  requiredAxis _ := False
  supportVisibleOn _ _ := False
  equationCoordinateVisibleOn _ _ := False
  violationWitnessVisibleOn _ _ := False
  axisReadableOn _ _ := False
  boundaryVisibleOn _ _ := True

/-- The circle AAT site with the B.9.3 equation system. -/
noncomputable def site : Site.AATSite FiniteModel.object where
  contextPreorder := contextPreorder
  equationSystem := circleEquationSystem
  signature := FiniteModel.signature
  requirements := circleRequirements
  overlap := contextOverlap

/-- The base context `W` (the empty index is the top context). -/
def base : site.category :=
  Site.ContextCategoryObject.of contextPreorder (context ∅)

/-- The four circle charts `W_i`. -/
def chartObj (i : Fin 4) : site.category :=
  Site.ContextCategoryObject.of contextPreorder (context {i})

/-- The covering morphism `W_i ⟶ W`. -/
def chartInclusion (i : Fin 4) : chartObj i ⟶ base :=
  homOfLE (Or.inr ⟨{i}, ∅, rfl, rfl, Finset.empty_subset _⟩)

/-- Overlap of two selected contexts is the selected union context. -/
theorem overlapContext_context (b : Site.ArchCtx FiniteModel.object)
    (s t : ContextIndex) :
    overlapContext b (context s) (context t) = context (s ∪ t) := by
  rw [overlapContext, dif_pos (recognized_context s),
    dif_pos (recognized_context t)]
  simp only [indexOf_context]

/-- The monomorphic ordered 4-cycle cover: adjacent pairs kept, no triples. -/
@[reducible] noncomputable def circleCover : MonomorphicOrderedCover site :=
  MonomorphicOrderedCover.ofOverlapPackage base (Fin 4) inferInstance
    chartObj chartInclusion
    (fun i => mono_of_contextHom (chartInclusion i))
    (fun i j => ({i, j} : ContextIndex) ∉ keptSets)
    (fun _ _ _ => False)

/-- The pairwise overlap context computes to the selected union context. -/
theorem circleCover_pairCtx (i j : Fin 4) :
    circleCover.pairCtx i j =
      Site.ContextCategoryObject.of contextPreorder (context ({i} ∪ {j})) := by
  show Site.ContextCategoryObject.of contextPreorder
      (overlapContext (context ∅) (context {i}) (context {j})) = _
  rw [overlapContext_context]

/-- The kept pairs of the 4-cycle are exactly the four adjacent edges. -/
theorem circleCover_keptPair_mem (p : circleCover.KeptPair) :
    ({p.fst, p.snd} : ContextIndex) ∈ keptSets := by
  by_contra h
  exact p.kept h

/-! ## B.9.2: occurrence reading on the circle site -/

theorem support_subsingleton {W : Site.ArchCtx FiniteModel.object}
    (h : Recognized W) : Subsingleton W.Support := by
  rw [context_indexOf h]
  exact ⟨fun _ _ => rfl⟩

theorem support_nonempty {W : Site.ArchCtx FiniteModel.object}
    (h : Recognized W) : Nonempty W.minimal.Support := by
  rw [context_indexOf h]
  exact ⟨PUnit.unit⟩

theorem supportReads_iff {W : Site.ArchCtx FiniteModel.object}
    (h : Recognized W) (atom : FiniteModel.carrier.Atom) :
    ∀ sup : W.minimal.Support,
      W.minimal.supportReads sup atom ↔
        FiniteModel.object.configuration.family.mem atom := by
  rw [context_indexOf h]
  exact fun _ => Iff.rfl

/-- The canonical occurrence of a family atom at a recognized context. -/
noncomputable def canonicalOccurrence (V : site.category) (h : Recognized V.ctx)
    (atom : FiniteModel.carrier.Atom)
    (hatom : FiniteModel.object.configuration.family.mem atom) :
    AtomOccurrence site V :=
  ⟨(Classical.choice (support_nonempty h), atom),
    (supportReads_iff h atom _).mpr hatom⟩

@[simp] theorem canonicalOccurrence_atom (V : site.category)
    (h : Recognized V.ctx) (atom : FiniteModel.carrier.Atom)
    (hatom : FiniteModel.object.configuration.family.mem atom) :
    (canonicalOccurrence V h atom hatom).atom = atom :=
  rfl

/-- Occurrences at a recognized context are determined by their atom. -/
theorem occurrence_ext {V : site.category} (h : Recognized V.ctx)
    {o o' : AtomOccurrence site V} (hatom : o.atom = o'.atom) : o = o' := by
  haveI := support_subsingleton h
  exact Subtype.ext (Prod.ext (Subsingleton.elim _ _) hatom)

/-- Transport of occurrences along a context equality. -/
def occCast {V V' : site.category} (h : V'.ctx = V.ctx)
    (o : AtomOccurrence site V) : AtomOccurrence site V' := by
  obtain ⟨c⟩ := V
  obtain ⟨c'⟩ := V'
  change c' = c at h
  subst h
  exact o

@[simp] theorem occCast_atom {V V' : site.category} (h : V'.ctx = V.ctx)
    (o : AtomOccurrence site V) : (occCast h o).atom = o.atom := by
  obtain ⟨c⟩ := V
  obtain ⟨c'⟩ := V'
  change c' = c at h
  subst h
  rfl

theorem occCast_self {V : site.category} (h : V.ctx = V.ctx)
    (o : AtomOccurrence site V) : occCast h o = o := by
  obtain ⟨c⟩ := V
  rfl

theorem occCast_occCast {V V' V'' : site.category}
    (h' : V''.ctx = V'.ctx) (h : V'.ctx = V.ctx) (o : AtomOccurrence site V) :
    occCast h' (occCast h o) = occCast (h'.trans h) o := by
  obtain ⟨c⟩ := V
  obtain ⟨c'⟩ := V'
  obtain ⟨c''⟩ := V''
  change c'' = c' at h'
  change c' = c at h
  subst h'
  subst h
  rfl

/-- The circle occurrence restriction: canonical on the selected family. -/
noncomputable def occRestrictFun {V' V : site.category} (f : V' ⟶ V)
    (o : AtomOccurrence site V) : AtomOccurrence site V' := by
  classical
  exact if h' : Recognized V'.ctx then
    canonicalOccurrence V' h' o.atom (AtomOccurrence.atom_objectFamily o)
  else occCast (eq_of_le_of_not_recognized (leOfHom f) h') o

theorem occRestrictFun_of_recognized {V' V : site.category} (f : V' ⟶ V)
    (o : AtomOccurrence site V) (h' : Recognized V'.ctx) :
    occRestrictFun f o =
      canonicalOccurrence V' h' o.atom (AtomOccurrence.atom_objectFamily o) := by
  rw [occRestrictFun]
  split
  · rfl
  · exact absurd h' (by assumption)

theorem occRestrictFun_of_not_recognized {V' V : site.category} (f : V' ⟶ V)
    (o : AtomOccurrence site V) (h' : ¬ Recognized V'.ctx) :
    occRestrictFun f o =
      occCast (eq_of_le_of_not_recognized (leOfHom f) h') o := by
  rw [occRestrictFun]
  split
  · exact absurd (by assumption) h'
  · rfl

@[simp] theorem occRestrictFun_atom {V' V : site.category} (f : V' ⟶ V)
    (o : AtomOccurrence site V) : (occRestrictFun f o).atom = o.atom := by
  by_cases h' : Recognized V'.ctx
  · rw [occRestrictFun_of_recognized f o h']
    rfl
  · rw [occRestrictFun_of_not_recognized f o h']
    exact occCast_atom _ o

/-- The circle atom-occurrence reading. -/
noncomputable def occurrenceReading : AtomOccurrenceReading site where
  occRestrict f o := occRestrictFun f o
  occRestrict_id V o := by
    by_cases h : Recognized V.ctx
    · rw [occRestrictFun_of_recognized _ o h]
      exact occurrence_ext h rfl
    · rw [occRestrictFun_of_not_recognized _ o h]
      exact occCast_self _ o
  occRestrict_comp {V'' V' V} f g o := by
    by_cases h'' : Recognized V''.ctx
    · rw [occRestrictFun_of_recognized (f ≫ g) o h'',
        occRestrictFun_of_recognized f _ h'']
      exact occurrence_ext h'' (by simp)
    · have hEq' : V''.ctx = V'.ctx :=
        eq_of_le_of_not_recognized (leOfHom f) h''
      have h' : ¬ Recognized V'.ctx := fun hr => h'' (hEq' ▸ hr)
      rw [occRestrictFun_of_not_recognized (f ≫ g) o h'',
        occRestrictFun_of_not_recognized f _ h'',
        occRestrictFun_of_not_recognized g o h',
        occCast_occCast]
  occRestrict_atom f o := occRestrictFun_atom f o

/-! ## B.9.2: the semantic presentation `M_sem = ℤ[σ]/(2σ)` -/

/-- One semantic atom on every selected context, none elsewhere. -/
noncomputable def semanticAtomData :
    SemanticAtomData site occurrenceReading where
  SemanticAtom V := PLift (Recognized V.ctx)
  restrictAtom {V' V} f l :=
    ⟨recognized_of_le_recognized (leOfHom f) l.down⟩
  restrictAtom_id _ _ := rfl
  restrictAtom_comp _ _ _ := rfl
  projection V l :=
    canonicalOccurrence V l.down FiniteModel.FiniteAtom.componentA
      (FiniteModel.allFamily_mem _ (by simp))
  projection_natural {V' V} f l := by
    refine occurrence_ext (recognized_of_le_recognized (leOfHom f) l.down) ?_
    show FiniteModel.FiniteAtom.componentA =
      (occurrenceReading.occRestrict f _).atom
    rw [occurrenceReading.occRestrict_atom]
    rfl
  supported _ _ := True
  supported_restrict _ _ _ := trivial

/-- The selected semantic generator `σ_V` at a recognized context. -/
def sigma (V : site.category) (h : Recognized V.ctx) :
    semanticAtomData.SupportedAtom V :=
  ⟨⟨h⟩, trivial⟩

/-- Supported atoms at one context form a subsingleton. -/
instance supportedAtom_subsingleton (V : site.category) :
    Subsingleton (semanticAtomData.SupportedAtom V) := by
  refine ⟨fun l l' => Subtype.ext ?_⟩
  obtain ⟨⟨hl⟩, _⟩ := l
  obtain ⟨⟨hl'⟩, _⟩ := l'
  rfl

/-- Coefficient evaluation of a supported word at the selected generator. -/
noncomputable def evalWord (V : site.category) (h : Recognized V.ctx) :
    semanticAtomData.SupportedWord V →+ ℤ :=
  Finsupp.applyAddHom (sigma V h)

@[simp] theorem evalWord_single (V : site.category) (h : Recognized V.ctx)
    (l : semanticAtomData.SupportedAtom V) (n : ℤ) :
    evalWord V h (Finsupp.single l n) = n := by
  rw [evalWord, Finsupp.applyAddHom_apply]
  rw [Subsingleton.elim l (sigma V h)]
  exact Finsupp.single_eq_same

/-- Any supported word is a multiple of the selected generator. -/
theorem word_eq_single (V : site.category) (h : Recognized V.ctx)
    (w : semanticAtomData.SupportedWord V) :
    w = Finsupp.single (sigma V h) (evalWord V h w) := by
  ext l
  rw [Subsingleton.elim l (sigma V h)]
  rw [Finsupp.single_eq_same]
  rfl

/-- The circle relation set: `2σ` on kept contexts, `σ` on unkept contexts. -/
def relSet (V : site.category) : Set (semanticAtomData.SupportedWord V) :=
  {w | (KeptCtx V.ctx ∧ ∃ l, w = (2 : ℤ) • Finsupp.single l 1) ∨
    (¬ KeptCtx V.ctx ∧ ∃ l, w = Finsupp.single l 1)}

/-- The circle semantic repair presentation. -/
noncomputable def presentation :
    SemanticRepairPresentation site occurrenceReading where
  atomData := semanticAtomData
  rel := relSet
  rel_restrict {V' V} f := by
    rintro w ⟨w₀, hw₀, rfl⟩
    rcases hw₀ with ⟨hkept, l, rfl⟩ | ⟨hunkept, l, rfl⟩
    · have hmap : semanticAtomData.wordRestrict f ((2 : ℤ) • Finsupp.single l 1) =
          (2 : ℤ) •
            Finsupp.single (semanticAtomData.restrictSupported f l) 1 := by
        rw [map_zsmul]
        exact congrArg _ (semanticAtomData.wordRestrict_singleWord f l)
      rw [hmap]
      by_cases hkept' : KeptCtx V'.ctx
      · exact AddSubgroup.subset_closure
          (Or.inl ⟨hkept', semanticAtomData.restrictSupported f l, rfl⟩)
      · rw [two_zsmul]
        exact add_mem
          (AddSubgroup.subset_closure
            (Or.inr ⟨hkept', semanticAtomData.restrictSupported f l, rfl⟩))
          (AddSubgroup.subset_closure
            (Or.inr ⟨hkept', semanticAtomData.restrictSupported f l, rfl⟩))
    · have hunkept' : ¬ KeptCtx V'.ctx := fun h =>
        hunkept (keptCtx_of_le (leOfHom f) h)
      rw [show semanticAtomData.wordRestrict f (Finsupp.single l 1) =
          Finsupp.single (semanticAtomData.restrictSupported f l) 1 from
        semanticAtomData.wordRestrict_singleWord f l]
      exact AddSubgroup.subset_closure
        (Or.inr ⟨hunkept', semanticAtomData.restrictSupported f l, rfl⟩)

/-! ## B.9.2/B.9.3: the two coefficient computations -/

theorem keptCtx_recognized {W : Site.ArchCtx FiniteModel.object}
    (h : KeptCtx W) : Recognized W :=
  h.1

/-- Even multiples of the generator lie in the kept relation span. -/
theorem single_mem_relSpan_of_even (V : site.category) (h : KeptCtx V.ctx)
    (n : ℤ) (hn : (2 : ℤ) ∣ n) :
    Finsupp.single (sigma V h.1) n ∈ presentation.relSpan V := by
  obtain ⟨k, rfl⟩ := hn
  have hmem : (2 : ℤ) • Finsupp.single (sigma V h.1) 1 ∈ relSet V :=
    Or.inl ⟨h, sigma V h.1, rfl⟩
  have hclosure := AddSubgroup.subset_closure hmem
  have hkey : Finsupp.single (sigma V h.1) (2 * k) =
      k • ((2 : ℤ) • Finsupp.single (sigma V h.1) 1) := by
    rw [smul_smul, Finsupp.smul_single, smul_eq_mul, mul_one, mul_comm 2 k]
  rw [hkey]
  exact zsmul_mem hclosure k

/-- The kept relation span evaluates to even integers. -/
theorem evalWord_relSpan_even (V : site.category) (h : KeptCtx V.ctx)
    {w : semanticAtomData.SupportedWord V} (hw : w ∈ presentation.relSpan V) :
    (2 : ℤ) ∣ evalWord V h.1 w := by
  refine AddSubgroup.closure_induction ?_ ?_ ?_ ?_ hw
  · rintro w₀ (⟨_, l, rfl⟩ | ⟨hunkept, _, _⟩)
    · rw [map_zsmul, Subsingleton.elim l (sigma V h.1), evalWord_single]
      exact ⟨1, by ring⟩
    · exact absurd h hunkept
  · exact ⟨0, by simp⟩
  · rintro x y _ _ ⟨a, ha⟩ ⟨b, hb⟩
    exact ⟨a + b, by rw [map_add, ha, hb]; ring⟩
  · rintro x _ ⟨a, ha⟩
    exact ⟨-a, by rw [map_neg, ha]; ring⟩

/-- `M_sem` at a kept context maps onto `ZMod 2` by generator evaluation. -/
noncomputable def mSemToZMod (V : site.category) (h : KeptCtx V.ctx) :
    presentation.MSem V →+ ZMod 2 :=
  QuotientAddGroup.lift _
    ((Int.castAddHom (ZMod 2)).comp (evalWord V h.1))
    (by
      intro w hw
      obtain ⟨k, hk⟩ := evalWord_relSpan_even V h hw
      show ((evalWord V h.1 w : ℤ) : ZMod 2) = 0
      rw [hk, Int.cast_mul,
        show ((2 : ℤ) : ZMod 2) = 0 by decide, zero_mul])

@[simp] theorem mSemToZMod_mk (V : site.category) (h : KeptCtx V.ctx)
    (w : semanticAtomData.SupportedWord V) :
    mSemToZMod V h (presentation.mSemMk V w) =
      ((evalWord V h.1 w : ℤ) : ZMod 2) :=
  rfl

theorem mSemToZMod_injective (V : site.category) (h : KeptCtx V.ctx) :
    Function.Injective (mSemToZMod V h) := by
  intro m m' hmm'
  induction m using QuotientAddGroup.induction_on with
  | H w =>
  induction m' using QuotientAddGroup.induction_on with
  | H w' =>
  have heval : (((evalWord V h.1 w - evalWord V h.1 w' : ℤ)) : ZMod 2) = 0 := by
    push_cast
    rw [sub_eq_zero]
    simpa using hmm'
  have heven : (2 : ℤ) ∣ evalWord V h.1 w - evalWord V h.1 w' :=
    (ZMod.intCast_zmod_eq_zero_iff_dvd _ 2).mp heval
  change (QuotientAddGroup.mk w :
    _ ⧸ presentation.relSpan V) = QuotientAddGroup.mk w'
  rw [QuotientAddGroup.eq]
  have hdiff : -w + w' =
      Finsupp.single (sigma V h.1) (evalWord V h.1 (-w + w')) :=
    word_eq_single V h.1 _
  rw [hdiff]
  refine single_mem_relSpan_of_even V h _ ?_
  rw [map_add, map_neg]
  omega

theorem mSemToZMod_surjective (V : site.category) (h : KeptCtx V.ctx) :
    Function.Surjective (mSemToZMod V h) := by
  intro x
  refine ⟨presentation.mSemMk V
    (Finsupp.single (sigma V h.1) (x.val : ℤ)), ?_⟩
  rw [mSemToZMod_mk, evalWord_single]
  exact ZMod.intCast_zmod_cast x

/-- `M_sem` vanishes at every unkept context. -/
theorem mSem_trivial_of_not_kept (V : site.category) (h : ¬ KeptCtx V.ctx) :
    ∀ m : presentation.MSem V, m = 0 := by
  intro m
  induction m using QuotientAddGroup.induction_on with
  | H w =>
  by_cases hrec : Recognized V.ctx
  · have hw : w = Finsupp.single (sigma V hrec) (evalWord V hrec w) :=
      word_eq_single V hrec w
    have hmem : Finsupp.single (sigma V hrec) 1 ∈ relSet V :=
      Or.inr ⟨h, sigma V hrec, rfl⟩
    have hsm : w ∈ presentation.relSpan V := by
      rw [hw]
      have : Finsupp.single (sigma V hrec) (evalWord V hrec w) =
          (evalWord V hrec w) • Finsupp.single (sigma V hrec) 1 := by
        rw [Finsupp.smul_single, smul_eq_mul, mul_one]
      rw [this]
      exact zsmul_mem (AddSubgroup.subset_closure hmem) _
    exact (QuotientAddGroup.eq_zero_iff w).mpr hsm
  · have hw : w = 0 := by
      ext l
      exact absurd l.1.down hrec
    rw [hw]
    rfl

/-! ## B.9.3: the equation coefficient computation -/

theorem two_dvd_modulus {W : Site.ArchCtx FiniteModel.object}
    (h : KeptCtx W) : (2 : ℕ) ∣ modulus W := by
  rw [modulus_eq_zero h]
  exact dvd_zero _

/-- The circle obstruction ideal is the span of the coordinate `2`. -/
theorem obstructionIdeal_eq_span_two (W : site.category) :
    circleEquationSystem.obstructionIdeal W =
      Ideal.span {(2 : ZMod (modulus W.ctx))} := by
  rw [ArchitecturalEquationSystem.obstructionIdeal_eq_iSup_required]
  apply le_antisymm
  · refine iSup_le fun i => ?_
    rw [show circleEquationSystem.witnessIdeal W i.1 =
      Ideal.span (Set.range
        (circleEquationSystem.violationCoordinate W i.1)) from rfl]
    apply Ideal.span_le.mpr
    rintro x ⟨atom, rfl⟩
    exact Ideal.subset_span rfl
  · apply Ideal.span_le.mpr
    rintro x rfl
    refine Ideal.mem_iSup_of_mem ⟨PUnit.unit, rfl⟩ ?_
    apply Ideal.subset_span
    exact ⟨FiniteModel.FiniteAtom.componentA, rfl⟩

/-- Kernel elements of the `ZMod` cast into `ZMod 2` are multiples of `2`. -/
theorem zmod_cast_ker_mem_span (n : ℕ) (hn : (2 : ℕ) ∣ n) (x : ZMod n)
    (hx : ZMod.castHom hn (ZMod 2) x = 0) :
    x ∈ Ideal.span {(2 : ZMod n)} := by
  rcases n with _ | k
  · have hdvd : (2 : ℤ) ∣ x := by
      rw [ZMod.castHom_apply] at hx
      have := (ZMod.intCast_zmod_eq_zero_iff_dvd x 2).mp hx
      exact_mod_cast this
    exact Ideal.mem_span_singleton.mpr hdvd
  · have hval : ((x.val : ℕ) : ZMod 2) = 0 := by
      rw [ZMod.castHom_apply, ← ZMod.natCast_val x] at hx
      exact hx
    obtain ⟨m, hm⟩ := (ZMod.natCast_eq_zero_iff _ 2).mp hval
    have hxeq : x = ((x.val : ℕ) : ZMod (k + 1)) :=
      (ZMod.natCast_rightInverse x).symm
    rw [hxeq, hm]
    push_cast
    exact Ideal.mem_span_singleton.mpr ⟨(m : ZMod (k + 1)), rfl⟩

/-- The equation quotient at a kept context maps into `ZMod 2`. -/
noncomputable def qEToZMod (W : site.category) (h : KeptCtx W.ctx) :
    circleEquationSystem.ObstructionQuotient W →+* ZMod 2 :=
  Ideal.Quotient.lift (circleEquationSystem.obstructionIdeal W)
    (ZMod.castHom (two_dvd_modulus h) (ZMod 2))
    (by
      intro x hx
      rw [obstructionIdeal_eq_span_two] at hx
      have hker : Ideal.span {(2 : ZMod (modulus W.ctx))} ≤
          RingHom.ker (ZMod.castHom (two_dvd_modulus h) (ZMod 2)) := by
        rw [Ideal.span_le]
        intro y hy
        rw [Set.mem_singleton_iff] at hy
        subst hy
        rw [SetLike.mem_coe, RingHom.mem_ker, map_ofNat]
        decide
      exact hker hx)

@[simp] theorem qEToZMod_mk (W : site.category) (h : KeptCtx W.ctx)
    (x : ZMod (modulus W.ctx)) :
    qEToZMod W h (Ideal.Quotient.mk _ x) =
      ZMod.castHom (two_dvd_modulus h) (ZMod 2) x :=
  rfl

theorem qEToZMod_injective (W : site.category) (h : KeptCtx W.ctx) :
    Function.Injective (qEToZMod W h) := by
  intro q q' hqq'
  induction q using Quotient.inductionOn with
  | h x =>
  induction q' using Quotient.inductionOn with
  | h x' =>
  change Ideal.Quotient.mk _ x = Ideal.Quotient.mk _ x'
  rw [Ideal.Quotient.eq]
  rw [obstructionIdeal_eq_span_two]
  apply zmod_cast_ker_mem_span (modulus W.ctx) (two_dvd_modulus h)
  rw [map_sub]
  rw [sub_eq_zero]
  exact hqq'

theorem qEToZMod_surjective (W : site.category) (h : KeptCtx W.ctx) :
    Function.Surjective (qEToZMod W h) := by
  intro x
  obtain ⟨y, hy⟩ := ZMod.castHom_surjective (two_dvd_modulus h) x
  exact ⟨Ideal.Quotient.mk _ y, hy⟩

/-- The equation quotient vanishes at every unkept context. -/
theorem qE_trivial_of_not_kept (W : site.category) (h : ¬ KeptCtx W.ctx) :
    ∀ q : circleEquationSystem.ObstructionQuotient W, q = 0 := by
  intro q
  induction q using Quotient.inductionOn with
  | h x =>
  have hone : (1 : ZMod (modulus W.ctx)) ∈
      circleEquationSystem.obstructionIdeal W := by
    rw [obstructionIdeal_eq_span_two]
    have hmod : modulus W.ctx = 1 := modulus_eq_one h
    have hx2 : (2 : ZMod (modulus W.ctx)) ∣ 1 := by
      rw [hmod]
      exact ⟨1, rfl⟩
    exact Ideal.mem_span_singleton.mpr (dvd_trans hx2 (dvd_refl 1))
  have := (Ideal.Quotient.eq_zero_iff_mem (I :=
    circleEquationSystem.obstructionIdeal W)).mpr
    (Ideal.mul_mem_left _ x hone)
  simpa using this

/-! ## B.9.4: the twisted local state systems `P_sem = P_E = F₂` -/

/-- Intersection-diagram contexts: kept and nonempty index. -/
def IntCtx (W : Site.ArchCtx FiniteModel.object) : Prop :=
  KeptCtx W ∧ indexOf W ≠ ∅

/-- The base context class. -/
def BaseCtx (W : Site.ArchCtx FiniteModel.object) : Prop :=
  Recognized W ∧ indexOf W = ∅

theorem intCtx_recognized {W : Site.ArchCtx FiniteModel.object}
    (h : IntCtx W) : Recognized W :=
  h.1.1

/-- State membership: full on the diagram, empty at base, singleton elsewhere. -/
def stateSpec (W : Site.ArchCtx FiniteModel.object) (x : ZMod 2) : Prop :=
  IntCtx W ∨ (¬ IntCtx W ∧ ¬ BaseCtx W ∧ x = 0)

/-- The circle local state carrier. -/
def StateCarrier (W : Site.ArchCtx FiniteModel.object) : Type :=
  {x : ZMod 2 // stateSpec W x}

/-- The base context carries no local state. -/
theorem stateCarrier_base_elim {W : Site.ArchCtx FiniteModel.object}
    (hb : BaseCtx W) (e : StateCarrier W) : False := by
  rcases e.2 with hint | ⟨_, hnb, _⟩
  · exact hint.2 hb.2
  · exact hnb hb

/-- Off the diagram and base, the state value is zero. -/
theorem stateCarrier_val_eq_zero {W : Site.ArchCtx FiniteModel.object}
    (hni : ¬ IntCtx W) (e : StateCarrier W) : e.1 = 0 := by
  rcases e.2 with hint | ⟨_, _, hz⟩
  · exact absurd hint hni
  · exact hz

instance stateCarrier_subsingleton_of_not_int
    (W : Site.ArchCtx FiniteModel.object) (hni : ¬ IntCtx W) :
    Subsingleton (StateCarrier W) := by
  refine ⟨fun e e' => Subtype.ext ?_⟩
  rw [stateCarrier_val_eq_zero hni e, stateCarrier_val_eq_zero hni e']

/-- Base contexts only lie below base contexts. -/
theorem baseCtx_of_le {W V : Site.ArchCtx FiniteModel.object}
    (hb : BaseCtx W) (hle : contextLe W V) : BaseCtx V := by
  rcases hle with rfl | ⟨s, t, hs, ht, hts⟩
  · exact hb
  · refine ⟨⟨t, ht⟩, ?_⟩
    have hsW : indexOf W = s := by rw [hs, indexOf_context]
    have hsE : s = ∅ := by rw [← hsW, hb.2]
    subst hsE
    have : t = ∅ := Finset.subset_empty.mp hts
    rw [ht, indexOf_context, this]

/-- Kept contexts above an intersection context stay in the diagram or base. -/
theorem keptCtx_of_le_int {W V : Site.ArchCtx FiniteModel.object}
    (hint : IntCtx W) (hle : contextLe W V) : KeptCtx V :=
  keptCtx_of_le hle hint.1

/-- B.9.4: the twist datum `t = (1,0,0,0)` on the edge `(0,1)`. -/
def twist (a b : ContextIndex) : ZMod 2 :=
  if a = ({0, 1} : ContextIndex) ∧ b = ({1} : ContextIndex) then 1 else 0

@[simp] theorem twist_self (a : ContextIndex) : twist a a = 0 := by
  rw [twist, if_neg]
  rintro ⟨rfl, h⟩
  exact absurd h (by decide)

/-- Twist additivity along kept chains in the diagram. -/
theorem twist_trans : ∀ a b c : ContextIndex, a ∈ keptSets → b ⊆ a →
    c ⊆ b → c ≠ ∅ → twist a c = twist a b + twist b c := by
  decide

/-- The circle state restriction with the B.9.4 twisted faces. -/
noncomputable def stateRestrict {V' V : site.category} (f : V' ⟶ V)
    (e : StateCarrier V.ctx) : StateCarrier V'.ctx := by
  classical
  exact if h' : IntCtx V'.ctx then
    ⟨e.1 + twist (indexOf V'.ctx) (indexOf V.ctx), Or.inl h'⟩
  else if hb : BaseCtx V'.ctx then
    (stateCarrier_base_elim (baseCtx_of_le hb (leOfHom f)) e).elim
  else ⟨0, Or.inr ⟨h', hb, rfl⟩⟩

theorem stateRestrict_of_int {V' V : site.category} (f : V' ⟶ V)
    (e : StateCarrier V.ctx) (h' : IntCtx V'.ctx) :
    stateRestrict f e =
      ⟨e.1 + twist (indexOf V'.ctx) (indexOf V.ctx), Or.inl h'⟩ := by
  rw [stateRestrict]
  split
  · rfl
  · exact absurd h' (by assumption)

theorem stateRestrict_val_of_int {V' V : site.category} (f : V' ⟶ V)
    (e : StateCarrier V.ctx) (h' : IntCtx V'.ctx) :
    (stateRestrict f e).1 = e.1 + twist (indexOf V'.ctx) (indexOf V.ctx) := by
  rw [stateRestrict_of_int f e h']

theorem stateRestrict_id (V : site.category) (e : StateCarrier V.ctx) :
    stateRestrict (𝟙 V) e = e := by
  by_cases h : IntCtx V.ctx
  · apply Subtype.ext
    rw [stateRestrict_val_of_int _ e h, twist_self, add_zero]
  · haveI := stateCarrier_subsingleton_of_not_int V.ctx h
    exact Subsingleton.elim _ _

theorem stateRestrict_comp {V'' V' V : site.category}
    (f : V'' ⟶ V') (g : V' ⟶ V) (e : StateCarrier V.ctx) :
    stateRestrict (f ≫ g) e = stateRestrict f (stateRestrict g e) := by
  by_cases h'' : IntCtx V''.ctx
  · have hV'kept : KeptCtx V'.ctx := keptCtx_of_le_int h'' (leOfHom f)
    have hVkept : KeptCtx V.ctx := keptCtx_of_le (leOfHom g) hV'kept
    by_cases hVbase : BaseCtx V.ctx
    · exact (stateCarrier_base_elim hVbase e).elim
    by_cases hV'base : BaseCtx V'.ctx
    · exact (stateCarrier_base_elim (baseCtx_of_le hV'base (leOfHom g))
        e).elim
    have hV'int : IntCtx V'.ctx := ⟨hV'kept, fun hE => hV'base ⟨hV'kept.1, hE⟩⟩
    have hVint : IntCtx V.ctx := ⟨hVkept, fun hE => hVbase ⟨hVkept.1, hE⟩⟩
    apply Subtype.ext
    rw [stateRestrict_val_of_int _ e h'',
      stateRestrict_val_of_int _ _ h'',
      stateRestrict_val_of_int _ e hV'int]
    have hsub' : indexOf V'.ctx ⊆ indexOf V''.ctx :=
      (le_iff_indexOf_subset (intCtx_recognized h'')
        (intCtx_recognized hV'int)).mp (leOfHom f)
    have hsub : indexOf V.ctx ⊆ indexOf V'.ctx :=
      (le_iff_indexOf_subset (intCtx_recognized hV'int)
        (intCtx_recognized hVint)).mp (leOfHom g)
    rw [twist_trans (indexOf V''.ctx) (indexOf V'.ctx) (indexOf V.ctx)
      h''.1.2 hsub' hsub hVint.2]
    ring
  · by_cases hVbase : BaseCtx V.ctx
    · exact (stateCarrier_base_elim hVbase e).elim
    by_cases hV''base : BaseCtx V''.ctx
    · have hV'base : BaseCtx V'.ctx := baseCtx_of_le hV''base (leOfHom f)
      exact (stateCarrier_base_elim (baseCtx_of_le hV'base (leOfHom g))
        e).elim
    haveI := stateCarrier_subsingleton_of_not_int V''.ctx h''
    exact Subsingleton.elim _ _

/-- The semantic action: word evaluation acts by addition on the diagram. -/
noncomputable def semAct (V : site.category)
    (w : semanticAtomData.SupportedWord V) (e : StateCarrier V.ctx) :
    StateCarrier V.ctx := by
  classical
  exact if h : IntCtx V.ctx then
    ⟨e.1 + ((evalWord V h.1.1 w : ℤ) : ZMod 2), Or.inl h⟩
  else e

theorem semAct_of_int (V : site.category)
    (w : semanticAtomData.SupportedWord V) (e : StateCarrier V.ctx)
    (h : IntCtx V.ctx) :
    semAct V w e = ⟨e.1 + ((evalWord V h.1.1 w : ℤ) : ZMod 2), Or.inl h⟩ := by
  rw [semAct]
  split
  · rfl
  · exact absurd h (by assumption)

theorem semAct_val_of_int (V : site.category)
    (w : semanticAtomData.SupportedWord V) (e : StateCarrier V.ctx)
    (h : IntCtx V.ctx) :
    (semAct V w e).1 = e.1 + ((evalWord V h.1.1 w : ℤ) : ZMod 2) := by
  rw [semAct_of_int V w e h]

theorem semAct_of_not_int (V : site.category)
    (w : semanticAtomData.SupportedWord V) (e : StateCarrier V.ctx)
    (h : ¬ IntCtx V.ctx) : semAct V w e = e := by
  rw [semAct]
  split
  · exact absurd (by assumption) h
  · rfl

/-- Word restriction sends generators to generators, coefficient-wise. -/
theorem wordRestrict_single {V' V : site.category} (f : V' ⟶ V)
    (l : semanticAtomData.SupportedAtom V) (n : ℤ) :
    semanticAtomData.wordRestrict f (Finsupp.single l n) =
      Finsupp.single (semanticAtomData.restrictSupported f l) n := by
  show Finsupp.mapDomain.addMonoidHom
    (semanticAtomData.restrictSupported f) (Finsupp.single l n) = _
  rw [Finsupp.mapDomain.addMonoidHom_apply, Finsupp.mapDomain_single]

/-- Word evaluation is preserved by word restriction. -/
theorem evalWord_wordRestrict {V' V : site.category} (f : V' ⟶ V)
    (h : Recognized V.ctx) (h' : Recognized V'.ctx)
    (w : semanticAtomData.SupportedWord V) :
    evalWord V' h' (semanticAtomData.wordRestrict f w) = evalWord V h w := by
  conv_lhs => rw [word_eq_single V h w]
  rw [wordRestrict_single, evalWord_single]

/-- Chart index sets are kept. -/
theorem singleton_mem_keptSets : ∀ i : Fin 4, ({i} : ContextIndex) ∈ keptSets := by
  decide

/-- Union of two chart singletons is the literal pair set. -/
theorem singleton_union_eq_pair : ∀ i j : Fin 4,
    ({i} ∪ {j} : ContextIndex) = {i, j} := by
  decide

/-- Every increasing triple of the 4-cycle contains an omitted pair. -/
theorem exists_omitted_pair_of_triple : ∀ i j k : Fin 4, i < j → j < k →
    (({i, j} : ContextIndex) ∉ keptSets) ∨
    (({i, k} : ContextIndex) ∉ keptSets) ∨
    (({j, k} : ContextIndex) ∉ keptSets) := by
  decide

/-- The pairwise overlap architecture context of the circle cover. -/
theorem circleCover_pairCtx_ctx (i j : Fin 4) :
    (circleCover.pairCtx i j).ctx = context ({i} ∪ {j}) :=
  congrArg Site.ContextCategoryObject.ctx (circleCover_pairCtx i j)

/-- Every intersection-diagram context of the circle cover is an `IntCtx`. -/
theorem intCtx_of_intersection (σ : IntersectionIndex circleCover) :
    IntCtx σ.ctx.ctx := by
  cases σ with
  | chart i =>
    show IntCtx (chartObj i).ctx
    refine ⟨⟨recognized_context _, ?_⟩, ?_⟩
    · rw [show (chartObj i).ctx = context {i} from rfl, indexOf_context]
      exact singleton_mem_keptSets i
    · rw [show (chartObj i).ctx = context {i} from rfl, indexOf_context]
      simp
  | pair p =>
    have hctx := circleCover_pairCtx_ctx p.fst p.snd
    show IntCtx (circleCover.pairCtx p.fst p.snd).ctx
    rw [hctx]
    refine ⟨⟨recognized_context _, ?_⟩, ?_⟩
    · rw [indexOf_context, singleton_union_eq_pair]
      exact circleCover_keptPair_mem p
    · rw [indexOf_context]
      simp
  | triple t =>
    exact absurd (by
      rcases exists_omitted_pair_of_triple t.fst t.snd t.trd t.lt₁ t.lt₂ with
        h | h | h
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr (Or.inl h))) t.kept

/-- Keptness of an intersection context, in the `KeptCtx` form. -/
theorem keptCtx_of_intersection (σ : IntersectionIndex circleCover) :
    KeptCtx σ.ctx.ctx :=
  (intCtx_of_intersection σ).1

/-- Cast of the `ZMod 2` value roundtrip. -/
theorem zmod_two_cast_val : ∀ q : ZMod 2, (((q.val : ℕ) : ℤ) : ZMod 2) = q := by
  decide

/-- B.9.4: the semantic local repair system `P_sem`. -/
noncomputable def repairSystem :
    AffineSemanticRepairSystem presentation circleCover where
  State V := StateCarrier V.ctx
  restrictState f e := stateRestrict f e
  restrictState_id := stateRestrict_id
  restrictState_comp := stateRestrict_comp
  act := semAct
  act_zero V e := by
    by_cases h : IntCtx V.ctx
    · apply Subtype.ext
      rw [semAct_val_of_int V 0 e h]
      simp
    · rw [semAct_of_not_int V 0 e h]
  act_add V x y e := by
    by_cases h : IntCtx V.ctx
    · apply Subtype.ext
      rw [semAct_val_of_int V (x + y) e h, semAct_val_of_int V x _ h,
        semAct_val_of_int V y e h, map_add]
      push_cast
      ring
    · rw [semAct_of_not_int V (x + y) e h, semAct_of_not_int V y e h,
        semAct_of_not_int V x e h]
  act_restrict {V' V} f x e := by
    by_cases h' : IntCtx V'.ctx
    · have hVkept : KeptCtx V.ctx := keptCtx_of_le_int h' (leOfHom f)
      by_cases hVbase : BaseCtx V.ctx
      · exact ((stateCarrier_base_elim hVbase e).elim :
          stateRestrict f (semAct V x e) = _)
      have hVint : IntCtx V.ctx := ⟨hVkept, fun hE => hVbase ⟨hVkept.1, hE⟩⟩
      apply Subtype.ext
      rw [stateRestrict_val_of_int f _ h', semAct_val_of_int V x e hVint,
        semAct_val_of_int V' _ _ h', stateRestrict_val_of_int f e h',
        show evalWord V' h'.1.1 ((presentation.atomData.wordRestrict f) x) =
            evalWord V hVint.1.1 x from
          evalWord_wordRestrict f hVint.1.1 h'.1.1 x]
      ring
    · by_cases hVbase : BaseCtx V.ctx
      · exact ((stateCarrier_base_elim hVbase e).elim :
          stateRestrict f (semAct V x e) = _)
      by_cases hV'base : BaseCtx V'.ctx
      · exact ((stateCarrier_base_elim
          (baseCtx_of_le hV'base (leOfHom f)) e).elim :
          stateRestrict f (semAct V x e) = _)
      haveI := stateCarrier_subsingleton_of_not_int V'.ctx h'
      exact Subsingleton.elim _ _
  relation_sound V hV x hx e := by
    obtain ⟨σ, rfl⟩ := hV
    have hint : IntCtx σ.ctx.ctx := intCtx_of_intersection σ
    apply Subtype.ext
    rw [semAct_val_of_int _ x e hint]
    obtain ⟨k, hk⟩ := evalWord_relSpan_even σ.ctx hint.1 hx
    rw [show evalWord σ.ctx hint.1.1 x = 2 * k from hk, Int.cast_mul,
      show ((2 : ℤ) : ZMod 2) = 0 by decide, zero_mul, add_zero]
  stabilizer_complete V hV e x hx := by
    obtain ⟨σ, rfl⟩ := hV
    have hint : IntCtx σ.ctx.ctx := intCtx_of_intersection σ
    have hval := congrArg Subtype.val hx
    rw [semAct_val_of_int _ x e hint] at hval
    have hcast : ((evalWord σ.ctx hint.1.1 x : ℤ) : ZMod 2) = 0 := by
      have := add_left_cancel (a := e.1)
        (b := ((evalWord σ.ctx hint.1.1 x : ℤ) : ZMod 2)) (c := 0)
      apply this
      rw [add_zero]
      exact hval
    have heven : (2 : ℤ) ∣ evalWord σ.ctx hint.1.1 x :=
      (ZMod.intCast_zmod_eq_zero_iff_dvd _ 2).mp hcast
    rw [word_eq_single σ.ctx hint.1.1 x]
    exact single_mem_relSpan_of_even σ.ctx hint.1 _ heven
  transitive V hV e e' := by
    obtain ⟨σ, rfl⟩ := hV
    have hint : IntCtx σ.ctx.ctx := intCtx_of_intersection σ
    refine ⟨Finsupp.single (sigma σ.ctx hint.1.1)
      (((e'.1 - e.1).val : ℕ) : ℤ), ?_⟩
    apply Subtype.ext
    rw [semAct_val_of_int _ _ e hint, evalWord_single, zmod_two_cast_val]
    ring

/-! ## B.9.3/B.9.4: the equation-side lift system and both atlases -/

/-- The equation quotient restriction is compatible with the `ZMod 2` casts. -/
theorem qEToZMod_restrict {W' W : site.category} (f : W' ⟶ W)
    (h' : KeptCtx W'.ctx) (h : KeptCtx W.ctx)
    (q : circleEquationSystem.ObstructionQuotient W) :
    qEToZMod W' h' (circleEquationSystem.obstructionQuotientRestrict f q) =
      qEToZMod W h q := by
  induction q using Quotient.inductionOn with
  | h x =>
  rw [show (Quotient.mk _ x :
      circleEquationSystem.ObstructionQuotient W) =
    Ideal.Quotient.mk (circleEquationSystem.obstructionIdeal W) x from rfl]
  rw [circleEquationSystem.obstructionQuotientRestrict_mk f x,
    qEToZMod_mk, qEToZMod_mk]
  have hcomp : (ZMod.castHom (two_dvd_modulus h') (ZMod 2)).comp
      (ZMod.castHom (modulus_dvd (leOfHom f)) (ZMod (modulus W'.ctx))) =
      ZMod.castHom (two_dvd_modulus h) (ZMod 2) :=
    Subsingleton.elim _ _
  exact RingHom.congr_fun hcomp x

/-- B.9.4: the equation-side local lift system `P_E`. -/
noncomputable def liftSystem :
    AffineCoefficientLiftSystem (equationCoefficient site circleCover) where
  State V := StateCarrier V.ctx
  restrictState f e := stateRestrict f e
  restrictState_id := stateRestrict_id
  restrictState_comp := stateRestrict_comp
  act σ q e :=
    ⟨e.1 + qEToZMod σ.ctx (keptCtx_of_intersection σ) q,
      Or.inl (intCtx_of_intersection σ)⟩
  act_zero σ e := by
    apply Subtype.ext
    show e.1 + qEToZMod σ.ctx (keptCtx_of_intersection σ) 0 = e.1
    rw [map_zero, add_zero]
  act_add σ q q' e := by
    apply Subtype.ext
    show e.1 + qEToZMod σ.ctx (keptCtx_of_intersection σ) (q + q') = _
    rw [map_add]
    show _ = (e.1 + qEToZMod σ.ctx (keptCtx_of_intersection σ) q') +
      qEToZMod σ.ctx (keptCtx_of_intersection σ) q
    ring
  act_restrict {σ τ} f q e := by
    apply Subtype.ext
    rw [stateRestrict_val_of_int f.hom _ (intCtx_of_intersection σ)]
    show (e.1 + qEToZMod τ.ctx (keptCtx_of_intersection τ) q) + _ =
      (stateRestrict f.hom e).1 +
        qEToZMod σ.ctx (keptCtx_of_intersection σ)
          (circleEquationSystem.obstructionQuotientRestrict f.hom q)
    rw [stateRestrict_val_of_int f.hom e (intCtx_of_intersection σ),
      qEToZMod_restrict f.hom (keptCtx_of_intersection σ)
        (keptCtx_of_intersection τ) q]
    ring
  free σ e q hq := by
    have hval := congrArg Subtype.val hq
    have : qEToZMod σ.ctx (keptCtx_of_intersection σ) q = 0 := by
      have := add_left_cancel (a := e.1)
        (b := qEToZMod σ.ctx (keptCtx_of_intersection σ) q) (c := 0)
      apply this
      rw [add_zero]
      exact hval
    apply qEToZMod_injective σ.ctx (keptCtx_of_intersection σ)
    rw [this, map_zero]
  transitive σ e e' := by
    obtain ⟨q, hq⟩ := qEToZMod_surjective σ.ctx
      (keptCtx_of_intersection σ) (e'.1 - e.1)
    refine ⟨q, ?_⟩
    apply Subtype.ext
    show e'.1 = e.1 + qEToZMod σ.ctx (keptCtx_of_intersection σ) q
    rw [hq]
    ring

/-- All-zero semantic local repair atlas (`p_i = 0`). -/
noncomputable def repairAtlas : SemanticRepairAtlas repairSystem where
  localRepair i :=
    ⟨0, Or.inl (intCtx_of_intersection (.chart i))⟩

/-- All-zero equation local lift atlas (`e_i = 0`). -/
noncomputable def liftAtlas : CoefficientLiftAtlas liftSystem where
  localLift i :=
    ⟨0, Or.inl (intCtx_of_intersection (.chart i))⟩

/-- B.9.3: the constant equation semantic realization. -/
noncomputable def realization :
    EquationSemanticRealization presentation circleCover where
  lawIndex _ _ := PUnit.unit
  lawIndex_required _ _ := rfl
  lawIndex_natural _ _ := rfl
  archReading _ _ := FiniteModel.object
  archReading_natural _ _ := rfl

/-- B.9.4: the identity-carrier primary state correspondence `β`. -/
noncomputable def stateCorrespondence :
    PrimaryStateCorrespondence realization.chiE repairSystem liftSystem where
  beta _ p := p
  beta_natural _ _ := rfl
  beta_equivariant σ l p := by
    apply Subtype.ext
    rw [show (repairSystem.act σ.ctx (Finsupp.single l 1) p).1 =
        p.1 + ((evalWord σ.ctx (intCtx_of_intersection σ).1.1
          (Finsupp.single l 1) : ℤ) : ZMod 2) from
      semAct_val_of_int σ.ctx _ p (intCtx_of_intersection σ)]
    rw [show evalWord σ.ctx (intCtx_of_intersection σ).1.1
        (Finsupp.single l 1) = 1 from by
      rw [@Subsingleton.elim _ (supportedAtom_subsingleton σ.ctx) l
        (sigma σ.ctx (intCtx_of_intersection σ).1.1), evalWord_single]]
    show p.1 + ((1 : ℤ) : ZMod 2) =
      p.1 + qEToZMod σ.ctx (keptCtx_of_intersection σ)
        (realization.chiE.chi σ l)
    congr 1
    rw [show realization.chiE.chi σ l =
        Ideal.Quotient.mk (circleEquationSystem.obstructionIdeal σ.ctx)
          (1 : ZMod (modulus σ.ctx.ctx)) from rfl,
      qEToZMod_mk, map_one]
    decide

/-- The B.9 empty-overlap normalization for the omitted circle overlaps. -/
theorem circle_pairCtx_not_kept {i j : Fin 4}
    (h : circleCover.omittedPair i j) :
    ¬ KeptCtx (circleCover.pairCtx i j).ctx := by
  intro hk
  rw [circleCover_pairCtx_ctx] at hk
  have hk2 := hk.2
  rw [indexOf_context, singleton_union_eq_pair] at hk2
  exact h hk2

/-- The triple overlap architecture context of the circle cover. -/
theorem circleCover_tripleCtx_ctx (i j k : Fin 4) :
    (circleCover.tripleCtx i j k).ctx = context (({i} ∪ {j}) ∪ {k}) := by
  show (overlapContext (context ∅)
    (overlapContext (context ∅) (context {i}) (context {j}))
    (context {k})) = _
  rw [overlapContext_context, overlapContext_context]

/-- Kept union-triples force all three pairs kept. -/
theorem pairs_kept_of_triple_kept : ∀ i j k : Fin 4,
    (({i} ∪ {j}) ∪ {k} : ContextIndex) ∈ keptSets →
    (({i, j} : ContextIndex) ∈ keptSets ∧
      ({i, k} : ContextIndex) ∈ keptSets ∧
      ({j, k} : ContextIndex) ∈ keptSets) := by
  decide

theorem circle_tripleCtx_not_kept {i j k : Fin 4}
    (h : circleCover.omittedTriple i j k) :
    ¬ KeptCtx (circleCover.tripleCtx i j k).ctx := by
  intro hk
  rw [circleCover_tripleCtx_ctx] at hk
  have hk2 := hk.2
  rw [indexOf_context] at hk2
  obtain ⟨hij, hik, hjk⟩ := pairs_kept_of_triple_kept i j k hk2
  rcases h with hp | hp | hp | hfalse
  · exact hp hij
  · exact hp hik
  · exact hp hjk
  · exact hfalse

/-- X.§1 入力8: the empty-overlap normalization on the omitted overlaps. -/
theorem normalization :
    EmptyOverlapNormalization presentation circleCover repairSystem
      liftSystem where
  msem_pair_trivial _ _ hom m :=
    mSem_trivial_of_not_kept _ (circle_pairCtx_not_kept hom) m
  msem_triple_trivial _ _ _ hom m :=
    mSem_trivial_of_not_kept _ (circle_tripleCtx_not_kept hom) m
  qE_pair_trivial _ _ hom q :=
    qE_trivial_of_not_kept _ (circle_pairCtx_not_kept hom) q
  qE_triple_trivial _ _ _ hom q :=
    qE_trivial_of_not_kept _ (circle_tripleCtx_not_kept hom) q
  psem_pair_subsingleton _ _ hom :=
    stateCarrier_subsingleton_of_not_int _
      (fun hint => circle_pairCtx_not_kept hom hint.1)
  psem_triple_subsingleton _ _ _ hom :=
    stateCarrier_subsingleton_of_not_int _
      (fun hint => circle_tripleCtx_not_kept hom hint.1)
  pE_pair_subsingleton _ _ hom :=
    stateCarrier_subsingleton_of_not_int _
      (fun hint => circle_pairCtx_not_kept hom hint.1)
  pE_triple_subsingleton _ _ _ hom :=
    stateCarrier_subsingleton_of_not_int _
      (fun hint => circle_tripleCtx_not_kept hom hint.1)

/-! ## 例10.2: the circle SAGA equation packet -/

/-- 例10.2: the complete SAGA input bundle on the circle. -/
noncomputable def packet : SagaEquationPacket site where
  occurrenceReading := occurrenceReading
  cover := circleCover
  presentation := presentation
  realization := realization
  repairSystem := repairSystem
  repairAtlas := repairAtlas
  liftSystem := liftSystem
  liftAtlas := liftAtlas
  stateCorrespondence := stateCorrespondence
  normalization := normalization

/-- The circle correspondence sends the generator to `[1]`. -/
theorem chiE_chi_eq (σ : IntersectionIndex circleCover)
    (l : presentation.atomData.SupportedAtom σ.ctx) :
    realization.chiE.chi σ l =
      Ideal.Quotient.mk (circleEquationSystem.obstructionIdeal σ.ctx)
        (1 : ZMod (modulus σ.ctx.ctx)) :=
  rfl

/-- The `ZMod 2` reading of the extended correspondence is word evaluation. -/
theorem qEToZMod_chiHom (σ : IntersectionIndex circleCover)
    (x : presentation.atomData.SupportedWord σ.ctx) :
    qEToZMod σ.ctx (keptCtx_of_intersection σ)
        (realization.chiE.chiHom σ x) =
      ((evalWord σ.ctx (keptCtx_of_intersection σ).1 x : ℤ) : ZMod 2) := by
  conv_lhs => rw [show x = Finsupp.single
    (sigma σ.ctx (keptCtx_of_intersection σ).1)
    (evalWord σ.ctx (keptCtx_of_intersection σ).1 x) from
    word_eq_single σ.ctx (keptCtx_of_intersection σ).1 x]
  rw [realization.chiE.chiHom_single, map_zsmul, chiE_chi_eq, qEToZMod_mk,
    map_one, zsmul_one]

/-- X.定義6.2 repair-relation completeness on the circle. -/
theorem relationComplete (σ : IntersectionIndex circleCover) :
    realization.chiE.RelationComplete σ := by
  intro x hx
  have hz : ((evalWord σ.ctx (keptCtx_of_intersection σ).1 x : ℤ) :
      ZMod 2) = 0 := by
    rw [← qEToZMod_chiHom σ x, hx, map_zero]
  have heven : (2 : ℤ) ∣ evalWord σ.ctx (keptCtx_of_intersection σ).1 x :=
    (ZMod.intCast_zmod_eq_zero_iff_dvd _ 2).mp hz
  rw [show x = Finsupp.single (sigma σ.ctx (keptCtx_of_intersection σ).1)
      (evalWord σ.ctx (keptCtx_of_intersection σ).1 x) from
    word_eq_single σ.ctx (keptCtx_of_intersection σ).1 x]
  exact single_mem_relSpan_of_even σ.ctx (keptCtx_of_intersection σ) _ heven

/-- X.定義6.2 target-generator completeness on the circle. -/
theorem generatorComplete (σ : IntersectionIndex circleCover) :
    realization.chiE.GeneratorComplete σ := by
  intro q
  induction q using Quotient.inductionOn with
  | h y =>
  obtain ⟨n, hn⟩ := ZMod.intCast_surjective y
  refine ⟨Finsupp.single (sigma σ.ctx (keptCtx_of_intersection σ).1) n, ?_⟩
  rw [realization.chiE.chiHom_single, chiE_chi_eq, ← hn]
  rw [show n • (Ideal.Quotient.mk
        (circleEquationSystem.obstructionIdeal σ.ctx))
        (1 : ZMod (modulus σ.ctx.ctx)) =
      (Ideal.Quotient.mk (circleEquationSystem.obstructionIdeal σ.ctx))
        (n • (1 : ZMod (modulus σ.ctx.ctx))) from (map_zsmul _ _ _).symm,
    zsmul_one]
  rfl

/-! ## B.9.5: the nonzero class by the edge-sum argument -/

/-- The four kept edges of the 4-cycle. -/
def edge01 : circleCover.KeptPair :=
  ⟨(0 : Fin 4), (1 : Fin 4), by decide, fun h => h (by decide)⟩
def edge12 : circleCover.KeptPair :=
  ⟨(1 : Fin 4), (2 : Fin 4), by decide, fun h => h (by decide)⟩
def edge23 : circleCover.KeptPair :=
  ⟨(2 : Fin 4), (3 : Fin 4), by decide, fun h => h (by decide)⟩
def edge03 : circleCover.KeptPair :=
  ⟨(0 : Fin 4), (3 : Fin 4), by decide, fun h => h (by decide)⟩

/-- Keptness of the pair context of a kept pair. -/
theorem pairCtx_keptCtx (p : circleCover.KeptPair) :
    KeptCtx (circleCover.pairCtx p.fst p.snd).ctx :=
  keptCtx_of_intersection (.pair p)

/-- The `ZMod 2` edge reading of a semantic degree-one cochain. -/
noncomputable def edgeRead (p : circleCover.KeptPair)
    (c : Cochain1 (presentation.mSemPresheaf.onIntersections circleCover)) :
    ZMod 2 :=
  mSemToZMod (circleCover.pairCtx p.fst p.snd) (pairCtx_keptCtx p) (c p)

/-- B.9.5: the oriented edge sum along the 4-cycle. -/
noncomputable def edgeSum :
    Cochain1 (presentation.mSemPresheaf.onIntersections circleCover) →+
      ZMod 2 :=
  AddMonoidHom.mk'
    (fun c => edgeRead edge01 c + edgeRead edge12 c + edgeRead edge23 c +
      edgeRead edge03 c)
    (by
      intro c d
      simp only [edgeRead]
      have hadd : ∀ p : circleCover.KeptPair,
          mSemToZMod (circleCover.pairCtx p.fst p.snd)
            (pairCtx_keptCtx p) ((c + d) p) =
          mSemToZMod (circleCover.pairCtx p.fst p.snd)
              (pairCtx_keptCtx p) (c p) +
            mSemToZMod (circleCover.pairCtx p.fst p.snd)
              (pairCtx_keptCtx p) (d p) := by
        intro p
        exact map_add (mSemToZMod (circleCover.pairCtx p.fst p.snd)
          (pairCtx_keptCtx p)) (c p) (d p)
      rw [hadd edge01, hadd edge12, hadd edge23, hadd edge03]
      ring)

/-- The `ZMod 2` reading commutes with semantic coefficient restriction. -/
theorem mSemToZMod_restrict {V' V : site.category} (f : V' ⟶ V)
    (h' : KeptCtx V'.ctx) (h : KeptCtx V.ctx) (m : presentation.MSem V) :
    mSemToZMod V' h' (presentation.mSemRestrict f m) = mSemToZMod V h m := by
  induction m using QuotientAddGroup.induction_on with
  | H w =>
  show mSemToZMod V' h'
      (presentation.mSemRestrict f (presentation.mSemMk V w)) =
    mSemToZMod V h (presentation.mSemMk V w)
  rw [show presentation.mSemRestrict f (presentation.mSemMk V w) =
      presentation.mSemMk V' (presentation.atomData.wordRestrict f w) from
    presentation.mSemRestrict_mk f w]
  rw [mSemToZMod_mk, mSemToZMod_mk]
  rw [show evalWord V' h'.1 ((presentation.atomData.wordRestrict f) w) =
      evalWord V h.1 w from evalWord_wordRestrict f h.1 h'.1 w]

/-- B.9.5: the edge sum kills every coboundary (`F₂` sign collapse). -/
theorem edgeSum_delta0
    (a : Cochain0 (presentation.mSemPresheaf.onIntersections circleCover)) :
    edgeSum (delta0 (presentation.mSemPresheaf.onIntersections circleCover)
      a) = 0 := by
  have hread : ∀ p : circleCover.KeptPair,
      edgeRead p (delta0
        (presentation.mSemPresheaf.onIntersections circleCover) a) =
      mSemToZMod (circleCover.chart p.snd)
          (keptCtx_of_intersection (.chart p.snd)) (a p.snd) -
        mSemToZMod (circleCover.chart p.fst)
          (keptCtx_of_intersection (.chart p.fst)) (a p.fst) := by
    intro p
    show mSemToZMod _ _
      (presentation.mSemRestrict (Face.pairRight p).hom (a p.snd) -
        presentation.mSemRestrict (Face.pairLeft p).hom (a p.fst)) = _
    rw [map_sub,
      mSemToZMod_restrict (Face.pairRight p).hom (pairCtx_keptCtx p)
        (keptCtx_of_intersection (.chart p.snd)) (a p.snd),
      mSemToZMod_restrict (Face.pairLeft p).hom (pairCtx_keptCtx p)
        (keptCtx_of_intersection (.chart p.fst)) (a p.fst)]
    rfl
  show edgeRead edge01 _ + edgeRead edge12 _ + edgeRead edge23 _ +
    edgeRead edge03 _ = 0
  rw [hread edge01, hread edge12, hread edge23, hread edge03]
  have hcycle : ∀ a b c d : ZMod 2,
      (b - a) + (c - b) + (d - c) + (d - a) = 0 := by decide
  exact hcycle
    (mSemToZMod (circleCover.chart (0 : Fin 4))
      (keptCtx_of_intersection (.chart (0 : Fin 4))) (a (0 : Fin 4)))
    (mSemToZMod (circleCover.chart (1 : Fin 4))
      (keptCtx_of_intersection (.chart (1 : Fin 4))) (a (1 : Fin 4)))
    (mSemToZMod (circleCover.chart (2 : Fin 4))
      (keptCtx_of_intersection (.chart (2 : Fin 4))) (a (2 : Fin 4)))
    (mSemToZMod (circleCover.chart (3 : Fin 4))
      (keptCtx_of_intersection (.chart (3 : Fin 4))) (a (3 : Fin 4)))

/-- The `ZMod 2` value of the lifted `M_sem` torsor action. -/
theorem mact_val (σ : IntersectionIndex circleCover)
    (m : presentation.MSem σ.ctx) (e : repairSystem.State σ.ctx) :
    (repairSystem.mact σ m e).1 =
      e.1 + mSemToZMod σ.ctx (keptCtx_of_intersection σ) m := by
  induction m using QuotientAddGroup.induction_on with
  | H w =>
  show (repairSystem.mact σ (presentation.mSemMk σ.ctx w) e).1 =
    e.1 + mSemToZMod σ.ctx (keptCtx_of_intersection σ)
      (presentation.mSemMk σ.ctx w)
  rw [show repairSystem.mact σ (presentation.mSemMk σ.ctx w) e =
      repairSystem.act σ.ctx w e from repairSystem.mact_mk σ w e]
  rw [show (repairSystem.act σ.ctx w e).1 =
      e.1 + ((evalWord σ.ctx (intCtx_of_intersection σ).1.1 w : ℤ) :
        ZMod 2) from
    semAct_val_of_int σ.ctx w e (intCtx_of_intersection σ)]
  rfl

/-- B.9.4: the `ZMod 2` edge reading of the generated semantic residual. -/
theorem edgeRead_residual (p : circleCover.KeptPair) :
    edgeRead p repairAtlas.semanticResidual =
      twist ({p.fst} ∪ {p.snd}) {p.snd} -
        twist ({p.fst} ∪ {p.snd}) {p.fst} := by
  have hact := AffineCoefficientLiftSystem.act_diffAt
    (L := repairSystem.toLiftSystem) (.pair p)
    (repairAtlas.toLiftAtlas.leftOn p) (repairAtlas.toLiftAtlas.rightOn p)
  have h1 : (repairAtlas.toLiftAtlas.rightOn p).1 =
      (repairAtlas.toLiftAtlas.leftOn p).1 +
        mSemToZMod (circleCover.pairCtx p.fst p.snd) (pairCtx_keptCtx p)
          (repairAtlas.semanticResidual p) := by
    conv_lhs => rw [← hact]
    exact mact_val (.pair p) (repairAtlas.semanticResidual p)
      (repairAtlas.toLiftAtlas.leftOn p)
  have hleft : (repairAtlas.toLiftAtlas.leftOn p).1 =
      twist ({p.fst} ∪ {p.snd}) {p.fst} := by
    show (stateRestrict (circleCover.pairFst p.fst p.snd)
        (repairAtlas.localRepair p.fst)).1 = _
    rw [stateRestrict_val_of_int _ _ (intCtx_of_intersection (.pair p))]
    show (0 : ZMod 2) +
      twist (indexOf (circleCover.pairCtx p.fst p.snd).ctx)
        (indexOf (chartObj p.fst).ctx) = _
    rw [zero_add, circleCover_pairCtx_ctx, indexOf_context,
      show (chartObj p.fst).ctx = context {p.fst} from rfl, indexOf_context]
  have hright : (repairAtlas.toLiftAtlas.rightOn p).1 =
      twist ({p.fst} ∪ {p.snd}) {p.snd} := by
    show (stateRestrict (circleCover.pairSnd p.fst p.snd)
        (repairAtlas.localRepair p.snd)).1 = _
    rw [stateRestrict_val_of_int _ _ (intCtx_of_intersection (.pair p))]
    show (0 : ZMod 2) +
      twist (indexOf (circleCover.pairCtx p.fst p.snd).ctx)
        (indexOf (chartObj p.snd).ctx) = _
    rw [zero_add, circleCover_pairCtx_ctx, indexOf_context,
      show (chartObj p.snd).ctx = context {p.snd} from rfl, indexOf_context]
  show mSemToZMod (circleCover.pairCtx p.fst p.snd) (pairCtx_keptCtx p)
    (repairAtlas.semanticResidual p) = _
  rw [show mSemToZMod (circleCover.pairCtx p.fst p.snd) (pairCtx_keptCtx p)
      (repairAtlas.semanticResidual p) =
    (repairAtlas.toLiftAtlas.rightOn p).1 -
      (repairAtlas.toLiftAtlas.leftOn p).1 from by rw [h1]; ring]
  rw [hleft, hright]

/-- B.9.5: the edge sum of the generated semantic residual is `1`. -/
theorem edgeSum_semanticResidual :
    edgeSum repairAtlas.semanticResidual = 1 := by
  show edgeRead edge01 _ + edgeRead edge12 _ + edgeRead edge23 _ +
    edgeRead edge03 _ = 1
  rw [edgeRead_residual edge01, edgeRead_residual edge12,
    edgeRead_residual edge23, edgeRead_residual edge03]
  decide

/-- B.9.5: the generated semantic residual class is nonzero. -/
theorem semanticResidualClass_ne_zero :
    ¬ (presentation.semanticComplex circleCover).H1IsZero
      repairAtlas.semanticResidualClass := by
  intro hzero
  obtain ⟨b, hb⟩ := Quotient.exact hzero
  have hcob : repairAtlas.semanticResidual =
      delta0 (presentation.mSemPresheaf.onIntersections circleCover) b := by
    have : repairAtlas.semanticResidual - 0 =
        delta0 (presentation.mSemPresheaf.onIntersections circleCover) b :=
      hb
    rwa [sub_zero] at this
  have hone := edgeSum_semanticResidual
  rw [hcob, edgeSum_delta0 b] at hone
  exact absurd hone (by decide)

/-! ## B.9.1/B.9.4: the nerve shape as named statements -/

/-- B.9.1: the 4-cycle nerve has no nondegenerate triple simplices, so
`C_sem² = C_E² = 0` (B.9.4). -/
theorem keptTriple_isEmpty : IsEmpty circleCover.KeptTriple :=
  ⟨fun t => t.kept (by
    rcases exists_omitted_pair_of_triple t.fst t.snd t.trd t.lt₁ t.lt₂ with
      h | h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr (Or.inl h)))⟩

/-- Kept pairs are determined by their chart components. -/
theorem keptPair_ext {p q : circleCover.KeptPair}
    (h1 : p.fst = q.fst) (h2 : p.snd = q.snd) : p = q := by
  cases p
  cases q
  cases h1
  cases h2
  rfl

/-- Increasing kept index pairs of the 4-cycle are the four adjacent edges. -/
theorem kept_components_eq_edges : ∀ i j : Fin 4, i < j →
    ({i, j} : ContextIndex) ∈ keptSets →
    (i, j) = ((0 : Fin 4), (1 : Fin 4)) ∨
    (i, j) = ((1 : Fin 4), (2 : Fin 4)) ∨
    (i, j) = ((2 : Fin 4), (3 : Fin 4)) ∨
    (i, j) = ((0 : Fin 4), (3 : Fin 4)) := by
  decide

/-- B.9.1: the kept pairs of the 4-cycle are exactly the four cycle edges. -/
theorem keptPair_eq_edges (p : circleCover.KeptPair) :
    p = edge01 ∨ p = edge12 ∨ p = edge23 ∨ p = edge03 := by
  have hmem : ({p.fst, p.snd} : ContextIndex) ∈ keptSets :=
    circleCover_keptPair_mem p
  rcases kept_components_eq_edges p.fst p.snd p.lt hmem with h | h | h | h
  · exact Or.inl (keptPair_ext (congrArg Prod.fst h) (congrArg Prod.snd h))
  · exact Or.inr (Or.inl
      (keptPair_ext (congrArg Prod.fst h) (congrArg Prod.snd h)))
  · exact Or.inr (Or.inr (Or.inl
      (keptPair_ext (congrArg Prod.fst h) (congrArg Prod.snd h))))
  · exact Or.inr (Or.inr (Or.inr
      (keptPair_ext (congrArg Prod.fst h) (congrArg Prod.snd h))))

/-! ## 例10.2 finale: non-identity `Φ` fires the nonzero class transfer -/

/-- 例10.2 / X.系6.7: `Φ` generated by exactness discharge.  Its two carriers
are constructed by distinct type formers (`QuotientAddGroup` of a `Finsupp`
presentation vs `Ideal.Quotient` of the obstruction ideal), so `AddEquiv.refl`
does not typecheck between them; this carrier-level distinctness is a
meta-level design condition (type inequality is not statable inside Lean),
which is how #3768 receives the #3718 negative condition. -/
noncomputable def circlePhi (σ : IntersectionIndex circleCover) :
    presentation.MSem σ.ctx ≃+
      (equationCoefficient site circleCover).carrier σ :=
  packet.phiEquiv σ (relationComplete σ) (generatorComplete σ)

/-- The audited `Φ` is the same `Φ` consumed by the transfer theorem below
(`kappaStar` reads `packet.phiFamily`); recorded to prevent silent drift. -/
theorem circlePhi_eq_phiFamily (σ : IntersectionIndex circleCover) :
    circlePhi σ = packet.phiFamily relationComplete generatorComplete σ :=
  rfl

/-- X.定理7.2 第1正方形の circle instance 発火: `κ¹ δ⁰ = δ⁰ κ⁰` for the
exactness-generated `Φ` family. -/
theorem circle_kappa_cochain_commutation
    (a : Cochain0 (presentation.mSemPresheaf.onIntersections circleCover)) :
    kappa1 (packet.phiFamily relationComplete generatorComplete)
        (delta0 (presentation.mSemPresheaf.onIntersections circleCover) a) =
      delta0 (equationCoefficient site circleCover)
        (kappa0
          (packet.phiFamily relationComplete generatorComplete) a) :=
  kappa1_delta0 _
    (fun f q =>
      packet.phiFamily_natural relationComplete generatorComplete f q) a

/-- X.定理7.4 の circle instance 発火(semantic 側): `κ_*` has a left
inverse on the circle. -/
theorem circleKappaStar_leftInverse
    (h : presentation.SemanticH1 circleCover) :
    packet.kappaStarInv relationComplete generatorComplete
      (packet.kappaStar relationComplete generatorComplete h) = h :=
  packet.kappaStar_leftInverse relationComplete generatorComplete h

/-- X.定理7.4 の circle instance 発火(equation 側): `κ_*` has a right
inverse on the circle. -/
theorem circleKappaStar_rightInverse
    (h : IncH1 (equationCoefficient site circleCover)) :
    packet.kappaStar relationComplete generatorComplete
      (packet.kappaStarInv relationComplete generatorComplete h) = h :=
  packet.kappaStar_rightInverse relationComplete generatorComplete h

/--
例10.2 / 付録B.9 / X.定理7.6: the independently generated circle comparison.
The non-identity `Φ` generated from presentation exactness transfers the
nonzero semantic residual class onto the nonzero equation residual class:
`κ_*([r_sem]) = [r_E]`, `[r_sem] ≠ 0`, and `[r_E] ≠ 0`.
-/
theorem circle_nonzero_class_transfer :
    (packet.kappaStar relationComplete generatorComplete
        packet.repairAtlas.semanticResidualClass =
      packet.liftAtlas.residualClass) ∧
    ¬ (packet.presentation.semanticComplex packet.cover).H1IsZero
        packet.repairAtlas.semanticResidualClass ∧
    ¬ (incComplex (equationCoefficient site packet.cover)).H1IsZero
        packet.liftAtlas.residualClass := by
  haveI : Fintype packet.cover.Index := (inferInstance : Fintype (Fin 4))
  obtain ⟨htransfer, hiff⟩ :=
    packet.sagaCentralTheorem_comparison relationComplete generatorComplete
  refine ⟨htransfer, semanticResidualClass_ne_zero, ?_⟩
  intro hzeroE
  exact semanticResidualClass_ne_zero (hiff.mpr hzeroE)

end CircleWitness
end Saga
end SemanticRepair
end AAT.AG

#assert_standard_axioms_only AAT.AG.SemanticRepair.Saga.CircleWitness
