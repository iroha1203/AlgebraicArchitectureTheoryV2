import ResearchLean.AG.QualitySurface.LawGeneratedBooleanCircleSite
import ResearchLean.AG.QualitySurface.LawGeneratedIdealPowerSequence
import Formal.Util.AssertStandardAxioms
import Mathlib.RingTheory.DualNumber

/-!
# Two law cores on one Boolean-circle ambient ring presheaf

This file fixes one finite ambient ring and one restriction operation on the
Cycle 17 Boolean-circle site.  Two law-equation cores reuse that data verbatim
and differ only in their violation witness.  The first witness is idempotent;
the second is square-zero on contexts of cardinality below three and zero on
the unique cardinality-three context.

No ideal profile, conormal conclusion, cocycle, cohomology class, or
sheafification comparison is accepted as a structure field.
-/

noncomputable section

namespace ResearchLean.AG.QualitySurface
namespace LawGeneratedBooleanCircleLawCore

open CategoryTheory
open AAT.AG
open AAT.AG.LawAlgebra
open LawGeneratedBooleanCircleSite

/-! ## One fixed ambient finite ring and restriction operation -/

abbrev AmbientField := ZMod 2
abbrev DualFactor := TrivSqZeroExt AmbientField AmbientField
abbrev AmbientRing := AmbientField × DualFactor

/-- Projection of the dual-number factor onto its constant term. -/
def killDual : DualFactor →+* DualFactor :=
  (TrivSqZeroExt.inlHom AmbientField AmbientField).comp
    (TrivSqZeroExt.fstHom AmbientField AmbientField AmbientField).toRingHom

/-- The ambient endomorphism that deletes only the square-zero coordinate. -/
def killEps : AmbientRing →+* AmbientRing :=
  RingHom.prod (RingHom.fst AmbientField DualFactor)
    (killDual.comp (RingHom.snd AmbientField DualFactor))

/-- Idempotent law generator. -/
def idempotentGenerator : AmbientRing := (1, 0)

/-- Nonzero square-zero law generator. -/
def squareZeroGenerator : AmbientRing :=
  (0, TrivSqZeroExt.inr 1)

theorem idempotentGenerator_sq : idempotentGenerator ^ 2 = idempotentGenerator := by
  ext <;> simp [pow_two, idempotentGenerator]

theorem squareZeroGenerator_sq : squareZeroGenerator ^ 2 = 0 := by
  ext <;> simp [pow_two, squareZeroGenerator]

theorem squareZeroGenerator_ne_zero : squareZeroGenerator ≠ 0 := by
  intro h
  have hsnd := congrArg (fun x : AmbientRing => x.2.snd) h
  norm_num [squareZeroGenerator] at hsnd

theorem killEps_idempotentGenerator :
    killEps idempotentGenerator = idempotentGenerator := by
  ext <;> simp [killEps, killDual, idempotentGenerator]

theorem killEps_squareZeroGenerator : killEps squareZeroGenerator = 0 := by
  ext <;> simp [killEps, killDual, squareZeroGenerator]

theorem killEps_idempotent (x : AmbientRing) :
    killEps (killEps x) = killEps x := by
  rcases x with ⟨a, b⟩
  ext <;> simp [killEps, killDual]

/-- The unique selected context of cardinality three. -/
def Deep (W : site.category) : Prop :=
  Recognized W.ctx ∧ indexOf W.ctx = Finset.univ

theorem deep_iff_card_eq_three (W : site.category) (hW : Recognized W.ctx) :
    Deep W ↔ (indexOf W.ctx).card = 3 := by
  constructor
  · intro h
    rw [h.2]
    decide
  · intro hcard
    refine ⟨hW, ?_⟩
    apply (indexOf W.ctx).card_eq_iff_eq_univ.mp
    simpa using hcard

theorem deep_source_of_deep_target {source target : site.category}
    (f : source ⟶ target) (h : Deep target) : Deep source := by
  by_cases heq : source = target
  · simpa [heq] using h
  obtain ⟨hsource, htarget⟩ := le_recognized_of_ne (leOfHom f) (by
    intro hctx
    apply heq
    cases source
    cases target
    cases hctx
    rfl)
  refine ⟨hsource, ?_⟩
  have hsubset :=
    (le_iff_indexOf_subset hsource htarget).mp (leOfHom f)
  rw [h.2] at hsubset
  exact Finset.eq_univ_iff_forall.mpr fun x => hsubset (Finset.mem_univ x)

theorem eq_of_hom_hom {X Y : site.category}
    (f : X ⟶ Y) (g : Y ⟶ X) : X = Y := by
  have hctx : X.ctx = Y.ctx := by
    rcases (show contextLe X.ctx Y.ctx from leOfHom f) with
      h | ⟨s, t, hs, ht, hst⟩
    · exact h
    rcases (show contextLe Y.ctx X.ctx from leOfHom g) with
      h | ⟨t', s', ht', hs', hts⟩
    · exact h.symm
    have htt' : t = t' := context_injective (ht.symm.trans ht')
    have hss' : s = s' := context_injective (hs.symm.trans hs')
    subst t'
    subst s'
    exact hs.trans
      ((congrArg context (Finset.Subset.antisymm hts hst)).trans ht.symm)
  cases X
  cases Y
  cases hctx
  rfl

/--
The one ambient restriction operation.  Identity arrows restrict by identity;
a nonidentity arrow whose source is the cardinality-three context deletes the
square-zero coordinate; all other arrows restrict by identity.
-/
noncomputable def ambientRestrict {source target : site.category}
    (_f : source ⟶ target) : AmbientRing →+* AmbientRing := by
  classical
  exact if source = target then RingHom.id AmbientRing
    else if Deep source then killEps else RingHom.id AmbientRing

theorem ambientRestrict_id (W : site.category) (x : AmbientRing) :
    ambientRestrict (𝟙 W) x = x := by
  simp [ambientRestrict]

theorem ambientRestrict_of_ne_of_deep {source target : site.category}
    (f : source ⟶ target) (hne : source ≠ target) (hdeep : Deep source) :
    ambientRestrict f = killEps := by
  simp [ambientRestrict, hne, hdeep]

theorem ambientRestrict_of_not_deep {source target : site.category}
    (f : source ⟶ target) (hdeep : ¬ Deep source) :
    ambientRestrict f = RingHom.id AmbientRing := by
  by_cases heq : source = target
  · simp [ambientRestrict, heq]
  · simp [ambientRestrict, heq, hdeep]

theorem ambientRestrict_comp {W₀ W₁ W₂ : site.category}
    (f : W₀ ⟶ W₁) (g : W₁ ⟶ W₂) (x : AmbientRing) :
    ambientRestrict (f ≫ g) x = ambientRestrict f (ambientRestrict g x) := by
  classical
  by_cases h01 : W₀ = W₁
  · subst W₁
    simp [ambientRestrict]
  have h02 : W₀ ≠ W₂ := by
    intro h
    subst W₂
    exact h01 (eq_of_hom_hom f g)
  by_cases hd0 : Deep W₀
  · simp only [ambientRestrict, if_neg h02, if_pos hd0, if_neg h01]
    by_cases h12 : W₁ = W₂
    · subst W₂
      simp
    · by_cases hd1 : Deep W₁
      · simp [h12, hd1, killEps_idempotent]
      · simp [h12, hd1]
  · have hd1 : ¬ Deep W₁ := fun h => hd0 (deep_source_of_deep_target f h)
    simp [ambientRestrict, h01, h02, hd0, hd1]

/-! ## Two equation systems sharing the ambient presheaf verbatim -/

/-- A generator restricted into the cardinality-three context. -/
def generatorWitness (g : AmbientRing) (W : site.category) : AmbientRing := by
  classical
  exact if Deep W then killEps g else g

/-- The square-zero witness is nonzero below cardinality three and zero at cardinality three. -/
def squareZeroWitness (W : site.category) : AmbientRing :=
  generatorWitness squareZeroGenerator W

theorem generatorWitness_idempotentGenerator (W : site.category) :
    generatorWitness idempotentGenerator W = idempotentGenerator := by
  classical
  by_cases h : Deep W
  · simp [generatorWitness, h, killEps_idempotentGenerator]
  · simp [generatorWitness, h]

theorem squareZeroWitness_of_deep (W : site.category) (h : Deep W) :
    squareZeroWitness W = 0 := by
  simp [squareZeroWitness, generatorWitness, h, killEps_squareZeroGenerator]

theorem squareZeroWitness_of_not_deep (W : site.category) (h : ¬ Deep W) :
    squareZeroWitness W = squareZeroGenerator := by
  simp [squareZeroWitness, generatorWitness, h]

theorem ambientRestrict_idempotentGenerator {source target : site.category}
    (f : source ⟶ target) :
    ambientRestrict f idempotentGenerator = idempotentGenerator := by
  classical
  by_cases heq : source = target
  · simp [ambientRestrict, heq]
  by_cases hs : Deep source
  · simp [ambientRestrict, heq, hs, killEps_idempotentGenerator]
  · simp [ambientRestrict, heq, hs]

theorem ambientRestrict_squareZeroWitness {source target : site.category}
    (f : source ⟶ target) :
    ambientRestrict f (squareZeroWitness target) = squareZeroWitness source := by
  classical
  by_cases heq : source = target
  · subst target
    simp [ambientRestrict]
  by_cases hs : Deep source
  · by_cases ht : Deep target
    · simp [ambientRestrict, squareZeroWitness, generatorWitness, heq, hs, ht,
        killEps_squareZeroGenerator]
    · simp [ambientRestrict, squareZeroWitness, generatorWitness, heq, hs, ht,
        killEps_squareZeroGenerator]
  · have ht : ¬ Deep target := fun h => hs (deep_source_of_deep_target f h)
    simp [ambientRestrict, squareZeroWitness, generatorWitness, heq, hs, ht]

theorem ambientRestrict_generatorWitness (g : AmbientRing)
    {source target : site.category} (f : source ⟶ target) :
    ambientRestrict f (generatorWitness g target) = generatorWitness g source := by
  classical
  by_cases heq : source = target
  · subst target
    simp [ambientRestrict]
  by_cases hs : Deep source
  · by_cases ht : Deep target
    · simp [ambientRestrict, generatorWitness, heq, hs, ht, killEps_idempotent]
    · simp [ambientRestrict, generatorWitness, heq, hs, ht]
  · have ht : ¬ Deep target := fun h => hs (deep_source_of_deep_target f h)
    simp [ambientRestrict, generatorWitness, heq, hs, ht]

/--
The common equation-system constructor.  Its only parameter is the symbolic
violation generator; fulfillment is still evaluated by the finite NoCycle
residual.
-/
noncomputable def core (g : AmbientRing) :
    ArchitecturalEquationSystem site.contextPreorder where
  Index := site.equationSystem.Index
  role := site.equationSystem.role
  Observable _ := AmbientRing
  observableCommRing _ := inferInstance
  restrict f := ambientRestrict f
  restrict_id := ambientRestrict_id
  restrict_comp := ambientRestrict_comp
  violationCoordinate W _ _ := generatorWitness g W
  violationCoordinate_restrict f _ _ := ambientRestrict_generatorWitness g f
  equationResidual _ A _ _ :=
    (FiniteModel.noCycleResidual A : AmbientRing)
  equationResidual_restrict := by
    intro source target f A equationIndex atom
    rw [map_intCast]

/-- The idempotent law core on the fixed ambient presheaf. -/
noncomputable abbrev idempotentCore := core idempotentGenerator

/-- The square-zero law core on exactly the same fixed ambient presheaf. -/
noncomputable abbrev squareZeroCore := core squareZeroGenerator

theorem cores_same_Observable (W : site.category) :
    idempotentCore.Observable W = squareZeroCore.Observable W := rfl

theorem cores_same_restrict {source target : site.category}
    (f : source ⟶ target) :
    idempotentCore.restrict f = squareZeroCore.restrict f := rfl

theorem cores_same_observableCommRing (W : site.category) :
    idempotentCore.observableCommRing W = squareZeroCore.observableCommRing W := rfl

theorem cores_differ_only_by_generator :
    idempotentCore = core idempotentGenerator ∧
      squareZeroCore = core squareZeroGenerator := ⟨rfl, rfl⟩

/-! ## Generated ideal-power and conormal profiles -/

theorem core_required (g : AmbientRing) (equationIndex : (core g).Index) :
    (core g).Required equationIndex := by
  cases equationIndex
  rfl

private theorem range_constant_eq_singleton (x : AmbientRing) :
    Set.range (fun _ : FiniteModel.carrier.Atom => x) = {x} := by
  ext y
  constructor
  · rintro ⟨atom, rfl⟩
    rfl
  · intro hy
    rw [Set.mem_singleton_iff] at hy
    subst y
    exact ⟨FiniteModel.FiniteAtom.componentA, rfl⟩

theorem idempotent_witnessIdeal (W : site.category)
    (equationIndex : idempotentCore.Index) :
    idempotentCore.witnessIdeal W equationIndex =
      Ideal.span {idempotentGenerator} := by
  rw [ArchitecturalEquationSystem.witnessIdeal]
  change Ideal.span (Set.range (fun _ : FiniteModel.carrier.Atom =>
    generatorWitness idempotentGenerator W)) = _
  simp only [generatorWitness_idempotentGenerator]
  rw [range_constant_eq_singleton]

theorem squareZero_witnessIdeal (W : site.category)
    (equationIndex : squareZeroCore.Index) :
    squareZeroCore.witnessIdeal W equationIndex =
      Ideal.span {squareZeroWitness W} := by
  rw [ArchitecturalEquationSystem.witnessIdeal]
  change Ideal.span (Set.range (fun _ : FiniteModel.carrier.Atom =>
    squareZeroWitness W)) = _
  rw [range_constant_eq_singleton]

theorem obstructionIdeal_eq_witnessIdeal
    (G : ArchitecturalEquationSystem site.contextPreorder)
    (W : site.category) (equationIndex : G.Index)
    (hrequired : G.Required equationIndex)
    (hunique :
      ∀ other : G.Index, G.Required other → other = equationIndex) :
    G.obstructionIdeal W = G.witnessIdeal W equationIndex := by
  apply le_antisymm
  · apply
      (ObstructionIdeal.SelectedLawWitnessIdealFamily.localObstructionIdeal_le_iff
        _ _ _).mpr
    intro other hother
    change G.witnessIdeal W other ≤ G.witnessIdeal W equationIndex
    rw [hunique other hother]
  · exact G.witnessIdeal_le_obstructionIdeal W hrequired

theorem idempotent_obstructionIdeal (W : site.category) :
    idempotentCore.obstructionIdeal W = Ideal.span {idempotentGenerator} := by
  rw [obstructionIdeal_eq_witnessIdeal idempotentCore W PUnit.unit
      (core_required idempotentGenerator PUnit.unit)
      (fun other _ => by cases other; rfl),
    idempotent_witnessIdeal]

theorem squareZero_obstructionIdeal (W : site.category) :
    squareZeroCore.obstructionIdeal W = Ideal.span {squareZeroWitness W} := by
  rw [obstructionIdeal_eq_witnessIdeal squareZeroCore W PUnit.unit
      (core_required squareZeroGenerator PUnit.unit)
      (fun other _ => by cases other; rfl),
    squareZero_witnessIdeal]

theorem idempotent_obstructionIdeal_sq (W : site.category) :
    idempotentCore.obstructionIdeal W ^ 2 = idempotentCore.obstructionIdeal W := by
  rw [idempotent_obstructionIdeal, Ideal.span_singleton_pow,
    idempotentGenerator_sq]

theorem squareZero_obstructionIdeal_sq (W : site.category) :
    squareZeroCore.obstructionIdeal W ^ 2 = ⊥ := by
  rw [squareZero_obstructionIdeal, Ideal.span_singleton_pow]
  apply Ideal.span_singleton_eq_bot.mpr
  by_cases h : Deep W
  · rw [squareZeroWitness_of_deep W h]
    exact zero_pow two_ne_zero
  · rw [squareZeroWitness_of_not_deep W h]
    exact squareZeroGenerator_sq

theorem squareZero_obstructionIdeal_of_deep (W : site.category)
    (h : Deep W) : squareZeroCore.obstructionIdeal W = ⊥ := by
  rw [squareZero_obstructionIdeal]
  rw [squareZeroWitness_of_deep W h, Ideal.span_singleton_eq_bot.mpr rfl]

theorem squareZero_obstructionIdeal_of_not_deep (W : site.category)
    (h : ¬ Deep W) :
    squareZeroCore.obstructionIdeal W = Ideal.span {squareZeroGenerator} := by
  rw [squareZero_obstructionIdeal]
  rw [squareZeroWitness_of_not_deep W h]

theorem squareZero_obstructionIdeal_of_card_lt_three (W : site.category)
    (hW : Recognized W.ctx) (hcard : (indexOf W.ctx).card < 3) :
    squareZeroCore.obstructionIdeal W = Ideal.span {squareZeroGenerator} := by
  apply squareZero_obstructionIdeal_of_not_deep
  intro hdeep
  have hthree := (deep_iff_card_eq_three W hW).mp hdeep
  omega

theorem squareZero_obstructionIdeal_of_card_eq_three (W : site.category)
    (hW : Recognized W.ctx) (hcard : (indexOf W.ctx).card = 3) :
    squareZeroCore.obstructionIdeal W = ⊥ :=
  squareZero_obstructionIdeal_of_deep W
    ((deep_iff_card_eq_three W hW).mpr hcard)

theorem idempotent_conormal_eq_zero (W : site.category)
    (x : LawGeneratedIdealPowerSequence.Raw.Conormal idempotentCore W) : x = 0 := by
  obtain ⟨y, rfl⟩ :=
    (idempotentCore.obstructionIdeal W).toCotangent_surjective x
  apply (idempotentCore.obstructionIdeal W).toCotangent_eq.mpr
  change ((y : idempotentCore.Observable W) -
    (0 : idempotentCore.Observable W)) ∈ idempotentCore.obstructionIdeal W ^ 2
  rw [idempotent_obstructionIdeal_sq]
  simpa only [sub_zero] using y.property

theorem squareZero_conormal_eq_zero_of_deep (W : site.category)
    (h : Deep W)
    (x : LawGeneratedIdealPowerSequence.Raw.Conormal squareZeroCore W) : x = 0 := by
  obtain ⟨y, rfl⟩ :=
    (squareZeroCore.obstructionIdeal W).toCotangent_surjective x
  apply (squareZeroCore.obstructionIdeal W).toCotangent_eq.mpr
  change ((y : squareZeroCore.Observable W) -
    (0 : squareZeroCore.Observable W)) ∈ squareZeroCore.obstructionIdeal W ^ 2
  rw [squareZero_obstructionIdeal_sq]
  simpa [squareZero_obstructionIdeal_of_deep W h] using y.property

/-- The displayed square-zero generator as a conormal class below cardinality three. -/
def squareZeroConormalGenerator (W : site.category) (h : ¬ Deep W) :
    LawGeneratedIdealPowerSequence.Raw.Conormal squareZeroCore W :=
  (squareZeroCore.obstructionIdeal W).toCotangent
    ⟨squareZeroGenerator, by
      rw [squareZero_obstructionIdeal_of_not_deep W h]
      exact Ideal.subset_span (by simp)⟩

theorem squareZeroConormalGenerator_ne_zero (W : site.category) (h : ¬ Deep W) :
    squareZeroConormalGenerator W h ≠ 0 := by
  intro hz
  have hmem := (squareZeroCore.obstructionIdeal W).toCotangent_eq.mp hz
  change squareZeroGenerator - 0 ∈ squareZeroCore.obstructionIdeal W ^ 2 at hmem
  rw [squareZero_obstructionIdeal_sq] at hmem
  exact squareZeroGenerator_ne_zero (by simpa using hmem)

end LawGeneratedBooleanCircleLawCore
end ResearchLean.AG.QualitySurface

#assert_standard_axioms_only ResearchLean.AG.QualitySurface.LawGeneratedBooleanCircleLawCore
