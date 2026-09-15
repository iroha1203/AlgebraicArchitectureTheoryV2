import ResearchLean.AG.RealizationReconstruction.FiniteAxisFoldBottomKernelOrbit
import Formal.Util.AssertStandardAxioms

/-!
# Source-to-semantic equivalence for the displayed C2 kernel

Cycle 63 classified the actual bottom-fiber orbit of the one displayed
restriction-kernel involution.  This file constructs the corresponding
two-element subgroup already inside the source-law quotient presentation and
an explicit multiplicative equivalence to the two-element subgroup of the
actual bottom restriction kernel.

The forward map sends the source identity to identity and the source ambient
comparison generator to the same actual kernel element traced through Cycles
59--61.  The inverse reads those two cases back.  Thus both directions are
proved for every element of this displayed C2 fragment.  No claim is made
that either subgroup is the full displayed comparison group or the full
semantic restriction kernel.

## Implementation notes

Both subgroup carriers are defined by the source-generated identity/generator
dichotomy.  Closure uses the source quotient square law on the presentation
side and its transported semantic square law on the kernel side.  The
equivalence accepts neither completed automorphisms nor a bijectivity
certificate; its two inverse laws and multiplication law are proved by the
four explicit cases.
-/

namespace AAT.AG.RealizationReconstruction

open CategoryTheory AtomFoundation DoctrineFiberProduct GeometryTransport
open TransportCoherence FullGeometryNormalization

noncomputable section

set_option synthInstance.maxHeartbeats 100000
set_option maxHeartbeats 500000

/-- Decidable atom equality for the fixed finite-axis-fold input. -/
local instance finiteAxisFoldDisplayedKernelEquivAtomDecidableEq :
    DecidableEq FiniteModel.carrier.Atom := by
  change DecidableEq FiniteModel.FiniteAtom
  infer_instance

namespace FiniteAxisFoldDisplayedKernelEquiv

open FiniteAxisFoldKernelExtendedPresentation
open FiniteAxisFoldBottomRestrictionKernel
open FiniteAxisFoldBottomKernelInvolution

/-- Classical equality used only to split the exact source C2 carrier. -/
local instance sourceComparisonDecidableEq : DecidableEq ComparisonSubgroup :=
  Classical.decEq _

/-- Classical equality used only to split the exact actual-kernel C2 carrier. -/
local instance actualKernelDecidableEq : DecidableEq bottomRestrictionHom.ker :=
  Classical.decEq _

/-- The exact two-element subgroup in the source-law comparison
presentation. -/
noncomputable def sourceSubgroup : Subgroup ComparisonSubgroup where
  carrier := {g | g = 1 ∨ g = ambientComparisonElement}
  one_mem' := Or.inl rfl
  mul_mem' := by
    intro a b ha hb
    rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
    · exact Or.inl (one_mul 1)
    · exact Or.inr (one_mul _)
    · exact Or.inr (mul_one _)
    · exact Or.inl ambientComparisonElement_mul_self
  inv_mem' := by
    intro a ha
    rcases ha with rfl | rfl
    · exact Or.inl inv_one
    · exact Or.inr
        (inv_eq_of_mul_eq_one_right ambientComparisonElement_mul_self)

/-- The exact two-element subgroup in the actual bottom restriction kernel. -/
noncomputable def actualSubgroup : Subgroup bottomRestrictionHom.ker where
  carrier := {g | g = 1 ∨ g = element}
  one_mem' := Or.inl rfl
  mul_mem' := by
    intro a b ha hb
    rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
    · exact Or.inl (one_mul 1)
    · exact Or.inr (one_mul _)
    · exact Or.inr (mul_one _)
    · exact Or.inl element_mul_self
  inv_mem' := by
    intro a ha
    rcases ha with rfl | rfl
    · exact Or.inl inv_one
    · exact Or.inr (inv_eq_of_mul_eq_one_right element_mul_self)

/-- The named source generator as an element of the source C2 subgroup. -/
noncomputable def sourceGenerator : sourceSubgroup :=
  ⟨ambientComparisonElement, Or.inr rfl⟩

/-- The named semantic generator as an element of the actual C2 subgroup. -/
noncomputable def actualGenerator : actualSubgroup :=
  ⟨element, Or.inr rfl⟩

/-- The displayed comparison generator is nonidentity already in the source
presentation group. -/
theorem ambientComparisonElement_ne_one : ambientComparisonElement ≠ 1 := by
  intro equality
  apply ambientComparisonElement_source_ne_one
  exact congrArg (fun g : ComparisonSubgroup => g.1.1) equality

/-- The named source subgroup generator is nonidentity. -/
theorem sourceGenerator_ne_one : sourceGenerator ≠ 1 := by
  intro equality
  apply ambientComparisonElement_ne_one
  exact congrArg Subtype.val equality

/-- The named actual subgroup generator is nonidentity. -/
theorem actualGenerator_ne_one : actualGenerator ≠ 1 := by
  intro equality
  apply element_ne_one
  exact congrArg Subtype.val equality

/-- Read the two source cases into the corresponding actual-kernel cases. -/
noncomputable def toActual (g : sourceSubgroup) : actualSubgroup :=
  if g.1 = 1 then 1 else actualGenerator

/-- Read the two actual-kernel cases back into the source-law presentation. -/
noncomputable def toSource (g : actualSubgroup) : sourceSubgroup :=
  if g.1 = 1 then 1 else sourceGenerator

/-- Every source C2 value is recovered after semantic evaluation and
readback. -/
theorem toSource_toActual (g : sourceSubgroup) :
    toSource (toActual g) = g := by
  rcases g.property with identity | generator
  · have g_eq_one : g = 1 := Subtype.ext identity
    subst g
    simp [toActual, toSource]
  · have g_eq_generator : g = sourceGenerator := Subtype.ext generator
    subst g
    simp [toActual, toSource, sourceGenerator, actualGenerator,
      ambientComparisonElement_ne_one, element_ne_one]

/-- Every actual displayed-kernel C2 value is recovered after source
readback and reevaluation. -/
theorem toActual_toSource (g : actualSubgroup) :
    toActual (toSource g) = g := by
  rcases g.property with identity | generator
  · have g_eq_one : g = 1 := Subtype.ext identity
    subst g
    simp [toActual, toSource]
  · have g_eq_generator : g = actualGenerator := Subtype.ext generator
    subst g
    simp [toActual, toSource, sourceGenerator, actualGenerator,
      ambientComparisonElement_ne_one, element_ne_one]

/-- The source-to-actual case map preserves multiplication. -/
theorem toActual_mul (a b : sourceSubgroup) :
    toActual (a * b) = toActual a * toActual b := by
  rcases a.property with aIdentity | aGenerator <;>
    rcases b.property with bIdentity | bGenerator
  · have a_eq : a = 1 := Subtype.ext aIdentity
    have b_eq : b = 1 := Subtype.ext bIdentity
    subst a; subst b
    simp [toActual]
  · have a_eq : a = 1 := Subtype.ext aIdentity
    have b_eq : b = sourceGenerator := Subtype.ext bGenerator
    subst a; subst b
    simp [toActual, sourceGenerator, actualGenerator,
      ambientComparisonElement_ne_one]
  · have a_eq : a = sourceGenerator := Subtype.ext aGenerator
    have b_eq : b = 1 := Subtype.ext bIdentity
    subst a; subst b
    simp [toActual, sourceGenerator, actualGenerator,
      ambientComparisonElement_ne_one]
  · have a_eq : a = sourceGenerator := Subtype.ext aGenerator
    have b_eq : b = sourceGenerator := Subtype.ext bGenerator
    subst a; subst b
    apply Subtype.ext
    simp [toActual, sourceGenerator, actualGenerator,
      ambientComparisonElement_ne_one,
      ambientComparisonElement_mul_self, element_mul_self]

/-- Forgetting the bottom and kernel qualifications, `toActual` is the actual
decoder evaluation on every element of the source C2 subgroup. -/
theorem toActual_underlying_evaluation (g : sourceSubgroup) :
    (((toActual g).1).1).1 = comparisonEvaluationHom g.1 := by
  rcases g.property with identity | generator
  · have g_eq : g = 1 := Subtype.ext identity
    subst g
    simp [toActual]
  · have g_eq : g = sourceGenerator := Subtype.ext generator
    subst g
    simp [toActual, sourceGenerator, actualGenerator,
      ambientComparisonElement_ne_one, element,
      bottomRawElement, FiniteAxisFoldComparisonRestrictionKernel.rawElement]

/-- Multiplicative equivalence between the source-law C2 fragment and the
same actual bottom restriction-kernel fragment. -/
noncomputable def sourceActualEquiv : sourceSubgroup ≃* actualSubgroup where
  toFun := toActual
  invFun := toSource
  left_inv := toSource_toActual
  right_inv := toActual_toSource
  map_mul' := toActual_mul

/-- The equivalence sends the source presentation generator to the exact
actual bottom restriction-kernel generator. -/
theorem sourceActualEquiv_sourceGenerator :
    sourceActualEquiv sourceGenerator = actualGenerator := by
  simp [sourceActualEquiv, toActual, sourceGenerator, actualGenerator,
    ambientComparisonElement_ne_one]

end FiniteAxisFoldDisplayedKernelEquiv

end

end AAT.AG.RealizationReconstruction

#assert_standard_axioms_only AAT.AG.RealizationReconstruction
