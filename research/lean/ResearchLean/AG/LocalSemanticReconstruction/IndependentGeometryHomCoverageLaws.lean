import ResearchLean.AG.LocalSemanticReconstruction.IndependentGeometryHomPrimitiveDeclaration
import ResearchLean.AG.LocalSemanticReconstruction.IndependentCoveragePrimitiveReadings
import ResearchLean.AG.GeometryTransport.Categories
import Formal.Util.AssertStandardAxioms

/-!
# All nine coverage implications on common Hom points

The point rules read the original nine coverage predicates at their primitive
arguments. Equation and signature references are selected carrier declarations;
the source object's typing conditions already reject inactive required roles.
The comparison API below connects these independent rules to the existing
native coverage field without placing that field in the local rules.
-/

namespace AAT.AG.LocalSemanticReconstruction.IndependentGeometryHomPrimitive.Coverage

noncomputable section

universe u v

open Site GeometryTransport AtomFoundation

variable {U : AtomCarrier.{u}} {mode : Mode} {A B : ArchitectureObject U}

/-- Coverage preservation is nine implications between primitive predicate cells and true Hom points. -/
structure PointLaws (I J K L : Type u)
    (r : IndependentCoveragePrimitive.Table A) (s : IndependentCoveragePrimitive.Table B)
    (h : Table.{u, v} U mode) : Prop where
  /-- Required support follows the true Atom point. -/
  requiredSupport : ∀ a b, h (.atom .forward a b) = true → r (.requiredSupport a) → s (.requiredSupport b)
  /-- Required coordinates retain their original required-role checks in the object table. -/
  requiredEquation : ∀ (i : I) (j : J) a b,
    h (.atObjects A B (.equation .forward (.edge I J i j))) = true → h (.atom .forward a b) = true →
    r (.requiredEquation I i a) → s (.requiredEquation J j b)
  /-- Selected witnesses use the full equation-index carrier. -/
  selectedWitness : ∀ (i : I) (j : J) a b,
    h (.atObjects A B (.equation .forward (.edge I J i j))) = true → h (.atom .forward a b) = true →
    r (.selectedWitness I i a) → s (.selectedWitness J j b)
  /-- Required signature axes use the directed axis graph. -/
  requiredAxis : ∀ (i : K) (j : L), h (.signatureAxis (.edge K L i j)) = true →
    r (.requiredAxis K i) → s (.requiredAxis L j)
  /-- Support visibility follows both the context and Atom points. -/
  supportVisible : ∀ W V a b, h (.atObjects A B (.context .forward W V)) = true →
    h (.atom .forward a b) = true → r (.supportVisible W a) → s (.supportVisible V b)
  /-- Required-coordinate visibility follows context, equation, and Atom points. -/
  equationVisible : ∀ W V (i : I) (j : J) a b, h (.atObjects A B (.context .forward W V)) = true →
    h (.atObjects A B (.equation .forward (.edge I J i j))) = true → h (.atom .forward a b) = true →
    r (.equationVisible W I i a) → s (.equationVisible V J j b)
  /-- Witness visibility has the same point arguments without a required-role restriction. -/
  witnessVisible : ∀ W V (i : I) (j : J) a b, h (.atObjects A B (.context .forward W V)) = true →
    h (.atObjects A B (.equation .forward (.edge I J i j))) = true → h (.atom .forward a b) = true →
    r (.witnessVisible W I i a) → s (.witnessVisible V J j b)
  /-- Axis readability follows context and directed signature-axis points. -/
  axisReadable : ∀ W V (i : K) (j : L), h (.atObjects A B (.context .forward W V)) = true →
    h (.signatureAxis (.edge K L i j)) = true → r (.axisReadable W K i) → s (.axisReadable V L j)
  /-- The ninth predicate follows two independent context points. -/
  boundaryVisible : ∀ W X V Y, h (.atObjects A B (.context .forward W V)) = true →
    h (.atObjects A B (.context .forward X Y)) = true → r (.boundaryVisible W X) → s (.boundaryVisible V Y)

variable {G H : GeometryPackage.{u, v} U}

/-- Comparison premises identify assembled component maps with their common points; these are not local laws. -/
structure Maps (f : PackageTotalHom G.core H.core) (h : Table.{u, v} U mode) : Prop where
  atom : ∀ a b, h (.atom .forward a b) = true ↔ f.upper.atomEquiv a = b
  equation : ∀ i j, h (.atObjects G.core.object H.core.object (.equation .forward
    (.edge G.core.equationSystem.Index H.core.equationSystem.Index i j))) = true ↔
      f.upper.equationEquiv i = j
  axis : ∀ i j, h (.signatureAxis
    (.edge G.core.algebra.signatureReading.Axis H.core.algebra.signatureReading.Axis i j)) = true ↔
      f.upper.axisMap i = j
  context : ∀ W V, h (.atObjects G.core.object H.core.object (.context .forward W V)) = true ↔
    contextMap f W = V

/-- The independently defined point laws on the original primitive coverage readings. -/
abbrev NativePoints (G H : GeometryPackage.{u, v} U) (h : Table.{u, v} U mode) :=
  PointLaws G.core.equationSystem.Index H.core.equationSystem.Index
    G.core.algebra.signatureReading.Axis H.core.algebra.signatureReading.Axis
    (IndependentCoveragePrimitive.read G.geometry.requirements)
    (IndependentCoveragePrimitive.read H.geometry.requirements) h

variable (f : PackageTotalHom G.core H.core) (h : Table.{u, v} U mode) (hm : Maps f h)

include hm in
/-- Each of the nine original native coverage fields follows from the primitive implication at its image points. -/
theorem assemble (hp : NativePoints G H h) : CoverageTransport G H f where
  requiredSupport a ha := hp.requiredSupport a _ ((hm.atom a _).2 rfl) ha
  requiredEquationCoordinate := by
    rintro ⟨⟨i, hi⟩, a⟩ ha
    have hi' : H.core.equationSystem.Required (f.upper.equationEquiv i) := (f.upper.required_iff i).1 hi
    have hh := hp.requiredEquation i _ a _ ((hm.equation i _).2 rfl) ((hm.atom a _).2 rfl)
    simpa [IndependentCoveragePrimitive.read, requiredCoordinateMap, hi, hi'] using hh (by simpa [IndependentCoveragePrimitive.read, hi] using ha)
  selectedViolationWitness := by
    rintro ⟨i, a⟩ ha
    have hh := hp.selectedWitness i _ a _ ((hm.equation i _).2 rfl) ((hm.atom a _).2 rfl)
    simpa [IndependentCoveragePrimitive.read, equationCoordinateMap] using hh (by simpa [IndependentCoveragePrimitive.read] using ha)
  requiredAxis := by
    intro i hi
    have hh := hp.requiredAxis i _ ((hm.axis i _).2 rfl)
    simpa [IndependentCoveragePrimitive.read] using hh (by simpa [IndependentCoveragePrimitive.read] using hi)
  supportVisibleOn W a ha :=
    hp.supportVisible W _ a _ ((hm.context W _).2 rfl) ((hm.atom a _).2 rfl) ha
  equationCoordinateVisibleOn := by
    rintro W ⟨⟨i, hi⟩, a⟩ ha
    have hi' : H.core.equationSystem.Required (f.upper.equationEquiv i) := (f.upper.required_iff i).1 hi
    have hh := hp.equationVisible W _ i _ a _ ((hm.context W _).2 rfl)
      ((hm.equation i _).2 rfl) ((hm.atom a _).2 rfl)
    simpa [IndependentCoveragePrimitive.read, requiredCoordinateMap, hi, hi'] using hh (by simpa [IndependentCoveragePrimitive.read, hi] using ha)
  violationWitnessVisibleOn := by
    rintro W ⟨i, a⟩ ha
    have hh := hp.witnessVisible W _ i _ a _ ((hm.context W _).2 rfl)
      ((hm.equation i _).2 rfl) ((hm.atom a _).2 rfl)
    simpa [IndependentCoveragePrimitive.read, equationCoordinateMap] using hh (by simpa [IndependentCoveragePrimitive.read] using ha)
  axisReadableOn := by
    intro W i hi
    have hh := hp.axisReadable W _ i _ ((hm.context W _).2 rfl) ((hm.axis i _).2 rfl)
    simpa [IndependentCoveragePrimitive.read] using hh (by simpa [IndependentCoveragePrimitive.read] using hi)
  boundaryVisibleOn W X hx :=
    hp.boundaryVisible W X _ _ ((hm.context W _).2 rfl) ((hm.context X _).2 rfl) hx

include hm in
/-- Native coverage preservation supplies all primitive point implications, including exact required-role checks. -/
theorem points_of_native (hp : CoverageTransport G H f) : NativePoints G H h := by
  constructor
  · intro a b hab ha
    obtain rfl := (hm.atom a b).1 hab
    exact hp.requiredSupport a ha
  · intro i j a b hij hab ha
    obtain rfl := (hm.equation i j).1 hij
    obtain rfl := (hm.atom a b).1 hab
    by_cases hi : G.core.equationSystem.Required i
    · have hi' : H.core.equationSystem.Required (f.upper.equationEquiv i) := (f.upper.required_iff i).1 hi
      simpa [IndependentCoveragePrimitive.read, requiredCoordinateMap, hi, hi'] using
        hp.requiredEquationCoordinate (⟨i, hi⟩, a) (by simpa [IndependentCoveragePrimitive.read, hi] using ha)
    · simp [IndependentCoveragePrimitive.read, hi] at ha
  · intro i j a b hij hab ha
    obtain rfl := (hm.equation i j).1 hij
    obtain rfl := (hm.atom a b).1 hab
    simpa [IndependentCoveragePrimitive.read, equationCoordinateMap] using
      hp.selectedViolationWitness (i, a) (by simpa [IndependentCoveragePrimitive.read] using ha)
  · intro i j hij hi
    obtain rfl := (hm.axis i j).1 hij
    simpa [IndependentCoveragePrimitive.read] using
      hp.requiredAxis i (by simpa [IndependentCoveragePrimitive.read] using hi)
  · intro W V a b hWV hab ha
    obtain rfl := (hm.context W V).1 hWV
    obtain rfl := (hm.atom a b).1 hab
    exact hp.supportVisibleOn W a ha
  · intro W V i j a b hWV hij hab ha
    obtain rfl := (hm.context W V).1 hWV
    obtain rfl := (hm.equation i j).1 hij
    obtain rfl := (hm.atom a b).1 hab
    by_cases hi : G.core.equationSystem.Required i
    · have hi' : H.core.equationSystem.Required (f.upper.equationEquiv i) := (f.upper.required_iff i).1 hi
      simpa [IndependentCoveragePrimitive.read, requiredCoordinateMap, hi, hi'] using
        hp.equationCoordinateVisibleOn W (⟨i, hi⟩, a)
          (by simpa [IndependentCoveragePrimitive.read, hi] using ha)
    · simp [IndependentCoveragePrimitive.read, hi] at ha
  · intro W V i j a b hWV hij hab ha
    obtain rfl := (hm.context W V).1 hWV
    obtain rfl := (hm.equation i j).1 hij
    obtain rfl := (hm.atom a b).1 hab
    simpa [IndependentCoveragePrimitive.read, equationCoordinateMap] using
      hp.violationWitnessVisibleOn W (i, a) (by simpa [IndependentCoveragePrimitive.read] using ha)
  · intro W V i j hWV hij hi
    obtain rfl := (hm.context W V).1 hWV
    obtain rfl := (hm.axis i j).1 hij
    simpa [IndependentCoveragePrimitive.read] using
      hp.axisReadableOn W i (by simpa [IndependentCoveragePrimitive.read] using hi)
  · intro W X V Y hWV hXY hx
    obtain rfl := (hm.context W V).1 hWV
    obtain rfl := (hm.context X Y).1 hXY
    exact hp.boundaryVisibleOn W X hx

include hm in
/-- The nine local implications are neither stronger nor weaker than the original native coverage contract. -/
theorem points_iff_native : NativePoints G H h ↔ CoverageTransport G H f :=
  ⟨assemble f h hm, points_of_native f h hm⟩

end

end AAT.AG.LocalSemanticReconstruction.IndependentGeometryHomPrimitive.Coverage

#assert_standard_axioms_only AAT.AG.LocalSemanticReconstruction.IndependentGeometryHomPrimitive.Coverage
