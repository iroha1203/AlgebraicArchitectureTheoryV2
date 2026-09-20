import ResearchLean.AG.LocalSemanticReconstruction.IndependentFiniteLawFormula
import ResearchLean.AG.LocalSemanticReconstruction.IndependentGeometryHomCoverageLaws
import ResearchLean.AG.LocalSemanticReconstruction.IndependentGeometryHomOverlapLaws
import ResearchLean.AG.LocalSemanticReconstruction.IndependentGeometryHomCoefficientLaws
import ResearchLean.AG.LocalSemanticReconstruction.IndependentGeometryPrimitiveAssembly
import Formal.Util.AssertStandardAxioms

/-!
# Three-table finite formulas for geometry Hom laws

Every expression in this module reads the source primitive object table, the
target primitive object table, and the common Hom table explicitly.  The
endpoint tables are the flattened independent object presentations, so their
cells are the same cells used by object reconstruction.  No endpoint fact is
passed as an external proposition.
-/

namespace AAT.AG.LocalSemanticReconstruction.IndependentGeometryHomPrimitive.JointLawFinite

noncomputable section

universe u v

open Site IndependentGeometryTableAssembly IndependentFiniteLawFormula

variable {U : AtomCarrier.{u}} {mode : Mode}

abbrev JointFormula (U : AtomCarrier.{u}) (mode : Mode) :=
  IndependentFiniteLawFormula.Formula.{u, v, max u v} U mode

theorem some_ulift_prop_true_iff (p : Prop) :
    (some (ULift.up p) = some (ULift.up True)) ↔ p := by
  constructor
  · intro h
    have hp : p = True := congrArg ULift.down (Option.some.inj h)
    exact hp.symm ▸ trivial
  · intro hp
    apply congrArg some
    apply ULift.ext
    exact propext (iff_true_intro hp)

theorem some_double_ulift_prop_true_iff (p : Prop) :
    (some (ULift.up (ULift.up p)) = some (ULift.up (ULift.up True))) ↔ p := by
  constructor
  · intro h
    have hp : p = True := congrArg (fun x => x.down.down) (Option.some.inj h)
    exact hp.symm ▸ trivial
  · intro hp
    apply congrArg some
    apply ULift.ext
    apply ULift.ext
    exact propext (iff_true_intro hp)

theorem some_double_ulift_bool_true_iff (b : Bool) :
    (some (ULift.up (ULift.up b)) = some (ULift.up (ULift.up true))) ↔ b = true := by
  constructor
  · intro h
    exact congrArg (fun x => x.down.down) (Option.some.inj h)
  · rintro rfl
    rfl

theorem double_ulift_option_eq_iff {α : Type v} (value : Option α) (x : α) :
    ULift.up (ULift.up value) = ULift.up (ULift.up (some x)) ↔ value = some x := by
  simp only [ULift.up_inj]

/-! ## Coverage -/

namespace Coverage

variable {A B : ArchitectureObject U}

/-- One true source coverage response. -/
def source (q : IndependentCoveragePrimitive.Query A) : JointFormula.{u, v} U mode :=
  .source (.atObject A (.coverage q)) (some ⟨True⟩)

/-- One true target coverage response. -/
def target (q : IndependentCoveragePrimitive.Query B) : JointFormula.{u, v} U mode :=
  .target (.atObject B (.coverage q)) (some ⟨True⟩)

def requiredSupport (a b : U.Atom) : JointFormula.{u, v} U mode :=
  .implies (.hom (.atom .forward a b) true)
    (.implies (source (A := A) (.requiredSupport a)) (target (B := B) (.requiredSupport b)))

def requiredEquation (I J : Type u) (i : I) (j : J) (a b : U.Atom) :
    JointFormula.{u, v} U mode :=
  .implies (.hom (.atObjects A B (.equation .forward (.edge I J i j))) true)
    (.implies (.hom (.atom .forward a b) true)
      (.implies (source (A := A) (.requiredEquation I i a))
        (target (B := B) (.requiredEquation J j b))))

def selectedWitness (I J : Type u) (i : I) (j : J) (a b : U.Atom) :
    JointFormula.{u, v} U mode :=
  .implies (.hom (.atObjects A B (.equation .forward (.edge I J i j))) true)
    (.implies (.hom (.atom .forward a b) true)
      (.implies (source (A := A) (.selectedWitness I i a))
        (target (B := B) (.selectedWitness J j b))))

def requiredAxis (K L : Type u) (i : K) (j : L) : JointFormula.{u, v} U mode :=
  .implies (.hom (.signatureAxis (.edge K L i j)) true)
    (.implies (source (A := A) (.requiredAxis K i)) (target (B := B) (.requiredAxis L j)))

def supportVisible (W : ArchCtx A) (V : ArchCtx B) (a b : U.Atom) :
    JointFormula.{u, v} U mode :=
  .implies (.hom (.atObjects A B (.context .forward W V)) true)
    (.implies (.hom (.atom .forward a b) true)
      (.implies (source (A := A) (.supportVisible W a)) (target (B := B) (.supportVisible V b))))

def equationVisible (W : ArchCtx A) (V : ArchCtx B) (I J : Type u)
    (i : I) (j : J) (a b : U.Atom) : JointFormula.{u, v} U mode :=
  .implies (.hom (.atObjects A B (.context .forward W V)) true)
    (.implies (.hom (.atObjects A B (.equation .forward (.edge I J i j))) true)
      (.implies (.hom (.atom .forward a b) true)
        (.implies (source (A := A) (.equationVisible W I i a))
          (target (B := B) (.equationVisible V J j b)))))

def witnessVisible (W : ArchCtx A) (V : ArchCtx B) (I J : Type u)
    (i : I) (j : J) (a b : U.Atom) : JointFormula.{u, v} U mode :=
  .implies (.hom (.atObjects A B (.context .forward W V)) true)
    (.implies (.hom (.atObjects A B (.equation .forward (.edge I J i j))) true)
      (.implies (.hom (.atom .forward a b) true)
        (.implies (source (A := A) (.witnessVisible W I i a))
          (target (B := B) (.witnessVisible V J j b)))))

def axisReadable (W : ArchCtx A) (V : ArchCtx B) (K L : Type u)
    (i : K) (j : L) : JointFormula.{u, v} U mode :=
  .implies (.hom (.atObjects A B (.context .forward W V)) true)
    (.implies (.hom (.signatureAxis (.edge K L i j)) true)
      (.implies (source (A := A) (.axisReadable W K i)) (target (B := B) (.axisReadable V L j))))

def boundaryVisible (W X : ArchCtx A) (V Y : ArchCtx B) : JointFormula.{u, v} U mode :=
  .implies (.hom (.atObjects A B (.context .forward W V)) true)
    (.implies (.hom (.atObjects A B (.context .forward X Y)) true)
      (.implies (source (A := A) (.boundaryVisible W X)) (target (B := B) (.boundaryVisible V Y))))

/-- The quantified family of all nine finite coverage instances. -/
def Instances (sourceTable targetTable : IndependentGeometryPrimitive.Table.{u, v} U)
    (h : Table.{u, v} U mode) (I J K L : Type u) : Prop :=
  (∀ a b, (requiredSupport (A := A) (B := B) a b).evaluate sourceTable targetTable h) ∧
  (∀ i j a b, (requiredEquation (A := A) (B := B) I J i j a b).evaluate sourceTable targetTable h) ∧
  (∀ i j a b, (selectedWitness (A := A) (B := B) I J i j a b).evaluate sourceTable targetTable h) ∧
  (∀ i j, (requiredAxis (A := A) (B := B) K L i j).evaluate sourceTable targetTable h) ∧
  (∀ W V a b, (supportVisible (A := A) (B := B) W V a b).evaluate sourceTable targetTable h) ∧
  (∀ W V i j a b, (equationVisible (A := A) (B := B) W V I J i j a b).evaluate sourceTable targetTable h) ∧
  (∀ W V i j a b, (witnessVisible (A := A) (B := B) W V I J i j a b).evaluate sourceTable targetTable h) ∧
  (∀ W V i j, (axisReadable (A := A) (B := B) W V K L i j).evaluate sourceTable targetTable h) ∧
  (∀ W X V Y, (boundaryVisible (A := A) (B := B) W X V Y).evaluate sourceTable targetTable h)

@[simp] theorem flatten_coverage_true_iff (d : ObjectData.{u, v} U)
    (q : IndependentCoveragePrimitive.Query
      (IndependentCoreTableAssembly.generatedObject d.1.val.1)) :
    IndependentGeometryPrimitive.flatten d (.atObject _ (.coverage q)) = some ⟨True⟩ ↔
      d.2.1.1.val q := by
  rw [IndependentGeometryPrimitive.flatten_at_generated]
  exact some_ulift_prop_true_iff _

/-- On independently flattened endpoints, the nine native point-law fields are
exactly the nine three-table finite formula families. -/
theorem pointLaws_iff_instances
    (s t : ObjectData.{u, v} U)
    (h : Table.{u, v} U mode)
    (I J K L : Type u) :
    IndependentGeometryHomPrimitive.Coverage.PointLaws I J K L
        s.2.1.1.val t.2.1.1.val h ↔
      Instances (A := IndependentCoreTableAssembly.generatedObject s.1.val.1)
        (B := IndependentCoreTableAssembly.generatedObject t.1.val.1)
        (IndependentGeometryPrimitive.flatten s)
        (IndependentGeometryPrimitive.flatten t) h I J K L := by
  constructor
  · intro hp
    simp only [Instances, Formula.evaluate, source, target, requiredSupport,
      requiredEquation, selectedWitness, requiredAxis, supportVisible,
      equationVisible, witnessVisible, axisReadable, boundaryVisible,
      flatten_coverage_true_iff]
    exact ⟨hp.requiredSupport, hp.requiredEquation, hp.selectedWitness,
      hp.requiredAxis, hp.supportVisible, hp.equationVisible,
      hp.witnessVisible, hp.axisReadable, hp.boundaryVisible⟩
  · intro hi
    simp only [Instances, Formula.evaluate, source, target, requiredSupport,
      requiredEquation, selectedWitness, requiredAxis, supportVisible,
      equationVisible, witnessVisible, axisReadable, boundaryVisible,
      flatten_coverage_true_iff] at hi
    rcases hi with ⟨hSupport, hEquation, hWitness, hAxis, hSupportVisible,
      hEquationVisible, hWitnessVisible, hAxisReadable, hBoundary⟩
    exact {
      requiredSupport := hSupport
      requiredEquation := hEquation
      selectedWitness := hWitness
      requiredAxis := hAxis
      supportVisible := hSupportVisible
      equationVisible := hEquationVisible
      witnessVisible := hWitnessVisible
      axisReadable := hAxisReadable
      boundaryVisible := hBoundary }

end Coverage

/-! ## Overlap -/

namespace Overlap

variable {A B : ArchitectureObject U}

def lawInstance (W X Y : ArchCtx A) (base left right : ArchCtx B)
    (R : ArchCtx A) (S T : ArchCtx B) : JointFormula.{u, v} U mode :=
  .implies (.hom (.atObjects A B (.context .backward W base)) true)
    (.implies (.hom (.atObjects A B (.context .backward X left)) true)
      (.implies (.hom (.atObjects A B (.context .backward Y right)) true)
        (.implies
          (.source (.atObject A (.overlap (.matching W X Y R))) (some ⟨⟨true⟩⟩))
          (.implies
            (.target (.atObject B (.overlap (.matching base left right S))) (some ⟨⟨true⟩⟩))
            (.implies (.hom (.atObjects A B (.context .forward R T)) true)
              (.and
                (.target (.atObject B (.context (.le T S))) (some ⟨⟨True⟩⟩))
                (.target (.atObject B (.context (.le S T))) (some ⟨⟨True⟩⟩))))))))

def Instances (sourceTable targetTable : IndependentGeometryPrimitive.Table.{u, v} U)
    (h : Table.{u, v} U mode) : Prop :=
  ∀ (W X Y : ArchCtx A) (base left right : ArchCtx B) (R : ArchCtx A) (S T : ArchCtx B),
    (lawInstance (U := U) (mode := mode) W X Y base left right R S T).evaluate
      sourceTable targetTable h

@[simp] theorem flatten_overlap_match_true_iff (d : ObjectData.{u, v} U)
    (base left right result : ArchCtx
      (IndependentCoreTableAssembly.generatedObject d.1.val.1)) :
    IndependentGeometryPrimitive.flatten d
        (.atObject _ (.overlap (.matching base left right result))) = some ⟨⟨true⟩⟩ ↔
      (d.2.1.2.val (.matching base left right result)).down = true := by
  rw [IndependentGeometryPrimitive.flatten_at_generated]
  exact some_double_ulift_bool_true_iff _

@[simp] theorem flatten_context_true_iff (d : ObjectData.{u, v} U)
    (W V : ArchCtx (IndependentCoreTableAssembly.generatedObject d.1.val.1)) :
    IndependentGeometryPrimitive.flatten d (.atObject _ (.context (.le W V))) =
        some ⟨⟨True⟩⟩ ↔
      (d.1.val.2.1.val (.le W V)).down := by
  rw [IndependentGeometryPrimitive.flatten_at_generated]
  exact some_double_ulift_prop_true_iff _

theorem pointLaws_iff_instances
    (s t : ObjectData.{u, v} U) (h : Table.{u, v} U mode) :
    IndependentGeometryHomPrimitive.Overlap.PointLaws
        s.2.1.2.val t.2.1.2.val t.1.val.2.1.val h ↔
      Instances (A := IndependentCoreTableAssembly.generatedObject s.1.val.1)
        (B := IndependentCoreTableAssembly.generatedObject t.1.val.1)
        (IndependentGeometryPrimitive.flatten s)
        (IndependentGeometryPrimitive.flatten t) h := by
  unfold IndependentGeometryHomPrimitive.Overlap.PointLaws
  simpa only [IndependentCoreTableAssembly.package_object, Instances, lawInstance, Formula.evaluate,
    flatten_overlap_match_true_iff, flatten_context_true_iff]

end Overlap

/-! ## Directed coefficient laws -/

namespace Coefficient

def sourceCarrier (K : Type v) : JointFormula.{u, v} U mode :=
  .source (.coefficient .carrier) ⟨K⟩

def targetCarrier (L : Type v) : JointFormula.{u, v} U mode :=
  .target (.coefficient .carrier) ⟨L⟩

def carriers (K : Type v) (L : Type v) : JointFormula.{u, v} U mode :=
  .and (sourceCarrier K) (targetCarrier L)

def typed (K : Type v) (L : Type v) (S T : Type v) (x : S) (y : T) :
    IndependentFiniteLawFormula.Formula.{u, v, v + 1} U mode :=
  .implies
    (.and (.source (.coefficient .carrier) ⟨K⟩)
      (.target (.coefficient .carrier) ⟨L⟩))
    (.implies (.or (.notEqual S K) (.notEqual T L))
      (.hom (.coefficient (.edge S T x y)) false))

def witness (K : Type v) (L : Type v) (x : K) (y : L) :
    JointFormula.{u, v} U mode :=
  .implies (carriers K L) (.hom (.coefficient (.edge K L x y)) true)

def unique (K : Type v) (L : Type v) (x : K) (y z : L) :
    IndependentFiniteLawFormula.Formula.{u, v, v} U mode :=
  .implies
    (.and (.source (.coefficient .carrier) ⟨K⟩)
      (.target (.coefficient .carrier) ⟨L⟩))
    (.implies
      (.and (.hom (.coefficient (.edge K L x y)) true)
        (.hom (.coefficient (.edge K L x z)) true))
      (.equal z y))

def sourceOperation (K : Type v) (q : IndependentRingPrimitive.Query K) (value : K) :
    JointFormula.{u, v} U mode :=
  .source (.coefficient (.operation K q)) ⟨⟨some value⟩⟩

def targetOperation (L : Type v) (q : IndependentRingPrimitive.Query L) (value : L) :
    JointFormula.{u, v} U mode :=
  .target (.coefficient (.operation L q)) ⟨⟨some value⟩⟩

def zero (K : Type v) (L : Type v) (a : K) (b : L) : JointFormula.{u, v} U mode :=
  .implies
    (.and (carriers K L)
      (.and (sourceOperation K .zero a) (targetOperation L .zero b)))
    (.hom (.coefficient (.edge K L a b)) true)

def one (K : Type v) (L : Type v) (a : K) (b : L) : JointFormula.{u, v} U mode :=
  .implies
    (.and (carriers K L)
      (.and (sourceOperation K .one a) (targetOperation L .one b)))
    (.hom (.coefficient (.edge K L a b)) true)

def add (K : Type v) (L : Type v) (a b r : K) (c d s : L) :
    JointFormula.{u, v} U mode :=
  .implies
    (.and (carriers K L)
      (.and (sourceOperation K (.add a b) r) (targetOperation L (.add c d) s)))
    (.implies (.hom (.coefficient (.edge K L a c)) true)
      (.implies (.hom (.coefficient (.edge K L b d)) true)
        (.hom (.coefficient (.edge K L r s)) true)))

def mul (K : Type v) (L : Type v) (a b r : K) (c d s : L) :
    JointFormula.{u, v} U mode :=
  .implies
    (.and (carriers K L)
      (.and (sourceOperation K (.mul a b) r) (targetOperation L (.mul c d) s)))
    (.implies (.hom (.coefficient (.edge K L a c)) true)
      (.implies (.hom (.coefficient (.edge K L b d)) true)
        (.hom (.coefficient (.edge K L r s)) true)))

def Instances (sourceTable targetTable : IndependentGeometryPrimitive.Table.{u, v} U)
    (h : Table.{u, v} U mode) (K : Type v) (L : Type v) : Prop :=
  (∀ S T x y, (typed (U := U) (mode := mode) K L S T x y).evaluate sourceTable targetTable h) ∧
  (∀ x : K, ∃ y : L,
    (witness (U := U) (mode := mode) K L x y).evaluate sourceTable targetTable h ∧
    ∀ z : L, (unique (U := U) (mode := mode) K L x y z).evaluate sourceTable targetTable h) ∧
  (∀ a b, (zero (U := U) (mode := mode) K L a b).evaluate sourceTable targetTable h) ∧
  (∀ a b, (one (U := U) (mode := mode) K L a b).evaluate sourceTable targetTable h) ∧
  (∀ a b r c d s, (add (U := U) (mode := mode) K L a b r c d s).evaluate sourceTable targetTable h) ∧
  (∀ a b r c d s, (mul (U := U) (mode := mode) K L a b r c d s).evaluate sourceTable targetTable h)

@[simp] theorem flatten_coefficient_carrier (d : ObjectData.{u, v} U) :
    IndependentGeometryPrimitive.flatten d (.coefficient .carrier) =
      ⟨IndependentRingPrimitive.Carrier.carrier d.2.2.1.val⟩ := rfl

@[simp] theorem flatten_coefficient_operation_iff (d : ObjectData.{u, v} U)
    (q : IndependentRingPrimitive.Query
      (IndependentRingPrimitive.Carrier.carrier d.2.2.1.val))
    (x : IndependentRingPrimitive.Carrier.carrier d.2.2.1.val) :
    IndependentGeometryPrimitive.flatten d
        (.coefficient (.operation _ q)) = ⟨⟨some x⟩⟩ ↔
      IndependentRingPrimitive.Carrier.active d.2.2.1.val d.2.2.1.property.choose q = x := by
  change ULift.up (ULift.up ((d.2.2.1.val (.operation _ q)).down)) =
      ULift.up (ULift.up (some x)) ↔ _
  rw [double_ulift_option_eq_iff]
  rw [show (d.2.2.1.val (.operation _ q)).down =
      some (IndependentRingPrimitive.Carrier.active d.2.2.1.val
        d.2.2.1.property.choose q) from
    (Option.some_get _).symm]
  simp

theorem pointLaws_iff_instances (s t : ObjectData.{u, v} U)
    (h : Table.{u, v} U mode) :
    IndependentGeometryHomPrimitive.Coefficient.PointLaws
        s.2.2.1.val t.2.2.1.val s.2.2.1.property.choose t.2.2.1.property.choose h ↔
      Instances (IndependentGeometryPrimitive.flatten s)
        (IndependentGeometryPrimitive.flatten t) h
        (IndependentRingPrimitive.Carrier.carrier s.2.2.1.val)
        (IndependentRingPrimitive.Carrier.carrier t.2.2.1.val) := by
  let K := IndependentRingPrimitive.Carrier.carrier s.2.2.1.val
  let L := IndependentRingPrimitive.Carrier.carrier t.2.2.1.val
  let rs := IndependentRingPrimitive.Carrier.active s.2.2.1.val s.2.2.1.property.choose
  let rt := IndependentRingPrimitive.Carrier.active t.2.2.1.val t.2.2.1.property.choose
  change (IndependentCarrierGraph.IsLawful K L (coefficient h) ∧
    IndependentRingCarrierGraph.Preserves rs rt (coefficient h)) ↔ _
  simp only [Instances, typed, witness, unique, zero, one, add, mul,
    carriers, sourceCarrier, targetCarrier, sourceOperation, targetOperation,
    Formula.evaluate, flatten_coefficient_carrier, flatten_coefficient_operation_iff,
    true_and, true_implies]
  constructor
  · rintro ⟨hrows, hpreserves⟩
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · exact hrows.1
    · intro x
      obtain ⟨y, hy, hu⟩ := hrows.2 x
      exact ⟨y, hy, fun z hz => hu z hz.2⟩
    · intro a b hab
      rcases hab with ⟨ha, hb⟩
      simpa [rs, rt, ha, hb] using hpreserves.zero
    · intro a b hab
      rcases hab with ⟨ha, hb⟩
      simpa [rs, rt, ha, hb] using hpreserves.one
    · intro a b r c d q hr ha hb
      rcases hr with ⟨hr, hq⟩
      simpa [rs, rt, hr, hq] using hpreserves.add a b c d ha hb
    · intro a b r c d q hr ha hb
      rcases hr with ⟨hr, hq⟩
      simpa [rs, rt, hr, hq] using hpreserves.mul a b c d ha hb
  · rintro ⟨htyped, htotal, hzero, hone, hadd, hmul⟩
    refine ⟨⟨htyped, ?_⟩, ⟨?_, ?_, ?_, ?_⟩⟩
    · intro x
      obtain ⟨y, hy, hu⟩ := htotal x
      exact ⟨y, hy, fun z hz => hu z ⟨hy, hz⟩⟩
    · exact hzero (rs .zero) (rt .zero) ⟨rfl, rfl⟩
    · exact hone (rs .one) (rt .one) ⟨rfl, rfl⟩
    · intro a b c d ha hb
      exact hadd a b (rs (.add a b)) c d (rt (.add c d)) ⟨rfl, rfl⟩ ha hb
    · intro a b c d ha hb
      exact hmul a b (rs (.mul a b)) c d (rt (.mul c d)) ⟨rfl, rfl⟩ ha hb

end Coefficient

end


end AAT.AG.LocalSemanticReconstruction.IndependentGeometryHomPrimitive.JointLawFinite

#assert_standard_axioms_only AAT.AG.LocalSemanticReconstruction.IndependentGeometryHomPrimitive.JointLawFinite
