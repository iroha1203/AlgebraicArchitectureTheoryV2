import ResearchLean.AG.LocalSemanticReconstruction.IndependentGeometryHomRepresentativeRealization
import Formal.Util.AssertStandardAxioms

/-!
# Exact native recovery of representative realization transport

The three point-family equalities here are comparison hypotheses for the
native reader. They yield all primitive local laws, and reconstruction then
recovers the complete native supply. They are not fields of local coherence.
-/

namespace AAT.AG.LocalSemanticReconstruction.IndependentGeometryHomPrimitive.RepresentativeRealization

noncomputable section

universe u v

open Site CategoryTheory AtomFoundation GeometryTransport

variable {U : AtomCarrier.{u}} {P Q : AATCorePackage U}
variable (f : PackageTotalHom P Q) (h : Table.{u, v} U .representative) (hm : Maps f h)
variable (R : RealizationTransportSupply P Q f)
variable (hs : support h = IndependentFixedIndexedPointGraph.read (forward f) (fun W => R.supportComp ⟨W⟩))
variable (ha : axis h = IndependentFixedIndexedPointGraph.read (forward f) (fun W => R.axisComp ⟨W⟩))
variable (ho : observable h = IndependentFixedIndexedPointGraph.read (forward f) (fun W => R.observableComp ⟨W⟩))

include hm hs ha ho in
/-- Every native directed realization supplies all primitive point rules, including all restriction squares. -/
theorem points_of_native : NativePoints P Q h := by
  classical
  have sp : ∀ W x y, support h W (forward f W) x y = true ↔ R.supportComp ⟨W⟩ x = y := by
    intro W x y
    rw [hs]
    exact IndependentFixedIndexedPointGraph.read_point_iff _ _ _ _ _
  have ap : ∀ W x y, axis h W (forward f W) x y = true ↔ R.axisComp ⟨W⟩ x = y := by
    intro W x y
    rw [ha]
    exact IndependentFixedIndexedPointGraph.read_point_iff _ _ _ _ _
  have op : ∀ W x y, observable h W (forward f W) x y = true ↔ R.observableComp ⟨W⟩ x = y := by
    intro W x y
    rw [ho]
    exact IndependentFixedIndexedPointGraph.read_point_iff _ _ _ _ _
  constructor
  · rw [hs]
    exact IndependentFixedIndexedPointGraph.read_isLawful _ hm.context _
  · rw [ha]
    exact IndependentFixedIndexedPointGraph.read_isLawful _ hm.context _
  · rw [ho]
    exact IndependentFixedIndexedPointGraph.read_isLawful _ hm.context _
  · intro W V x y a b hWV hxy hab hx
    obtain rfl := (hm.context W V).1 hWV
    obtain rfl := (sp W x y).1 hxy
    obtain rfl := (hm.atom a b).1 hab
    exact R.supportReads ⟨W⟩ x a hx
  · intro W V x y hWV hxy hx
    obtain rfl := (hm.context W V).1 hWV
    obtain rfl := (ap W x y).1 hxy
    exact R.axisReads ⟨W⟩ x hx
  · intro W V x y hWV hxy hx
    obtain rfl := (hm.context W V).1 hWV
    obtain rfl := (op W x y).1 hxy
    exact R.observableReads ⟨W⟩ x hx
  · intro W X V Y x y xx yy hWV hXY hxy hxx hyy
    obtain rfl := (hm.context W V).1 hWV
    obtain rfl := (hm.context X Y).1 hXY
    obtain rfl := (sp W x y).1 hxy
    by_cases hWX : P.contextPreorder.le W X
    · have hVY : Q.contextPreorder.le (forward f W) (forward f X) :=
        leOfHom ((coreContextFunctor f).map (homOfLE hWX))
      have hx : (P.contextPreorder.morphism hWX).supportMap x = xx := Option.some.inj ((contextSupport_read P.contextPreorder hWX x).symm.trans hxx)
      have hy : (Q.contextPreorder.morphism hVY).supportMap (R.supportComp ⟨W⟩ x) = yy := Option.some.inj ((contextSupport_read Q.contextPreorder hVY _).symm.trans hyy)
      have hn := R.support_naturality (homOfLE hWX) x
      change (Q.contextPreorder.morphism hVY).supportMap (R.supportComp ⟨W⟩ x) =
        R.supportComp ⟨X⟩ ((P.contextPreorder.morphism hWX).supportMap x) at hn
      rw [hx, hy] at hn
      exact (sp X xx yy).2 hn.symm
    · simp [IndependentContextPrimitive.read, hWX] at hxx
  · intro W X V Y x y xx yy hWV hXY hxy hxx hyy
    obtain rfl := (hm.context W V).1 hWV
    obtain rfl := (hm.context X Y).1 hXY
    obtain rfl := (ap W x y).1 hxy
    by_cases hWX : P.contextPreorder.le W X
    · have hVY : Q.contextPreorder.le (forward f W) (forward f X) :=
        leOfHom ((coreContextFunctor f).map (homOfLE hWX))
      have hx : (P.contextPreorder.morphism hWX).axisMap x = xx := Option.some.inj ((contextAxis_read P.contextPreorder hWX x).symm.trans hxx)
      have hy : (Q.contextPreorder.morphism hVY).axisMap (R.axisComp ⟨W⟩ x) = yy := Option.some.inj ((contextAxis_read Q.contextPreorder hVY _).symm.trans hyy)
      have hn := R.axis_naturality (homOfLE hWX) x
      change (Q.contextPreorder.morphism hVY).axisMap (R.axisComp ⟨W⟩ x) =
        R.axisComp ⟨X⟩ ((P.contextPreorder.morphism hWX).axisMap x) at hn
      rw [hx, hy] at hn
      exact (ap X xx yy).2 hn.symm
    · simp [IndependentContextPrimitive.read, hWX] at hxx
  · intro W X V Y x y xx yy hWV hXY hxy hxx hyy
    obtain rfl := (hm.context W V).1 hWV
    obtain rfl := (hm.context X Y).1 hXY
    obtain rfl := (op X x y).1 hxy
    by_cases hWX : P.contextPreorder.le W X
    · have hVY : Q.contextPreorder.le (forward f W) (forward f X) :=
        leOfHom ((coreContextFunctor f).map (homOfLE hWX))
      have hx : (P.contextPreorder.morphism hWX).observableRestrict x = xx := Option.some.inj ((contextObservable_read P.contextPreorder hWX x).symm.trans hxx)
      have hy : (Q.contextPreorder.morphism hVY).observableRestrict (R.observableComp ⟨X⟩ x) = yy := Option.some.inj ((contextObservable_read Q.contextPreorder hVY _).symm.trans hyy)
      have hn := R.observable_naturality (homOfLE hWX) x
      change (Q.contextPreorder.morphism hVY).observableRestrict (R.observableComp ⟨X⟩ x) =
        R.observableComp ⟨W⟩ ((P.contextPreorder.morphism hWX).observableRestrict x) at hn
      rw [hx, hy] at hn
      exact (op W xx yy).2 hn.symm
    · simp [IndependentContextPrimitive.read, hWX] at hxx

/-- Reassembly of every native representative realization recovers all three computational families. -/
theorem assemble_points_of_native : assemble f h hm (points_of_native f h hm R hs ha ho) = R := by
  apply RemainingComponentGraphCoherence.RealizationGraphCode.supply_ext
  · funext W x
    apply (IndependentFixedIndexedPointGraph.point_iff (forward f) hm.context (support h)
      (points_of_native f h hm R hs ha ho).supportRows W.ctx x (R.supportComp W x)).1
    rw [hs]
    exact (IndependentFixedIndexedPointGraph.read_point_iff _ _ _ _ _).2 rfl
  · funext W x
    apply (IndependentFixedIndexedPointGraph.point_iff (forward f) hm.context (axis h)
      (points_of_native f h hm R hs ha ho).axisRows W.ctx x (R.axisComp W x)).1
    rw [ha]
    exact (IndependentFixedIndexedPointGraph.read_point_iff _ _ _ _ _).2 rfl
  · funext W x
    apply (IndependentFixedIndexedPointGraph.point_iff (forward f) hm.context (observable h)
      (points_of_native f h hm R hs ha ho).observableRows W.ctx x (R.observableComp W x)).1
    rw [ho]
    exact (IndependentFixedIndexedPointGraph.read_point_iff _ _ _ _ _).2 rfl

end

end AAT.AG.LocalSemanticReconstruction.IndependentGeometryHomPrimitive.RepresentativeRealization

#assert_standard_axioms_only AAT.AG.LocalSemanticReconstruction.IndependentGeometryHomPrimitive.RepresentativeRealization
