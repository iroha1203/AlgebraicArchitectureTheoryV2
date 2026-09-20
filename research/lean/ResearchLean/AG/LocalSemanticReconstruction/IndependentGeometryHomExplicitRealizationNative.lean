import ResearchLean.AG.LocalSemanticReconstruction.IndependentGeometryHomExplicitRealizationPoints
import Formal.Util.AssertStandardAxioms

/-!
# Native recovery for explicit realization

Implementation notes: every native explicit supply yields all independent
carrier and action laws.
The comparison equalities here describe its reader; they are not extra local
fields. Reassembly recovers the actual context action as well as both
directions of all three carrier equivalences.
-/

namespace AAT.AG.LocalSemanticReconstruction.IndependentGeometryHomPrimitive.ExplicitRealization

noncomputable section

universe u v

open Site CategoryTheory AtomFoundation GeometryTransport RealizationReconstruction

variable {U : AtomCarrier.{u}} {P Q : AATCorePackage U}
variable (f : PackageTotalHom P Q) (h : Table.{u, v} U .explicit) (hm : Maps f h)
variable (R : ExplicitRealizationTransportSupply P Q f)
variable (hs : ∀ d, support h d = IndependentFixedIndexedPointGraph.read (forward f) (fun W => R.supportEquiv ⟨W⟩))
variable (ha : ∀ d, axis h d = IndependentFixedIndexedPointGraph.read (forward f) (fun W => R.axisEquiv ⟨W⟩))
variable (ho : ∀ d, observable h d = IndependentFixedIndexedPointGraph.read (forward f) (fun W => R.observableEquiv ⟨W⟩))
variable (hcs : actualSupport (A := P.object) (B := Q.object) h = readActualSupport f R)
variable (hca : actualAxis (A := P.object) (B := Q.object) h = readActualAxis f R)
variable (hco : actualObservable (A := P.object) (B := Q.object) h = readActualObservable f R)

include hm hs ha ho hcs hca hco in
/-- Every native explicit realization satisfies all primitive inverse, reading, and action conditions. -/
theorem points_of_native : PointLaws P.object Q.object h := by
  classical
  have sp : ∀ W x y, support h .forward W (forward f W) x y = true ↔ R.supportEquiv ⟨W⟩ x = y := by
    intro W x y
    rw [hs .forward]
    exact IndependentFixedIndexedPointGraph.read_point_iff _ _ _ _ _
  have ap : ∀ W x y, axis h .forward W (forward f W) x y = true ↔ R.axisEquiv ⟨W⟩ x = y := by
    intro W x y
    rw [ha .forward]
    exact IndependentFixedIndexedPointGraph.read_point_iff _ _ _ _ _
  have op : ∀ W x y, observable h .forward W (forward f W) x y = true ↔ R.observableEquiv ⟨W⟩ x = y := by
    intro W x y
    rw [ho .forward]
    exact IndependentFixedIndexedPointGraph.read_point_iff _ _ _ _ _
  constructor
  · rw [hs .forward, hs .backward]
    exact IndependentFixedIndexedPointGraph.read_inverseLaws _ hm.context _
  · rw [ha .forward, ha .backward]
    exact IndependentFixedIndexedPointGraph.read_inverseLaws _ hm.context _
  · rw [ho .forward, ho .backward]
    exact IndependentFixedIndexedPointGraph.read_inverseLaws _ hm.context _
  · intro W V x y a b hWV hxy hab
    obtain rfl := (hm.context W V).1 hWV
    obtain rfl := (sp W x y).1 hxy
    obtain rfl := (hm.atom a b).1 hab
    exact R.supportReads_iff ⟨W⟩ x a
  · intro W V x y hWV hxy
    obtain rfl := (hm.context W V).1 hWV
    obtain rfl := (ap W x y).1 hxy
    exact R.axisReads_iff ⟨W⟩ x
  · intro W V x y hWV hxy
    obtain rfl := (hm.context W V).1 hWV
    obtain rfl := (op W x y).1 hxy
    exact R.observableReads_iff ⟨W⟩ x
  · intro W X V Y g y z hn
    rw [hcs]
    rcases hn with hn | hn
    · have ne : forward f W ≠ V := fun he => Bool.noConfusion (hn.symm.trans ((hm.context W V).2 he))
      simp [readActualSupport, ne]
    · have ne : forward f X ≠ Y := fun he => Bool.noConfusion (hn.symm.trans ((hm.context X Y).2 he))
      simp [readActualSupport, ne]
  · intro W X V Y g y z hn
    rw [hca]
    rcases hn with hn | hn
    · have ne : forward f W ≠ V := fun he => Bool.noConfusion (hn.symm.trans ((hm.context W V).2 he))
      simp [readActualAxis, ne]
    · have ne : forward f X ≠ Y := fun he => Bool.noConfusion (hn.symm.trans ((hm.context X Y).2 he))
      simp [readActualAxis, ne]
  · intro W X V Y g y z hn
    rw [hco]
    rcases hn with hn | hn
    · have ne : forward f W ≠ V := fun he => Bool.noConfusion (hn.symm.trans ((hm.context W V).2 he))
      simp [readActualObservable, ne]
    · have ne : forward f X ≠ Y := fun he => Bool.noConfusion (hn.symm.trans ((hm.context X Y).2 he))
      simp [readActualObservable, ne]
  · intro W X V Y g x y z hWV hXY hxy
    obtain rfl := (hm.context W V).1 hWV
    obtain rfl := (hm.context X Y).1 hXY
    obtain rfl := (sp W x y).1 hxy
    rw [hcs]
    apply Bool.eq_iff_iff.mpr
    refine (readActualSupport_point_iff f R W X g _ z).trans ?_
    rw [R.support_naturality]
    exact (sp X (g.supportMap x) z).symm
  · intro W X V Y g x y z hWV hXY hxy
    obtain rfl := (hm.context W V).1 hWV
    obtain rfl := (hm.context X Y).1 hXY
    obtain rfl := (ap W x y).1 hxy
    rw [hca]
    apply Bool.eq_iff_iff.mpr
    refine (readActualAxis_point_iff f R W X g _ z).trans ?_
    rw [R.axis_naturality]
    exact (ap X (g.axisMap x) z).symm
  · intro W X V Y g x y z hWV hXY hxy
    obtain rfl := (hm.context W V).1 hWV
    obtain rfl := (hm.context X Y).1 hXY
    obtain rfl := (op X x y).1 hxy
    rw [hco]
    apply Bool.eq_iff_iff.mpr
    refine (readActualObservable_point_iff f R W X g _ z).trans ?_
    rw [R.observable_naturality]
    exact (op W (g.observableRestrict x) z).symm

include hs ha ho in
/-- Reassembly recovers every native field; naturality determines the complete actual context action. -/
theorem assemble_eq_native (hp : PointLaws P.object Q.object h) : assemble f h hm hp = R := by
  have es : ∀ W, supportEquiv f h hm hp W = R.supportEquiv ⟨W⟩ := by
    intro W
    apply Equiv.ext
    intro x
    apply (IndependentFixedIndexedPointGraph.point_iff (forward f) hm.context _ hp.supportRows.forward W x _).1
    rw [hs .forward]
    exact (IndependentFixedIndexedPointGraph.read_point_iff _ _ _ _ _).2 rfl
  have ea : ∀ W, axisEquiv f h hm hp W = R.axisEquiv ⟨W⟩ := by
    intro W
    apply Equiv.ext
    intro x
    apply (IndependentFixedIndexedPointGraph.point_iff (forward f) hm.context _ hp.axisRows.forward W x _).1
    rw [ha .forward]
    exact (IndependentFixedIndexedPointGraph.read_point_iff _ _ _ _ _).2 rfl
  have eo : ∀ W, observableEquiv f h hm hp W = R.observableEquiv ⟨W⟩ := by
    intro W
    apply Equiv.ext
    intro x
    apply (IndependentFixedIndexedPointGraph.point_iff (forward f) hm.context _ hp.observableRows.forward W x _).1
    rw [ho .forward]
    exact (IndependentFixedIndexedPointGraph.read_point_iff _ _ _ _ _).2 rfl
  apply IndependentExplicitRealization.read_injective
  funext q
  cases q with
  | support W x => exact congrArg (fun e => e x) (es W.ctx)
  | supportBack W y => exact congrArg (fun e => e.symm y) (es W.ctx)
  | axis W x => exact congrArg (fun e => e x) (ea W.ctx)
  | axisBack W y => exact congrArg (fun e => e.symm y) (ea W.ctx)
  | observable W x => exact congrArg (fun e => e x) (eo W.ctx)
  | observableBack W y => exact congrArg (fun e => e.symm y) (eo W.ctx)
  | @contextSupport W X g y =>
    change supportEquiv f h hm hp X.ctx (g.supportMap ((supportEquiv f h hm hp W.ctx).symm y)) =
      (R.contextMorphism g).supportMap y
    rw [es W.ctx, es X.ctx]
    have hn := R.support_naturality g ((R.supportEquiv W).symm y)
    rw [Equiv.apply_symm_apply] at hn
    exact hn.symm
  | @contextAxis W X g y =>
    change axisEquiv f h hm hp X.ctx (g.axisMap ((axisEquiv f h hm hp W.ctx).symm y)) =
      (R.contextMorphism g).axisMap y
    rw [ea W.ctx, ea X.ctx]
    have hn := R.axis_naturality g ((R.axisEquiv W).symm y)
    rw [Equiv.apply_symm_apply] at hn
    exact hn.symm
  | @contextObservable W X g y =>
    change observableEquiv f h hm hp W.ctx (g.observableRestrict ((observableEquiv f h hm hp X.ctx).symm y)) =
      (R.contextMorphism g).observableRestrict y
    rw [eo W.ctx, eo X.ctx]
    have hn := R.observable_naturality g ((R.observableEquiv X).symm y)
    rw [Equiv.apply_symm_apply] at hn
    exact hn.symm

/-- Reading a native explicit supply and rebuilding it is the identity on the complete supply. -/
theorem assemble_points_of_native :
    assemble f h hm (points_of_native f h hm R hs ha ho hcs hca hco) = R :=
  assemble_eq_native f h hm R hs ha ho _

end

end AAT.AG.LocalSemanticReconstruction.IndependentGeometryHomPrimitive.ExplicitRealization

#assert_standard_axioms_only AAT.AG.LocalSemanticReconstruction.IndependentGeometryHomPrimitive.ExplicitRealization
