import ResearchLean.AG.LocalSemanticReconstruction.IndependentGeometryHomExplicitRealization
import Formal.Util.AssertStandardAxioms

/-!
# Recovery of explicit realization point queries

Implementation notes: all carrier directions and all actual-action queries
survive reconstruction. Candidate context equalities transport each point's
carrier; a reading only at the native pair would omit inactive query values.
Action recovery consumes the primitive action equations and the inactive-row
clauses, including inputs outside a chosen forward representative.
-/

namespace AAT.AG.LocalSemanticReconstruction.IndependentGeometryHomPrimitive.ExplicitRealization

noncomputable section

universe u v

open Site CategoryTheory AtomFoundation GeometryTransport RealizationReconstruction

variable {U : AtomCarrier.{u}} {P Q : AATCorePackage U}
variable (f : PackageTotalHom P Q)

/-- Read the support action at every pair of candidate target contexts. -/
def readActualSupport (R : ExplicitRealizationTransportSupply P Q f)
    (W X : ArchCtx P.object) (V Y : ArchCtx Q.object) (g : ContextMorphism W X)
    (y : V.Support) (z : Y.Support) : Bool := by
  classical
  exact if hw : forward f W = V then if hx : forward f X = Y then
    decide (cast (congrArg (fun Z => Z.Support) hx)
      ((R.contextMorphism (W := ⟨W⟩) (V := ⟨X⟩) g).supportMap
        (cast (congrArg (fun Z => Z.Support) hw.symm) y)) = z)
    else false else false

/-- Read the actual axis action, making either inactive context pair false. -/
def readActualAxis (R : ExplicitRealizationTransportSupply P Q f)
    (W X : ArchCtx P.object) (V Y : ArchCtx Q.object) (g : ContextMorphism W X)
    (y : V.Axis) (z : Y.Axis) : Bool := by
  classical
  exact if hw : forward f W = V then if hx : forward f X = Y then
    decide (cast (congrArg (fun Z => Z.Axis) hx)
      ((R.contextMorphism (W := ⟨W⟩) (V := ⟨X⟩) g).axisMap
        (cast (congrArg (fun Z => Z.Axis) hw.symm) y)) = z)
    else false else false

/-- Read every point of the contravariant actual observable action. -/
def readActualObservable (R : ExplicitRealizationTransportSupply P Q f)
    (W X : ArchCtx P.object) (V Y : ArchCtx Q.object) (g : ContextMorphism W X)
    (y : Y.Observable) (z : V.Observable) : Bool := by
  classical
  exact if hw : forward f W = V then if hx : forward f X = Y then
    decide (cast (congrArg (fun Z => Z.Observable) hw)
      ((R.contextMorphism (W := ⟨W⟩) (V := ⟨X⟩) g).observableRestrict
        (cast (congrArg (fun Z => Z.Observable) hx.symm) y)) = z)
    else false else false

/-- At the native context pair, support reading is equality with the actual image. -/
theorem readActualSupport_point_iff (R : ExplicitRealizationTransportSupply P Q f)
    (W X : ArchCtx P.object) (g : ContextMorphism W X)
    (y : (forward f W).Support) (z : (forward f X).Support) :
    readActualSupport f R W X (forward f W) (forward f X) g y z = true ↔
      (R.contextMorphism (W := ⟨W⟩) (V := ⟨X⟩) g).supportMap y = z := by
  classical
  simp [readActualSupport]

/-- At the native context pair, axis reading is equality with the actual image. -/
theorem readActualAxis_point_iff (R : ExplicitRealizationTransportSupply P Q f)
    (W X : ArchCtx P.object) (g : ContextMorphism W X)
    (y : (forward f W).Axis) (z : (forward f X).Axis) :
    readActualAxis f R W X (forward f W) (forward f X) g y z = true ↔
      (R.contextMorphism (W := ⟨W⟩) (V := ⟨X⟩) g).axisMap y = z := by
  classical
  simp [readActualAxis]

/-- At the native context pair, observable reading retains the actual reverse image. -/
theorem readActualObservable_point_iff (R : ExplicitRealizationTransportSupply P Q f)
    (W X : ArchCtx P.object) (g : ContextMorphism W X)
    (y : (forward f X).Observable) (z : (forward f W).Observable) :
    readActualObservable f R W X (forward f W) (forward f X) g y z = true ↔
      (R.contextMorphism (W := ⟨W⟩) (V := ⟨X⟩) g).observableRestrict y = z := by
  classical
  simp [readActualObservable]

variable (h : Table.{u, v} U .explicit) (hm : Maps f h) (hp : PointLaws P.object Q.object h)

/-- Support fiber reading recovers either original direction on every candidate context pair. -/
theorem read_support (d : Direction) :
    IndependentFixedIndexedPointGraph.read (forward f)
      (fun W => (assemble f h hm hp).supportEquiv ⟨W⟩) = support h d := by
  cases d with
  | forward => exact IndependentFixedIndexedPointGraph.read_assembleEquiv _ hm.context _ _ hp.supportRows
  | backward => exact IndependentFixedIndexedPointGraph.read_assembleEquiv_backward _ hm.context _ _ hp.supportRows

/-- Axis fiber reading recovers both inverse graph directions. -/
theorem read_axis (d : Direction) :
    IndependentFixedIndexedPointGraph.read (forward f)
      (fun W => (assemble f h hm hp).axisEquiv ⟨W⟩) = axis h d := by
  cases d with
  | forward => exact IndependentFixedIndexedPointGraph.read_assembleEquiv _ hm.context _ _ hp.axisRows
  | backward => exact IndependentFixedIndexedPointGraph.read_assembleEquiv_backward _ hm.context _ _ hp.axisRows

/-- Observable fiber reading recovers both inverse graph directions. -/
theorem read_observable (d : Direction) :
    IndependentFixedIndexedPointGraph.read (forward f)
      (fun W => (assemble f h hm hp).observableEquiv ⟨W⟩) = observable h d := by
  cases d with
  | forward => exact IndependentFixedIndexedPointGraph.read_assembleEquiv _ hm.context _ _ hp.observableRows
  | backward => exact IndependentFixedIndexedPointGraph.read_assembleEquiv_backward _ hm.context _ _ hp.observableRows

/-- All actual support action cells are recovered, including both kinds of inactive context pair. -/
theorem read_actualSupport : readActualSupport f (assemble f h hm hp) = actualSupport (A := P.object) (B := Q.object) h := by
  classical
  funext W X V Y g y z
  by_cases hw : forward f W = V
  · subst V
    by_cases hx : forward f X = Y
    · subst Y
      let x := (supportEquiv f h hm hp W).symm y
      have hpnt : support h .forward W (forward f W) x y = true :=
        (IndependentFixedIndexedPointGraph.point_iff _ hm.context _ hp.supportRows.forward W x y).2
          ((supportEquiv f h hm hp W).apply_symm_apply y)
      rw [hp.supportAction W X _ _ g x y z ((hm.context _ _).2 rfl) ((hm.context _ _).2 rfl) hpnt]
      apply Bool.eq_iff_iff.mpr
      exact (readActualSupport_point_iff f _ W X g y z).trans
        (IndependentFixedIndexedPointGraph.point_iff _ hm.context _ hp.supportRows.forward X (g.supportMap x) z).symm
    · have hn : contextPoints h X Y = false := Bool.eq_false_iff.mpr (fun hh => hx ((hm.context X Y).1 hh))
      rw [hp.supportInactive W X _ Y g y z (Or.inr hn)]
      simp [readActualSupport, hx]
  · have hn : contextPoints h W V = false := Bool.eq_false_iff.mpr (fun hh => hw ((hm.context W V).1 hh))
    rw [hp.supportInactive W X V Y g y z (Or.inl hn)]
    simp [readActualSupport, hw]

/-- Every actual axis action cell is recovered without assuming a chosen representative input. -/
theorem read_actualAxis : readActualAxis f (assemble f h hm hp) = actualAxis (A := P.object) (B := Q.object) h := by
  classical
  funext W X V Y g y z
  by_cases hw : forward f W = V
  · subst V
    by_cases hx : forward f X = Y
    · subst Y
      let x := (axisEquiv f h hm hp W).symm y
      have hpnt : axis h .forward W (forward f W) x y = true :=
        (IndependentFixedIndexedPointGraph.point_iff _ hm.context _ hp.axisRows.forward W x y).2
          ((axisEquiv f h hm hp W).apply_symm_apply y)
      rw [hp.axisAction W X _ _ g x y z ((hm.context _ _).2 rfl) ((hm.context _ _).2 rfl) hpnt]
      apply Bool.eq_iff_iff.mpr
      exact (readActualAxis_point_iff f _ W X g y z).trans
        (IndependentFixedIndexedPointGraph.point_iff _ hm.context _ hp.axisRows.forward X (g.axisMap x) z).symm
    · have hn : contextPoints h X Y = false := Bool.eq_false_iff.mpr (fun hh => hx ((hm.context X Y).1 hh))
      rw [hp.axisInactive W X _ Y g y z (Or.inr hn)]
      simp [readActualAxis, hx]
  · have hn : contextPoints h W V = false := Bool.eq_false_iff.mpr (fun hh => hw ((hm.context W V).1 hh))
    rw [hp.axisInactive W X V Y g y z (Or.inl hn)]
    simp [readActualAxis, hw]

/-- All actual observable action cells survive with their original contravariant direction. -/
theorem read_actualObservable : readActualObservable f (assemble f h hm hp) = actualObservable (A := P.object) (B := Q.object) h := by
  classical
  funext W X V Y g y z
  by_cases hw : forward f W = V
  · subst V
    by_cases hx : forward f X = Y
    · subst Y
      let x := (observableEquiv f h hm hp X).symm y
      have hpnt : observable h .forward X (forward f X) x y = true :=
        (IndependentFixedIndexedPointGraph.point_iff _ hm.context _ hp.observableRows.forward X x y).2
          ((observableEquiv f h hm hp X).apply_symm_apply y)
      rw [hp.observableAction W X _ _ g x y z ((hm.context _ _).2 rfl) ((hm.context _ _).2 rfl) hpnt]
      apply Bool.eq_iff_iff.mpr
      exact (readActualObservable_point_iff f _ W X g y z).trans
        (IndependentFixedIndexedPointGraph.point_iff _ hm.context _ hp.observableRows.forward W (g.observableRestrict x) z).symm
    · have hn : contextPoints h X Y = false := Bool.eq_false_iff.mpr (fun hh => hx ((hm.context X Y).1 hh))
      rw [hp.observableInactive W X _ Y g y z (Or.inr hn)]
      simp [readActualObservable, hx]
  · have hn : contextPoints h W V = false := Bool.eq_false_iff.mpr (fun hh => hw ((hm.context W V).1 hh))
    rw [hp.observableInactive W X V Y g y z (Or.inl hn)]
    simp [readActualObservable, hw]

end

end AAT.AG.LocalSemanticReconstruction.IndependentGeometryHomPrimitive.ExplicitRealization

#assert_standard_axioms_only AAT.AG.LocalSemanticReconstruction.IndependentGeometryHomPrimitive.ExplicitRealization
