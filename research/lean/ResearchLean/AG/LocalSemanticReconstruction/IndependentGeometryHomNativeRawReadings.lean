import ResearchLean.AG.LocalSemanticReconstruction.IndependentGeometryHomNativeRecovery
import ResearchLean.AG.LocalSemanticReconstruction.IndependentGeometryHomExplicitRawRecovery
import Formal.Util.AssertStandardAxioms

/-!
# Native explicit raw maps on the common Hom reader

The raw projections of the common reader are the original all-candidate
coordinate, relation, and local-data readings. These comparisons discharge
the existing raw converse's map and row premises. Both directions retain
source/target query order and every inactive carrier and context candidate.
-/

namespace AAT.AG.LocalSemanticReconstruction.IndependentGeometryHomPrimitive.NativeReader

noncomputable section

universe u v

open Site CategoryTheory AtomFoundation GeometryTransport LawAlgebra RealizationReconstruction

variable {U : AtomCarrier.{u}} {G H : GeometryPackage.{u, v} U}
variable (f : PackageTotalHom G.core H.core) (a : G.Coefficient →+* H.Coefficient)
variable (raw : RawQuery G.core.object H.core.object .explicit → Bool)
variable (realization : RealizationQuery G.core.object H.core.object .explicit → Bool)

/-- The common reader supplies exactly the original inverse-context and directed coefficient points. -/
theorem readWith_explicitRaw_maps : ExplicitRaw.Maps f a (readWith .explicit f a raw realization) where
  context := readWith_context_backward_point_iff .explicit f a raw realization
  coefficient := readWith_coefficient_point_iff .explicit f a raw realization

variable (R : RawAmbientRestrictionSystemExactMapAgainst G.site H.site (coreContextInverse f) a G.raw H.raw)

/-- Every coordinate graph cell of the common reader is the original native all-candidate reading. -/
theorem readWith_raw_coordinate (W : ArchCtx G.core.object) (V : ArchCtx H.core.object) :
    ExplicitRaw.readCoordinate R W V = InverseRows.coordinate
      (readWith .explicit f a (ExplicitRaw.readRaw f a R) realization) G.core.object H.core.object W V := by
  symm
  funext q
  cases q with
  | forward q => exact readWith_raw .explicit f a (ExplicitRaw.readRaw f a R) realization (.coordinate .forward W V q)
  | backward q =>
    have he := readWith_raw .explicit f a (ExplicitRaw.readRaw f a R) realization
      (.coordinate .backward W V (InverseRows.reverse q))
    simpa only [ExplicitRaw.readRaw, InverseRows.fromInverse, InverseRows.reverse_reverse] using he

/-- Every relation graph cell retains the original native generator equivalence, including inactive candidates. -/
theorem readWith_raw_relation (W : ArchCtx G.core.object) (V : ArchCtx H.core.object) :
    ExplicitRaw.readRelation R W V = InverseRows.relation
      (readWith .explicit f a (ExplicitRaw.readRaw f a R) realization) G.core.object H.core.object W V := by
  symm
  funext q
  cases q with
  | forward q => exact readWith_raw .explicit f a (ExplicitRaw.readRaw f a R) realization (.relation .forward W V q)
  | backward q =>
    have he := readWith_raw .explicit f a (ExplicitRaw.readRaw f a R) realization
      (.relation .backward W V (InverseRows.reverse q))
    simpa only [ExplicitRaw.readRaw, InverseRows.fromInverse, InverseRows.reverse_reverse] using he

/-- Every dependent local-data row retains both original graph directions at all candidate coordinate references. -/
theorem readWith_raw_localData (W : ArchCtx G.core.object) (V : ArchCtx H.core.object)
    (C D : Type u) (c : C) (d : D) :
    ExplicitRaw.readLocalData R W V C D c d = InverseRows.localData
      (readWith .explicit f a (ExplicitRaw.readRaw f a R) realization) G.core.object H.core.object W V C D c d := by
  symm
  funext q
  cases q with
  | forward q => exact readWith_raw .explicit f a (ExplicitRaw.readRaw f a R) realization (.localData .forward W V C D c d q)
  | backward q =>
    have he := readWith_raw .explicit f a (ExplicitRaw.readRaw f a R) realization
      (.localData .backward W V C D c d (InverseRows.reverse q))
    simpa only [ExplicitRaw.readRaw, InverseRows.fromInverse, InverseRows.reverse_reverse] using he

/-- An arbitrary original explicit raw map supplies every primitive raw law on this same common reader. -/
theorem readWith_explicitRaw_points : ExplicitRaw.NativePoints G H
    (readWith .explicit f a (ExplicitRaw.readRaw f a R) realization) :=
  ExplicitRaw.points_of_native f a R _ (readWith_explicitRaw_maps f a _ realization)
    (readWith_raw_coordinate f a realization R) (readWith_raw_relation f a realization R)
    (readWith_raw_localData f a realization R)

/-- Raw assembly on the common reader recovers every original native coordinate, relation, and local-data component. -/
theorem readWith_explicitRaw_assemble : ExplicitRaw.assemble f a
    (readWith .explicit f a (ExplicitRaw.readRaw f a R) realization)
    (readWith_explicitRaw_maps f a _ realization) (readWith_explicitRaw_points f a realization R) = R :=
  ExplicitRaw.assemble_eq_native f a R _ (readWith_explicitRaw_maps f a _ realization)
    (readWith_raw_coordinate f a realization R) (readWith_raw_relation f a realization R)
    (readWith_raw_localData f a realization R) _

end

end AAT.AG.LocalSemanticReconstruction.IndependentGeometryHomPrimitive.NativeReader

#assert_standard_axioms_only AAT.AG.LocalSemanticReconstruction.IndependentGeometryHomPrimitive.NativeReader
