import ResearchLean.AG.LocalSemanticReconstruction.IndependentGeometryHomNativeReader
import ResearchLean.AG.LocalSemanticReconstruction.IndependentGeometryHomInvariantQuotient
import Formal.Util.AssertStandardAxioms

/-!
# Reading native complete Hom points through invariant witness erasure

Implementation notes: the existing native invariant transport property supplies
the auxiliary coherent presentation for the common Boolean reader. The existing
quotient erases those auxiliary choices and retains every original query. Adding
a selected invariant-value equivalence to the native Hom would change its data,
so this construction uses the original existence property instead. The local
class below discharges invariant presentation laws; the remaining complete Hom
point laws are separate obligations.
-/

namespace AAT.AG.LocalSemanticReconstruction.IndependentGeometryHomPrimitive.NativeReader

noncomputable section

universe u v

open Site CategoryTheory AtomFoundation GeometryTransport RealizationReconstruction

variable {U : AtomCarrier.{u}} {G H : GeometryPackage.{u, v} U} (mode : Mode)
variable (f : PackageTotalHom G.core H.core) (a : G.Coefficient →+* H.Coefficient)
variable (raw : RawQuery G.core.object H.core.object mode → Bool)
variable (realization : RealizationQuery G.core.object H.core.object mode → Bool)

/-- The complete reader supplies total, unique native object rows without an object inverse. -/
theorem readWith_object_rows : CoreLaws.ObjectRows (readWith mode f a raw realization) := by
  intro A
  refine ⟨f.upper.objectMap A, (readWith_object_iff mode f a raw realization A _).2 rfl, ?_⟩
  intro B hB
  exact ((readWith_object_iff mode f a raw realization A B).1 hB).symm

/-- Restrict all native query responses to finite sets while retaining their object and index rows. -/
def retainedWith : InvariantWitness.Retained.{u, v}
    G.core.reading.invariantReading H.core.reading.invariantReading mode where
  family := TagChange.read (readWith mode f a raw realization)
  objectRows := readWith_object_rows mode f a raw realization
  indexRows := IndependentCarrierGraph.read_isLawful _ _ f.upper.invariantMap

/-- Finite restriction and singleton assembly preserve the entire common native table. -/
theorem retainedWith_table : (retainedWith mode f a raw realization).table =
    readWith mode f a raw realization :=
  TagChange.assemble_read (readWith mode f a raw realization)

/-- The retained object action recovers the actual native object action. -/
theorem retainedWith_objectMap : (retainedWith mode f a raw realization).objectMap =
    f.upper.objectMap := by
  funext A
  apply ((retainedWith mode f a raw realization).object_point_iff A _).1
  rw [retainedWith_table]
  exact (readWith_object_iff mode f a raw realization A _).2 rfl

/-- The retained directed invariant-index graph recovers the actual native index action. -/
theorem retainedWith_indexMap : (retainedWith mode f a raw realization).indexMap =
    f.upper.invariantMap :=
  IndependentCarrierGraph.assemble_read _ _ f.upper.invariantMap

/-- The original native invariant existence property holds on the recovered object and index points. -/
def nativeWith : InvariantWitness.Native.{u, v}
    G.core.reading.invariantReading H.core.reading.invariantReading mode := by
  refine ⟨retainedWith mode f a raw realization, ?_⟩
  rw [retainedWith_indexMap, retainedWith_objectMap]
  exact f.upper.invariant_transport

/-- Supply the coherent invariant presentation and erase auxiliary choices for every common native query. -/
def localWith : InvariantWitness.Local.{u, v}
    G.core.reading.invariantReading H.core.reading.invariantReading mode :=
  InvariantWitness.read _ _ (nativeWith mode f a raw realization)

/-- Witness erasure preserves the entire coherent family, including raw and realization points. -/
theorem retained_localWith : InvariantWitness.retained _ _ (localWith mode f a raw realization) =
    retainedWith mode f a raw realization := rfl

/-- Every original common query survives the native invariant presentation and quotient. -/
theorem point_localWith (q : Query.{u, v} U mode) :
    InvariantWitness.point _ _ (localWith mode f a raw realization) q =
      readWith mode f a raw realization q :=
  (InvariantWitness.point_read _ _ (nativeWith mode f a raw realization) q).trans
    (congrFun (retainedWith_table mode f a raw realization) q)

/-- Invariant assembly restores the native existence property together with all retained finite points. -/
theorem assemble_localWith : InvariantWitness.assemble _ _ (localWith mode f a raw realization) =
    nativeWith mode f a raw realization :=
  InvariantWitness.assemble_read _ _ (nativeWith mode f a raw realization)

/-- Read a representative native Hom into its invariant quotient with the original directed realization data. -/
def localRepresentative (F : GeometryTotalHom G H) : InvariantWitness.Local.{u, v}
    G.core.reading.invariantReading H.core.reading.invariantReading .representative :=
  localWith .representative F.base F.geometry.coefficientHom (fun q => nomatch q)
    (representativeRealizationRead F.base (CompleteGeometryGraphAssembly.realizationSupplyOfGeometry F.geometry))

/-- Read an explicit native Hom into the same invariant quotient, retaining raw and actual-action queries. -/
def localExplicit (F : ExplicitExactGeometryHom G H) : InvariantWitness.Local.{u, v}
    G.core.reading.invariantReading H.core.reading.invariantReading .explicit :=
  localWith .explicit F.base F.coefficientHom (ExplicitRaw.readRaw F.base F.coefficientHom F.raw)
    (explicitRealizationRead F.base F.realization)

/-- Every representative native query is unchanged by auxiliary invariant choice erasure. -/
theorem point_localRepresentative (F : GeometryTotalHom G H) (q : Query.{u, v} U .representative) :
    InvariantWitness.point _ _ (localRepresentative F) q = readRepresentative F q :=
  point_localWith .representative F.base F.geometry.coefficientHom (fun q => nomatch q)
    (representativeRealizationRead F.base (CompleteGeometryGraphAssembly.realizationSupplyOfGeometry F.geometry)) q

/-- Every explicit native query is unchanged by auxiliary invariant choice erasure. -/
theorem point_localExplicit (F : ExplicitExactGeometryHom G H) (q : Query.{u, v} U .explicit) :
    InvariantWitness.point _ _ (localExplicit F) q = readExplicit F q :=
  point_localWith .explicit F.base F.coefficientHom (ExplicitRaw.readRaw F.base F.coefficientHom F.raw)
    (explicitRealizationRead F.base F.realization) q

end

end AAT.AG.LocalSemanticReconstruction.IndependentGeometryHomPrimitive.NativeReader

#assert_standard_axioms_only AAT.AG.LocalSemanticReconstruction.IndependentGeometryHomPrimitive.NativeReader
