import ResearchLean.AG.LocalSemanticReconstruction.IndependentGeometryHomNativeFamilies
import ResearchLean.AG.LocalSemanticReconstruction.IndependentGeometryHomExplicitRawRecovery
import ResearchLean.AG.LocalSemanticReconstruction.IndependentGeometryHomExplicitRealizationNative
import ResearchLean.AG.LocalSemanticReconstruction.IndependentGeometryHomRepresentativeRealizationNative
import Formal.Util.AssertStandardAxioms

/-!
# One common point reader for both original complete geometry Hom modes

Implementation notes: the shared reader fills dependent families after reading
their object, axis, and context indices. The two public native readers supply
only their original raw and realization actions to this same declaration.
Every response is a Boolean and inactive object candidates are normalized.
The projection APIs identify the exact tables used by the existing component
law and recovery theorems; complete-Hom law integration follows these APIs.
-/

namespace AAT.AG.LocalSemanticReconstruction.IndependentGeometryHomPrimitive.NativeReader

noncomputable section

universe u v

open Site CategoryTheory AtomFoundation GeometryTransport RealizationReconstruction

variable {U : AtomCarrier.{u}} {G H : GeometryPackage.{u, v} U} (mode : Mode)
variable (f : PackageTotalHom G.core H.core) (a : G.Coefficient →+* H.Coefficient)
variable (raw : RawQuery G.core.object H.core.object mode → Bool)
variable (realization : RealizationQuery G.core.object H.core.object mode → Bool)

/-- Fill every dependent native role at the actual endpoint pair. -/
def dependentRead : DependentQuery mode G.core.object H.core.object → Bool
  | .observable direction W V q => InverseRows.fromInverse
    (fun q => observableRows mode f a (.edge W V q)) direction q
  | .raw q => raw q
  | .realization q => realization q
  | q => dependentIndices mode f q

/-- Read all common Hom roles using the same scalar/index table and the three native dependent families. -/
def readWith : Table.{u, v} U mode
  | .operation A B A' B' q => operationRows mode f a (.edge (A, B) (A', B') q)
  | .signatureCoordinate direction I J i j q => InverseRows.fromInverse
    (fun q => signatureRows mode f a (.edge I J i j q)) direction q
  | .atObjects A B q => liftDependent mode G.core.object H.core.object
    (dependentRead mode f a raw realization) A B q
  | q => indices mode f a q

/-- The shared reader exposes every active dependent cell through its component reader. -/
theorem readWith_dependent (q : DependentQuery mode G.core.object H.core.object) :
    readWith mode f a raw realization (.atObjects _ _ q) = dependentRead mode f a raw realization q :=
  liftDependent_active mode _ _ _ q

/-- All dependent cells outside the original source/target object pair are false. -/
theorem readWith_inactive (A B : ArchitectureObject U) (q : DependentQuery mode A B)
    (hi : A ≠ G.core.object ∨ B ≠ H.core.object) :
    readWith mode f a raw realization (.atObjects A B q) = false :=
  liftDependent_inactive mode _ _ _ A B q hi

/-- The complete reader retains the original lower source graph. -/
theorem readWith_source : source (readWith mode f a raw realization) =
    IndependentCarrierGraph.read _ _ f.base.doctrineHom.sourceMap := rfl

/-- Both pointed Atom directions survive filling the other Hom roles. -/
theorem readWith_pointed : Atom.pointed (readWith mode f a raw realization) =
    Atom.read f.base.doctrineHom.atomEquiv := rfl

/-- The separate upper Atom directions are retained exactly. -/
theorem readWith_atom : Atom.upper (readWith mode f a raw realization) = Atom.read f.upper.atomEquiv := rfl

/-- Object points in the complete reader are precisely the original native object-map points. -/
theorem readWith_object_iff (A B : ArchitectureObject U) :
    readWith mode f a raw realization (.object A B) = true ↔ f.upper.objectMap A = B :=
  object_indices_iff mode f a A B

/-- The complete reader retains every native invariant-index candidate cell. -/
theorem readWith_invariant : invariant (readWith mode f a raw realization) =
    IndependentCarrierGraph.read _ _ f.upper.invariantMap := rfl

/-- The complete reader retains the directed native axis graph. -/
theorem readWith_axis : signatureAxis (readWith mode f a raw realization) =
    IndependentCarrierGraph.read _ _ f.upper.axisMap := rfl

/-- The coefficient role is precisely the original directed ring-hom graph. -/
theorem readWith_coefficient : coefficient (readWith mode f a raw realization) =
    IndependentCarrierGraph.read _ _ a := rfl

/-- The operation projection is the complete candidate endpoint/carrier reading already constructed. -/
theorem readWith_operation : Operation.points (readWith mode f a raw realization) = operationRows mode f a := by
  funext q
  cases q with
  | edge p p' q =>
    cases p
    cases p'
    rfl

/-- Signature projection keeps both directions and all candidate outer and inner carrier references. -/
theorem readWith_signature : Signature.points (readWith mode f a raw realization) = signatureRows mode f a := by
  funext q
  cases q with
  | edge I J i j q =>
    exact congrFun (InverseRows.asInverse_fromInverse (fun q => signatureRows mode f a (.edge I J i j q))) q

/-- All native equation-index graph cells occur at the original active object pair. -/
theorem readWith_equation : InverseRows.equation (readWith mode f a raw realization) G.core.object H.core.object =
    IndependentInverseGraph.read _ _ f.upper.equationEquiv := by
  funext q
  cases q with
  | forward q => exact readWith_dependent mode f a raw realization (.equation .forward q)
  | backward q =>
    have he := readWith_dependent mode f a raw realization (.equation .backward (InverseRows.reverse q))
    simpa only [dependentRead, dependentIndices, InverseRows.fromInverse, InverseRows.reverse_reverse] using he

/-- The complete reader preserves the native context-equivalence point table. -/
theorem readWith_context : Context.points (readWith mode f a raw realization) G.core.object H.core.object =
    Context.read G.core.contextPreorder H.core.contextPreorder f.upper.equationTransport.contextEquivalence := by
  funext direction W V
  exact readWith_dependent mode f a raw realization (.context direction W V)

/-- Observable projection exposes the complete candidate context/carrier family reading. -/
theorem readWith_observable : Observable.points (readWith mode f a raw realization) G.core.object H.core.object =
    observableRows mode f a := by
  funext q
  cases q with
  | edge W V q =>
    cases q with
    | forward q => exact readWith_dependent mode f a raw realization (.observable .forward W V q)
    | backward q =>
      have he := readWith_dependent mode f a raw realization (.observable .backward W V (InverseRows.reverse q))
      simpa only [dependentRead, InverseRows.fromInverse, InverseRows.reverse_reverse] using he

/-- Every raw cell is exactly the supplied native mode-specific point reader. -/
theorem readWith_raw (q : RawQuery G.core.object H.core.object mode) :
    readWith mode f a raw realization (.atObjects _ _ (.raw q)) = raw q :=
  readWith_dependent mode f a raw realization (.raw q)

/-- Every realization cell is exactly its original directed or explicit action reading. -/
theorem readWith_realization (q : RealizationQuery G.core.object H.core.object mode) :
    readWith mode f a raw realization (.atObjects _ _ (.realization q)) = realization q :=
  readWith_dependent mode f a raw realization (.realization q)

/-- Read all directed representative realization actions at every candidate context pair. -/
def representativeRealizationRead (R : RealizationTransportSupply G.core H.core f) :
    RealizationQuery G.core.object H.core.object .representative → Bool
  | .representativeSupport W V x y => IndependentFixedIndexedPointGraph.read (RepresentativeRealization.forward f)
    (fun W => R.supportComp ⟨W⟩) W V x y
  | .representativeAxis W V x y => IndependentFixedIndexedPointGraph.read (RepresentativeRealization.forward f)
    (fun W => R.axisComp ⟨W⟩) W V x y
  | .representativeObservable W V x y => IndependentFixedIndexedPointGraph.read (RepresentativeRealization.forward f)
    (fun W => R.observableComp ⟨W⟩) W V x y

/-- Read explicit fiber points and every actual context-morphism action in its original direction. -/
def explicitRealizationRead (R : ExplicitRealizationTransportSupply G.core H.core f) :
    RealizationQuery G.core.object H.core.object .explicit → Bool
  | .explicitSupport _ W V x y => IndependentFixedIndexedPointGraph.read (ExplicitRealization.forward f)
    (fun W => R.supportEquiv ⟨W⟩) W V x y
  | .explicitAxis _ W V x y => IndependentFixedIndexedPointGraph.read (ExplicitRealization.forward f)
    (fun W => R.axisEquiv ⟨W⟩) W V x y
  | .explicitObservable _ W V x y => IndependentFixedIndexedPointGraph.read (ExplicitRealization.forward f)
    (fun W => R.observableEquiv ⟨W⟩) W V x y
  | .actualSupport W X V Y g x y => ExplicitRealization.readActualSupport f R W X V Y g x y
  | .actualAxis W X V Y g x y => ExplicitRealization.readActualAxis f R W X V Y g x y
  | .actualObservable W X V Y g x y => ExplicitRealization.readActualObservable f R W X V Y g x y

/-- Read an arbitrary original representative complete geometry Hom into the common primitive declaration. -/
def readRepresentative (F : GeometryTotalHom G H) : Table.{u, v} U .representative :=
  readWith .representative F.base F.geometry.coefficientHom (fun q => nomatch q)
    (representativeRealizationRead F.base (CompleteGeometryGraphAssembly.realizationSupplyOfGeometry F.geometry))

/-- Read an arbitrary original explicit complete geometry Hom with all raw and actual-action fields retained. -/
def readExplicit (F : ExplicitExactGeometryHom G H) : Table.{u, v} U .explicit :=
  readWith .explicit F.base F.coefficientHom (ExplicitRaw.readRaw F.base F.coefficientHom F.raw)
    (explicitRealizationRead F.base F.realization)

end

end AAT.AG.LocalSemanticReconstruction.IndependentGeometryHomPrimitive.NativeReader

#assert_standard_axioms_only AAT.AG.LocalSemanticReconstruction.IndependentGeometryHomPrimitive.NativeReader
