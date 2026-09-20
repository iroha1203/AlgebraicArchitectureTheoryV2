import ResearchLean.AG.LocalSemanticReconstruction.IndependentGeometryHomLocalCompositionLaws

/-!
# Direct primitive identity tables for complete geometry Homs

The common Hom identity is constructed from object, carrier, dependent,
raw, and realization identity rows before comparison with either completed
Hom interface. The comparison theorems show that both the representative and
explicit readings recover the corresponding native identity exactly.

Implementation notes: every mode-specific raw and realization response is
constructed before the native comparison. Defining the table by reading a
completed identity Hom would hide the primitive identity construction.
-/

namespace AAT.AG.LocalSemanticReconstruction.IndependentGeometryHomPrimitive.Identity

noncomputable section

universe u v

open Site CategoryTheory AtomFoundation GeometryTransport RealizationReconstruction
open IndependentGeometryTableAssembly

variable {U : AtomCarrier.{u}}

/-- Diagonal inverse graph used by the direct equation and raw identity rows. -/
def inverseIdentity (X : Type u) : IndependentInverseGraph.Table.{u, u} :=
  IndependentInverseGraph.read X X (Equiv.refl X)

/-- The inverse-context action of the primitive core identity is definitionally
the identity on context references. -/
@[simp] theorem explicitRaw_inverse_id (G : GeometryPackage.{u, v} U)
    (W : ArchCtx G.core.object) :
    ExplicitRaw.inverse (PackageTotalHom.id G.core) W = W := rfl

/-- The full context object selected by the inverse identity functor is the
input context object itself. -/
@[simp] theorem coreContextInverse_id_obj (G : GeometryPackage.{u, v} U)
    (W : ContextCategoryObject G.core.contextPreorder) :
    (coreContextInverse (PackageTotalHom.id G.core)).obj W = W := rfl

/-- One directed coordinate point of the raw identity, constructed directly
from the diagonal graph on the declared coordinate carrier. -/
def rawCoordinate (G : GeometryPackage.{u, v} U) (direction : Direction)
    (W V : ArchCtx G.core.object) (q : IndependentCarrierGraph.Query.{u, u}) : Bool := by
  classical
  by_cases h : W = V
  · subst V
    exact InverseRows.fromInverse
      (IndependentInverseGraph.read _ _
        (Equiv.refl (G.raw.coordFamily ⟨W⟩).Coord)) direction q
  · exact false

/-- One directed relation point of the raw identity, constructed directly
from the diagonal graph on the declared relation carrier. -/
def rawRelation (G : GeometryPackage.{u, v} U) (direction : Direction)
    (W V : ArchCtx G.core.object) (q : IndependentCarrierGraph.Query.{u, u}) : Bool := by
  classical
  by_cases h : W = V
  · subst V
    exact InverseRows.fromInverse
      (IndependentInverseGraph.read _ _
        (Equiv.refl (G.raw.relationFamily ⟨W⟩).Relation)) direction q
  · exact false

/-- One directed dependent local-data point of the raw identity.  The row is
active only at the declared coordinate carriers and the diagonal coordinate
point, after which it is the diagonal graph on the dependent local-data
carrier. -/
def rawLocalData (G : GeometryPackage.{u, v} U) (direction : Direction)
    (W V : ArchCtx G.core.object) (C D : Type u) (c : C) (d : D)
    (q : IndependentCarrierGraph.Query.{u, u}) : Bool := by
  classical
  by_cases hW : W = V
  · subst V
    by_cases hC : C = (G.raw.coordFamily ⟨W⟩).Coord
    · subst C
      by_cases hD : D = (G.raw.coordFamily ⟨W⟩).Coord
      · subst D
        by_cases hd : c = d
        · subst d
          exact InverseRows.fromInverse
            (IndependentInverseGraph.read _ _
              (Equiv.refl ((G.raw.coordFamily ⟨W⟩).LocalData c))) direction q
        · exact false
      · exact false
    · exact false
  · exact false

/-- Direct diagonal rows for the three representative realization families. -/
def representativeRealization (G : GeometryPackage.{u, v} U) :
    RealizationQuery G.core.object G.core.object .representative → Bool
  | .representativeSupport W V x y => by
      classical
      exact if h : W = V then decide (cast (congrArg (fun Z => Z.Support) h) x = y) else false
  | .representativeAxis W V x y => by
      classical
      exact if h : W = V then decide (cast (congrArg (fun Z => Z.Axis) h) x = y) else false
  | .representativeObservable W V x y => by
      classical
      exact if h : W = V then decide (cast (congrArg (fun Z => Z.Observable) h) x = y) else false

/-- Direct diagonal fiber rows and actual context-action values for explicit realization. -/
def explicitRealization (G : GeometryPackage.{u, v} U) :
    RealizationQuery G.core.object G.core.object .explicit → Bool
  | .explicitSupport _ W V x y => by
      classical
      exact if h : W = V then decide (cast (congrArg (fun Z => Z.Support) h) x = y) else false
  | .explicitAxis _ W V x y => by
      classical
      exact if h : W = V then decide (cast (congrArg (fun Z => Z.Axis) h) x = y) else false
  | .explicitObservable _ W V x y => by
      classical
      exact if h : W = V then decide (cast (congrArg (fun Z => Z.Observable) h) x = y) else false
  | .actualSupport W X V Y g x y => by
      classical
      by_cases hW : W = V
      · subst V
        by_cases hX : X = Y
        · subst Y
          exact decide (g.supportMap x = y)
        · exact false
      · exact false
  | .actualAxis W X V Y g x y => by
      classical
      by_cases hW : W = V
      · subst V
        by_cases hX : X = Y
        · subst Y
          exact decide (g.axisMap x = y)
        · exact false
      · exact false
  | .actualObservable W X V Y g x y => by
      classical
      by_cases hW : W = V
      · subst V
        by_cases hX : X = Y
        · subst Y
          exact decide (g.observableRestrict x = y)
        · exact false
      · exact false

/-- Direct explicit raw identity on every coordinate, relation, and local-data query. -/
def explicitRaw (G : GeometryPackage.{u, v} U) :
    RawQuery G.core.object G.core.object .explicit → Bool
  | .coordinate d W V q => rawCoordinate G d W V q
  | .localData d W V C D c e q => rawLocalData G d W V C D c e q
  | .relation d W V q => rawRelation G d W V q

/-- Direct identity rows for equation and context indices before filling their values. -/
def dependentIndicesIdentity (mode : Mode) (G : GeometryPackage.{u, v} U) :
    DependentQuery mode G.core.object G.core.object → Bool
  | .equation d q => InverseRows.fromInverse
      (inverseIdentity G.core.equationSystem.Index) d q
  | .context d W V => Context.identity G.core.object d W V
  | _ => false

theorem dependentIndicesIdentity_eq_native (mode : Mode) (G : GeometryPackage.{u, v} U) :
    dependentIndicesIdentity mode G =
      NativeReader.dependentIndices mode (PackageTotalHom.id G.core) := by
  funext q
  cases q with
  | equation d q => rfl
  | context d W V =>
      exact congrFun (congrFun (congrFun (Context.identity_eq_read G.core.contextPreorder) d) W) V
  | observable d W V q => rfl
  | raw q => rfl
  | realization q => rfl

/-- Direct identity table for all scalar and dependent index constructors. -/
def indicesIdentity (mode : Mode) (G : GeometryPackage.{u, v} U) : Table.{u, v} U mode := by
  classical
  intro q
  cases q with
  | source q => exact IndependentCarrierGraph.identity G.core.reading.doctrine.Source q
  | pointedAtom d a b => exact Atom.identity d a b
  | atom d a b => exact Atom.identity d a b
  | object A B => exact decide (A = B)
  | invariant q => exact IndependentCarrierGraph.identity G.core.reading.invariantReading.Index q
  | signatureAxis q => exact IndependentCarrierGraph.identity G.core.algebra.signatureReading.Axis q
  | coefficient q => exact IndependentCarrierGraph.identity G.Coefficient q
  | familyTransport F F' => exact decide (F' = F.transport (Equiv.refl U.Atom))
  | configurationTransport C C' => exact decide (C' = C.transport (Equiv.refl U.Atom))
  | atObjects A B q =>
      exact NativeReader.liftDependent mode G.core.object G.core.object
        (dependentIndicesIdentity mode G) A B q
  | _ => exact false

theorem indicesIdentity_eq_native (mode : Mode) (G : GeometryPackage.{u, v} U) :
    indicesIdentity mode G = NativeReader.indices mode (PackageTotalHom.id G.core)
      (RingHom.id G.Coefficient) := by
  funext q
  cases q with
  | source q => rfl
  | pointedAtom d a b => rfl
  | atom d a b => rfl
  | object A B => rfl
  | invariant q => rfl
  | operation A B A' B' q => rfl
  | signatureAxis q => rfl
  | signatureCoordinate d I J i j q => rfl
  | coefficient q => rfl
  | familyTransport F F' => rfl
  | configurationTransport C C' => rfl
  | atObjects A B q =>
      simp only [indicesIdentity, NativeReader.indices]
      rw [dependentIndicesIdentity_eq_native]

/-- The direct object identity rows are total and single-valued. -/
theorem objectRowsIdentity (mode : Mode) (G : GeometryPackage.{u, v} U) :
    CoreLaws.ObjectRows (indicesIdentity mode G) := by
  intro A
  refine ⟨A, ?_, ?_⟩
  · simp [indicesIdentity]
  · intro B hB
    exact (by simpa [indicesIdentity] using hB : A = B).symm

theorem objectMapIdentity (mode : Mode) (G : GeometryPackage.{u, v} U) :
    CoreLaws.objectMap (indicesIdentity mode G) (objectRowsIdentity mode G) = id := by
  funext A
  apply (CoreLaws.objectGraph (indicesIdentity mode G) (objectRowsIdentity mode G)).target_eq_of_edge
  change indicesIdentity mode G (.object A A) = true
  simp [indicesIdentity]

/-- Reindex the native operation family along the proved identity object map. -/
def operationFamilyIdentity (mode : Mode) (G : GeometryPackage.{u, v} U) :
    ∀ A B, G.core.reading.operationReading.Op A B →
      G.core.reading.operationReading.Op
        (CoreLaws.objectMap (indicesIdentity mode G) (objectRowsIdentity mode G) A)
        (CoreLaws.objectMap (indicesIdentity mode G) (objectRowsIdentity mode G) B) :=
  cast (congrArg (fun F => ∀ A B, G.core.reading.operationReading.Op A B →
    G.core.reading.operationReading.Op (F A) (F B))
      (objectMapIdentity mode G)).symm (fun _ _ x => x)

/-- Read the reindexed identity operation family into primitive rows. -/
def operationRowsIdentity (mode : Mode) (G : GeometryPackage.{u, v} U) :=
  (Operation.readingEquiv (indicesIdentity mode G) (objectRowsIdentity mode G)
    G.core.reading.operationReading.Op G.core.reading.operationReading.Op
    (operationFamilyIdentity mode G)).val

theorem operationFamilyIdentity_heq (mode : Mode) (G : GeometryPackage.{u, v} U) :
    HEq (operationFamilyIdentity mode G)
      ((fun _ _ x => x) : ∀ A B, G.core.reading.operationReading.Op A B →
        G.core.reading.operationReading.Op A B) := cast_heq _ _

theorem operationRowsIdentity_eq_native (mode : Mode) (G : GeometryPackage.{u, v} U) :
    operationRowsIdentity mode G = NativeReader.operationRows mode
      (PackageTotalHom.id G.core) (RingHom.id G.Coefficient) := by
  unfold operationRowsIdentity NativeReader.operationRows
  congr 1

/-- The direct signature-axis identity graph is lawful. -/
theorem axisRowsIdentity (mode : Mode) (G : GeometryPackage.{u, v} U) :
    IndependentCarrierGraph.IsLawful G.core.algebra.signatureReading.Axis
      G.core.algebra.signatureReading.Axis (signatureAxis (indicesIdentity mode G)) := by
  change IndependentCarrierGraph.IsLawful _ _
    (IndependentCarrierGraph.identity G.core.algebra.signatureReading.Axis)
  exact IndependentCarrierGraph.identity_isLawful _

theorem axisMapIdentity (mode : Mode) (G : GeometryPackage.{u, v} U) :
    Signature.axisMap (indicesIdentity mode G) _ _ (axisRowsIdentity mode G) = id := by
  exact IndependentCarrierGraph.assemble_identity _

/-- Reindex the signature coordinate family along the proved identity axis map. -/
def signatureFamilyIdentity (mode : Mode) (G : GeometryPackage.{u, v} U) :
    ∀ i, G.core.algebra.signatureReading.Coordinate i ≃
      G.core.algebra.signatureReading.Coordinate
        (Signature.axisMap (indicesIdentity mode G) _ _ (axisRowsIdentity mode G) i) :=
  cast (congrArg (fun F => ∀ i, G.core.algebra.signatureReading.Coordinate i ≃
    G.core.algebra.signatureReading.Coordinate (F i))
      (axisMapIdentity mode G)).symm (fun _ => Equiv.refl _)

/-- Read the reindexed identity signature family into primitive rows. -/
def signatureRowsIdentity (mode : Mode) (G : GeometryPackage.{u, v} U) :=
  (Signature.readingEquiv (indicesIdentity mode G) _ _ (axisRowsIdentity mode G)
    G.core.algebra.signatureReading.Coordinate G.core.algebra.signatureReading.Coordinate
    (signatureFamilyIdentity mode G)).val

theorem signatureRowsIdentity_eq_native (mode : Mode) (G : GeometryPackage.{u, v} U) :
    signatureRowsIdentity mode G = NativeReader.signatureRows mode
      (PackageTotalHom.id G.core) (RingHom.id G.Coefficient) := by
  unfold signatureRowsIdentity NativeReader.signatureRows
  congr 1

theorem contextPointsIdentity (mode : Mode) (G : GeometryPackage.{u, v} U) :
    Context.points (indicesIdentity mode G) G.core.object G.core.object =
      Context.identity G.core.object := by
  funext d W V
  simp [Context.points, indicesIdentity, NativeReader.liftDependent,
    dependentIndicesIdentity]

/-- The direct bidirectional context identity rows are lawful. -/
theorem contextRowsIdentity (mode : Mode) (G : GeometryPackage.{u, v} U) :
    Context.IsLawful G.core.contextPreorder.le G.core.contextPreorder.le
      (Context.points (indicesIdentity mode G) G.core.object G.core.object) := by
  rw [contextPointsIdentity]
  exact Context.identity_isLawful G.core.contextPreorder

theorem contextAssembleIdentity (mode : Mode) (G : GeometryPackage.{u, v} U) :
    Context.assemble G.core.contextPreorder G.core.contextPreorder
      (Context.points (indicesIdentity mode G) G.core.object G.core.object)
      (contextRowsIdentity mode G) = CategoryTheory.Equivalence.refl := by
  have he : (⟨Context.points (indicesIdentity mode G) G.core.object G.core.object,
      contextRowsIdentity mode G⟩ :
      {p // Context.IsLawful G.core.contextPreorder.le G.core.contextPreorder.le p}) =
      ⟨Context.identity G.core.object, Context.identity_isLawful G.core.contextPreorder⟩ :=
    Subtype.ext (contextPointsIdentity mode G)
  exact (congrArg (Context.readingEquiv G.core.contextPreorder G.core.contextPreorder).symm he).trans
    (Context.assemble_identity G.core.contextPreorder)

/-- Reindex observable rings along the assembled identity context equivalence. -/
def observableFamilyIdentity (mode : Mode) (G : GeometryPackage.{u, v} U) :
    ∀ W : ContextCategoryObject G.core.contextPreorder,
      G.core.equationSystem.Observable W ≃+*
        G.core.equationSystem.Observable
          ((Context.assemble G.core.contextPreorder G.core.contextPreorder
            (Context.points (indicesIdentity mode G) G.core.object G.core.object)
            (contextRowsIdentity mode G)).functor.obj W) :=
  cast (congrArg (fun E : ContextCategoryObject G.core.contextPreorder ≌
      ContextCategoryObject G.core.contextPreorder =>
        ∀ W, G.core.equationSystem.Observable W ≃+*
          G.core.equationSystem.Observable (E.functor.obj W))
      (contextAssembleIdentity mode G)).symm (fun _ => RingEquiv.refl _)

/-- Read the reindexed observable identity family into primitive rows. -/
def observableRowsIdentity (mode : Mode) (G : GeometryPackage.{u, v} U) :=
  (Observable.readingEquiv G.core.contextPreorder G.core.contextPreorder
    (indicesIdentity mode G) (contextRowsIdentity mode G)
    (fun W => G.core.equationSystem.Observable ⟨W⟩)
    (fun V => G.core.equationSystem.Observable ⟨V⟩)
    (observableFamilyIdentity mode G)).val

theorem observableFamilyIdentity_heq (mode : Mode) (G : GeometryPackage.{u, v} U) :
    HEq (observableFamilyIdentity mode G)
      ((fun _ => RingEquiv.refl _) : ∀ W : ContextCategoryObject G.core.contextPreorder,
        G.core.equationSystem.Observable W ≃+* G.core.equationSystem.Observable W) := cast_heq _ _

theorem observableReadingVal_congr (mode : Mode) (G : GeometryPackage.{u, v} U)
    (h k : Table.{u, v} U mode) (he : h = k)
    (hh : Context.IsLawful G.core.contextPreorder.le G.core.contextPreorder.le
      (Context.points h G.core.object G.core.object))
    (hk : Context.IsLawful G.core.contextPreorder.le G.core.contextPreorder.le
      (Context.points k G.core.object G.core.object))
    (f : ∀ W : ContextCategoryObject G.core.contextPreorder,
      G.core.equationSystem.Observable W ≃+*
        G.core.equationSystem.Observable
          ((Context.assemble G.core.contextPreorder G.core.contextPreorder
            (Context.points h G.core.object G.core.object) hh).functor.obj W))
    (g : ∀ W : ContextCategoryObject G.core.contextPreorder,
      G.core.equationSystem.Observable W ≃+*
        G.core.equationSystem.Observable
          ((Context.assemble G.core.contextPreorder G.core.contextPreorder
            (Context.points k G.core.object G.core.object) hk).functor.obj W))
    (hfg : HEq f g) :
    ((Observable.readingEquiv G.core.contextPreorder G.core.contextPreorder h hh
      (fun W => G.core.equationSystem.Observable ⟨W⟩)
      (fun V => G.core.equationSystem.Observable ⟨V⟩)) f).val =
      ((Observable.readingEquiv G.core.contextPreorder G.core.contextPreorder k hk
        (fun W => G.core.equationSystem.Observable ⟨W⟩)
        (fun V => G.core.equationSystem.Observable ⟨V⟩)) g).val := by
  subst k
  have hp : hh = hk := Subsingleton.elim _ _
  subst hk
  cases hfg
  rfl

theorem observableRowsIdentity_eq_native (mode : Mode) (G : GeometryPackage.{u, v} U) :
    observableRowsIdentity mode G = NativeReader.observableRows mode
      (PackageTotalHom.id G.core) (RingHom.id G.Coefficient) := by
  unfold observableRowsIdentity NativeReader.observableRows
  exact observableReadingVal_congr mode G _ _ (indicesIdentity_eq_native mode G) _ _ _ _
    ((observableFamilyIdentity_heq mode G).trans
      (NativeReader.observableFamily_heq mode
        (PackageTotalHom.id G.core) (RingHom.id G.Coefficient)).symm)

/-- Fill every dependent identity constructor from direct index, value, raw, and realization rows. -/
def fullDependentIdentity (mode : Mode) (G : GeometryPackage.{u, v} U)
    (raw : RawQuery G.core.object G.core.object mode → Bool)
    (realization : RealizationQuery G.core.object G.core.object mode → Bool) :
    DependentQuery mode G.core.object G.core.object → Bool
  | .equation d q => InverseRows.fromInverse
      (inverseIdentity G.core.equationSystem.Index) d q
  | .context d W V => Context.identity G.core.object d W V
  | .observable d W V q => InverseRows.fromInverse
      (fun a => observableRowsIdentity mode G (.edge W V a)) d q
  | .raw q => raw q
  | .realization q => realization q

/-- Complete direct common identity table parameterized only by its mode-specific rows. -/
def identityWith (mode : Mode) (G : GeometryPackage.{u, v} U)
    (raw : RawQuery G.core.object G.core.object mode → Bool)
    (realization : RealizationQuery G.core.object G.core.object mode → Bool) : Table.{u, v} U mode := by
  classical
  intro q
  cases q with
  | source q => exact IndependentCarrierGraph.identity G.core.reading.doctrine.Source q
  | pointedAtom d a b => exact Atom.identity d a b
  | atom d a b => exact Atom.identity d a b
  | object A B => exact decide (A = B)
  | invariant q => exact IndependentCarrierGraph.identity G.core.reading.invariantReading.Index q
  | operation A B A' B' q => exact operationRowsIdentity mode G (.edge (A, B) (A', B') q)
  | signatureAxis q => exact IndependentCarrierGraph.identity G.core.algebra.signatureReading.Axis q
  | signatureCoordinate d I J i j q =>
      exact InverseRows.fromInverse
        (fun a => signatureRowsIdentity mode G (.edge I J i j a)) d q
  | coefficient q => exact IndependentCarrierGraph.identity G.Coefficient q
  | familyTransport F F' => exact decide (F' = F.transport (Equiv.refl U.Atom))
  | configurationTransport C C' => exact decide (C' = C.transport (Equiv.refl U.Atom))
  | atObjects A B q =>
      exact NativeReader.liftDependent mode G.core.object G.core.object
        (fullDependentIdentity mode G raw realization) A B q

/-- The representative query type has no explicit raw constructors. -/
def representativeRaw (G : GeometryPackage.{u, v} U) :
    RawQuery G.core.object G.core.object .representative → Bool := fun q => nomatch q

/-- Complete direct identity table for representative geometry Homs. -/
def representativeTable (G : GeometryPackage.{u, v} U) : Table.{u, v} U .representative :=
  identityWith .representative G (representativeRaw G) (representativeRealization G)

/-- Complete direct identity table for explicit geometry Homs. -/
def explicitTable (G : GeometryPackage.{u, v} U) : Table.{u, v} U .explicit :=
  identityWith .explicit G (explicitRaw G) (explicitRealization G)

theorem representativeRealization_eq_native (G : GeometryPackage.{u, v} U) :
    representativeRealization G =
      NativeReader.representativeRealizationRead (GeometryTotalHom.id G).base
        (CompleteGeometryGraphAssembly.realizationSupplyOfGeometry
          (GeometryTotalHom.id G).geometry) := by
  funext q
  cases q with
  | representativeSupport W V x y =>
      have hf : RepresentativeRealization.forward (GeometryTotalHom.id G).base W = W := rfl
      by_cases h : W = V
      · subst V
        simp only [representativeRealization, NativeReader.representativeRealizationRead,
          IndependentFixedIndexedPointGraph.read]
        rw [dif_pos (by trivial)]
        rw [dif_pos hf]
        rfl
      · simp [representativeRealization, NativeReader.representativeRealizationRead,
          IndependentFixedIndexedPointGraph.read, hf, h]

  | representativeAxis W V x y =>
      have hf : RepresentativeRealization.forward (GeometryTotalHom.id G).base W = W := rfl
      by_cases h : W = V
      · subst V
        simp only [representativeRealization, NativeReader.representativeRealizationRead,
          IndependentFixedIndexedPointGraph.read]
        rw [dif_pos (by trivial)]
        rw [dif_pos hf]
        rfl
      · simp [representativeRealization, NativeReader.representativeRealizationRead,
          IndependentFixedIndexedPointGraph.read, hf, h]
  | representativeObservable W V x y =>
      have hf : RepresentativeRealization.forward (GeometryTotalHom.id G).base W = W := rfl
      by_cases h : W = V
      · subst V
        simp only [representativeRealization, NativeReader.representativeRealizationRead,
          IndependentFixedIndexedPointGraph.read]
        rw [dif_pos (by trivial)]
        rw [dif_pos hf]
        rfl
      · simp [representativeRealization, NativeReader.representativeRealizationRead,
          IndependentFixedIndexedPointGraph.read, hf, h]

theorem representativeTable_eq_native (G : GeometryPackage.{u, v} U) :
    representativeTable G = NativeReader.readRepresentative (GeometryTotalHom.id G) := by
  funext q
  cases q with
  | source q => rfl
  | pointedAtom d a b => rfl
  | atom d a b => rfl
  | object A B => rfl
  | invariant q => rfl
  | operation A B A' B' q =>
      exact congrFun (operationRowsIdentity_eq_native .representative G) (.edge (A, B) (A', B') q)
  | signatureAxis q => rfl
  | signatureCoordinate d I J i j q =>
      exact congrArg (fun t => InverseRows.fromInverse
        (fun a => t (.edge I J i j a)) d q) (signatureRowsIdentity_eq_native .representative G)
  | coefficient q => rfl
  | familyTransport F F' => rfl
  | configurationTransport C C' => rfl
  | atObjects A B q =>
      classical
      by_cases hA : A = G.core.object
      · subst A
        by_cases hB : B = G.core.object
        · subst B
          simp only [representativeTable, identityWith, NativeReader.readRepresentative,
            NativeReader.readWith, NativeReader.liftDependent_active]
          cases q with
          | equation d q => rfl
          | context d W V =>
              exact congrFun (congrFun
                (congrFun (Context.identity_eq_read G.core.contextPreorder) d) W) V
          | observable d W V q =>
              exact congrArg (fun t => InverseRows.fromInverse
                (fun a => t (.edge W V a)) d q)
                (observableRowsIdentity_eq_native .representative G)
          | raw q => exact nomatch q
          | realization q => exact congrFun (representativeRealization_eq_native G) q
        · simp [representativeTable, identityWith, NativeReader.readRepresentative,
            NativeReader.readWith, NativeReader.liftDependent, hB]
      · simp [representativeTable, identityWith, NativeReader.readRepresentative,
          NativeReader.readWith, NativeReader.liftDependent, hA]

theorem explicitRealization_eq_native (G : GeometryPackage.{u, v} U) :
    explicitRealization G = NativeReader.explicitRealizationRead
      (ExplicitExactGeometryHom.id G).base (ExplicitExactGeometryHom.id G).realization := by
  funext q
  cases q with
  | explicitSupport d W V x y =>
      have hf : ExplicitRealization.forward (ExplicitExactGeometryHom.id G).base W = W := rfl
      by_cases h : W = V
      · subst V
        simp only [explicitRealization, NativeReader.explicitRealizationRead,
          IndependentFixedIndexedPointGraph.read]
        rw [dif_pos (by trivial)]
        rw [dif_pos hf]
        rfl
      · simp [explicitRealization, NativeReader.explicitRealizationRead,
          IndependentFixedIndexedPointGraph.read, hf, h]
  | explicitAxis d W V x y =>
      have hf : ExplicitRealization.forward (ExplicitExactGeometryHom.id G).base W = W := rfl
      by_cases h : W = V
      · subst V
        simp only [explicitRealization, NativeReader.explicitRealizationRead,
          IndependentFixedIndexedPointGraph.read]
        rw [dif_pos (by trivial)]
        rw [dif_pos hf]
        rfl
      · simp [explicitRealization, NativeReader.explicitRealizationRead,
          IndependentFixedIndexedPointGraph.read, hf, h]
  | explicitObservable d W V x y =>
      have hf : ExplicitRealization.forward (ExplicitExactGeometryHom.id G).base W = W := rfl
      by_cases h : W = V
      · subst V
        simp only [explicitRealization, NativeReader.explicitRealizationRead,
          IndependentFixedIndexedPointGraph.read]
        rw [dif_pos (by trivial)]
        rw [dif_pos hf]
        rfl
      · simp [explicitRealization, NativeReader.explicitRealizationRead,
          IndependentFixedIndexedPointGraph.read, hf, h]
  | actualSupport W X V Y g x y =>
      have hfW : ExplicitRealization.forward (PackageTotalHom.id G.core) W = W := rfl
      have hfX : ExplicitRealization.forward (PackageTotalHom.id G.core) X = X := rfl
      have epW : ExplicitRealization.forward (ExplicitExactGeometryHom.id G).base W = W := rfl
      have epX : ExplicitRealization.forward (ExplicitExactGeometryHom.id G).base X = X := rfl
      by_cases hW : W = V
      · subst V
        by_cases hX : X = Y
        · subst Y
          simp [explicitRealization, NativeReader.explicitRealizationRead,
            ExplicitRealization.readActualSupport, hfW, hfX,
            ExplicitExactGeometryHom.id, ExplicitRealizationTransportSupply.id]
        · have hnX : ExplicitRealization.forward (ExplicitExactGeometryHom.id G).base X ≠ Y :=
            fun he => hX (epX.symm.trans he)
          simp [explicitRealization, NativeReader.explicitRealizationRead,
            ExplicitRealization.readActualSupport, epW, hnX, hX]
      · have hnW : ExplicitRealization.forward (ExplicitExactGeometryHom.id G).base W ≠ V :=
          fun he => hW (epW.symm.trans he)
        simp [explicitRealization, NativeReader.explicitRealizationRead,
          ExplicitRealization.readActualSupport, hnW, hW]
  | actualAxis W X V Y g x y =>
      have hfW : ExplicitRealization.forward (PackageTotalHom.id G.core) W = W := rfl
      have hfX : ExplicitRealization.forward (PackageTotalHom.id G.core) X = X := rfl
      have epW : ExplicitRealization.forward (ExplicitExactGeometryHom.id G).base W = W := rfl
      have epX : ExplicitRealization.forward (ExplicitExactGeometryHom.id G).base X = X := rfl
      by_cases hW : W = V
      · subst V
        by_cases hX : X = Y
        · subst Y
          simp [explicitRealization, NativeReader.explicitRealizationRead,
            ExplicitRealization.readActualAxis, hfW, hfX,
            ExplicitExactGeometryHom.id, ExplicitRealizationTransportSupply.id]
        · have hnX : ExplicitRealization.forward (ExplicitExactGeometryHom.id G).base X ≠ Y :=
            fun he => hX (epX.symm.trans he)
          simp [explicitRealization, NativeReader.explicitRealizationRead,
            ExplicitRealization.readActualAxis, epW, hnX, hX]
      · have hnW : ExplicitRealization.forward (ExplicitExactGeometryHom.id G).base W ≠ V :=
          fun he => hW (epW.symm.trans he)
        simp [explicitRealization, NativeReader.explicitRealizationRead,
          ExplicitRealization.readActualAxis, hnW, hW]
  | actualObservable W X V Y g x y =>
      have hfW : ExplicitRealization.forward (PackageTotalHom.id G.core) W = W := rfl
      have hfX : ExplicitRealization.forward (PackageTotalHom.id G.core) X = X := rfl
      have epW : ExplicitRealization.forward (ExplicitExactGeometryHom.id G).base W = W := rfl
      have epX : ExplicitRealization.forward (ExplicitExactGeometryHom.id G).base X = X := rfl
      by_cases hW : W = V
      · subst V
        by_cases hX : X = Y
        · subst Y
          simp [explicitRealization, NativeReader.explicitRealizationRead,
            ExplicitRealization.readActualObservable, hfW, hfX,
            ExplicitExactGeometryHom.id, ExplicitRealizationTransportSupply.id]
        · have hnX : ExplicitRealization.forward (ExplicitExactGeometryHom.id G).base X ≠ Y :=
            fun he => hX (epX.symm.trans he)
          simp [explicitRealization, NativeReader.explicitRealizationRead,
            ExplicitRealization.readActualObservable, epW, hnX, hX]
      · have hnW : ExplicitRealization.forward (ExplicitExactGeometryHom.id G).base W ≠ V :=
          fun he => hW (epW.symm.trans he)
        simp [explicitRealization, NativeReader.explicitRealizationRead,
          ExplicitRealization.readActualObservable, hnW, hW]

theorem explicitRaw_eq_native (G : GeometryPackage.{u, v} U) :
    explicitRaw G = ExplicitRaw.readRaw (ExplicitExactGeometryHom.id G).base
      (ExplicitExactGeometryHom.id G).coefficientHom
      (ExplicitExactGeometryHom.id G).raw := by
  funext q
  cases q with
  | coordinate direction W V q =>
      by_cases hWV : W = V
      · subst V
        cases direction <;> cases q
        all_goals
          simp [explicitRaw, rawCoordinate, ExplicitRaw.readRaw, ExplicitRaw.readCoordinate,
            ExplicitRaw.inverse, ExplicitExactGeometryHom.id, coreContextInverse_id_obj,
            InverseRows.fromInverse, RawAmbientRestrictionSystemExactMapAgainst.refl,
            CoordinateFamilyExactEquiv.refl]
      · have hVW : V ≠ W := Ne.symm hWV
        cases direction <;> cases q
        all_goals
          simp [explicitRaw, rawCoordinate, ExplicitRaw.readRaw, ExplicitRaw.readCoordinate,
            ExplicitExactGeometryHom.id, explicitRaw_inverse_id, InverseRows.fromInverse,
            hWV, hVW]
  | relation direction W V q =>
      by_cases hWV : W = V
      · subst V
        cases direction <;> cases q
        all_goals
          simp [explicitRaw, rawRelation, ExplicitRaw.readRaw, ExplicitRaw.readRelation,
            ExplicitRaw.inverse, ExplicitExactGeometryHom.id, coreContextInverse_id_obj,
            InverseRows.fromInverse, RawAmbientRestrictionSystemExactMapAgainst.refl,
            CoordinateFamilyExactEquiv.refl, LawAlgebra.StructuralRelationFamily.baseChange]
      · have hVW : V ≠ W := Ne.symm hWV
        cases direction <;> cases q
        all_goals
          simp [explicitRaw, rawRelation, ExplicitRaw.readRaw, ExplicitRaw.readRelation,
            ExplicitExactGeometryHom.id, explicitRaw_inverse_id, InverseRows.fromInverse,
            hWV, hVW]
  | localData direction W V C D c d q =>
      by_cases hWV : W = V
      · subst V
        by_cases hC : C = (G.raw.coordFamily ⟨W⟩).Coord
        · subst C
          by_cases hD : D = (G.raw.coordFamily ⟨W⟩).Coord
          · subst D
            by_cases hcd : c = d
            · subst d
              cases direction <;> cases q
              all_goals
                simp [explicitRaw, rawLocalData, ExplicitRaw.readRaw,
                  ExplicitRaw.readLocalData, ExplicitRaw.inverse, ExplicitExactGeometryHom.id,
                  coreContextInverse_id_obj, InverseRows.fromInverse,
                  RawAmbientRestrictionSystemExactMapAgainst.refl,
                  CoordinateFamilyExactEquiv.refl]
            · cases direction <;> cases q
              all_goals
                simp [explicitRaw, rawLocalData, ExplicitRaw.readRaw,
                  ExplicitRaw.readLocalData, ExplicitRaw.inverse, ExplicitExactGeometryHom.id,
                  coreContextInverse_id_obj, InverseRows.fromInverse,
                  RawAmbientRestrictionSystemExactMapAgainst.refl,
                  CoordinateFamilyExactEquiv.refl, hcd]
          · cases direction <;> cases q
            all_goals
              simp [explicitRaw, rawLocalData, ExplicitRaw.readRaw,
                ExplicitRaw.readLocalData, ExplicitRaw.inverse, ExplicitExactGeometryHom.id,
                coreContextInverse_id_obj, InverseRows.fromInverse,
                RawAmbientRestrictionSystemExactMapAgainst.refl,
                CoordinateFamilyExactEquiv.refl, hD]
        · cases direction <;> cases q
          all_goals
            simp [explicitRaw, rawLocalData, ExplicitRaw.readRaw,
              ExplicitRaw.readLocalData, ExplicitRaw.inverse, ExplicitExactGeometryHom.id,
              coreContextInverse_id_obj, InverseRows.fromInverse,
              RawAmbientRestrictionSystemExactMapAgainst.refl,
              CoordinateFamilyExactEquiv.refl, hC]
      · have hVW : V ≠ W := Ne.symm hWV
        cases direction <;> cases q
        all_goals
          simp [explicitRaw, rawLocalData, ExplicitRaw.readRaw, ExplicitRaw.readLocalData,
            ExplicitExactGeometryHom.id, explicitRaw_inverse_id, InverseRows.fromInverse,
            hWV, hVW]

theorem explicitTable_eq_native (G : GeometryPackage.{u, v} U) :
    explicitTable G = NativeReader.readExplicit (ExplicitExactGeometryHom.id G) := by
  funext q
  cases q with
  | source q => rfl
  | pointedAtom d a b => rfl
  | atom d a b => rfl
  | object A B => rfl
  | invariant q => rfl
  | operation A B A' B' q =>
      exact congrFun (operationRowsIdentity_eq_native .explicit G) (.edge (A, B) (A', B') q)
  | signatureAxis q => rfl
  | signatureCoordinate d I J i j q =>
      exact congrArg (fun t => InverseRows.fromInverse
        (fun a => t (.edge I J i j a)) d q) (signatureRowsIdentity_eq_native .explicit G)
  | coefficient q => rfl
  | familyTransport F F' => rfl
  | configurationTransport C C' => rfl
  | atObjects A B q =>
      classical
      by_cases hA : A = G.core.object
      · subst A
        by_cases hB : B = G.core.object
        · subst B
          simp only [explicitTable, identityWith, NativeReader.readExplicit,
            NativeReader.readWith, NativeReader.liftDependent_active]
          cases q with
          | equation d q => rfl
          | context d W V =>
              exact congrFun (congrFun
                (congrFun (Context.identity_eq_read G.core.contextPreorder) d) W) V
          | observable d W V q =>
              exact congrArg (fun t => InverseRows.fromInverse
                (fun a => t (.edge W V a)) d q)
                (observableRowsIdentity_eq_native .explicit G)
          | raw q => exact congrFun (explicitRaw_eq_native G) q
          | realization q => exact congrFun (explicitRealization_eq_native G) q
        · simp [explicitTable, identityWith, NativeReader.readExplicit,
            NativeReader.readWith, NativeReader.liftDependent, hB]
      · simp [explicitTable, identityWith, NativeReader.readExplicit,
          NativeReader.readWith, NativeReader.liftDependent, hA]

end

end AAT.AG.LocalSemanticReconstruction.IndependentGeometryHomPrimitive.Identity

#assert_standard_axioms_only AAT.AG.LocalSemanticReconstruction.IndependentGeometryHomPrimitive.Identity
