import ResearchLean.AG.LocalSemanticReconstruction.IndependentCorePrimitiveReadings
import ResearchLean.AG.LocalSemanticReconstruction.IndependentContextPrimitiveReadings
import ResearchLean.AG.LocalSemanticReconstruction.IndependentEquationPrimitiveReadings
import ResearchLean.AG.LocalSemanticReconstruction.IndependentInvariantSignaturePrimitiveReadings
import Mathlib.Logic.Equiv.Basic
import Formal.Util.AssertStandardAxioms

/-!
# Dependent assembly of a complete native core from primitive tables

Implementation notes: this bridge follows the native dependency order. Each
stored computational component is a primitive point table. Finite-family and
circuit witnesses remain propositions. Dependent sigma transport connects the
component equivalences and recovers the exact native generated object.

The table family here is indexed by its preceding assembled stages.
IndependentGeometryPrimitiveAssembly connects these stages to the common
realization-independent query declaration and proves both inverse laws.
The native source views below are used only to prove the bridge; they are not
local response types.
-/

namespace AAT.AG.LocalSemanticReconstruction.IndependentCoreTableAssembly

universe u

open Site

variable {U : AtomCarrier.{u}}

/-- Typed primitive context tables with their independent preorder and point laws. -/
abbrev ContextData (A : ArchitectureObject U) :=
  {t : IndependentContextPrimitive.Table A // ∃ ht : IndependentContextPrimitive.IsTyped t, IndependentContextPrimitive.IsLawful t ht}

/-- Construct the native context preorder from the independent table. -/
noncomputable def context (c : ContextData (U := U) A) : ContextPreorderCategory A :=
  IndependentContextPrimitive.assemble c.val c.property.choose c.property.choose_spec

/-- Primitive equation tables on the context preorder selected at the preceding stage. -/
abbrev EquationData {A : ArchitectureObject U} (C : ContextPreorderCategory A) :=
  {t : IndependentEquationPrimitive.Table A // ∃ ht : IndependentEquationPrimitive.IsTyped C t, IndependentEquationPrimitive.IsLawful t ht}

/-- Construct the native equation system from primitive rings and coordinate values. -/
noncomputable def equation {A : ArchitectureObject U} {C : ContextPreorderCategory A}
    (e : EquationData C) : ArchitecturalEquationSystem C :=
  IndependentEquationPrimitive.assemble e.val e.property.choose e.property.choose_spec

/-- Circuit-code tables carry only the independent local nonzero-witness condition. -/
abbrev CircuitData {A : ArchitectureObject U} {C : ContextPreorderCategory A}
    (e : EquationData C) :=
  {c : IndependentEquationPrimitive.Circuit.Table U // ∃ hc : IndependentEquationPrimitive.Circuit.IsTyped (IndependentEquationPrimitive.index e.val) c,
    IndependentEquationPrimitive.Circuit.IsLawful e.val e.property.choose c hc}

/-- Native sound circuit syntax is equivalent to the local nonzero-witness table at this stage. -/
noncomputable def circuitEquiv {A : ArchitectureObject U} {C : ContextPreorderCategory A}
    (e : EquationData C) :
    {R : EquationCircuitReading (equation e) // R.Sound} ≃ CircuitData e where
  toFun R := ⟨IndependentEquationPrimitive.Circuit.read R.val, IndependentEquationPrimitive.Circuit.read_isTyped R.val,
    (IndependentEquationPrimitive.Circuit.lawful_iff_sound e.val e.property.choose e.property.choose_spec
      (IndependentEquationPrimitive.Circuit.read R.val) (IndependentEquationPrimitive.Circuit.read_isTyped R.val)).2 (by
        simpa only [IndependentEquationPrimitive.Circuit.assemble_read] using R.property)⟩
  invFun c := ⟨IndependentEquationPrimitive.Circuit.assemble (equation e) c.val c.property.choose,
    IndependentEquationPrimitive.Circuit.assemble_sound e.val e.property.choose e.property.choose_spec
      c.val c.property.choose c.property.choose_spec⟩
  left_inv R := Subtype.ext (IndependentEquationPrimitive.Circuit.assemble_read R.val)
  right_inv c := Subtype.ext (IndependentEquationPrimitive.Circuit.read_assemble (equation e) c.val c.property.choose)

/-- Primitive equation and circuit stages on a fixed native context preorder. -/
abbrev EquationCircuitData {A : ArchitectureObject U} (C : ContextPreorderCategory A) :=
  (e : EquationData C) × CircuitData e

/-- Context, equation, and circuit primitive stages in their dependent order. -/
abbrev EquationReadingData (A : ArchitectureObject U) :=
  (c : ContextData A) × EquationCircuitData (context c)

/-- A source-only dependent view of the native equation reading. -/
def equationNativeEquiv (A : ArchitectureObject U) :
    EquationReading A ≃ (C : ContextPreorderCategory A) ×
      (E : ArchitecturalEquationSystem C) × {R : EquationCircuitReading E // R.Sound} where
  toFun R := ⟨R.contextPreorder, R.equationSystem, R.circuits, R.circuitSound⟩
  invFun r := ⟨r.1, r.2.1, r.2.2.val, r.2.2.property⟩
  left_inv R := by cases R; rfl
  right_inv r := by rcases r with ⟨C, E, R, hs⟩; rfl

/-- Dependent equation and circuit reconstruction uses their primitive equivalences. -/
noncomputable def equationCircuitEquiv {A : ArchitectureObject U} (C : ContextPreorderCategory A) :
    ((E : ArchitecturalEquationSystem C) × {R : EquationCircuitReading E // R.Sound}) ≃
      EquationCircuitData C :=
  (Equiv.sigmaCongrLeft' (IndependentEquationPrimitive.readingEquiv (C := C))).trans
    (Equiv.sigmaCongrRight fun e => circuitEquiv e)

/-- All native equation-reading fields are assembled from primitive tables in dependency order. -/
noncomputable def equationReadingEquiv (A : ArchitectureObject U) :
    EquationReading A ≃ EquationReadingData A :=
  (equationNativeEquiv A).trans
    ((Equiv.sigmaCongrRight fun C => equationCircuitEquiv C).trans
      (Equiv.sigmaCongrLeft' (IndependentContextPrimitive.readingEquiv (A := A))))

/-- A native pointed doctrine with its original finite extracted-family condition. -/
abbrev FinitePointedDoctrine (U : AtomCarrier.{u}) :=
  {p : IndependentCorePrimitive.Extraction.PointedDoctrine U // (p.1.atomize p.2).ListFinite}

/-- Primitive extraction tables retain finite-family evidence only as a proposition. -/
abbrev FiniteExtractionData (U : AtomCarrier.{u}) :=
  {e : {t : IndependentCorePrimitive.Extraction.Table U // IndependentCorePrimitive.Extraction.IsTyped t} //
    (IndependentCorePrimitive.Generation.family e.val e.property).ListFinite}

/-- The primitive extraction equivalence preserves exactly the native finite-family condition. -/
noncomputable def finiteExtractionEquiv : FinitePointedDoctrine U ≃ FiniteExtractionData U :=
  Equiv.subtypeEquiv IndependentCorePrimitive.Extraction.readingEquiv (fun p => by
    change (p.1.atomize p.2).ListFinite ↔
      (IndependentCorePrimitive.Generation.family (IndependentCorePrimitive.Extraction.read p)
        (IndependentCorePrimitive.Extraction.read_isTyped p)).ListFinite
    rw [IndependentCorePrimitive.Generation.family_read])

/-- Source-only view of the native components that precede the dependent equation reading. -/
abbrev NativeFoundation (U : AtomCarrier.{u}) :=
  FinitePointedDoctrine U × CompositionReading U × ObjectReading U ×
    InvariantFamily U × ArchitectureSignature U × OperationReading U

/-- Every foundational computational field is represented by its primitive table. -/
abbrev FoundationData (U : AtomCarrier.{u}) :=
  FiniteExtractionData U ×
    {t : IndependentCorePrimitive.Composition.Table U // IndependentCorePrimitive.Composition.IsLawful t} ×
    IndependentCorePrimitive.ObjectFormation.Table U ×
    {t : IndependentInvariantSignaturePrimitive.Invariants.Table U // IndependentInvariantSignaturePrimitive.Invariants.IsTyped t} ×
    {t : IndependentInvariantSignaturePrimitive.Signature.Table U // IndependentInvariantSignaturePrimitive.Signature.IsTyped t} ×
    {t : IndependentCorePrimitive.Operations.Table U //
      ∃ ht : IndependentCorePrimitive.Operations.IsTyped t, IndependentCorePrimitive.Operations.IsLawful t ht}

/-- Reconstruct all foundational fields using the established primitive component equivalences. -/
noncomputable def foundationEquiv : NativeFoundation U ≃ FoundationData U :=
  Equiv.prodCongr finiteExtractionEquiv
    (Equiv.prodCongr IndependentCorePrimitive.Composition.readingEquiv
      (Equiv.prodCongr IndependentCorePrimitive.ObjectFormation.readingEquiv
        (Equiv.prodCongr IndependentInvariantSignaturePrimitive.Invariants.readingEquiv
          (Equiv.prodCongr IndependentInvariantSignaturePrimitive.Signature.readingEquiv IndependentCorePrimitive.Operations.readingEquiv))))

/-- Native generation from the source-only foundation view. -/
def nativeObject (f : NativeFoundation U) : ArchitectureObject U :=
  f.2.2.1.object (f.2.1.compose (f.1.val.1.atomize f.1.val.2) f.1.property)

/-- Generate the dependent architecture object from primitive extraction, composition, and formation. -/
noncomputable def generatedObject (f : FoundationData U) : ArchitectureObject U :=
  nativeObject (foundationEquiv.symm f)

/-- The foundation bridge uses exactly the previously verified primitive object constructor. -/
theorem generatedObject_eq (f : FoundationData U) :
    generatedObject f = IndependentCorePrimitive.Generation.object f.1.val.val f.1.val.property
      f.2.1.val f.2.1.property f.2.2.1 f.1.property := rfl

/-- Primitive foundation and equation-reading tables form the complete dependent core input. -/
abbrev CoreData (U : AtomCarrier.{u}) :=
  (f : FoundationData U) × EquationReadingData (generatedObject f)

/-- Source-only dependent decomposition of all native core fields. -/
def coreNativeEquiv : CoreReading U ≃ (f : NativeFoundation U) × EquationReading (nativeObject f) where
  toFun R := ⟨⟨⟨⟨R.doctrine, R.source⟩, R.family_listFinite⟩,
    R.composition, R.objectReading, R.invariantReading, R.signatureReading, R.operationReading⟩,
      R.equationReading⟩
  invFun r :=
    { doctrine := r.1.1.val.1
      source := r.1.1.val.2
      family_listFinite := r.1.1.property
      composition := r.1.2.1
      objectReading := r.1.2.2.1
      equationReading := r.2
      invariantReading := r.1.2.2.2.1
      signatureReading := r.1.2.2.2.2.1
      operationReading := r.1.2.2.2.2.2 }
  left_inv R := by cases R; rfl
  right_inv r := by rcases r with ⟨⟨p, c, o, i, s, op⟩, e⟩; rfl

/-- Full native core readings have exact dependent primitive-table presentations. -/
noncomputable def coreEquiv : CoreReading U ≃ CoreData U :=
  coreNativeEquiv.trans
    ((Equiv.sigmaCongrRight fun f => equationReadingEquiv (nativeObject f)).trans
      (Equiv.sigmaCongrLeft' foundationEquiv))

/-- Assemble the full native core reading from the primitive stages. -/
noncomputable def assemble (d : CoreData U) : CoreReading U := coreEquiv.symm d

/-- Read every native core field into its primitive table stage. -/
noncomputable def read (R : CoreReading U) : CoreData U := coreEquiv R

/-- Full native core assembly has no lost computational field. -/
theorem assemble_read (R : CoreReading U) : assemble (read R) = R := coreEquiv.left_inv R

/-- All primitive stage tables are recovered, including candidate inactivity and proof choices. -/
theorem read_assemble (d : CoreData U) : read (assemble d) = d := coreEquiv.right_inv d

/-- The assembled native core uses the exact generated architecture object of its primitive foundation. -/
theorem object_assemble (d : CoreData U) :
    (assemble d).objectReading.object
      ((assemble d).composition.compose
        ((assemble d).doctrine.atomize (assemble d).source) (assemble d).family_listFinite) =
      generatedObject d.1 := rfl

/-- The two original Atom laws, retained as propositions on the fixed primitive carrier. -/
def AtomLaws (U : AtomCarrier.{u}) : Prop :=
  Nonempty U.Atom ∧ ∀ a b, SameCoordinates U a b ↔ a = b

/-- Complete primitive core tables with the original Atom laws. -/
abbrev PackageData (U : AtomCarrier.{u}) := {_d : CoreData U // AtomLaws U}

/-- Assemble the native core package; no completed Atom law record is stored locally. -/
noncomputable def assemblePackage (d : PackageData U) : AATCorePackage U where
  axioms := ⟨d.property.1, d.property.2⟩
  reading := assemble d.val

/-- Read a native package into primitive tables and its two original Atom laws. -/
noncomputable def readPackage (P : AATCorePackage U) : PackageData U :=
  ⟨read P.reading, P.axioms.primitiveExistence, P.axioms.predicateStability⟩

/-- Native package assembly restores both the complete reading and original Atom axioms. -/
theorem assemblePackage_readPackage (P : AATCorePackage U) : assemblePackage (readPackage P) = P := by
  apply AATCorePackage.ext
  · rfl
  · exact assemble_read P.reading

/-- The primitive package table is restored without retaining alternative proof witnesses. -/
theorem readPackage_assemblePackage (d : PackageData U) : readPackage (assemblePackage d) = d :=
  Subtype.ext (read_assemble d.val)

/-- Every native AAT core package has an exact dependent primitive-table presentation. -/
noncomputable def packageEquiv : AATCorePackage U ≃ PackageData U where
  toFun := readPackage
  invFun := assemblePackage
  left_inv := assemblePackage_readPackage
  right_inv := readPackage_assemblePackage

/-- The package's generated object is exactly the foundation object used by its equation tables. -/
theorem package_object (d : PackageData U) :
    (assemblePackage d).object = generatedObject d.val.1 := rfl

end AAT.AG.LocalSemanticReconstruction.IndependentCoreTableAssembly

#assert_standard_axioms_only AAT.AG.LocalSemanticReconstruction.IndependentCoreTableAssembly
