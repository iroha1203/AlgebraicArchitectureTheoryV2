import ResearchLean.AG.LocalSemanticReconstruction.IndependentGeometryHomIdentityTable

/-!
# Coherent local identity classes for complete geometry Homs

The direct identity table is equipped with diagonal invariant value rows and
then quotiented by retained-table equality. This constructs the local identity
before comparison with either completed Hom interface.

Implementation notes: auxiliary function rows are retained until their typing
and row laws are proved, then erased by the existing quotient. Choosing a
native invariant transport first would retain an implementation choice that
the local Hom equality is designed to forget.
-/

namespace AAT.AG.LocalSemanticReconstruction.IndependentGeometryHomPrimitive.IdentityLocal

noncomputable section

universe u v

open Site AtomFoundation GeometryTransport RealizationReconstruction
open IndependentGeometryTableAssembly

variable {U : AtomCarrier.{u}}

/-- Retain every direct identity query together with its object and invariant-index row laws. -/
def retainedIdentity (mode : Mode) (G : GeometryPackage.{u, v} U) :
    InvariantWitness.Retained.{u, v}
      G.core.reading.invariantReading G.core.reading.invariantReading mode where
  family := TagChange.read (Identity.identityWith mode G
    (match mode with
      | .representative => Identity.representativeRaw G
      | .explicit => Identity.explicitRaw G)
    (match mode with
      | .representative => Identity.representativeRealization G
      | .explicit => Identity.explicitRealization G))
  objectRows := Identity.objectRowsIdentity mode G
  indexRows := by
    rw [TagChange.assemble_read]
    change IndependentCarrierGraph.IsLawful _ _
      (IndependentCarrierGraph.identity G.core.reading.invariantReading.Index)
    exact IndependentCarrierGraph.identity_isLawful _

/-- Select the mode-specific raw and realization rows in the common direct identity table. -/
def tableIdentity (mode : Mode) (G : GeometryPackage.{u, v} U) :
    Table.{u, v} U mode :=
  Identity.identityWith mode G
    (match mode with
      | .representative => Identity.representativeRaw G
      | .explicit => Identity.explicitRaw G)
    (match mode with
      | .representative => Identity.representativeRealization G
      | .explicit => Identity.explicitRealization G)

/-- Singleton assembly restores the complete direct identity table. -/
theorem retainedIdentity_table (mode : Mode) (G : GeometryPackage.{u, v} U) :
    (retainedIdentity mode G).table = tableIdentity mode G :=
  TagChange.assemble_read _

/-- The retained object graph assembles to the identity object function. -/
theorem retainedIdentity_objectMap (mode : Mode) (G : GeometryPackage.{u, v} U) :
    (retainedIdentity mode G).objectMap = id := by
  funext A
  apply ((retainedIdentity mode G).object_point_iff A A).1
  rw [retainedIdentity_table]
  simp [tableIdentity, Identity.identityWith]

/-- The retained invariant-index graph assembles to the identity index function. -/
theorem retainedIdentity_indexMap (mode : Mode) (G : GeometryPackage.{u, v} U) :
    (retainedIdentity mode G).indexMap = id := by
  funext i
  apply IndependentCarrierGraph.assemble_eq_of_edge
  rw [retainedIdentity_table]
  change IndependentCarrierGraph.identity G.core.reading.invariantReading.Index
    (.edge _ _ i i) = true
  exact (IndependentCarrierGraph.identity_edge _ i i).2 rfl

/-- Diagonal function-invariant rows are identity inverse graphs; predicate and inactive rows are false. -/
def auxiliaryIdentity (I : InvariantFamily U) : InvariantWitness.Table.{u} := by
  classical
  intro q
  cases q with
  | row M N i j q =>
      exact if hM : M = I.Index then
        if hN : N = I.Index then
          if hij : hM ▸ i = hN ▸ j then
            InvariantWitness.identityRow (I.invariant (hM ▸ i)) q
          else false
        else false
      else false

/-- A selected diagonal index exposes exactly the primitive identity row for that invariant. -/
theorem auxiliaryIdentity_row (I : InvariantFamily U) (i : I.Index) :
    InvariantWitness.row (auxiliaryIdentity I) I.Index I.Index i i =
      InvariantWitness.identityRow (I.invariant i) := by
  funext q
  simp [InvariantWitness.row, auxiliaryIdentity]

/-- Candidate carrier pairs outside the selected invariant-index carrier are inactive. -/
theorem auxiliaryIdentity_wrong_indices (I : InvariantFamily U)
    (M N : Type u) (i : M) (j : N) (q : IndependentInverseGraph.Query.{u, u})
    (h : M ≠ I.Index ∨ N ≠ I.Index) :
    auxiliaryIdentity I (.row M N i j q) = false := by
  classical
  rcases h with hM | hN
  · simp [auxiliaryIdentity, hM]
  · by_cases hM : M = I.Index <;> simp [auxiliaryIdentity, hM, hN]

/-- The invariant-index projection of the common identity table is the diagonal graph. -/
theorem tableIdentity_invariant (mode : Mode) (G : GeometryPackage.{u, v} U) :
    invariant (tableIdentity mode G) =
      IndependentCarrierGraph.identity G.core.reading.invariantReading.Index := by
  funext q
  rfl

/-- A direct identity object point is true exactly on equal object candidates. -/
theorem tableIdentity_object_iff (mode : Mode) (G : GeometryPackage.{u, v} U)
    (A B : ArchitectureObject U) :
    tableIdentity mode G (.object A B) = true ↔ A = B := by
  simp [tableIdentity, Identity.identityWith]

/-- The auxiliary identity table obeys all carrier, index, and invariant-kind inactivity rules. -/
theorem auxiliaryIdentity_typed (mode : Mode) (G : GeometryPackage.{u, v} U) :
    InvariantWitness.IsAuxTyped G.core.reading.invariantReading
      G.core.reading.invariantReading (retainedIdentity mode G)
      (auxiliaryIdentity G.core.reading.invariantReading) := by
  classical
  constructor
  · exact auxiliaryIdentity_wrong_indices _
  · intro i j q hn
    by_cases hij : i = j
    · subst j
      change InvariantWitness.row (auxiliaryIdentity G.core.reading.invariantReading)
        _ _ i i q = false
      rw [auxiliaryIdentity_row]
      rcases hn with hp | hn
      · rw [retainedIdentity_table] at hp
        change invariant (tableIdentity mode G) (.edge _ _ i i) = false at hp
        rw [tableIdentity_invariant] at hp
        exact False.elim (Bool.noConfusion
          (hp.symm.trans ((IndependentCarrierGraph.identity_edge _ i i).2 rfl)))
      · cases hI : G.core.reading.invariantReading.invariant i with
        | function F =>
            simp [InvariantWitness.isFunction, hI] at hn
        | predicate P =>
            rfl
    · simp [auxiliaryIdentity, hij]

/-- Package the direct common identity table and diagonal auxiliary rows as one coherent presentation. -/
def presentationIdentity (mode : Mode) (G : GeometryPackage.{u, v} U) :
    InvariantWitness.Presentation.{u, v}
      G.core.reading.invariantReading G.core.reading.invariantReading mode where
  retained := retainedIdentity mode G
  auxiliary := TagChange.read (auxiliaryIdentity G.core.reading.invariantReading)
  auxiliaryTyped := by
    rw [TagChange.assemble_read]
    exact auxiliaryIdentity_typed mode G
  rows := by
    intro i j hij
    have he : i = j := by
      rw [retainedIdentity_table] at hij
      change invariant (tableIdentity mode G) (.edge _ _ i j) = true at hij
      rw [tableIdentity_invariant] at hij
      exact (IndependentCarrierGraph.identity_edge _ i j).1 hij
    subst j
    rw [TagChange.assemble_read, auxiliaryIdentity_row]
    apply InvariantWitness.identityRow_law
    intro A B hAB
    rw [retainedIdentity_table] at hAB
    exact (tableIdentity_object_iff mode G A B).1 hAB

/-- Erase the auxiliary identity-row choice while preserving every common Hom query. -/
def localIdentity (mode : Mode) (G : GeometryPackage.{u, v} U) :
    InvariantWitness.Local.{u, v}
      G.core.reading.invariantReading G.core.reading.invariantReading mode :=
  Quotient.mk _ (presentationIdentity mode G)

/-- Every point of the quotient identity class is its direct common-table value. -/
theorem localIdentity_point (mode : Mode) (G : GeometryPackage.{u, v} U)
    (q : Query.{u, v} U mode) :
    InvariantWitness.point _ _ (localIdentity mode G) q = tableIdentity mode G q := by
  exact congrFun (retainedIdentity_table mode G) q

/-- Every finite fragment of the quotient identity class is the restriction of
the same directly constructed identity table. -/
theorem localIdentity_fragment (mode : Mode) (G : GeometryPackage.{u, v} U)
    (S : Finset (Query.{u, v} U mode)) :
    InvariantWitness.fragment _ _ (localIdentity mode G) S =
      TagChange.LocalTagTable.read (tableIdentity mode G) S := by
  funext q
  exact (NativeReader.local_fragment_point _ _ (localIdentity mode G) S q).trans
    (localIdentity_point mode G q.1)

/-- Replacing the diagonal auxiliary rows by any coherent presentation with
the same retained common declaration does not create another identity Hom. -/
theorem localIdentity_choice_independent (mode : Mode) (G : GeometryPackage.{u, v} U)
    (p : InvariantWitness.Presentation.{u, v}
      G.core.reading.invariantReading G.core.reading.invariantReading mode)
    (h : p.retained = (presentationIdentity mode G).retained) :
    (Quotient.mk _ p : InvariantWitness.Local
      G.core.reading.invariantReading G.core.reading.invariantReading mode) =
      localIdentity mode G := by
  exact InvariantWitness.auxiliary_choice_independent _ _ p
    (presentationIdentity mode G) h

/-- The direct representative local identity equals the reading of the completed representative identity. -/
theorem representativeLocalIdentity_eq_native (G : GeometryPackage.{u, v} U) :
    localIdentity .representative G =
      NativeReader.localRepresentative (GeometryTotalHom.id G) := by
  apply InvariantWitness.point_ext
  intro q
  exact (localIdentity_point .representative G q).trans
    ((congrFun (Identity.representativeTable_eq_native G) q).trans
      (NativeReader.point_localRepresentative (GeometryTotalHom.id G) q).symm)

/-- The direct explicit local identity equals the reading of the completed explicit identity. -/
theorem explicitLocalIdentity_eq_native (G : GeometryPackage.{u, v} U) :
    localIdentity .explicit G =
      NativeReader.localExplicit (ExplicitExactGeometryHom.id G) := by
  apply InvariantWitness.point_ext
  intro q
  exact (localIdentity_point .explicit G q).trans
    ((congrFun (Identity.explicitTable_eq_native G) q).trans
      (NativeReader.point_localExplicit (ExplicitExactGeometryHom.id G) q).symm)

variable (s : ObjectData.{u, v} U)

/-- Representative local identity on an independently assembled geometry object. -/
def representativeIdentity : InvariantWitness.Local.{u, v}
    (assemble s).core.reading.invariantReading
    (assemble s).core.reading.invariantReading .representative :=
  localIdentity .representative (assemble s)

/-- Explicit local identity on the same independently assembled geometry object. -/
def explicitIdentity : InvariantWitness.Local.{u, v}
    (assemble s).core.reading.invariantReading
    (assemble s).core.reading.invariantReading .explicit :=
  localIdentity .explicit (assemble s)

/-- The direct representative identity satisfies every complete primitive point law. -/
theorem representativeIdentity_points :
    FullRepresentative.PointLaws s s (representativeIdentity s) := by
  rw [representativeIdentity, representativeLocalIdentity_eq_native]
  exact NativeReader.localRepresentative_points s s (GeometryTotalHom.id (assemble s))

/-- The direct explicit identity satisfies every complete primitive point law. -/
theorem explicitIdentity_points :
    FullExplicit.PointLaws s s (explicitIdentity s) := by
  rw [explicitIdentity, explicitLocalIdentity_eq_native]
  exact NativeReader.localExplicit_points s s (ExplicitExactGeometryHom.id (assemble s))

/-- Full representative assembly recovers the completed identity Hom. -/
theorem representativeIdentity_assemble :
    FullRepresentative.assembleHom s s (representativeIdentity s)
      (representativeIdentity_points s) = GeometryTotalHom.id (assemble s) := by
  apply (NativeReader.representativeHomReadingEquiv s s).injective
  apply Subtype.ext
  exact (NativeReader.localRepresentative_read_assemble s s _ _).trans
    (representativeLocalIdentity_eq_native (assemble s))

/-- Full explicit assembly recovers the completed identity Hom. -/
theorem explicitIdentity_assemble :
    FullExplicit.assembleHom s s (explicitIdentity s)
      (explicitIdentity_points s) = ExplicitExactGeometryHom.id (assemble s) := by
  apply (NativeReader.explicitHomReadingEquiv s s).injective
  apply Subtype.ext
  exact (NativeReader.localExplicit_read_assemble s s _ _).trans
    (explicitLocalIdentity_eq_native (assemble s))

end

end AAT.AG.LocalSemanticReconstruction.IndependentGeometryHomPrimitive.IdentityLocal

#assert_standard_axioms_only AAT.AG.LocalSemanticReconstruction.IndependentGeometryHomPrimitive.IdentityLocal
