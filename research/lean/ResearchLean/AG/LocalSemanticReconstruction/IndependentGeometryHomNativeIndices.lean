import ResearchLean.AG.LocalSemanticReconstruction.IndependentGeometryHomGeometryComponents
import Formal.Util.AssertStandardAxioms

/-!
# Native index points for the common complete-Hom reader

Implementation notes: object, axis, and context points are read before their
dependent operation, coordinate, and observable rows. The auxiliary index
table below supplies those index readers and the scalar roles; dependent
families are filled by the complete reader. It is not itself asserted to be
a lawful complete Hom. Native maps are inputs of the reader, while every
query response remains one Boolean on the original declaration.
-/

namespace AAT.AG.LocalSemanticReconstruction.IndependentGeometryHomPrimitive.NativeReader

noncomputable section

universe u v

open Site CategoryTheory AtomFoundation GeometryTransport

variable {U : AtomCarrier.{u}}

/-- Extend an active dependent reader to all candidate object pairs, fixing every other pair to false. -/
def liftDependent (mode : Mode) (A₀ B₀ : ArchitectureObject U)
    (r : DependentQuery mode A₀ B₀ → Bool) (A B : ArchitectureObject U)
    (q : DependentQuery mode A B) : Bool := by
  classical
  by_cases hA : A = A₀
  · subst A
    by_cases hB : B = B₀
    · subst B
      exact r q
    · exact false
  · exact false

/-- Extension preserves every query at the declared active endpoint pair. -/
theorem liftDependent_active (mode : Mode) (A B : ArchitectureObject U)
    (r : DependentQuery mode A B → Bool) (q : DependentQuery mode A B) :
    liftDependent mode A B r A B q = r q := by
  simp [liftDependent]

/-- A mismatch at either endpoint forces the extended query response to false. -/
theorem liftDependent_inactive (mode : Mode) (A₀ B₀ : ArchitectureObject U)
    (r : DependentQuery mode A₀ B₀ → Bool) (A B : ArchitectureObject U)
    (q : DependentQuery mode A B) (hi : A ≠ A₀ ∨ B ≠ B₀) :
    liftDependent mode A₀ B₀ r A B q = false := by
  classical
  rcases hi with hA | hB
  · simp [liftDependent, hA]
  · by_cases hA : A = A₀
    · subst A
      simp [liftDependent, hB]
    · simp [liftDependent, hA]

variable {G H : GeometryPackage.{u, v} U} (mode : Mode)
variable (f : PackageTotalHom G.core H.core) (a : G.Coefficient →+* H.Coefficient)

/-- Read the equation and context index roles before filling dependent observable/raw/realization rows. -/
def dependentIndices : DependentQuery mode G.core.object H.core.object → Bool
  | .equation direction q => InverseRows.fromInverse
    (IndependentInverseGraph.read _ _ f.upper.equationEquiv) direction q
  | .context direction W V => Context.read G.core.contextPreorder H.core.contextPreorder
    f.upper.equationTransport.contextEquivalence direction W V
  | _ => false

/-- Read native scalar and index roles; complete dependent families are added after their index recovery. -/
def indices : Table.{u, v} U mode := by
  classical
  intro q
  exact match q with
  | .source q => IndependentCarrierGraph.read _ _ f.base.doctrineHom.sourceMap q
  | .pointedAtom direction x y => Atom.read f.base.doctrineHom.atomEquiv direction x y
  | .atom direction x y => Atom.read f.upper.atomEquiv direction x y
  | .object A B => decide (f.upper.objectMap A = B)
  | .invariant q => IndependentCarrierGraph.read _ _ f.upper.invariantMap q
  | .signatureAxis q => IndependentCarrierGraph.read _ _ f.upper.axisMap q
  | .coefficient q => IndependentCarrierGraph.read _ _ a q
  | .familyTransport F F' => decide (F' = F.transport f.upper.atomEquiv)
  | .configurationTransport C C' => decide (C' = C.transport f.upper.atomEquiv)
  | .atObjects A B q => liftDependent mode G.core.object H.core.object (dependentIndices mode f) A B q
  | _ => false

/-- The lower source role is the original directed source-map reading at all candidate carriers. -/
theorem source_indices : source (indices mode f a) =
    IndependentCarrierGraph.read _ _ f.base.doctrineHom.sourceMap := rfl

/-- The separate pointed Atom role is retained exactly. -/
theorem pointed_indices : Atom.pointed (indices mode f a) = Atom.read f.base.doctrineHom.atomEquiv := rfl

/-- The upper Atom role also retains both of its original directions. -/
theorem atom_indices : Atom.upper (indices mode f a) = Atom.read f.upper.atomEquiv := rfl

/-- Invariant indices keep their original directed carrier graph. -/
theorem invariant_indices : invariant (indices mode f a) =
    IndependentCarrierGraph.read _ _ f.upper.invariantMap := rfl

/-- Axis indices keep their original directed carrier graph. -/
theorem axis_indices : signatureAxis (indices mode f a) =
    IndependentCarrierGraph.read _ _ f.upper.axisMap := rfl

/-- Coefficients are read as the given directed ring hom, without an inverse requirement. -/
theorem coefficient_indices : coefficient (indices mode f a) = IndependentCarrierGraph.read _ _ a := rfl

/-- The native object map supplies precisely the true object point pairs. -/
theorem object_indices_iff (A B : ArchitectureObject U) :
    indices mode f a (.object A B) = true ↔ f.upper.objectMap A = B := by
  simp [indices]

/-- Native object points are total and unique even for a noninvertible object map. -/
theorem object_rows : CoreLaws.ObjectRows (indices mode f a) := by
  intro A
  refine ⟨f.upper.objectMap A, (object_indices_iff mode f a A _).2 rfl, ?_⟩
  intro B hB
  exact ((object_indices_iff mode f a A B).1 hB).symm

/-- The object index assembled from these primitive rows is the actual native object map. -/
theorem objectMap_indices : CoreLaws.objectMap (indices mode f a) (object_rows mode f a) = f.upper.objectMap := by
  funext A
  exact (CoreLaws.objectGraph (indices mode f a) (object_rows mode f a)).target_eq_of_edge
    ((object_indices_iff mode f a A _).2 rfl)

/-- Axis rows satisfy the exact candidate-carrier graph laws of the native axis map. -/
theorem axis_rows : IndependentCarrierGraph.IsLawful G.core.algebra.signatureReading.Axis
    H.core.algebra.signatureReading.Axis (signatureAxis (indices mode f a)) :=
  IndependentCarrierGraph.read_isLawful _ _ f.upper.axisMap

/-- Assembling axis points recovers the actual native directed map. -/
theorem axisMap_indices : Signature.axisMap (indices mode f a) _ _ (axis_rows mode f a) = f.upper.axisMap :=
  IndependentCarrierGraph.assemble_read _ _ f.upper.axisMap

/-- At the actual endpoints, the context role is the original complete context-equivalence reading. -/
theorem context_indices : Context.points (indices mode f a) G.core.object H.core.object =
    Context.read G.core.contextPreorder H.core.contextPreorder f.upper.equationTransport.contextEquivalence := by
  funext direction W V
  exact liftDependent_active mode _ _ (dependentIndices mode f) (.context direction W V)

/-- Context rows retain both original functors and their preorder comparison laws. -/
theorem context_rows : Context.IsLawful G.core.contextPreorder.le H.core.contextPreorder.le
    (Context.points (indices mode f a) G.core.object H.core.object) := by
  rw [context_indices]
  exact Context.read_isLawful _ _ f.upper.equationTransport.contextEquivalence

/-- Assembly of the index context points recovers the complete original context equivalence. -/
theorem context_assemble_indices : Context.assemble G.core.contextPreorder H.core.contextPreorder
    (Context.points (indices mode f a) G.core.object H.core.object) (context_rows mode f a) =
      f.upper.equationTransport.contextEquivalence := by
  have he : (⟨Context.points (indices mode f a) G.core.object H.core.object, context_rows mode f a⟩ :
      {p // Context.IsLawful G.core.contextPreorder.le H.core.contextPreorder.le p}) =
    ⟨Context.read G.core.contextPreorder H.core.contextPreorder f.upper.equationTransport.contextEquivalence,
      Context.read_isLawful _ _ f.upper.equationTransport.contextEquivalence⟩ := Subtype.ext (context_indices mode f a)
  exact (congrArg (Context.readingEquiv G.core.contextPreorder H.core.contextPreorder).symm he).trans
    (Context.assemble_read _ _ f.upper.equationTransport.contextEquivalence)

end

end AAT.AG.LocalSemanticReconstruction.IndependentGeometryHomPrimitive.NativeReader

#assert_standard_axioms_only AAT.AG.LocalSemanticReconstruction.IndependentGeometryHomPrimitive.NativeReader
