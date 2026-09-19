import ResearchLean.AG.LocalSemanticReconstruction.IndependentGeometryHomCoreLaws
import ResearchLean.AG.LocalSemanticReconstruction.IndependentIndexedCarrierGraphs
import Formal.Util.AssertStandardAxioms

/-!
# Directed operation families from the common Hom point rows

The object graph activates an ordered endpoint pair. The operation-role rows
then supply an ordinary directed function between the corresponding operation
carriers. Both inverse readings recover every candidate endpoint and carrier
cell. Naturality remains an additional point law, not a restriction to
invertible operation maps.
-/

namespace AAT.AG.LocalSemanticReconstruction.IndependentGeometryHomPrimitive.Operation

noncomputable section

universe u v

variable {U : AtomCarrier.{u}} {mode : Mode}

/-- Both endpoint flags activate the dependent operation row. -/
def endpoints (h : Table.{u, v} U mode)
    (p q : ArchitectureObject U × ArchitectureObject U) : Bool :=
  h (.object p.1 q.1) && h (.object p.2 q.2)

/-- Exact-one object rows supply exact-one ordered endpoint rows without bijectivity. -/
theorem endpoints_total (h : Table.{u, v} U mode) (ho : CoreLaws.ObjectRows h) :
    ∀ p, ∃! q, endpoints h p q = true := by
  intro p
  refine ⟨(CoreLaws.objectMap h ho p.1, CoreLaws.objectMap h ho p.2), ?_, ?_⟩
  · change (h (.object p.1 _) && h (.object p.2 _)) = true
    have ha := (CoreLaws.objectGraph h ho).edge_target p.1
    have hb := (CoreLaws.objectGraph h ho).edge_target p.2
    change h (.object p.1 (CoreLaws.objectMap h ho p.1)) = true at ha
    change h (.object p.2 (CoreLaws.objectMap h ho p.2)) = true at hb
    simp [ha, hb]
  · intro q hq
    have hh : h (.object p.1 q.1) = true ∧ h (.object p.2 q.2) = true := by
      simpa [endpoints] using hq
    obtain ⟨ha, hb⟩ := hh
    exact Prod.ext ((CoreLaws.objectGraph h ho).target_eq_of_edge ha).symm
      ((CoreLaws.objectGraph h ho).target_eq_of_edge hb).symm

/-- The endpoint index assembled from true pairs equals the pair of independently assembled object images. -/
theorem index_eq (h : Table.{u, v} U mode) (ho : CoreLaws.ObjectRows h)
    (p : ArchitectureObject U × ArchitectureObject U) :
    IndependentIndexedCarrierGraph.index (endpoints h) (endpoints_total h ho) p =
      (CoreLaws.objectMap h ho p.1, CoreLaws.objectMap h ho p.2) := by
  apply (IndependentIndexedCarrierGraph.indexGraph (endpoints h) (endpoints_total h ho)).target_eq_of_edge
  change (h (.object p.1 _) && h (.object p.2 _)) = true
  have ha := (CoreLaws.objectGraph h ho).edge_target p.1
  have hb := (CoreLaws.objectGraph h ho).edge_target p.2
  change h (.object p.1 (CoreLaws.objectMap h ho p.1)) = true at ha
  change h (.object p.2 (CoreLaws.objectMap h ho p.2)) = true at hb
  simp [ha, hb]

/-- The common operation-role query is exactly the candidate endpoint/carrier graph projection. -/
def points (h : Table.{u, v} U mode) :
    IndependentIndexedCarrierGraph.Table.{u + 1, u + 1, u, u}
      (ArchitectureObject U × ArchitectureObject U) (ArchitectureObject U × ArchitectureObject U)
  | .edge (A, B) (A', B') q => h (.operation A B A' B' q)

/-- The primitive operation-family carrier at a fixed native ordered endpoint pair. -/
abbrev Fiber (O : ArchitectureObject U → ArchitectureObject U → Type u)
    (p : ArchitectureObject U × ArchitectureObject U) := O p.1 p.2

variable (h : Table.{u, v} U mode) (ho : CoreLaws.ObjectRows h)
variable (S T : ArchitectureObject U → ArchitectureObject U → Type u)

/-- Reindexing along the proved endpoint equation identifies the primitive family with the native operation family. -/
def nativeFamilyEquiv :
    (∀ p, Fiber S p → Fiber T (IndependentIndexedCarrierGraph.index (endpoints h) (endpoints_total h ho) p)) ≃
      (∀ A B, S A B → T (CoreLaws.objectMap h ho A) (CoreLaws.objectMap h ho B)) where
  toFun f A B x := cast (congrArg (Fiber T) (index_eq h ho (A, B))) (f (A, B) x)
  invFun g p x := cast (congrArg (Fiber T) (index_eq h ho p)).symm (g p.1 p.2 x)
  left_inv f := by
    funext p x
    simp only [cast_cast, cast_eq]
  right_inv g := by
    funext A B x
    simp only [cast_cast, cast_eq]

/-- The exact local row requirements for the operation-role projection. -/
abbrev IsLawful := IndependentIndexedCarrierGraph.IsLawful (endpoints h) (Fiber S) (Fiber T) (points h)

/-- All native directed operation families have complete candidate point presentations. -/
def readingEquiv :
    (∀ A B, S A B → T (CoreLaws.objectMap h ho A) (CoreLaws.objectMap h ho B)) ≃
      {t : IndependentIndexedCarrierGraph.Table.{u + 1, u + 1, u, u}
          (ArchitectureObject U × ArchitectureObject U) (ArchitectureObject U × ArchitectureObject U) //
        IndependentIndexedCarrierGraph.IsLawful (endpoints h) (Fiber S) (Fiber T) t} :=
  (nativeFamilyEquiv h ho S T).symm.trans
    (IndependentIndexedCarrierGraph.readingEquiv (endpoints h) (endpoints_total h ho) (Fiber S) (Fiber T))

/-- Construct the native operation family directly from the common Hom operation points. -/
def assemble (hl : IsLawful h S T) :
    ∀ A B, S A B → T (CoreLaws.objectMap h ho A) (CoreLaws.objectMap h ho B) :=
  (readingEquiv h ho S T).symm ⟨points h, hl⟩

/-- Native assembly and reading restore every operation query, including inactive endpoint/carrier rows. -/
theorem read_assemble (hl : IsLawful h S T) :
    (readingEquiv h ho S T (assemble h ho S T hl)).val = points h :=
  congrArg Subtype.val ((readingEquiv h ho S T).apply_symm_apply ⟨points h, hl⟩)

/-- Every native operation family is restored exactly from its point table. -/
theorem assemble_read (f : ∀ A B, S A B → T (CoreLaws.objectMap h ho A) (CoreLaws.objectMap h ho B)) :
    (readingEquiv h ho S T).symm (readingEquiv h ho S T f) = f :=
  (readingEquiv h ho S T).symm_apply_apply f

/-- Equality of the operation point table separates all native operation families. -/
theorem read_injective : Function.Injective (fun f => (readingEquiv h ho S T f).val) := by
  intro f g he
  exact (readingEquiv h ho S T).injective (Subtype.ext he)

end

end AAT.AG.LocalSemanticReconstruction.IndependentGeometryHomPrimitive.Operation

#assert_standard_axioms_only AAT.AG.LocalSemanticReconstruction.IndependentGeometryHomPrimitive.Operation
