import ResearchLean.AG.LocalSemanticReconstruction.IndependentGeometryHomInvariantPresentationComposition
import Formal.Util.AssertStandardAxioms

/-!
# Auxiliary erasure after primitive coherent composition

The two input local classes provide coherent representatives by quotient
induction. Their primitive rows construct a coherent composite presentation.
Only then is a representative chosen and erased. Every original query and
every finite fragment is the directly supplied composite table, independently
of the auxiliary presentation chosen for that table.
-/

namespace AAT.AG.LocalSemanticReconstruction.IndependentGeometryHomPrimitive.InvariantWitness

noncomputable section

universe u v

variable {U : AtomCarrier.{u}} {mode : Mode} {I J K : InvariantFamily U}
variable (p : Local.{u, v} I J mode) (q : Local.{u, v} J K mode)
variable (h : IndependentGeometryHomPrimitive.Table.{u, v} U mode)
variable (ho : ∀ A C, h (.object A C) = (retained J K q).table (.object ((retained I J p).objectMap A) C))
variable (hi : invariant h = IndependentCarrierGraph.compose I.Index J.Index K.Index
  (invariant (retained I J p).table) (retained I J p).indexRows (invariant (retained J K q).table))

include ho hi in
/-- Coherent input representatives construct a coherent presentation for the primitive composite table. -/
theorem exists_compositePresentation : ∃ r : Presentation.{u, v} I K mode, r.retained.table = h := by
  induction p using Quotient.inductionOn with
  | _ p =>
    induction q using Quotient.inductionOn with
    | _ q => exact ⟨composePresentation p q h ho hi, composePresentation_table p q h ho hi⟩

/-- Erase auxiliary choices only after composing their original primitive coherent rows. -/
def composeLocal : Local.{u, v} I K mode :=
  Quotient.mk _ (exists_compositePresentation p q h ho hi).choose

/-- The composite local class retains exactly the primitive table supplied to its construction. -/
theorem composeLocal_table : (retained I K (composeLocal p q h ho hi)).table = h :=
  (exists_compositePresentation p q h ho hi).choose_spec

/-- Every original point of the composed local class is its directly composed query value. -/
theorem composeLocal_point (a : IndependentGeometryHomPrimitive.Query.{u, v} U mode) :
    point I K (composeLocal p q h ho hi) a = h a :=
  congrFun (composeLocal_table p q h ho hi) a

/-- Every finite fragment of the composite is the restriction of that same primitive point table. -/
theorem composeLocal_fragment (S : Finset (IndependentGeometryHomPrimitive.Query.{u, v} U mode)) :
    fragment I K (composeLocal p q h ho hi) S = TagChange.LocalTagTable.read h S :=
  congrArg (fun f : TagChange.CoherentFamily (IndependentGeometryHomPrimitive.Query.{u, v} U mode) => f.value S)
    ((TagChange.read_assemble (retained I K (composeLocal p q h ho hi)).family).symm.trans
      (congrArg TagChange.read (composeLocal_table p q h ho hi)))

/-- Any coherent auxiliary presentation of the same composed points gives the same local Hom. -/
theorem composeLocal_choice_independent (r : Presentation.{u, v} I K mode) (hr : r.retained.table = h) :
    (Quotient.mk _ r : Local I K mode) = composeLocal p q h ho hi := by
  apply point_ext
  intro a
  exact (congrFun hr a).trans (composeLocal_point p q h ho hi a).symm

end

end AAT.AG.LocalSemanticReconstruction.IndependentGeometryHomPrimitive.InvariantWitness

#assert_standard_axioms_only AAT.AG.LocalSemanticReconstruction.IndependentGeometryHomPrimitive.InvariantWitness
