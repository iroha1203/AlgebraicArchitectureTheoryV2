import Formal.Util.AssertStandardAxioms
import ResearchLean.AG.RelativeRepairComposition.GeneratedCoverAction
import ResearchLean.AG.RelativeRepairComposition.GeneratedPublicRelations

/-!
# All-range inclusions of the same strict generated interfaces

## Implementation notes

Only the forbidden-candidate predicate changes with the allowed range.
Local matrices, sections, public relations and private kernels are identical.
-/
namespace AAT.AG.RelativeRepairComposition
open CategoryTheory TransportCoherence AbelianLiftingObstruction
universe uk uG uA uI
namespace GeneratedRangeInclusion
set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 200000
variable {k : Type uk} [Field k] [Fintype k] [DecidableEq k]
variable {K : FiniteTransportPresentation.{uG}} {I : Type uI} [Fintype I] [DecidableEq I]
variable (M : LocalCoefficients.{uG,uA} K) [∀ v, Module k (M.A v)]
variable (bases : FiniteFamily.Bases (k := k) M.A) (P : ClosedRegion K) (U : I → ClosedRegion K)
variable [DecidablePred (· ∈ P.edges)] [DecidablePred (· ∈ P.faces)]
variable [∀ i, DecidablePred (· ∈ (U i).vertices)]
variable [∀ i, DecidablePred (· ∈ (U i).edges)] [∀ i, DecidablePred (· ∈ (U i).faces)]
variable (candidates : Set (EdgeName (K := K))) [DecidablePred (· ∈ candidates)]
variable (hlinear : ∀ {i j : K.Vertex} (e : K.Edge i j) (t : k) (x : M.A i),
  M.edge e (t • x) = t • M.edge e x)
variable (δ : RelativeCover.C2 M ClosedRegion.all P)
variable [Fintype (EdgeName (K := K))] [DecidableEq (EdgeName (K := K))]
variable [Fintype K.TwoCell] [DecidableEq K.TwoCell]
variable (enumK : FiniteElimination.Enumeration k)
variable (enumEdges : FiniteElimination.Enumeration (EdgeName (K := K)))
variable (enumFaces : FiniteElimination.Enumeration K.TwoCell)

variable {S V : Set (EdgeName (K := K))}

/-- Support relaxation includes every original compatible label with its complete vertex values. -/
def labelsInclusion (h : S ⊆ V) : StrictSupportedCover.Labels M P U candidates S →+
    StrictSupportedCover.Labels M P U candidates V where
  toFun b := ⟨fun i => ⟨(b.1 i).1,by
    intro e he
    exact (b.1 i).2 e ⟨he.1,fun hs => he.2 (h hs)⟩⟩,b.2⟩
  map_zero' := Subtype.ext (by funext i; exact Subtype.ext rfl)
  map_add' _ _ := Subtype.ext (by funext i; exact Subtype.ext rfl)

/-- Range relaxation leaves all generated local relations and all private kernel vectors unchanged. -/
def objectsInclusion (h : S ⊆ V)
    (y : GeneratedStrictCover.Objects M bases P U candidates hlinear δ enumK enumEdges enumFaces S) :
    GeneratedStrictCover.Objects M bases P U candidates hlinear δ enumK enumEdges enumFaces V :=
  ⟨y.1,fun i e he => y.2.1 i e ⟨he.1,fun hs => he.2 (h hs)⟩,y.2.2⟩

/-- Public feasibility relaxes only the forbidden candidate conditions on the same relation. -/
def publicInclusion (h : S ⊆ V)
    (z : GeneratedPublicRelations.Objects M bases P U candidates hlinear δ enumK enumEdges enumFaces S) :
    GeneratedPublicRelations.Objects M bases P U candidates hlinear δ enumK enumEdges enumFaces V :=
  ⟨z.1,fun i e he => z.2.1 i e ⟨he.1,fun hs => he.2 (h hs)⟩,z.2.2⟩

/-- Relaxation commutes with every full generated gauge action. -/
theorem equivariant (h : S ⊆ V)
    (b : Multiplicative (StrictSupportedCover.Labels M P U candidates S))
    (y : GeneratedStrictCover.Objects M bases P U candidates hlinear δ enumK enumEdges enumFaces S) :
    objectsInclusion M bases P U candidates hlinear δ enumK enumEdges enumFaces h (b • y) =
      (labelsInclusion M P U candidates h).toMultiplicative b •
        objectsInclusion M bases P U candidates hlinear δ enumK enumEdges enumFaces h y := by
  apply Subtype.ext
  rfl

/-- Range relaxation is a full original-label functor on the same generated strict interfaces. -/
def functor (h : S ⊆ V) :
    GeneratedCoverAction.Groupoid M bases P U candidates hlinear δ enumK enumEdges enumFaces S ⥤
      GeneratedCoverAction.Groupoid M bases P U candidates hlinear δ enumK enumEdges enumFaces V :=
  actionLabelFunctor (labelsInclusion M P U candidates h).toMultiplicative
    (objectsInclusion M bases P U candidates hlinear δ enumK enumEdges enumFaces h)
    (equivariant M bases P U candidates hlinear δ enumK enumEdges enumFaces h)

/-- The range functor retains all generated public and private values. -/
theorem functor_obj_values (h : S ⊆ V)
    (y : GeneratedCoverAction.Groupoid M bases P U candidates hlinear δ enumK enumEdges enumFaces S) :
    ((functor M bases P U candidates hlinear δ enumK enumEdges enumFaces h).obj y).back.1 = y.back.1 := rfl

/-- The range functor keeps every compatible original vertex label on all arrows. -/
theorem functor_label_value (h : S ⊆ V)
    {x y : GeneratedCoverAction.Groupoid M bases P U candidates hlinear δ enumK enumEdges enumFaces S}
    (b : x ⟶ y) (i : I) (v : (U i).vertices) :
    ((((functor M bases P U candidates hlinear δ enumK enumEdges enumFaces h).map b).1.toAdd).1 i).1.1 v =
      (b.1.toAdd.1 i).1.1 v := rfl

/-- Successive range relaxations compose on full objects and all full labeled arrows. -/
theorem functor_comp {W : Set (EdgeName (K := K))} (h : S ⊆ V) (g : V ⊆ W) :
    functor M bases P U candidates hlinear δ enumK enumEdges enumFaces h ⋙
      functor M bases P U candidates hlinear δ enumK enumEdges enumFaces g =
        functor M bases P U candidates hlinear δ enumK enumEdges enumFaces (h.trans g) := rfl

/-- Public extraction commutes with range relaxation on the same generated relation. -/
theorem public_inclusion_comm (h : S ⊆ V)
    (y : GeneratedStrictCover.Objects M bases P U candidates hlinear δ enumK enumEdges enumFaces S) :
    GeneratedPublicRelations.publicCoordinates M bases P U candidates hlinear δ enumK enumEdges enumFaces V
      (objectsInclusion M bases P U candidates hlinear δ enumK enumEdges enumFaces h y) =
    publicInclusion M bases P U candidates hlinear δ enumK enumEdges enumFaces h
      (GeneratedPublicRelations.publicCoordinates M bases P U candidates hlinear δ enumK enumEdges enumFaces S y) := rfl

end GeneratedRangeInclusion
end AAT.AG.RelativeRepairComposition
#assert_standard_axioms_only AAT.AG.RelativeRepairComposition
