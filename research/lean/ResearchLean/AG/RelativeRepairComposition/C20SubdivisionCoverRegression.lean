import ResearchLean.AG.RelativeRepairComposition.SubdivisionPublicNames
import ResearchLean.AG.RelativeRepairComposition.C18SubdivisionRegression
import ResearchLean.AG.RelativeRepairComposition.C17ForbiddenRange

/-!
# The specified W4 has a generated closed cover and unchanged public candidate

## Implementation notes

One cover member is the complete original W4 and the second is its fixed vertex
region. The overlap contains the actual old vertex and no edge. This applies
the general cover construction to the same authored face with two occurrences
of the chosen a, rather than a face-free surrogate. Candidate b stays public
while both actual factors are private in the first member.
-/
namespace AAT.AG.RelativeRepairComposition.C20SubdivisionCoverRegression
open TransportCoherence Subdivision C17SubdivisionInput

/-- Two original closed members retain the full face and its actual fixed overlap. -/
def regions : Bool → ClosedRegion geometry
  | false => ClosedRegion.all
  | true => fixedRegion

/-- The original two-member family covers every original 0–3 cell. -/
theorem regions_cover : ClosedRegion.IndexedCover regions := by
  refine ⟨fun _ => ⟨false,trivial⟩,fun _ => ⟨false,trivial⟩,
    fun _ => ⟨false,trivial⟩,fun _ => ⟨false,trivial⟩⟩

/-- The actual chosen a is a private always edge in the complete member. -/
theorem chosen_private : chosen ∈ ClosedRegion.privateAlwaysEdges regions fixedRegion {candidate} false := by
  refine ⟨trivial,not_false,C18SubdivisionRegression.chosen_not_candidate,?_⟩
  rintro ⟨j,hj,he⟩
  cases j
  · exact hj rfl
  · exact he

/-- The general construction covers the complete actual subdivided W4. -/
theorem split_regions_cover :
    ClosedRegion.IndexedCover (fun j => expandedRegion geometry chosen (regions j)) :=
  expanded_indexed_cover geometry chosen regions regions_cover

/-- The first actual factor remains a private variable in the same member. -/
theorem first_private : firstEdgeName geometry chosen ∈ ClosedRegion.privateAlwaysEdges
    (fun j => expandedRegion geometry chosen (regions j)) (expandedRegion geometry chosen fixedRegion)
    (oldEdgeSet geometry chosen {candidate}) false :=
  (first_private_iff geometry chosen regions fixedRegion {candidate}
    C18SubdivisionRegression.chosen_not_candidate false).mpr chosen_private

/-- The full second actual factor also remains private, rather than being fixed to a section value. -/
theorem second_private : secondEdgeName geometry chosen ∈ ClosedRegion.privateAlwaysEdges
    (fun j => expandedRegion geometry chosen (regions j)) (expandedRegion geometry chosen fixedRegion)
    (oldEdgeSet geometry chosen {candidate}) false :=
  (second_private_iff geometry chosen regions fixedRegion {candidate}
    C18SubdivisionRegression.chosen_not_candidate false).mpr chosen_private

/-- The complete original candidate b is a public name in the original full member. -/
theorem candidate_public : candidate ∈ publicEdges geometry regions fixedRegion {candidate} false := by
  refine ⟨trivial,not_false,?_⟩
  exact ClosedRegion.candidate_not_private regions fixedRegion {candidate} false candidate rfl

/-- The candidate at its original endpoints remains in the independently generated new public complement. -/
theorem split_candidate_public : oldEdgeName geometry chosen candidate chosen_ne_candidate.symm ∈
    publicEdges (presentation geometry chosen) (fun j => expandedRegion geometry chosen (regions j))
      (expandedRegion geometry chosen fixedRegion) (oldEdgeSet geometry chosen {candidate}) false := by
  rw [expanded_public_edges geometry chosen regions fixedRegion {candidate}
    C18SubdivisionRegression.chosen_not_candidate]
  exact candidate_public

/-- The whole public comparison reads the same b name, rather than a chosen column image. -/
theorem candidate_name_value :
    (publicNameEquiv geometry chosen regions fixedRegion {candidate} false chosen_private false
      ⟨oldEdgeName geometry chosen candidate chosen_ne_candidate.symm,split_candidate_public⟩).1 = candidate := rfl

/-- The actual full public coefficient families use the general two-sided comparison. -/
noncomputable def publicValuesEquiv := PublicKernels.familyEquiv geometry chosen regions fixedRegion
  {candidate} originalTower factors false chosen_private false

/-- Every actual public candidate value is retained in the full kernel, without image restriction. -/
theorem candidate_coefficient_value
    (x : ∀ a : publicEdges (presentation geometry chosen)
      (fun j => expandedRegion geometry chosen (regions j)) (expandedRegion geometry chosen fixedRegion)
      (oldEdgeSet geometry chosen {candidate}) false,
      splitTower.toTower.localCoefficients.A a.1.2.1) :
    publicValuesEquiv x ⟨candidate,candidate_public⟩ =
      x ⟨oldEdgeName geometry chosen candidate chosen_ne_candidate.symm,split_candidate_public⟩ := rfl

/-- The distinct-member overlap stays precisely the same fixed original vertex region. -/
theorem split_overlap_fixed :
    ClosedRegion.inter (expandedRegion geometry chosen (regions false))
      (expandedRegion geometry chosen (regions true)) = expandedRegion geometry chosen fixedRegion := by
  rw [← expanded_inter]
  congr 1
  apply closedRegion_eq <;> simp [regions,ClosedRegion.inter,ClosedRegion.all]

/-- The new vertex is absent from the fixed overlap and remains free. -/
theorem fresh_not_fixed : (Sum.inr () : (presentation geometry chosen).Vertex) ∉
    (expandedRegion geometry chosen fixedRegion).vertices := not_false

/-- The authored original face substitutes b,a,a in the same full temporal order. -/
theorem full_face_word : (presentation geometry chosen).twoLeft () =
    PresentedPath.cons (oldEdge geometry chosen candidate chosen_ne_candidate.symm)
      (.cons (firstEdge geometry chosen) (.cons (secondEdge geometry chosen)
        (.cons (firstEdge geometry chosen) (.cons (secondEdge geometry chosen) (.nil (Sum.inl () : Vertex geometry)))))) := by
  change substitutePath geometry chosen (.cons (i := ()) (j := ()) true
    (.cons (i := ()) (j := ()) false (.cons (i := ()) (j := ()) false (.nil ())))) = _
  simp only [substitutePath]
  have hb : edgeWord geometry chosen (⟨(),(),true⟩ : EdgeName (K := geometry)) =
      .cons (oldEdge geometry chosen candidate chosen_ne_candidate.symm) (.nil (Sum.inl () : Vertex geometry)) :=
    edgeWord_old geometry chosen candidate chosen_ne_candidate.symm
  have ha : edgeWord geometry chosen (⟨(),(),false⟩ : EdgeName (K := geometry)) =
      factorPath geometry chosen := edgeWord_chosen geometry chosen
  simp only [hb,ha,factorPath,PresentedPath.append]

/-- Both factor names occur in the same actual nontrivial authored face. -/
theorem both_factors_in_face :
    firstEdgeName geometry chosen ∈ pathEdges ((presentation geometry chosen).twoLeft ()) ∧
    secondEdgeName geometry chosen ∈ pathEdges ((presentation geometry chosen).twoLeft ()) := by
  rw [full_face_word]
  exact ⟨Or.inr (Or.inl rfl),Or.inr (Or.inr (Or.inl rfl))⟩

/-- Every permission S keeps exactly the same forbidden public b condition. -/
theorem candidate_mask (S : Set (EdgeName (K := geometry))) :
    oldEdgeName geometry chosen candidate chosen_ne_candidate.symm ∈ oldEdgeSet geometry chosen ({candidate} \ S) ↔
      candidate ∉ S := by
  rw [retained_forbidden_mask geometry chosen {candidate}
    C18SubdivisionRegression.chosen_not_candidate]
  exact and_iff_right rfl

/-- The factors in this same cover are precisely those generated from the whole affine operations. -/
theorem actual_factor_origin :
    NativeAffine.subdivisionFactors geometry reference reference comparison linear_faces chosen first second
      (by simpa [reference,chosen] using factor_product) = factors :=
  C18SubdivisionRegression.factors_generated

end AAT.AG.RelativeRepairComposition.C20SubdivisionCoverRegression
#assert_standard_axioms_only AAT.AG.RelativeRepairComposition.C20SubdivisionCoverRegression
