import ResearchLean.AG.VisibleCycleReflection.OpenSupport
import ResearchLean.AG.ObstructionDiagnosticBridge.AATLocallyConstantObstruction
import Mathlib.Topology.Sheaves.SheafCondition.Sites
import Formal.Util.AssertStandardAxioms

/-!
# G-132: continuity of the input-generated open support functor

## Implementation notes

The generated precoverage need not be stable under base change. Continuity
is proved by mapping its generated pullback sieves to open covers, using the
point coverage of each admissible family and preservation of actual product
contexts. No continuity certificate is accepted as external input.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits Set TopologicalSpace

namespace AAT.AG.VisibleCycleReflection
namespace OpenSupport

open CanonicalResolution ObstructionDiagnosticBridge

universe u

variable {Source Space : Type u} {laws : FiniteLawFamily Source}
variable (P : GeneratorPresentation laws) [TopologicalSpace Space]

/-- A: the context product is a pullback cone for two actual restrictions. -/
def contextPullbackCone {X Y Z : (site (X := Space) P).category} (f : X ⟶ Z) (g : Y ⟶ Z) :
    PullbackCone f g :=
  PullbackCone.mk
    (homOfLE (Site.productContextFiniteMeet.meet_le_left X.ctx Y.ctx))
    (homOfLE (Site.productContextFiniteMeet.meet_le_right X.ctx Y.ctx))
    (Subsingleton.elim _ _)

/-- A: the product-context cone has the required pullback universal property. -/
def contextPullbackConeIsLimit {X Y Z : (site (X := Space) P).category} (f : X ⟶ Z) (g : Y ⟶ Z) :
    IsLimit ((contextPullbackCone P) f g) :=
  PullbackCone.IsLimit.mk _
    (fun s => homOfLE
      (Site.productContextFiniteMeet.le_meet (leOfHom s.fst) (leOfHom s.snd)))
    (fun _ => Subsingleton.elim _ _)
    (fun _ => Subsingleton.elim _ _)
    (fun _ _ _ _ => Subsingleton.elim _ _)

/-- A: local pullback instances for the generated-topology sheaf criterion. -/
noncomputable local instance contextHasPullback
    {X Y Z : (site (X := Space) P).category} (f : X ⟶ Z) (g : Y ⟶ Z) : HasPullback f g :=
  ⟨⟨⟨(contextPullbackCone P) f g, (contextPullbackConeIsLimit P) f g⟩⟩⟩

/-- A: the support image of the context pullback is the open intersection. -/
def supportMapPullbackConeIsLimit {X Y Z : (site (X := Space) P).category} (f : X ⟶ Z) (g : Y ⟶ Z) :
    IsLimit
      (PullbackCone.mk
        ((supportFunctor (X := Space) P).map ((contextPullbackCone P) f g).fst)
        ((supportFunctor (X := Space) P).map ((contextPullbackCone P) f g).snd)
        (Subsingleton.elim _ _) :
        PullbackCone ((supportFunctor (X := Space) P).map f) ((supportFunctor (X := Space) P).map g)) :=
  PullbackCone.IsLimit.mk _
    (fun s => homOfLE (by
      change s.pt ≤ (supportFunctor (X := Space) P).obj
        (Site.ContextCategoryObject.of (contextPreorder (X := Space) P)
          (Site.productContext X.ctx Y.ctx))
      rw [supportFunctor_obj_product P X.ctx Y.ctx]
      exact le_inf (leOfHom s.fst) (leOfHom s.snd)))
    (fun _ => Subsingleton.elim _ _)
    (fun _ => Subsingleton.elim _ _)
    (fun _ _ _ _ => Subsingleton.elim _ _)

/-- A: the support functor preserves pullbacks of actual restrictions. -/
theorem supportFunctor_preservesPullback
    {X Y Z : (site (X := Space) P).category} (f : X ⟶ Z) (g : Y ⟶ Z) :
    PreservesLimit (cospan f g) (supportFunctor (X := Space) P) :=
  preservesLimit_of_preserves_limit_cone
    ((contextPullbackConeIsLimit P) f g)
    ((PullbackCone.isLimitMapConeEquiv
      ((contextPullbackCone P) f g) (supportFunctor (X := Space) P)).symm
      ((supportMapPullbackConeIsLimit P) f g))

/-- A: generated pullback sieves of admissible covers map to genuine open covers. -/
theorem mapped_pullback_mem_open_topology
    {X Y : (site (X := Space) P).category} (f : Y ⟶ X)
    (F : Site.AATCoverageFamily (coverageRequirements (X := Space) P) (overlap (X := Space) P) X) :
    Sieve.generate
        (((Sieve.generate F.presieve).pullback f).arrows.map (supportFunctor (X := Space) P)) ∈
      Opens.grothendieckTopology Space ((supportFunctor (X := Space) P).obj Y) := by
  intro x hx
  obtain ⟨i, hi⟩ := F.admissible.atomSupportCoverage (.inl x) trivial
  let patchObject := Site.ContextCategoryObject.of (contextPreorder (X := Space) P) (F.patch i)
  let Q := Site.ContextCategoryObject.of (contextPreorder (X := Space) P)
    (Site.productContext Y.ctx (F.patch i))
  let q : Q ⟶ Y :=
    homOfLE (Site.productContextFiniteMeet.meet_le_left Y.ctx (F.patch i))
  let qpatch : Q ⟶ patchObject :=
    homOfLE (Site.productContextFiniteMeet.meet_le_right Y.ctx (F.patch i))
  have hq : (Sieve.generate F.presieve).pullback f q := by
    change Sieve.generate F.presieve (q ≫ f)
    have hinclusion : Sieve.generate F.presieve
        (homOfLE (F.inclusion i)) :=
      Sieve.le_generate F.presieve _ (Presieve.ofArrows.mk i)
    have hcomp := (Sieve.generate F.presieve).downward_closed hinclusion qpatch
    convert hcomp using 1
  refine ⟨(supportFunctor (X := Space) P).obj Q, (supportFunctor (X := Space) P).map q, ?_, ?_⟩
  · exact Sieve.le_generate _ _ (Presieve.map.of hq)
  · rw [supportFunctor_obj_product P Y.ctx (F.patch i)]
    exact ⟨hx, hi⟩

/-- A: continuity follows from input-generated coverage and preservation of pullbacks. -/
theorem supportFunctor_isContinuous :
    Functor.IsContinuous.{u} (supportFunctor (X := Space) P) (site (X := Space) P).topology
      (Opens.grothendieckTopology Space) where
  op_comp_isSheaf_of_types := by
    rintro ⟨G, hG⟩
    rw [isSheaf_iff_isSheaf_of_type] at hG
    rw [Site.AATSite.topology, Site.AATGrothendieckTopology]
    rw [Precoverage.isSheaf_toGrothendieck_iff]
    intro X Y f R hR
    rcases hR with ⟨F, rfl⟩
    letI : (supportFunctor (X := Space) P).PreservesPairwisePullbacks
        ((Sieve.generate F.presieve).pullback f).arrows := {
      preservesLimit := by
        intro R Y left right hleft hright
        exact (supportFunctor_preservesPullback P) left right
    }
    letI : ((Sieve.generate F.presieve).pullback f).arrows.HasPairwisePullbacks :=
      ⟨by
        intro Y Z left hleft right hright
        exact contextHasPullback P left right⟩
    rw [Presieve.IsSheafFor.comp_iff_of_preservesPairwisePullbacks]
    apply (Presieve.isSheafFor_iff_generate _).mpr
    exact hG _ ((mapped_pullback_mem_open_topology P) f F)

/-- A: package the proved continuity with the constructed support for the G-125 API. -/
def contextOpenSupport : ContextOpenSupport (site (X := Space) P) where
  space := TopCat.of Space
  support := (supportFunctor (X := Space) P)
  continuous := (supportFunctor_isContinuous P)

/-- A: public normalization of the support package on an input open context. -/
@[simp]
theorem contextOpenSupport_obj_openContext (W : Opens Space) :
    (contextOpenSupport (Space := Space) P).support.obj
      (Site.ContextCategoryObject.of (contextPreorder (X := Space) P) (openContext P W)) = W :=
  contextSupport_openContext P W

end OpenSupport
end AAT.AG.VisibleCycleReflection

#assert_standard_axioms_only AAT.AG.VisibleCycleReflection.OpenSupport
