import ResearchLean.AG.SFT.ConwayCoherentCommonRefinementFamily

/-!
Cycle 13 evidence for `G-sft-conway-01`.

Cycle 12 introduced coherent common-refinement support for a selected family of
forks.  This file records the selected morphism/naturality layer that is still
available without claiming arbitrary-cover naturality: if a source family is
obtained by reindexing or selecting forks from a target family, coherent support
and coherent global/common-refinement vanishing pull back along that family
morphism.

This is still selected finite Conway vocabulary.  It rules out one local
naturality failure for the selected family interface; it does not claim a full
cover category, sheaf condition, or arbitrary refinement naturality.
-/

namespace ResearchLean.AG
namespace SFT
namespace ConwayTwoTopology

/-! ## Selected morphisms of fork families -/

/--
A selected morphism of fork families over one atlas.  The source fork at each
index is exactly the target fork selected by `map`; this models subfamilies and
reindexings of the selected finite family.
-/
structure SupportForkFamilyMorphism {atlas : TwoCoverAtlas}
    (source target : SupportForkFamily atlas) where
  map : source.ForkIdx -> target.ForkIdx
  preserves_fork :
    forall idx, source.fork idx = target.fork (map idx)

namespace SupportForkFamilyMorphism

/-- The identity selected family morphism. -/
def id {atlas : TwoCoverAtlas}
    (family : SupportForkFamily atlas) :
    SupportForkFamilyMorphism family family where
  map idx := idx
  preserves_fork := by
    intro idx
    rfl

/-- Composition of selected family morphisms. -/
def comp {atlas : TwoCoverAtlas}
    {source middle target : SupportForkFamily atlas}
    (left : SupportForkFamilyMorphism source middle)
    (right : SupportForkFamilyMorphism middle target) :
    SupportForkFamilyMorphism source target where
  map idx := right.map (left.map idx)
  preserves_fork := by
    intro idx
    calc
      source.fork idx = middle.fork (left.map idx) := left.preserves_fork idx
      _ = target.fork (right.map (left.map idx)) :=
        right.preserves_fork (left.map idx)

/--
Coherent common-refinement support pulls back along a selected family morphism:
the same shared refinement span is used, and each source fork chooses the block
already chosen for its target image.
-/
def pullbackSupport {atlas : TwoCoverAtlas}
    {source target : SupportForkFamily atlas}
    (morphism : SupportForkFamilyMorphism source target)
    (support : CoherentCommonRefinementSupport target) :
    CoherentCommonRefinementSupport source where
  span := support.span
  ref idx := support.ref (morphism.map idx)
  refines_comm := by
    intro idx
    rw [morphism.preserves_fork idx]
    exact support.refines_comm (morphism.map idx)
  covers_comm := by
    intro idx context hcomm
    rw [morphism.preserves_fork idx] at hcomm
    exact support.covers_comm (morphism.map idx) context hcomm

end SupportForkFamilyMorphism

/-- Coherent family support is preserved by selected reindexing/subfamily maps. -/
theorem coherentCommonRefinementSupport_pullback
    {atlas : TwoCoverAtlas}
    {source target : SupportForkFamily atlas}
    (morphism : SupportForkFamilyMorphism source target)
    (support : CoherentCommonRefinementSupport target) :
    ForkFamilyHasCoherentCommonRefinementSupport source :=
  ⟨morphism.pullbackSupport support⟩

/--
Family-level coherent global/common-refinement vanishing pulls back along a
selected family morphism.  This is the selected naturality theorem available at
the current Conway interface.
-/
theorem coherentGlobalCommonRefinement_vanishes_pullback
    {atlas : TwoCoverAtlas}
    {source target : SupportForkFamily atlas}
    (morphism : SupportForkFamilyMorphism source target)
    (hvanish :
      SupportForkFamilyVanishesModuloCoherentGlobalCommonRefinement target) :
    SupportForkFamilyVanishesModuloCoherentGlobalCommonRefinement source := by
  rcases hvanish with ⟨hzero, hsupport⟩
  rcases hsupport with ⟨support⟩
  exact
    ⟨hzero,
      coherentCommonRefinementSupport_pullback morphism support⟩

/-! ## Reindexing and subfamily constructors -/

/-- Reindex a selected fork family by an arbitrary index map. -/
def SupportForkFamily.reindex {atlas : TwoCoverAtlas}
    (family : SupportForkFamily atlas)
    (Index : Type)
    (map : Index -> family.ForkIdx) :
    SupportForkFamily atlas where
  ForkIdx := Index
  fork idx := family.fork (map idx)

/-- The canonical morphism from a reindexed family back to its target family. -/
def SupportForkFamily.reindexMorphism {atlas : TwoCoverAtlas}
    (family : SupportForkFamily atlas)
    (Index : Type)
    (map : Index -> family.ForkIdx) :
    SupportForkFamilyMorphism
      (family.reindex Index map)
      family where
  map idx := map idx
  preserves_fork := by
    intro idx
    rfl

/-- Restrict a selected fork family to a chosen predicate on its indices. -/
def SupportForkFamily.subfamily {atlas : TwoCoverAtlas}
    (family : SupportForkFamily atlas)
    (predicate : family.ForkIdx -> Prop) :
    SupportForkFamily atlas where
  ForkIdx := { idx : family.ForkIdx // predicate idx }
  fork idx := family.fork idx.1

/-- The canonical inclusion morphism from a selected subfamily. -/
def SupportForkFamily.subfamilyInclusion {atlas : TwoCoverAtlas}
    (family : SupportForkFamily atlas)
    (predicate : family.ForkIdx -> Prop) :
    SupportForkFamilyMorphism
      (family.subfamily predicate)
      family where
  map idx := idx.1
  preserves_fork := by
    intro idx
    rfl

/-- Reindexed families inherit coherent support from the target family. -/
theorem reindexedFamily_coherentSupport
    {atlas : TwoCoverAtlas}
    (family : SupportForkFamily atlas)
    (Index : Type)
    (map : Index -> family.ForkIdx)
    (support : CoherentCommonRefinementSupport family) :
    ForkFamilyHasCoherentCommonRefinementSupport
      (family.reindex Index map) :=
  coherentCommonRefinementSupport_pullback
    (family.reindexMorphism Index map)
    support

/-- Selected subfamilies inherit coherent support from the target family. -/
theorem subfamily_coherentSupport
    {atlas : TwoCoverAtlas}
    (family : SupportForkFamily atlas)
    (predicate : family.ForkIdx -> Prop)
    (support : CoherentCommonRefinementSupport family) :
    ForkFamilyHasCoherentCommonRefinementSupport
      (family.subfamily predicate) :=
  coherentCommonRefinementSupport_pullback
    (family.subfamilyInclusion predicate)
    support

/-! ## Selected naturality receiver -/

/--
A selected naturality failure would be a morphism whose target family vanishes
but whose source family does not.  The pullback theorem rules this out.
-/
def CoherentFamilyMorphismNaturalityFailure {atlas : TwoCoverAtlas}
    {source target : SupportForkFamily atlas}
    (_morphism : SupportForkFamilyMorphism source target) : Prop :=
  SupportForkFamilyVanishesModuloCoherentGlobalCommonRefinement target /\
    Not
      (SupportForkFamilyVanishesModuloCoherentGlobalCommonRefinement source)

/-- Selected family morphisms have no coherent global/common-refinement naturality failure. -/
theorem no_coherentFamilyMorphismNaturalityFailure
    {atlas : TwoCoverAtlas}
    {source target : SupportForkFamily atlas}
    (morphism : SupportForkFamilyMorphism source target) :
    Not (CoherentFamilyMorphismNaturalityFailure morphism) := by
  intro hfailure
  exact hfailure.2
    (coherentGlobalCommonRefinement_vanishes_pullback
      morphism
      hfailure.1)

/--
The selected Cycle 13 package: coherent support and coherent global/common-
refinement vanishing are stable under selected family morphisms, and therefore
the selected morphism naturality failure is impossible.
-/
theorem selectedCoherentFamilyMorphismPackage :
    (forall {atlas : TwoCoverAtlas}
      {source target : SupportForkFamily atlas}
      (_morphism : SupportForkFamilyMorphism source target)
      (_support : CoherentCommonRefinementSupport target),
        ForkFamilyHasCoherentCommonRefinementSupport source) /\
      (forall {atlas : TwoCoverAtlas}
        {source target : SupportForkFamily atlas}
        (_morphism : SupportForkFamilyMorphism source target),
          SupportForkFamilyVanishesModuloCoherentGlobalCommonRefinement target ->
            SupportForkFamilyVanishesModuloCoherentGlobalCommonRefinement
              source) /\
      (forall {atlas : TwoCoverAtlas}
        {source target : SupportForkFamily atlas}
        (morphism : SupportForkFamilyMorphism source target),
          Not (CoherentFamilyMorphismNaturalityFailure morphism)) := by
  exact
    ⟨(by
        intro atlas source target morphism support
        exact coherentCommonRefinementSupport_pullback morphism support),
      (by
        intro atlas source target morphism hvanish
        exact coherentGlobalCommonRefinement_vanishes_pullback morphism hvanish),
      (by
        intro atlas source target morphism
        exact no_coherentFamilyMorphismNaturalityFailure morphism)⟩

end ConwayTwoTopology
end SFT
end ResearchLean.AG
