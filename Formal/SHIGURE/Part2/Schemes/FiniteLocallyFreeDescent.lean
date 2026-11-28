import Formal.SHIGURE.Part2.Schemes.Effective.FppfStack
import Formal.SHIGURE.Part2.Schemes.FiniteLocallyFreeFppf
import Formal.SHIGURE.Part2.Schemes.ConstantRank

/-! # Effective descent of finite locally free module sheaves

Appendix B.3 restricts effective quasi-coherent descent to finite locally
free objects, retaining every module morphism.

## Implementation notes

The descent category is a full subcategory of the actual quasi-coherent
descent category. Its extra predicate requires local finite freeness of
the given modules; it contains no effectivity certificate. Reflection
along the original fppf cover proves that the existing inverse lands in
finite locally free modules.
-/

namespace SHIGURE.SchemeDescent

open AlgebraicGeometry CategoryTheory CategoryTheory.Pseudofunctor Opposite

noncomputable section

universe u v

private abbrev Q := quasiCoherentModulesPseudofunctor.{u}

/-- B.3 local finite freeness is invariant under isomorphism of actual module sheaves. -/
theorem IsFiniteLocallyFreeModule.ofIso {X : Scheme.{u}} {M N : X.Modules}
    (h : IsFiniteLocallyFreeModule M) (e : M ≅ N) : IsFiniteLocallyFreeModule N := by
  obtain ⟨ι, U, covers, presentations⟩ := h
  refine ⟨ι, U, covers, fun i => ?_⟩
  obtain ⟨P, finite, ⟨presentation⟩⟩ := presentations i
  exact ⟨P, finite, ⟨presentation ≪≫
    (Scheme.Modules.restrictFunctor (U i).property.fromSpec).mapIso e⟩⟩

/-- The local-freeness predicate on quasi-coherent modules in Appendix B.3. -/
def finiteLocallyFreeProperty (X : Scheme.{u}) : ObjectProperty (Q.obj (.mk (op X))) :=
  fun M => IsFiniteLocallyFreeModule M.obj

/-- All finite locally free module sheaves, with every module morphism retained. -/
abbrev FiniteLocallyFreeModules (X : Scheme.{u}) := (finiteLocallyFreeProperty X).FullSubcategory

variable {X : Scheme.{u}} (cover : FppfCover.{u,v} X)

/-- Evaluate actual descent data on one specified member of the original cover. -/
def fppfModuleDescentEvaluation (i : cover.I₀) :
    FppfModuleDescentData cover ⥤ Q.obj (.mk (op (cover.X i))) where
  obj D := D.obj i
  map f := f.hom i

/-- The B.3 condition on the modules already specified by a descent datum. -/
def finiteLocallyFreeDescentProperty : ObjectProperty (FppfModuleDescentData cover) :=
  fun D => ∀ i, IsFiniteLocallyFreeModule (D.obj i).obj

/-- Finite locally free descent data, retaining all compatible module maps. -/
abbrev FiniteLocallyFreeDescentData := (finiteLocallyFreeDescentProperty cover).FullSubcategory

/-- Pullback to the original fppf family gives finite locally free descent data. -/
def finiteLocallyFreeComparison : FiniteLocallyFreeModules X ⥤ FiniteLocallyFreeDescentData cover where
  obj M := ⟨(fppfModuleComparison cover).obj M.obj, fun _ => M.property.pullback⟩
  map f := ObjectProperty.homMk ((fppfModuleComparison cover).map f.hom)

/-- B.3 compatible local arrows between finite locally free objects descend uniquely. -/
def finiteLocallyFreeComparison_fullyFaithful : (finiteLocallyFreeComparison cover).FullyFaithful := by
  letI := fppfModuleComparison_isEquivalence cover
  let ff := Functor.FullyFaithful.ofFullyFaithful (fppfModuleComparison cover)
  exact
    { preimage := fun f => ObjectProperty.homMk (ff.preimage f.hom)
      map_preimage := fun f => ObjectProperty.hom_ext _ (ff.map_preimage f.hom)
      preimage_map := fun f => ObjectProperty.hom_ext _ (ff.preimage_map f.hom) }

/-- B.3 the existing quasi-coherent inverse is finite locally free: the property
is reflected by the original cover, using its actual local comparison isomorphisms. -/
theorem finiteLocallyFreeComparison_essSurj : (finiteLocallyFreeComparison cover).EssSurj := by
  letI := fppfModuleComparison_isEquivalence cover
  let F := fppfModuleComparison cover
  refine ⟨fun D => ?_⟩
  let M := F.objPreimage D.obj
  let e := F.objObjPreimageIso D.obj
  have finite : IsFiniteLocallyFreeModule M.obj := by
    let small : FppfCover.{u,u} X := {
      I₀ := X
      X x := cover.X (cover.idx x)
      f x := cover.f (cover.idx x)
      mem₀ := by
        rw [Scheme.presieve₀_mem_precoverage_iff]
        exact ⟨fun x => ⟨x, cover.covers x⟩, fun x => cover.map_prop (cover.idx x)⟩ }
    apply isFiniteLocallyFreeModule_of_fppfCover small M.property
    intro x
    let i := cover.idx x
    let ei := (fppfModuleDescentEvaluation cover i).mapIso e
    exact (D.property i).ofIso
      ((ObjectProperty.ι _).mapIso ei).symm
  exact ⟨⟨M, finite⟩, ⟨ObjectProperty.isoMk _ e⟩⟩

/-- Appendix B.3 effective descent for finite locally free modules and every
compatible module map over an arbitrary fppf covering family. -/
theorem finiteLocallyFreeComparison_isEquivalence :
    (finiteLocallyFreeComparison cover).IsEquivalence := by
  let ff := finiteLocallyFreeComparison_fullyFaithful cover
  exact ⟨ff.faithful, ff.full, finiteLocallyFreeComparison_essSurj cover⟩

/-- The actual B.3 comparison, as an equivalence of categories. -/
def finiteLocallyFreeComparisonEquivalence :
    FiniteLocallyFreeModules X ≌ FiniteLocallyFreeDescentData cover := by
  letI := finiteLocallyFreeComparison_isEquivalence cover
  exact (finiteLocallyFreeComparison cover).asEquivalence

/-- Prescribed-rank module sheaves in Definition 6.1, retaining all module maps. -/
def constantRankProperty (n : ℕ) : ObjectProperty (Q.obj (.mk (op X))) :=
  fun M => IsFiniteLocallyFreeOfRank M.obj n

/-- The prescribed-rank predicate on the actual local modules of a datum. -/
def constantRankDescentProperty (n : ℕ) : ObjectProperty (FppfModuleDescentData cover) :=
  fun D => ∀ i, IsFiniteLocallyFreeOfRank (D.obj i).obj n

/-- Pullback with its actual overlap comparisons at a fixed rank. -/
def constantRankComparison (n : ℕ) :
    (constantRankProperty (X := X) n).FullSubcategory ⥤
      (constantRankDescentProperty cover n).FullSubcategory where
  obj M := ⟨(fppfModuleComparison cover).obj M.obj, fun _ => M.property.pullback⟩
  map f := ObjectProperty.homMk ((fppfModuleComparison cover).map f.hom)

/-- All compatible local module maps at a fixed rank descend uniquely. -/
def constantRankComparison_fullyFaithful (n : ℕ) :
    (constantRankComparison cover n).FullyFaithful := by
  letI := fppfModuleComparison_isEquivalence cover
  let ff := Functor.FullyFaithful.ofFullyFaithful (fppfModuleComparison cover)
  exact
    { preimage := fun f => ObjectProperty.homMk (ff.preimage f.hom)
      map_preimage := fun f => ObjectProperty.hom_ext _ (ff.map_preimage f.hom)
      preimage_map := fun f => ObjectProperty.hom_ext _ (ff.preimage_map f.hom) }

/-- Effectivity at a prescribed rank follows from actual fppf rank reflection,
using the local components of the quasi-coherent comparison isomorphism. -/
theorem constantRankComparison_essSurj (n : ℕ) : (constantRankComparison cover n).EssSurj := by
  letI := fppfModuleComparison_isEquivalence cover
  let F := fppfModuleComparison cover
  refine ⟨fun D => ?_⟩
  let M := F.objPreimage D.obj
  let e := F.objObjPreimageIso D.obj
  have ranks : IsFiniteLocallyFreeOfRank M.obj n := by
    apply isFiniteLocallyFreeOfRank_of_fppfCover cover M.property
    intro i
    let ei := (fppfModuleDescentEvaluation cover i).mapIso e
    exact (D.property i).ofIso ((ObjectProperty.ι _).mapIso ei).symm
  exact ⟨⟨M, ranks⟩, ⟨ObjectProperty.isoMk _ e⟩⟩

/-- Appendix B.3 and Lemma 6.2: the actual fppf comparison is an equivalence
for modules of any prescribed rank, including rank zero. -/
theorem constantRankComparison_isEquivalence (n : ℕ) :
    (constantRankComparison cover n).IsEquivalence := by
  let ff := constantRankComparison_fullyFaithful cover n
  exact ⟨ff.faithful, ff.full, constantRankComparison_essSurj cover n⟩

/-- The prescribed-rank comparison as an actual equivalence of categories. -/
def constantRankComparisonEquivalence (n : ℕ) :
    (constantRankProperty (X := X) n).FullSubcategory ≌
      (constantRankDescentProperty cover n).FullSubcategory := by
  letI := constantRankComparison_isEquivalence cover n
  exact (constantRankComparison cover n).asEquivalence

end

end SHIGURE.SchemeDescent
