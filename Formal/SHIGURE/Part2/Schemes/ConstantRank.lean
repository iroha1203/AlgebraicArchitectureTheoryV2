import Formal.SHIGURE.Part2.Schemes.FiniteLocallyFreeFppf

/-! # Constant rank for finite locally free module sheaves

The ranks in Definition 6.1 are the stalk ranks of the modules in affine
associated-sheaf presentations. Full faithfulness makes this independent
of the presentation. Pullback and fppf reflection use the actual section
ring maps and the coefficient rank base-change formula of Appendix B.5.
-/

namespace SHIGURE.SchemeDescent

open AlgebraicGeometry CategoryTheory Scheme.Modules TopologicalSpace
open SHIGURE.CoefficientDescent

noncomputable section

universe u v

variable {X Y : Scheme.{u}} {M : X.Modules}

/-- The rank condition of Definition 6.1 on one affine open, measured by
`Module.rankAtStalk` in an associated-sheaf presentation. -/
def HasConstantRankOn (M : X.Modules) {U : X.Opens} (affine : IsAffineOpen U) (n : ℕ) : Prop :=
  ∃ N : ModuleCat.{u} Γ(X, U),
    Nonempty ((tilde.functor Γ(X, U)).obj N ≅ M.restrict affine.fromSpec) ∧
    ∀ p : PrimeSpectrum Γ(X, U), Module.rankAtStalk N p = n

/-- Finite locally free module sheaves of the prescribed rank in Definition
6.1. The finite local freeness is the existing sheaf property from B.3. -/
def IsFiniteLocallyFreeOfRank (M : X.Modules) (n : ℕ) : Prop :=
  IsFiniteLocallyFreeModule M ∧ ∀ U : X.affineOpens, HasConstantRankOn M U.property n

/-- Full faithfulness of the associated-sheaf functor identifies the ranks
in any two affine presentations; no finite or connected base is required. -/
theorem HasConstantRankOn.rank {U : X.Opens} {hU : IsAffineOpen U} {n : ℕ}
    (h : HasConstantRankOn M hU n) (N : ModuleCat.{u} Γ(X, U))
    (e : (tilde.functor Γ(X, U)).obj N ≅ M.restrict hU.fromSpec)
    (p : PrimeSpectrum Γ(X, U)) : Module.rankAtStalk N p = n := by
  obtain ⟨P, ⟨k⟩, ranks⟩ := h
  let comparison := (tilde.fullyFaithfulFunctor (R := Γ(X, U))).preimageIso (e ≪≫ k.symm)
  exact (congrFun (Module.rankAtStalk_eq_of_equiv comparison.toLinearEquiv) p).trans (ranks p)

/-- A prescribed affine presentation suffices for the rank predicate of
Definition 6.1, and every other presentation then has the same ranks. -/
theorem hasConstantRankOn_iff {U : X.Opens} {hU : IsAffineOpen U} (n : ℕ)
    (N : ModuleCat.{u} Γ(X, U))
    (e : (tilde.functor Γ(X, U)).obj N ≅ M.restrict hU.fromSpec) :
    HasConstantRankOn M hU n ↔ ∀ p : PrimeSpectrum Γ(X, U), Module.rankAtStalk N p = n :=
  ⟨fun h => h.rank N e, fun ranks => ⟨N, ⟨e⟩, ranks⟩⟩

/-- The coefficient base-change rank formula expressed for the actual
categorical extension-of-scalars functor used by sheaf pullback. -/
private theorem rank_extendScalars {R S : CommRingCat.{u}} (f : R ⟶ S)
    (N : ModuleCat.{u} R) (finite : FiniteLocallyFree R N) (q : PrimeSpectrum S) :
    Module.rankAtStalk ((ModuleCat.extendScalars f.hom).obj N) q =
      Module.rankAtStalk N (q.comap f.hom) := by
  letI : Algebra R S := f.hom.toAlgebra
  letI := finite.finitePresentation
  letI := finite.flat
  exact (congrFun (Module.rankAtStalk_eq_of_equiv
    (extendScalarsTensorIso (B := S) N).toLinearEquiv) q).trans
      (Module.rankAtStalk_baseChange (R := R) (M := N) q)

/-- The point of the source affine chart maps to the coefficient prime
specified by the actual map on section rings. -/
private theorem fromSpec_comap (f : Y ⟶ X) {U : X.Opens} {V : Y.Opens}
    (hU : IsAffineOpen U) (hV : IsAffineOpen V) (inside : V ≤ f ⁻¹ᵁ U)
    (q : PrimeSpectrum Γ(Y, V)) :
    hU.fromSpec (q.comap (f.appLE U V inside).hom) = f (hV.fromSpec q) := by
  change (Spec.map (f.appLE U V inside) ≫ hU.fromSpec) q = (hV.fromSpec ≫ f) q
  rw [IsAffineOpen.SpecMap_appLE_fromSpec f hU hV inside]

/-- On compatible affine charts, prescribed rank pulls back along any
scheme map. Finiteness and flatness come from the existing local-free
predicate, rather than additional hypotheses on the scheme map. -/
theorem HasConstantRankOn.pullback {f : Y ⟶ X} {U : X.Opens} {V : Y.Opens}
    {hU : IsAffineOpen U} {hV : IsAffineOpen V} {n : ℕ}
    (inside : V ≤ f ⁻¹ᵁ U) (finite : HasFiniteLocallyFreeOn M hU)
    (ranks : HasConstantRankOn M hU n) :
    HasConstantRankOn ((Scheme.Modules.pullback f).obj M) hV n := by
  obtain ⟨N, hn, ⟨e⟩⟩ := finite
  let a := f.appLE U V inside
  refine ⟨(ModuleCat.extendScalars a.hom).obj N,
    ⟨pullbackTildePresentationIso (hV := hV) inside e⟩, fun q => ?_⟩
  exact (rank_extendScalars a N hn q).trans (ranks.rank N e _)

/-- Isomorphisms of the actual module sheaves preserve the affine rank
condition, by composition of their tilde presentations. -/
theorem HasConstantRankOn.ofIso {N : X.Modules} {U : X.Opens} {hU : IsAffineOpen U} {n : ℕ}
    (h : HasConstantRankOn M hU n) (e : M ≅ N) : HasConstantRankOn N hU n := by
  obtain ⟨P, ⟨k⟩, ranks⟩ := h
  exact ⟨P, ⟨k ≪≫ (restrictFunctor hU.fromSpec).mapIso e⟩, ranks⟩

/-- Restricting finite locally free presentations gives the same rank at
coefficient primes mapping to a prescribed point of the larger chart. -/
private theorem rank_restrict_at {U V : X.Opens} {hU : IsAffineOpen U} {hV : IsAffineOpen V}
    (inside : V ≤ U) (N : ModuleCat.{u} Γ(X, U)) (finite : FiniteLocallyFree Γ(X, U) N)
    (e : (tilde.functor Γ(X, U)).obj N ≅ M.restrict hU.fromSpec)
    {n : ℕ} (ranks : HasConstantRankOn M hV n) (q : PrimeSpectrum Γ(X, V)) :
    Module.rankAtStalk N (q.comap (X.presheaf.map (homOfLE inside).op).hom) = n := by
  let a := X.presheaf.map (homOfLE inside).op
  let k := restrictTildePresentationIso (hV := hV) inside e
  exact (rank_extendScalars a N finite q).symm.trans (ranks.rank _ k q)

/-- A rank condition restricts to a smaller affine open, by the actual
section restriction ring map. Finite local freeness supplies the finite
flatness needed for the coefficient rank formula of B.5. -/
theorem HasConstantRankOn.restrict {U V : X.Opens} {hU : IsAffineOpen U} {hV : IsAffineOpen V}
    {n : ℕ} (inside : V ≤ U) (finite : HasFiniteLocallyFreeOn M hU)
    (ranks : HasConstantRankOn M hU n) : HasConstantRankOn M hV n := by
  obtain ⟨N, hn, ⟨e⟩⟩ := finite
  let a := X.presheaf.map (homOfLE inside).op
  refine ⟨(ModuleCat.extendScalars a.hom).obj N,
    ⟨restrictTildePresentationIso (hV := hV) inside e⟩, fun q => ?_⟩
  exact (rank_extendScalars a N hn q).trans (ranks.rank N e _)

/-- Affine-cover presentations of a prescribed rank yield the global
finite locally free rank condition of Definition 6.1. The cover can be
infinite; each coefficient prime is checked on a smaller affine overlap. -/
theorem IsFiniteLocallyFreeOfRank.of_affineCover {n : ℕ} {ι : Type u}
    (U : ι → X.affineOpens) (cover : (⨆ i, (U i : X.Opens)) = ⊤)
    (finite : ∀ i, HasFiniteLocallyFreeOn M (U i).property)
    (ranks : ∀ i, HasConstantRankOn M (U i).property n) : IsFiniteLocallyFreeOfRank M n := by
  have localFree : IsFiniteLocallyFreeModule M := ⟨ι, U, cover, finite⟩
  refine ⟨localFree, fun V => ?_⟩
  obtain ⟨P, hp, ⟨eP⟩⟩ := isFiniteLocallyFreeModule_iff_on_affineOpens.mp localFree V
  refine ⟨P, ⟨eP⟩, fun p => ?_⟩
  let x := V.property.fromSpec p
  have hx : x ∈ ⨆ i, (U i : X.Opens) := by rw [cover]; trivial
  obtain ⟨i, hxi⟩ := Opens.mem_iSup.mp hx
  have hxV : x ∈ V.1 := V.property.range_fromSpec.le ⟨p, rfl⟩
  obtain ⟨_, ⟨W, hW, rfl⟩, hxW, inside⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open (show x ∈ V.1 ⊓ (U i).1 from ⟨hxV, hxi⟩)
      (V.1 ⊓ (U i).1).isOpen
  have range : x ∈ Set.range hW.fromSpec := by rw [hW.range_fromSpec]; exact hxW
  obtain ⟨q, hq⟩ := range
  have rankW := (ranks i).restrict (hV := hW) (inside.trans inf_le_right) (finite i)
  have point : q.comap (X.presheaf.map (homOfLE (inside.trans inf_le_left)).op).hom = p := by
    apply V.property.fromSpec.isOpenEmbedding.injective
    change (Spec.map (X.presheaf.map (homOfLE (inside.trans inf_le_left)).op) ≫ V.property.fromSpec) q = _
    rw [V.property.map_fromSpec hW (homOfLE (inside.trans inf_le_left)).op]
    exact hq
  have result := rank_restrict_at (hU := V.property) (hV := hW) (inside.trans inf_le_left) P hp eP rankW q
  exact (congrArg (fun z : PrimeSpectrum Γ(X, V.1) => Module.rankAtStalk P z) point).symm.trans result

/-- Isomorphisms preserve finite locally free sheaves of a prescribed rank
in Definition 6.1, including the affine coefficient presentations. -/
theorem IsFiniteLocallyFreeOfRank.ofIso {N : X.Modules} {n : ℕ}
    (h : IsFiniteLocallyFreeOfRank M n) (e : M ≅ N) : IsFiniteLocallyFreeOfRank N n := by
  obtain ⟨ι, U, cover, finite⟩ := h.1
  refine ⟨⟨ι, U, cover, fun i => ?_⟩, fun V => (h.2 V).ofIso e⟩
  obtain ⟨P, hp, ⟨k⟩⟩ := finite i
  exact ⟨P, hp, ⟨k ≪≫ (restrictFunctor (U i).property.fromSpec).mapIso e⟩⟩

/-- Arbitrary scheme pullback preserves the finite locally free sheaf and
its prescribed constant rank in Definition 6.1, including rank zero. -/
theorem IsFiniteLocallyFreeOfRank.pullback {f : Y ⟶ X} {n : ℕ}
    (h : IsFiniteLocallyFreeOfRank M n) :
    IsFiniteLocallyFreeOfRank ((Scheme.Modules.pullback f).obj M) n := by
  refine ⟨h.1.pullback, ?_⟩
  intro V
  obtain ⟨P, hp, ⟨eP⟩⟩ := isFiniteLocallyFreeModule_iff_on_affineOpens.mp h.1.pullback V
  refine ⟨P, ⟨eP⟩, fun p => ?_⟩
  let y := V.property.fromSpec p
  obtain ⟨U, hyU⟩ := Opens.mem_iSup.mp ((iSup_affineOpens_eq_top X).ge (Set.mem_univ (f y)))
  have hy : y ∈ V.1 ⊓ f ⁻¹ᵁ U.1 :=
    ⟨V.property.range_fromSpec.le ⟨p, rfl⟩, hyU⟩
  obtain ⟨_, ⟨W, hW, rfl⟩, hyW, inside⟩ :=
    Y.isBasis_affineOpens.exists_subset_of_mem_open hy (V.1 ⊓ f ⁻¹ᵁ U.1).isOpen
  have range : y ∈ Set.range hW.fromSpec := by rw [hW.range_fromSpec]; exact hyW
  obtain ⟨q, hq⟩ := range
  have ranks := (h.2 U).pullback (hV := hW) (inside.trans inf_le_right)
    (isFiniteLocallyFreeModule_iff_on_affineOpens.mp h.1 U)
  have point : q.comap (Y.presheaf.map (homOfLE (inside.trans inf_le_left)).op).hom = p := by
    apply V.property.fromSpec.isOpenEmbedding.injective
    change (Spec.map (Y.presheaf.map (homOfLE (inside.trans inf_le_left)).op) ≫ V.property.fromSpec) q = _
    rw [V.property.map_fromSpec hW (homOfLE (inside.trans inf_le_left)).op]
    exact hq
  have result := rank_restrict_at (hU := V.property) (hV := hW) (inside.trans inf_le_left) P hp eP ranks q
  exact (congrArg (fun z : PrimeSpectrum Γ(Y, V.1) => Module.rankAtStalk P z) point).symm.trans result

/-- Fppf reflection of prescribed rank in Definition 6.1. Quasi-coherence
is the ambient descent hypothesis of B.3; finite local freeness is reflected
by the existing fppf theorem, and points lift through the given family. -/
theorem isFiniteLocallyFreeOfRank_of_fppfCover {n : ℕ} (cover : FppfCover.{u,v} X)
    (coherent : IsQuasiCoherentModule M)
    (localRanks : ∀ i, IsFiniteLocallyFreeOfRank ((Scheme.Modules.pullback (cover.f i)).obj M) n) :
    IsFiniteLocallyFreeOfRank M n := by
  let small : FppfCover.{u,u} X := {
    I₀ := X
    X x := cover.X (cover.idx x)
    f x := cover.f (cover.idx x)
    mem₀ := by
      rw [Scheme.presieve₀_mem_precoverage_iff]
      exact ⟨fun x => ⟨x, cover.covers x⟩, fun x => cover.map_prop (cover.idx x)⟩ }
  have finite := isFiniteLocallyFreeModule_of_fppfCover small coherent (fun x => (localRanks (cover.idx x)).1)
  refine ⟨finite, fun U => ?_⟩
  obtain ⟨N, hn, ⟨e⟩⟩ := isFiniteLocallyFreeModule_iff_on_affineOpens.mp finite U
  refine ⟨N, ⟨e⟩, fun p => ?_⟩
  let x := U.property.fromSpec p
  let i := cover.idx x
  let f := cover.f i
  obtain ⟨y, hy⟩ := cover.covers x
  have hyU : y ∈ f ⁻¹ᵁ U.1 := by
    change f y ∈ U.1
    rw [hy]
    exact U.property.range_fromSpec.le ⟨p, rfl⟩
  obtain ⟨_, ⟨V, hV, rfl⟩, hyV, inside⟩ :=
    (cover.X i).isBasis_affineOpens.exists_subset_of_mem_open hyU (f ⁻¹ᵁ U.1).isOpen
  have range : y ∈ Set.range hV.fromSpec := by rw [hV.range_fromSpec]; exact hyV
  obtain ⟨q, hq⟩ := range
  let a := f.appLE U.1 V inside
  let comparison := pullbackTildePresentationIso (hV := hV) inside e
  have ranks := (localRanks i).2 ⟨V, hV⟩
  have point : q.comap a.hom = p := by
    apply U.property.fromSpec.isOpenEmbedding.injective
    rw [fromSpec_comap f U.property hV inside q, hq]
    exact hy
  have result := (rank_extendScalars a N hn q).symm.trans (ranks.rank _ comparison q)
  rwa [point] at result

/-- The prescribed finite locally free rank of Definition 6.1 can be
checked on every component of an arbitrary fppf covering family. -/
theorem isFiniteLocallyFreeOfRank_iff_fppfCover {n : ℕ} (cover : FppfCover.{u,v} X)
    (coherent : IsQuasiCoherentModule M) : IsFiniteLocallyFreeOfRank M n ↔
      ∀ i, IsFiniteLocallyFreeOfRank ((Scheme.Modules.pullback (cover.f i)).obj M) n :=
  ⟨fun h _ => h.pullback, isFiniteLocallyFreeOfRank_of_fppfCover cover coherent⟩

end

end SHIGURE.SchemeDescent
