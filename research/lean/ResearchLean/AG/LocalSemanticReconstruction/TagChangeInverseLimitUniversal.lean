import ResearchLean.AG.LocalSemanticReconstruction.TagChangeFiniteGroupReconstruction
import Formal.Util.AssertStandardAxioms

/-! Universal property of the existing finite tagged table family.

Implementation notes: `Projections` records maps into the accepted finite
`LocalTagTable` groups and their restriction equations. The lift is constructed
through the existing coherent-family equivalence, so its codomain is the
actual tagged source-choice subgroup used by the local reconstruction. -/

namespace AAT.AG.LocalSemanticReconstruction

namespace TagChangeInverseLimitUniversal

open TagChange

/-- A group acting by compatible finite tag tables. The only data are finite
projections and their restriction equations. -/
structure Projections (G : Type*) [Group G] where
  map : ∀ S : Finset TaggedArchitectureIndex,
    G →* Multiplicative (LocalTagTable S)
  coherent : ∀ (S T : Finset TaggedArchitectureIndex) (h : S ⊆ T)
    (g : G), LocalTagTable.restrict h ((map T g).toAdd) = (map S g).toAdd

variable {G : Type*} [Group G]

/-- The universal compatible finite projections give a group map into the
existing coherent-family group, using singleton assembly only later. -/
noncomputable def toCoherentFamily (p : Projections G) :
    G →* Multiplicative (CoherentFamily TaggedArchitectureIndex) where
  toFun g := Multiplicative.ofAdd
    { value := fun S => (p.map S g).toAdd
      coherent := fun S T h => p.coherent S T h g }
  map_one' := by
    apply congrArg Multiplicative.ofAdd
    apply CoherentFamily.ext
    intro S
    exact congrArg Multiplicative.toAdd (map_one (p.map S))
  map_mul' g h := by
    apply congrArg Multiplicative.ofAdd
    apply CoherentFamily.ext
    intro S
    exact congrArg Multiplicative.toAdd (map_mul (p.map S) g h)

/-- Any coherent family of finite group projections lifts to the accepted
tagged source-choice subgroup. -/
noncomputable def lift (p : Projections G) : G →* taggedSourceChoiceAutSubgroup :=
  taggedSourceChoiceSubgroupMulEquivCoherentFamily.symm.toMonoidHom.comp
    (toCoherentFamily p)

/-- The lift has exactly the prescribed projection at each finite source set;
this is the projection API for the universal property. -/
theorem lift_value (p : Projections G) (g : G)
    (S : Finset TaggedArchitectureIndex) :
    (taggedSourceChoiceSubgroupMulEquivCoherentFamily (lift p g)).toAdd.value S =
      (p.map S g).toAdd := by
  simp [lift, toCoherentFamily]

/-- The finite projections determine their group lift uniquely. -/
theorem lift_unique (p : Projections G)
    (other : G →* taggedSourceChoiceAutSubgroup)
    (h : ∀ g S,
      (taggedSourceChoiceSubgroupMulEquivCoherentFamily (other g)).toAdd.value S =
        (p.map S g).toAdd) : other = lift p := by
  apply MonoidHom.ext
  intro g
  apply taggedSourceChoiceSubgroupMulEquivCoherentFamily.injective
  apply congrArg Multiplicative.ofAdd
  apply CoherentFamily.ext
  intro S
  change (taggedSourceChoiceSubgroupMulEquivCoherentFamily (other g)).toAdd.value S =
    (taggedSourceChoiceSubgroupMulEquivCoherentFamily (lift p g)).toAdd.value S
  rw [h, lift_value]

#assert_standard_axioms_only AAT.AG.LocalSemanticReconstruction.TagChangeInverseLimitUniversal

end TagChangeInverseLimitUniversal

end AAT.AG.LocalSemanticReconstruction
