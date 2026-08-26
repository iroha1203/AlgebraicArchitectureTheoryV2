import ResearchLean.AG.DoctrineFiberProduct.IndexedBaseDiagram
import ResearchLean.AG.DoctrineFiberProduct.IndexedBaseChangeTwoCellNoGo

/-!
# Raw indexed-family liftability classification

This module proves G-111 K5.  It separates the uniform local cancellation
question at one vertex index from the sufficient condition for one finite raw
family.  The family support records the sources of its generating squares and
declared cells.  Epimorphicity on that support generates the target declared
relations and hence a coherent diagnostic-free diagram morphism.

A separate finite coherent example has a non-epimorphic source index, distinct
parallel path syntax, and a nonidentity participating target edge.  It is kept
independent of the Cycle 15 diagnostic witness.  The Cycle 7 validated-square
counterexample remains the negative branch for arbitrary raw families.

## Implementation notes

`IndexedRawSquareFamily` is total on every generating edge of one fixed finite
shape because the target statement classifies a selected finite family rather
than a partial subgraph.  Consequently support is source incidence in that
owned shape; it does not inspect equality of semantic arrow values.  A partial
edge-family was rejected because it would add membership data absent from K5
and obscure which squares the family owns.  The raw structure deliberately has
no target-relation field: relations are generated from source relations and
support liftability, preventing the desired conclusion from being supplied as
input.  `SupportEpiProduction` retains the pointwise local theorem beside the
generated target and hom so every support premise remains auditable; returning
only the hom would erase that proof-use.  A fixed-family converse was rejected
because accidental coherence need not imply epimorphicity.
-/

namespace AAT.AG.DoctrineFiberProduct

universe u

open CategoryTheory
open AtomFoundation

/-- Uniform target-base liftability at one index, with the endpoint and both
right legs universally quantified in the exact order fixed by G-111. -/
def UniformTargetBaseLiftableAt {U : AtomCarrier.{u}}
    {source target : ExtractionInstance U} (index : source ⟶ target) : Prop :=
  ∀ (endpoint : ExtractionInstance U) (left right : target ⟶ endpoint),
    index ≫ left = index ≫ right → left = right

/-- The new local name is definitionally the Cycle 7 cancellation predicate. -/
theorem uniformTargetBaseLiftableAt_iff_indexedTargetBaseCongruenceAt
    {U : AtomCarrier.{u}} {source target : ExtractionInstance U}
    (index : source ⟶ target) :
    UniformTargetBaseLiftableAt index ↔ IndexedTargetBaseCongruenceAt index :=
  Iff.rfl

/-- Uniform target-base liftability at one index is exactly epimorphicity. -/
theorem uniformTargetBaseLiftableAt_iff_epi
    {U : AtomCarrier.{u}} {source target : ExtractionInstance U}
    (index : source ⟶ target) :
    UniformTargetBaseLiftableAt index ↔ Epi index := by
  simpa only [uniformTargetBaseLiftableAt_iff_indexedTargetBaseCongruenceAt]
    using indexedTargetBaseCongruenceAt_iff_epi index

/-! ## One finite raw family and its support -/

/-- A finite raw square family over a coherent source diagram.  It supplies
target vertices, vertex indices, target generating edges, and the actual
commutative generating squares, but no target declared relation. -/
structure IndexedRawSquareFamily {G : IndexedBaseTwoShape.{u}}
    {U : AtomCarrier.{u}} (source : IndexedBaseDiagram G U) where
  /-- Target extraction instance at every vertex. -/
  targetVertex : G.Vertex → ExtractionInstance U
  /-- Vertexwise transport index. -/
  index : ∀ vertex, source.vertex vertex ⟶ targetVertex vertex
  /-- Target arrow assigned to every generating edge. -/
  targetEdge : {i j : G.Vertex} → G.Edge i j →
    (targetVertex i ⟶ targetVertex j)
  /-- Each generating edge is equipped with its actual validated square. -/
  square : ∀ {i j : G.Vertex} (edge : G.Edge i j),
    ValidatedIndexedBaseSquare U (index i) (source.edge edge)
      (targetEdge edge) (index j)

namespace IndexedRawSquareFamily

/-- A vertex participates in a raw family when it is the source of a
generating square or of a declared cell. -/
def Supports {G : IndexedBaseTwoShape.{u}} {U : AtomCarrier.{u}}
    {source : IndexedBaseDiagram G U} (_family : IndexedRawSquareFamily source)
    (vertex : G.Vertex) : Prop :=
  (∃ target, Nonempty (G.Edge vertex target)) ∨
    ∃ cell : G.TwoCell, G.twoSource cell = vertex

/- Because `IndexedRawSquareFamily` is total on the fixed finite shape, every
shape edge is an owned generating square.  Thus support depends on the
family's edge/cell incidence, not on equality of its semantic arrow values. -/

/-- The finite support of one raw family. -/
noncomputable def support {G : IndexedBaseTwoShape.{u}}
    {U : AtomCarrier.{u}} {source : IndexedBaseDiagram G U}
    (family : IndexedRawSquareFamily source) : Finset G.Vertex := by
  classical
  exact Finset.univ.filter family.Supports

/-- Every generating square contributes its source vertex to support. -/
theorem edgeSource_mem_support {G : IndexedBaseTwoShape.{u}}
    {U : AtomCarrier.{u}} {source : IndexedBaseDiagram G U}
    (family : IndexedRawSquareFamily source) {i j : G.Vertex}
    (edge : G.Edge i j) : i ∈ family.support := by
  classical
  simp only [support, Finset.mem_filter, Finset.mem_univ, true_and, Supports]
  exact Or.inl ⟨j, ⟨edge⟩⟩

/-- Every declared cell contributes its source vertex to support. -/
theorem twoSource_mem_support {G : IndexedBaseTwoShape.{u}}
    {U : AtomCarrier.{u}} {source : IndexedBaseDiagram G U}
    (family : IndexedRawSquareFamily source) (cell : G.TwoCell) :
    G.twoSource cell ∈ family.support := by
  classical
  simp only [support, Finset.mem_filter, Finset.mem_univ, true_and, Supports]
  exact Or.inr ⟨cell, rfl⟩

/-- Vertexwise epimorphicity restricted to the owned finite support. -/
def SupportEpi {G : IndexedBaseTwoShape.{u}} {U : AtomCarrier.{u}}
    {source : IndexedBaseDiagram G U} (family : IndexedRawSquareFamily source) :
    Prop :=
  ∀ vertex, vertex ∈ family.support → Epi (family.index vertex)

/-- Uniform local target liftability restricted to the same finite support. -/
def SupportUniformLiftable {G : IndexedBaseTwoShape.{u}}
    {U : AtomCarrier.{u}} {source : IndexedBaseDiagram G U}
    (family : IndexedRawSquareFamily source) : Prop :=
  ∀ vertex, vertex ∈ family.support →
    UniformTargetBaseLiftableAt (family.index vertex)

/-- The local epi equivalence lifts pointwise to the entire finite support. -/
theorem supportUniformLiftable_iff_supportEpi
    {G : IndexedBaseTwoShape.{u}} {U : AtomCarrier.{u}}
    {source : IndexedBaseDiagram G U} (family : IndexedRawSquareFamily source) :
    family.SupportUniformLiftable ↔ family.SupportEpi := by
  constructor
  · intro liftable vertex supported
    exact (uniformTargetBaseLiftableAt_iff_epi (family.index vertex)).1
      (liftable vertex supported)
  · intro epi vertex supported
    exact (uniformTargetBaseLiftableAt_iff_epi (family.index vertex)).2
      (epi vertex supported)

/-- Evaluate a finite path using the raw target edges. -/
def targetPath {G : IndexedBaseTwoShape.{u}} {U : AtomCarrier.{u}}
    {source : IndexedBaseDiagram G U} (family : IndexedRawSquareFamily source)
    {i j : G.Vertex} (path : IndexedBasePath G.toIndexedBaseShape i j) :
    family.targetVertex i ⟶ family.targetVertex j :=
  IndexedBasePath.eval family.targetVertex family.targetEdge path

/-- The generating square laws paste to every finite path. -/
theorem path_naturality {G : IndexedBaseTwoShape.{u}} {U : AtomCarrier.{u}}
    {source : IndexedBaseDiagram G U} (family : IndexedRawSquareFamily source)
    {i j : G.Vertex} (path : IndexedBasePath G.toIndexedBaseShape i j) :
    family.index i ≫ family.targetPath path =
      source.path path ≫ family.index j := by
  induction path with
  | nil vertex =>
      simp [targetPath, IndexedBasePath.eval, IndexedBaseDiagram.path]
  | cons edge tail inductionHypothesis =>
      calc
        family.index _ ≫ family.targetPath (.cons edge tail) =
            (family.index _ ≫ family.targetEdge edge) ≫
              family.targetPath tail := by
          simp [targetPath, IndexedBasePath.eval, Category.assoc]
        _ = (source.edge edge ≫ family.index _) ≫
              family.targetPath tail := by
          rw [(family.square edge).term.commutes]
        _ = source.edge edge ≫
              (family.index _ ≫ family.targetPath tail) := by
          rw [Category.assoc]
        _ = source.edge edge ≫
              (source.path tail ≫ family.index _) := by
          rw [inductionHypothesis]
        _ = (source.edge edge ≫ source.path tail) ≫
              family.index _ := by rw [Category.assoc]
        _ = source.path (.cons edge tail) ≫ family.index _ := rfl

/-- Epimorphicity at the declared-cell source generates its target relation. -/
theorem targetRelation_of_epi {G : IndexedBaseTwoShape.{u}}
    {U : AtomCarrier.{u}} {source : IndexedBaseDiagram G U}
    (family : IndexedRawSquareFamily source) (cell : G.TwoCell)
    (epiSource : Epi (family.index (G.twoSource cell))) :
    family.targetPath (G.twoLeft cell) =
      family.targetPath (G.twoRight cell) := by
  letI : Epi (family.index (G.twoSource cell)) := epiSource
  apply (cancel_epi (family.index (G.twoSource cell))).mp
  rw [family.path_naturality (G.twoLeft cell),
    family.path_naturality (G.twoRight cell), source.relation_path cell]

/-- Every support epi hypothesis is converted pointwise to the corresponding
uniform local liftability theorem. -/
theorem supportLiftable_of_supportEpi
    {G : IndexedBaseTwoShape.{u}} {U : AtomCarrier.{u}}
    {source : IndexedBaseDiagram G U} (family : IndexedRawSquareFamily source)
    (supportEpi : family.SupportEpi) : family.SupportUniformLiftable :=
  (family.supportUniformLiftable_iff_supportEpi).2 supportEpi

/-- Uniform liftability at the declared-cell source generates its target
relation without changing the quantifier order of the local theorem. -/
theorem targetRelation_of_supportLiftable
    {G : IndexedBaseTwoShape.{u}} {U : AtomCarrier.{u}}
    {source : IndexedBaseDiagram G U} (family : IndexedRawSquareFamily source)
    (supportLiftable : family.SupportUniformLiftable) (cell : G.TwoCell) :
    family.targetPath (G.twoLeft cell) =
      family.targetPath (G.twoRight cell) := by
  apply supportLiftable (G.twoSource cell) (family.twoSource_mem_support cell)
    (family.targetVertex (G.twoTarget cell))
  rw [family.path_naturality (G.twoLeft cell),
    family.path_naturality (G.twoRight cell), source.relation_path cell]

/-- Epimorphicity on precisely the finite support generates the target
diagnostic-free diagram. -/
noncomputable def toTargetDiagram_of_supportEpi
    {G : IndexedBaseTwoShape.{u}} {U : AtomCarrier.{u}}
    {source : IndexedBaseDiagram G U} (family : IndexedRawSquareFamily source)
    (supportEpi : family.SupportEpi) :
    IndexedBaseDiagram G U where
  vertex := family.targetVertex
  edge := family.targetEdge
  relation := fun cell => family.targetRelation_of_supportLiftable
    (family.supportLiftable_of_supportEpi supportEpi) cell

/-- The support-indexed vertexwise-epi producer: a raw family becomes a
coherent diagram morphism without any necessity claim for unused vertices. -/
noncomputable def toDiagramHom_of_supportEpi
    {G : IndexedBaseTwoShape.{u}} {U : AtomCarrier.{u}}
    {source : IndexedBaseDiagram G U} (family : IndexedRawSquareFamily source)
    (supportEpi : family.SupportEpi) :
    IndexedBaseDiagramHom source (family.toTargetDiagram_of_supportEpi supportEpi) where
  app := family.index
  naturality := fun edge => (family.square edge).term.commutes.symm

/-- Auditable output of the support-indexed producer.  It retains the local
uniform theorem at every support vertex together with the generated target and
diagram morphism. -/
structure SupportEpiProduction {G : IndexedBaseTwoShape.{u}}
    {U : AtomCarrier.{u}} {source : IndexedBaseDiagram G U}
    (family : IndexedRawSquareFamily source) where
  uniformAtSupport : family.SupportUniformLiftable
  target : IndexedBaseDiagram G U
  hom : IndexedBaseDiagramHom source target

/-- Produce the complete support certificate and coherent diagram morphism. -/
noncomputable def produce_of_supportEpi
    {G : IndexedBaseTwoShape.{u}} {U : AtomCarrier.{u}}
    {source : IndexedBaseDiagram G U} (family : IndexedRawSquareFamily source)
    (supportEpi : family.SupportEpi) : family.SupportEpiProduction where
  uniformAtSupport := family.supportLiftable_of_supportEpi supportEpi
  target := family.toTargetDiagram_of_supportEpi supportEpi
  hom := family.toDiagramHom_of_supportEpi supportEpi

end IndexedRawSquareFamily

/-! ## A finite coherent positive with a non-epimorphic index -/

/-- The sole vertex of the finite coherent positive. -/
inductive FiniteNonEpiCoherentVertex : Type
  | point
  deriving DecidableEq, Fintype

/-- Two parallel generating loops of the finite coherent positive. -/
inductive FiniteNonEpiCoherentEdge :
    FiniteNonEpiCoherentVertex → FiniteNonEpiCoherentVertex → Type
  | left : FiniteNonEpiCoherentEdge .point .point
  | right : FiniteNonEpiCoherentEdge .point .point

/-- Boolean enumeration of the two parallel loops. -/
def finiteNonEpiCoherentEdgeEquiv : Bool ≃
    FiniteNonEpiCoherentEdge FiniteNonEpiCoherentVertex.point
      FiniteNonEpiCoherentVertex.point where
  toFun
    | false => .left
    | true => .right
  invFun
    | .left => false
    | .right => true
  left_inv value := by cases value <;> rfl
  right_inv edge := by cases edge <;> rfl

instance finiteNonEpiCoherentEdgeFintype
    (i j : FiniteNonEpiCoherentVertex) :
    Fintype (FiniteNonEpiCoherentEdge i j) := by
  cases i
  cases j
  exact Fintype.ofEquiv Bool finiteNonEpiCoherentEdgeEquiv

/-- The named declared cell of the finite coherent positive. -/
inductive FiniteNonEpiCoherentCell : Type
  | beta
  deriving DecidableEq, Fintype

/-- The underlying finite one-vertex, two-loop shape. -/
noncomputable abbrev finiteNonEpiCoherentBaseShape : IndexedBaseShape where
  Vertex := FiniteNonEpiCoherentVertex
  vertexFintype := inferInstance
  Edge := FiniteNonEpiCoherentEdge
  edgeFintype := finiteNonEpiCoherentEdgeFintype
  TwoCell := FiniteNonEpiCoherentCell
  twoCellFintype := inferInstance
  twoSource := fun _ => FiniteNonEpiCoherentVertex.point
  twoTarget := fun _ => FiniteNonEpiCoherentVertex.point

/-- The first named parallel path. -/
def finiteNonEpiCoherentLeftPath : IndexedBasePath
    finiteNonEpiCoherentBaseShape FiniteNonEpiCoherentVertex.point
      FiniteNonEpiCoherentVertex.point :=
  @IndexedBasePath.cons finiteNonEpiCoherentBaseShape
    FiniteNonEpiCoherentVertex.point FiniteNonEpiCoherentVertex.point
    FiniteNonEpiCoherentVertex.point FiniteNonEpiCoherentEdge.left
    (@IndexedBasePath.nil finiteNonEpiCoherentBaseShape
      FiniteNonEpiCoherentVertex.point)

/-- The second named parallel path. -/
def finiteNonEpiCoherentRightPath : IndexedBasePath
    finiteNonEpiCoherentBaseShape FiniteNonEpiCoherentVertex.point
      FiniteNonEpiCoherentVertex.point :=
  @IndexedBasePath.cons finiteNonEpiCoherentBaseShape
    FiniteNonEpiCoherentVertex.point FiniteNonEpiCoherentVertex.point
    FiniteNonEpiCoherentVertex.point FiniteNonEpiCoherentEdge.right
    (@IndexedBasePath.nil finiteNonEpiCoherentBaseShape
      FiniteNonEpiCoherentVertex.point)

/-- One vertex, two parallel loop edges, and one named cell. -/
noncomputable abbrev finiteNonEpiCoherentShape : IndexedBaseTwoShape where
  toIndexedBaseShape := finiteNonEpiCoherentBaseShape
  twoLeft := fun _ => finiteNonEpiCoherentLeftPath
  twoRight := fun _ => finiteNonEpiCoherentRightPath

/-- The named vertex in the coherent positive's indexed shape. -/
abbrev finiteNonEpiCoherentVertex : finiteNonEpiCoherentShape.Vertex :=
  FiniteNonEpiCoherentVertex.point

/-- The named declared cell in the coherent positive's indexed shape. -/
abbrev finiteNonEpiCoherentCell : finiteNonEpiCoherentShape.TwoCell :=
  FiniteNonEpiCoherentCell.beta

/-- The first participating edge in the coherent positive's indexed shape. -/
abbrev finiteNonEpiCoherentLeftEdge :
    finiteNonEpiCoherentShape.Edge finiteNonEpiCoherentVertex
      finiteNonEpiCoherentVertex :=
  FiniteNonEpiCoherentEdge.left

/-- Coherent source diagram with two identity loops. -/
noncomputable def finiteNonEpiCoherentSource :
    IndexedBaseDiagram finiteNonEpiCoherentShape FiniteModel.carrier where
  vertex := fun _ => finiteFixtureInstance
  edge := fun _ => 𝟙 finiteFixtureInstance
  relation := fun cell => by
    change FiniteNonEpiCoherentCell at cell
    cases cell
    simp [finiteNonEpiCoherentShape, finiteNonEpiCoherentLeftPath,
      finiteNonEpiCoherentRightPath, IndexedBasePath.eval]

/-- Coherent target diagram with two copies of the same nonidentity constant
target action. -/
noncomputable def finiteNonEpiCoherentTarget :
    IndexedBaseDiagram finiteNonEpiCoherentShape FiniteModel.carrier where
  vertex := fun _ => finiteDuplicatedInstance
  edge := fun _ => finiteDuplicateConstant
  relation := fun cell => by
    change FiniteNonEpiCoherentCell at cell
    cases cell
    simp [finiteNonEpiCoherentShape, finiteNonEpiCoherentLeftPath,
      finiteNonEpiCoherentRightPath, IndexedBasePath.eval]

/-- The non-epimorphic vertex index nevertheless defines a coherent diagram
morphism on the finite positive. -/
noncomputable def finiteNonEpiCoherentHom :
    IndexedBaseDiagramHom finiteNonEpiCoherentSource
      finiteNonEpiCoherentTarget where
  app := fun _ => finiteDuplicateIndex
  naturality := fun edge => by
    simpa [finiteNonEpiCoherentSource, finiteNonEpiCoherentTarget,
      finiteDuplicateIdentity] using
        finiteDuplicateIndex_comp_identity_eq_constant.symm

/-- The participating vertex index of the coherent positive is not epi. -/
theorem finiteDuplicateIndex_not_epi : ¬ Epi finiteDuplicateIndex := by
  intro epiIndex
  letI : Epi finiteDuplicateIndex := epiIndex
  exact finiteDuplicateIdentity_ne_constant
    ((cancel_epi finiteDuplicateIndex).mp
      finiteDuplicateIndex_comp_identity_eq_constant)

/-- Read the first edge label of a path, if present. -/
def finiteNonEpiFirstEdge :
    IndexedBasePath finiteNonEpiCoherentShape.toIndexedBaseShape
      finiteNonEpiCoherentVertex finiteNonEpiCoherentVertex → Option Bool
  | .nil _ => none
  | .cons edge _ => by
      change FiniteNonEpiCoherentEdge FiniteNonEpiCoherentVertex.point
        FiniteNonEpiCoherentVertex.point at edge
      cases edge
      · exact some false
      · exact some true

/-- The named positive cell has syntactically distinct parallel paths. -/
theorem finiteNonEpiCoherent_paths_ne :
    finiteNonEpiCoherentShape.twoLeft finiteNonEpiCoherentCell ≠
      finiteNonEpiCoherentShape.twoRight finiteNonEpiCoherentCell := by
  intro equality
  have firstEdgeEquality := congrArg finiteNonEpiFirstEdge equality
  simp [finiteNonEpiCoherentShape, finiteNonEpiCoherentLeftPath,
    finiteNonEpiCoherentRightPath, finiteNonEpiFirstEdge] at firstEdgeEquality

/-- The target action participating in the named cell is nonidentity. -/
theorem finiteNonEpiCoherent_action_ne_identity :
    finiteNonEpiCoherentTarget.edge
        (i := finiteNonEpiCoherentVertex)
        (j := finiteNonEpiCoherentVertex)
        finiteNonEpiCoherentLeftEdge ≠
      𝟙 (finiteNonEpiCoherentTarget.vertex finiteNonEpiCoherentVertex) := by
  simpa [finiteNonEpiCoherentTarget, finiteDuplicateIdentity] using
    finiteDuplicateIdentity_ne_constant.symm

/-- K5 coherent positive: non-epi source index, distinct parallel syntax,
nonidentity participating action, and an authored target relation coexist. -/
theorem finiteNonEpiCoherent_positive :
    (¬ Epi (finiteNonEpiCoherentHom.app finiteNonEpiCoherentVertex)) ∧
      (finiteNonEpiCoherentShape.twoLeft finiteNonEpiCoherentCell ≠
        finiteNonEpiCoherentShape.twoRight finiteNonEpiCoherentCell) ∧
      (finiteNonEpiCoherentTarget.edge
          (i := finiteNonEpiCoherentVertex)
          (j := finiteNonEpiCoherentVertex)
          finiteNonEpiCoherentLeftEdge ≠
        𝟙 (finiteNonEpiCoherentTarget.vertex finiteNonEpiCoherentVertex)) ∧
      (finiteNonEpiCoherentTarget.path
          (finiteNonEpiCoherentShape.twoLeft finiteNonEpiCoherentCell) =
        finiteNonEpiCoherentTarget.path
          (finiteNonEpiCoherentShape.twoRight finiteNonEpiCoherentCell)) := by
  exact ⟨finiteDuplicateIndex_not_epi, finiteNonEpiCoherent_paths_ne,
    finiteNonEpiCoherent_action_ne_identity,
    finiteNonEpiCoherentTarget.relation_path finiteNonEpiCoherentCell⟩

/-! ## Concrete instance pairs for the classification predicates -/

/-- Identity transport is a concrete positive instance of local uniform
target-base liftability. -/
theorem finiteIdentity_uniformTargetBaseLiftableAt :
    UniformTargetBaseLiftableAt (𝟙 finiteFixtureInstance) :=
  (uniformTargetBaseLiftableAt_iff_epi (𝟙 finiteFixtureInstance)).2
    (inferInstance : Epi (𝟙 finiteFixtureInstance))

/-- The duplicated finite index is a concrete negative instance of local
uniform target-base liftability. -/
theorem finiteDuplicate_not_uniformTargetBaseLiftableAt :
    ¬ UniformTargetBaseLiftableAt finiteDuplicateIndex := by
  intro liftable
  exact finiteDuplicateIndex_not_epi
    ((uniformTargetBaseLiftableAt_iff_epi finiteDuplicateIndex).1 liftable)

/-- A nonempty identity-index raw family on the coherent two-loop shape. -/
noncomputable def finiteIdentityRawSquareFamily :
    IndexedRawSquareFamily finiteNonEpiCoherentSource where
  targetVertex := finiteNonEpiCoherentSource.vertex
  index := fun vertex => 𝟙 (finiteNonEpiCoherentSource.vertex vertex)
  targetEdge := finiteNonEpiCoherentSource.edge
  square := fun edge => ValidatedIndexedBaseSquare.ofTerm (.leaf (by simp))

/-- The named vertex concretely belongs to the identity family's support. -/
theorem finiteIdentityRawSquareFamily_supports_vertex :
    finiteIdentityRawSquareFamily.Supports finiteNonEpiCoherentVertex :=
  Or.inl ⟨finiteNonEpiCoherentVertex,
    ⟨finiteNonEpiCoherentLeftEdge⟩⟩

/-- The identity family satisfies epimorphicity at every support vertex. -/
theorem finiteIdentityRawSquareFamily_supportEpi :
    finiteIdentityRawSquareFamily.SupportEpi := by
  intro vertex _supported
  dsimp [finiteIdentityRawSquareFamily]
  infer_instance

/-- The identity family satisfies local uniform liftability at every support
vertex. -/
theorem finiteIdentityRawSquareFamily_supportUniformLiftable :
    finiteIdentityRawSquareFamily.SupportUniformLiftable :=
  finiteIdentityRawSquareFamily.supportLiftable_of_supportEpi
    finiteIdentityRawSquareFamily_supportEpi

/-- The support-indexed producer fires on a concrete nonempty finite family. -/
noncomputable def finiteIdentityRawSquareFamily_production :
    finiteIdentityRawSquareFamily.SupportEpiProduction :=
  finiteIdentityRawSquareFamily.produce_of_supportEpi
    finiteIdentityRawSquareFamily_supportEpi

/-- Two vertices with no generating edges or declared cells provide a concrete
unsupported vertex. -/
inductive FiniteIsolatedSupportVertex : Type
  | active
  | isolated
  deriving DecidableEq, Fintype

/-- Empty incidence on the two support-test vertices. -/
noncomputable abbrev finiteIsolatedSupportBaseShape : IndexedBaseShape where
  Vertex := FiniteIsolatedSupportVertex
  vertexFintype := inferInstance
  Edge := fun _ _ => Empty
  edgeFintype := fun _ _ => inferInstance
  TwoCell := Empty
  twoCellFintype := inferInstance
  twoSource := fun cell => nomatch cell
  twoTarget := fun cell => nomatch cell

/-- Empty finite two-shape used only for the negative support instance. -/
noncomputable abbrev finiteIsolatedSupportShape : IndexedBaseTwoShape where
  toIndexedBaseShape := finiteIsolatedSupportBaseShape
  twoLeft := fun cell => nomatch cell
  twoRight := fun cell => nomatch cell

/-- Constant source diagram on the empty-incidence support-test shape. -/
noncomputable def finiteIsolatedSupportSource :
    IndexedBaseDiagram finiteIsolatedSupportShape FiniteModel.carrier where
  vertex := fun _ => finiteFixtureInstance
  edge := fun edge => nomatch edge
  relation := fun cell => nomatch cell

/-- Empty-incidence raw family witnessing a vertex outside support. -/
noncomputable def finiteIsolatedRawSquareFamily :
    IndexedRawSquareFamily finiteIsolatedSupportSource where
  targetVertex := finiteIsolatedSupportSource.vertex
  index := fun vertex => 𝟙 (finiteIsolatedSupportSource.vertex vertex)
  targetEdge := fun edge => nomatch edge
  square := fun edge => nomatch edge

/-- The isolated vertex is a concrete negative instance of `Supports`. -/
theorem finiteIsolatedRawSquareFamily_not_supports_isolated :
    ¬ finiteIsolatedRawSquareFamily.Supports
      FiniteIsolatedSupportVertex.isolated := by
  simp [IndexedRawSquareFamily.Supports, finiteIsolatedSupportShape,
    finiteIsolatedSupportBaseShape]

/-! ## Preserved negative branch -/

/-- The Cycle 7 target assignment, now placed on the K5 raw-family shape. -/
noncomputable def cycle7RawTargetEdge
    {i j : finiteNonEpiCoherentShape.Vertex}
    (edge : finiteNonEpiCoherentShape.Edge i j) :
    finiteDuplicatedInstance ⟶ finiteDuplicatedInstance := by
  change FiniteNonEpiCoherentEdge FiniteNonEpiCoherentVertex.point
    FiniteNonEpiCoherentVertex.point at edge
  cases edge
  · exact finiteDuplicateIdentity
  · exact finiteDuplicateConstant

/-- The two Cycle 7 validated squares form an actual K5 raw family. -/
noncomputable def cycle7RawSquareFamily :
    IndexedRawSquareFamily finiteNonEpiCoherentSource where
  targetVertex := fun _ => finiteDuplicatedInstance
  index := fun _ => finiteDuplicateIndex
  targetEdge := cycle7RawTargetEdge
  square := fun edge => by
    change FiniteNonEpiCoherentEdge FiniteNonEpiCoherentVertex.point
      FiniteNonEpiCoherentVertex.point at edge
    cases edge
    · simpa [finiteNonEpiCoherentSource, cycle7RawTargetEdge] using
        finiteDuplicateIdentitySquare
    · simpa [finiteNonEpiCoherentSource, cycle7RawTargetEdge] using
        finiteDuplicateConstantSquare

/-- The Cycle 7 raw family fails the K5 support-epimorphicity hypothesis at
the source of its first generating square. -/
theorem cycle7RawSquareFamily_not_supportEpi :
    ¬ cycle7RawSquareFamily.SupportEpi := by
  intro supportEpi
  exact finiteDuplicateIndex_not_epi
    (supportEpi finiteNonEpiCoherentVertex
      (cycle7RawSquareFamily.edgeSource_mem_support
        finiteNonEpiCoherentLeftEdge))

/-- The Cycle 7 family is also a concrete negative instance of support-wide
uniform liftability. -/
theorem cycle7RawSquareFamily_not_supportUniformLiftable :
    ¬ cycle7RawSquareFamily.SupportUniformLiftable := by
  intro liftable
  exact cycle7RawSquareFamily_not_supportEpi
    (cycle7RawSquareFamily.supportUniformLiftable_iff_supportEpi.1 liftable)

/-- No support-epi production certificate exists for the Cycle 7 family. -/
theorem cycle7RawSquareFamily_no_production :
    ¬ Nonempty cycle7RawSquareFamily.SupportEpiProduction := by
  rintro ⟨production⟩
  exact cycle7RawSquareFamily_not_supportUniformLiftable
    production.uniformAtSupport

/-- The same raw family assigns distinct target arrows to its declared
parallel one-edge paths, so no target relation can be generated without the
missing cancellation premise. -/
theorem cycle7RawSquareFamily_targetPaths_ne :
    cycle7RawSquareFamily.targetPath
        (finiteNonEpiCoherentShape.twoLeft finiteNonEpiCoherentCell) ≠
      cycle7RawSquareFamily.targetPath
        (finiteNonEpiCoherentShape.twoRight finiteNonEpiCoherentCell) := by
  simpa [IndexedRawSquareFamily.targetPath, finiteNonEpiCoherentShape,
    finiteNonEpiCoherentLeftPath, finiteNonEpiCoherentRightPath,
    cycle7RawSquareFamily, cycle7RawTargetEdge, IndexedBasePath.eval,
    finiteDuplicateIdentity] using finiteDuplicateIdentity_ne_constant

/-- Cycle 7 remains the finite validated non-liftable raw-family branch; it is
not a counterexample to the coherent-domain producer above. -/
theorem cycle7_finiteValidatedSquares_nonLiftable :
    ¬ IndexedValidatedTwoCellBaseGeneration FiniteModel.carrier :=
  finiteValidatedSquares_refute_twoCellBaseGeneration

end AAT.AG.DoctrineFiberProduct

#assert_standard_axioms_only AAT.AG.DoctrineFiberProduct
