import Formal.Util.AssertStandardAxioms

/-!
# The permanent `G_local-v1` observation value

This module fixes the presentation-independent codomain of the observation
used in claim (v) of `G-107-aat-uniform-invariance-characterization`.  The
types below are a direct transcription of the permanent sixteen-line
`G_LOCAL_V1_SPEC` contract.  They deliberately contain no raw cell identifier,
target-subset identifier, fixture name, hash, rank, cohomology dimension, or
uniformity result.

Multiplicity is clipped at two.  Zero occurrences are represented by an
absent histogram row; every row therefore has multiplicity `one` or
`atLeastTwo`.  `gLocalV1Histogram` is the single normalization constructor used
by the observation pipeline: it sorts payloads, removes duplicate rows, and
computes the clipped count from the complete occurrence list.

## Implementation notes

Closed Lean inductives and structures mirror the sixteen rows of the permanent
`g_local_v1.py` observation contract while keeping serialization outside the
mathematical value.  Raw JSON objects and string-tagged records were rejected:
they would expose encoding choices and could carry forbidden fixture identifiers.
Exact multiplicities above two were also rejected because the permanent
grammar deliberately identifies them; the normalized clip-two histogram is the
single owner of that quotient.
-/

namespace AAT.AG.ResolutionInvariance

universe u

/-! ## Closed registries -/

/-- The side of a cell in a comparison presentation. -/
inductive GLocalV1Side
  | coarse
  | fine
  deriving DecidableEq, Repr, Ord

/-- The four typed cell roles retained by the radius-one incidence record. -/
inductive GLocalV1CellType
  | chart
  | vertex
  | edge
  | face
  deriving DecidableEq, Repr, Ord

/-- The only map-status information exposed by the permanent grammar. -/
inductive GLocalV1MapStatus
  | none
  | mapped
  deriving DecidableEq, Repr, Ord

/-- The four collapse-packet kinds registered by permanent `G_local-v1`. -/
inductive GLocalV1PacketKind
  | v4Coarse
  | v4FineOnly
  | coordinateDependency
  | closedDoubledCycle
  deriving DecidableEq, Repr, Ord

/-- Typed and signed incidence relations visible inside a rooted ball. -/
inductive GLocalV1Relation
  | chartAt
  | endpoint0
  | endpoint1
  | boundary0Pos
  | boundary1Neg
  | boundary2Pos
  deriving DecidableEq, Repr, Ord

/-- The coarser slot registry used by outward stubs.  Endpoint zero and face
boundary zero intentionally share `slot0`, and signs are discarded. -/
inductive GLocalV1StubSlot
  | chartAt
  | slot0
  | slot1
  | slot2
  deriving DecidableEq, Repr, Ord

/-- A positive occurrence count clipped at two. -/
inductive GLocalV1Multiplicity
  | one
  | atLeastTwo
  deriving DecidableEq, Repr, Ord

/-- Clip a natural count at two; zero is represented by no histogram row. -/
def gLocalV1Clip2 : Nat → Option GLocalV1Multiplicity
  | 0 => none
  | 1 => some .one
  | _ + 2 => some .atLeastTwo

/-! ## Canonical histograms -/

/-- One canonical histogram row. -/
structure GLocalV1HistogramRow (α : Type u) where
  payload : α
  multiplicity : GLocalV1Multiplicity
  deriving DecidableEq, Repr, Ord

/-- A normalized list of clipped multiplicity rows.  Observation constructors
produce this type only through `gLocalV1Histogram`. -/
structure GLocalV1Histogram (α : Type u) where
  rows : List (GLocalV1HistogramRow α)
  deriving DecidableEq, Repr, Ord

/-- The deterministic weak order induced by a type's `Ord` instance. -/
def gLocalV1OrdLE {α : Type u} [Ord α] (left right : α) : Bool :=
  (compare left right).isLE

/-- Normalize a complete occurrence list into sorted, unique, clip-two rows. -/
def gLocalV1Histogram {α : Type u} [Ord α] [DecidableEq α]
    (occurrences : List α) : GLocalV1Histogram α :=
  let sorted := occurrences.mergeSort gLocalV1OrdLE
  let payloads := sorted.eraseDups
  ⟨payloads.filterMap fun payload =>
    (gLocalV1Clip2 (occurrences.countP fun candidate => decide (candidate = payload))).map
      fun multiplicity => ⟨payload, multiplicity⟩⟩

/-! ## Closed observation records -/

/-- The six registered unary flags.  Flags outside their documented cell
domain are set to `false` by the observation constructor. -/
structure GLocalV1Flags where
  critical : Bool
  guard : Bool
  port : Bool
  bridge : Bool
  selfLoop : Bool
  faceTwin : Bool
  deriving DecidableEq, Repr, Ord

/-- A target-relabelled cell label.  Supports and factor images are sorted
lists of relabelled target codes, never raw cell or subset identifiers. -/
structure GLocalV1CellLabel where
  side : GLocalV1Side
  cellType : GLocalV1CellType
  mapStatus : GLocalV1MapStatus
  support : List Nat
  piImage : List Nat
  flags : GLocalV1Flags
  deriving DecidableEq, Repr, Ord

/-- An outward radius-two clipping stub, retaining only cell type and the
collapsed incidence slot. -/
structure GLocalV1OutwardStub where
  cellType : GLocalV1CellType
  slot : GLocalV1StubSlot
  deriving DecidableEq, Repr, Ord

/-- One neighbor group in a radius-one rooted ball.  Relations retain their
full slot/sign multiplicity; outward stubs are clipped separately. -/
structure GLocalV1NeighborDescriptor where
  neighborLabel : GLocalV1CellLabel
  relations : List GLocalV1Relation
  outwardStubHistogram : GLocalV1Histogram GLocalV1OutwardStub
  deriving DecidableEq, Repr, Ord

/-- A root-preserving, side-local radius-one typed incidence ball. -/
structure GLocalV1RootedBall where
  rootLabel : GLocalV1CellLabel
  neighborDescriptors : GLocalV1Histogram GLocalV1NeighborDescriptor
  deriving DecidableEq, Repr, Ord

/-- Whole-scope condition coordinates. -/
structure GLocalV1WholeConditions where
  c0 : Bool
  c5 : Bool
  c6 : Bool
  deriving DecidableEq, Repr, Ord

/-- Nonempty-target-subset condition coordinates. -/
structure GLocalV1AConditions where
  c1 : Bool
  c2 : Bool
  c3 : Bool
  c4 : Bool
  deriving DecidableEq, Repr, Ord

/-- A scope record formed from the universal terminal condition, the union of
all outgoing packet kinds over all reachable states, and all terminal balls. -/
structure GLocalV1ScopeRecord (Conditions : Type u) where
  conditions : Conditions
  packetKindUnion : List GLocalV1PacketKind
  rootedBallHistogram : GLocalV1Histogram GLocalV1RootedBall
  deriving DecidableEq, Repr, Ord

/-- The aggregate seven-coordinate permanent condition vector. -/
structure GLocalV1ConditionVector where
  c0 : Bool
  c1 : Bool
  c2 : Bool
  c3 : Bool
  c4 : Bool
  c5 : Bool
  c6 : Bool
  deriving DecidableEq, Repr, Ord

/-- Presentation-independent permanent `G_local-v1` observation value. -/
structure GLocalV1ObsValue where
  aggregate : GLocalV1ConditionVector
  whole : GLocalV1ScopeRecord GLocalV1WholeConditions
  aRecordHistogram : GLocalV1Histogram (GLocalV1ScopeRecord GLocalV1AConditions)
  deriving DecidableEq, Repr, Ord

/-! ## Permanent contract inventory -/

/-- The sixteen registered contract rows, used to audit that every permanent
component has one definition-level owner in the Lean observation kernel. -/
inductive GLocalV1ContractComponent
  | scope
  | terminal
  | conditions
  | packets
  | chartRole
  | ball
  | relations
  | mapStatus
  | neighbor
  | stubs
  | multiplicity
  | flags
  | supports
  | faces
  | targets
  | forbidden
  deriving DecidableEq, Repr, Ord

/-- The complete permanent contract-component registry, in specification
order. -/
def gLocalV1ContractComponents : List GLocalV1ContractComponent :=
  [.scope, .terminal, .conditions, .packets, .chartRole, .ball, .relations,
    .mapStatus, .neighbor, .stubs, .multiplicity, .flags, .supports, .faces,
    .targets, .forbidden]

/-- The immutable upstream source contract hash recorded for provenance.  It
is not a field of, or input to, `GLocalV1ObsValue`. -/
def gLocalV1PermanentContractSha256 : String :=
  "5a14faf44049b8906200d5dbd052bc9fd5669ff84dfb6452e6137e98dfbd51c8"

/-- The registry contains exactly sixteen contract components. -/
theorem gLocalV1ContractComponents_length :
    gLocalV1ContractComponents.length = 16 := by
  decide

/-- Every contract component occurs exactly once in the registry. -/
theorem gLocalV1ContractComponents_nodup :
    gLocalV1ContractComponents.Nodup := by
  decide

end AAT.AG.ResolutionInvariance

#assert_standard_axioms_only AAT.AG.ResolutionInvariance
