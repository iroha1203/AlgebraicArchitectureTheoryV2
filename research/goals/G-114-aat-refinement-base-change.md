# G-114 — AAT Refinement Category and Realized-Support Base Change

- `id`: `G-114-aat-refinement-base-change`
- `status`: `active`
- `priority`: `high`
- `research mode`: `target-theorem`
- `tracking issue`: [#4239](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/issues/4239)
- `predecessors`: G-110, G-112
- `successors`: G-115, G-116
- `revision`: 2
- `source note`: [n1007](../../docs/note/n1007_aat_sakura_gr4_completion_design.md)

## Program context

G-112 established exact-bottom base change: an exact cospan has a selected pullback,
exact reindexing, and strong cartesian lifts. G-114 asks how this behaves under a
pointed endpoint refinement. Every refinement has a canonical forward pulled
square. Reverse package transport is stronger and exists exactly on the realized
part of the refinement.

This is the first Gr4 stratification:

1. every refinement belongs to the doctrine-lax, forward layer;
2. a refinement satisfying realized-locus extraction reflection belongs to the
   package-reverse layer;
3. an actual target package promotes a point to the active mate-bearing context
   consumed by G-115;
4. G-116 decides exchange only where the relevant mate is defined.

An empty package fiber is inactive. It can test total definitions, but it is
neither the positive nor the negative nonvacuity witness.

## Research aim

Construct the category of exact-bottom pointed refinement configurations, prove
that exact reindexing is functorial under refinement, and classify reverse
cartesian base change by the single geometric condition
`RealizedLocusExtractionReflecting`.

## Rival

> Every pointed refinement of an exact cospan admits reverse package transport and
> a cartesian base-change cleavage.

This is false. A strict refinement may extract a target atom while omitting its
chosen source. G-114 retains the forward square and classifies that configuration
as forward-only; it does not add the desired cleavage as input data.

## Claim boundary

### Raw configuration

`RefinementBCConfiguration` contains only an exact cospan
`s₁ ⟶ b ⟵ s₂`, a pointed refinement `ρ : s₁ ⟶ s₁'`, and the marked point
required by the existing refinement interface. It contains no package, regime,
reverse lift, mate, or hypothesis implying the conclusion.

### Compatible sources and repointing

For `C : RefinementBCConfiguration`, `CompatibleSource C` contains a source
and chosen point satisfying the AAT bottom equations. For
`p : CompatibleSource C`, define canonically `C.repoint p`, `C.baseAt p`,
`C.pullbackAt p`, `C.refinementAt p`, and `C.pulledRefinementAt p`.
These are generated, not independent fixtures.

### Realized support

```lean
def RealizedAt (C : RefinementBCConfiguration) (p : CompatibleSource C) : Prop :=
  Nonempty (CoreFiber (C.baseAt p).target)
```

The exact spelling may follow G-112, but the predicate must mean existence of an
actual package over the target base atom. It may not be a configuration field.

### Fixed geometric condition

`RealizedLocusExtractionReflecting C` has exactly one mathematical constructor:

> for every compatible source `p`, if `C.baseAt p` is realized and the target
> atom is extracted by the refinement target, then its chosen source atom is
> extracted by the refinement source.

Forward extraction is already supplied by refinement preservation. The condition
adds only reverse extraction on package-realized targets. Its statement mentions
no lift, cleavage, mate, equivalence, `IsIso`, or regime availability.

### Regime and active context

`RefinementBCRegimeAt C p` consists of the base and pulled reverse cartesian
cleavages. `RefinementBCRegime C` is their dependent family. Exact reindexing,
comparison maps, and mates are derived from G-112 and the cleavages, not fields.

```lean
def Active (C : RefinementBCConfiguration) : Prop :=
  Nonempty (Sigma fun p : CompatibleSource C => CoreFiber (C.baseAt p).target)

def ActiveRegimeAvailable (C : RefinementBCConfiguration) : Prop :=
  Active C ∧ Nonempty (RefinementBCRegime C)
```

`ActiveRefinementBCContext` packages a configuration, compatible source, actual
target package, and the local regime produced by the classification theorem. It is
the sole G-114 interface supplied to G-115 and the refinement component of G-116.

## Target theorem

Prove **Refinement Category and Realized-Support Base-Change Stratification** with
all clauses below.

### (a) Refinement category

1. Define identity and composition of pointed refinements.
2. Prove category laws and compatibility with repointing.
3. Show that exact comparison refinements embed functorially.

### (b) Unconditional forward base change

For every raw configuration and compatible source, construct the pulled refinement
square, prove commutativity, identity and composition laws, and compatibility with
the G-112 exact-comparison image. No package-support hypothesis is allowed here.

### (c) Realized-support classification

For every raw configuration `C`, prove

```lean
Nonempty (RefinementBCRegime C) ↔ RealizedLocusExtractionReflecting C
```

The forward proof must recover extraction reflection from an actual package and
the cartesian lift. The reverse proof must construct base and pulled cleavages and
include the support-transfer lemma

```lean
RealizedAt (C.pullbackAt p) → RealizedAt (C.baseAt p)
```

derived from exact projection and package transport. Thus a pulled realized point
cannot evade the fixed condition at the base. Reverse transport must be two-sided
and cartesian, not merely a map: transport all package structure along the atom
equivalence forced by local extraction reflection and prove its universal property.

### (d) Condition qualification

Prove that `RealizedLocusExtractionReflecting` is invariant under configuration
isomorphism, holds for identities, is closed under composition, is preserved by
pulled refinement, holds on the exact-comparison image, and is strictly broader
than that image by the active positive witness in clause (e). No equivalent
condition may be substituted without revising this GOAL from scratch.

### (e) Support-stratified nonvacuity

Provide three independent examples.

1. **Active forward-only witness.** A finite strict refinement with a nonempty
   target package fiber, nonidentity/nontrivial pulled square, failure of the fixed
   condition, and hence no regime.
2. **Active reverse witness.** A nonidentity strict refinement outside the exact
   comparison image, with a nonempty target package fiber, nontrivial pulled
   square, the fixed condition, a constructed regime, and a concrete mate that
   evaluates nontrivially.
3. **Inactive regression witness.** The known infinite configuration with empty
   target fibers. Prove it inactive and prove that total regime construction there
   cannot discharge either active witness obligation.

The first two witnesses must be distinct and must not derive support from a regime
fixture.

### (f) Gr4 supply theorem

Export a theorem constructing `ActiveRefinementBCContext` from a compatible
source, actual target package, and the fixed condition. Export the canonical base
and pulled mates from this context. G-115 and G-116 must import these declarations
rather than reconstructing reverse transport.

## Target theorem boundary

The target proves support-stratified base change for pointed endpoint refinements
of G-112 exact cospans. It does not assert reverse transport for every refinement.
It does not decide invertibility of upper-stage or Gr4 exchange mates; those are
G-115 and G-116 responsibilities. The carrier `U`, coefficient data, law
universe, site, and cover are fixed; carrier change, coefficient base change,
derived fiber products, and new cover topologies are excluded. The theorem is not
finite-only, but the active forward-only witness is finite; all other universe
parameters must elaborate in the existing G-112 universe discipline. Lean
artifacts live under `ResearchLean/AAT/AG/RefinementBaseChange/`; accepted Lean
declarations are static evidence until premise, provenance, proof-use, nonvacuity,
review, CI, merge, and ledger gates also pass.

## Target proof artifacts

- `research/lean/ResearchLean/AAT/AG/RefinementBaseChange/Configuration.lean`
- `research/lean/ResearchLean/AAT/AG/RefinementBaseChange/Category.lean`
- `research/lean/ResearchLean/AAT/AG/RefinementBaseChange/Pullback.lean`
- `research/lean/ResearchLean/AAT/AG/RefinementBaseChange/RealizedSupport.lean`
- `research/lean/ResearchLean/AAT/AG/RefinementBaseChange/Regime.lean`
- `research/lean/ResearchLean/AAT/AG/RefinementBaseChange/Classification.lean`
- `research/lean/ResearchLean/AAT/AG/RefinementBaseChange/Witnesses.lean`
- `research/lean/ResearchLean/AAT/AG/RefinementBaseChange.lean`
- `research/reports/G-114-aat-refinement-base-change.md`

Existing names may be retained when their mathematical roles are unchanged. The
completion packet must give the exact final declaration map.

## Target proof strategy

1. Reuse G-112 exact cospans, selected pullbacks, reindexing, and strong lifts.
2. Define refinement composition and prove forward pullback functoriality.
3. At a realized source, use extraction reflection to identify chosen atoms,
   transport the complete package along that equivalence, and prove cartesianness.
4. Transport pulled support through exact projection and construct the pulled lift.
5. Assemble the local constructions into the global regime.
6. Recover the fixed condition from a regime using an actual target package.
7. Prove closure and all three witnesses independently.

If step 3 fails because atom equivalence does not transport all package structure,
revision 2 is mathematically refuted; the missing transport must not be added as a
configuration field.

## Target premise discharge policy

Every material premise must be a raw input above, a reviewed G-112/refinement
theorem, a declaration proved in the required artifacts, or witness-local data
constructed by its witness theorem. No completion theorem may assume the fixed
condition, regime, cleavage, mate, or package-equivalence conclusion as an opaque
fixture. The main classification is an equivalence: each direction constructs the
other side.

## Target material premise ledger

| premise | supports | role | provenance / discharge artifact | required proof-use | why not conclusion-equivalent |
| --- | --- | --- | --- | --- | --- |
| exact cospan | clauses (a)–(c) | `ambient-boundary` | fixed reviewed G-112 declaration; exact-head citation required | selected pullback and exact reindexing | it supplies the base square, not refinement reverse transport |
| pointed refinement | clauses (a)–(e) | `ambient-boundary` | raw G-114 configuration field | forward square and extraction preservation | it has only forward extraction |
| compatible source | clauses (b)–(f) | `ambient-boundary` | generated source index with bottom equations | repointing and local base selection | it contains no package-level lift |
| target package | clauses (c), (e), (f) | `direction-hypothesis` | active-context input or concrete witness constructed in `Witnesses.lean` | support firing, converse extraction, and mate evaluation | an object of the fiber is not a cleavage or mate |
| fixed condition | reverse implication of (c), clauses (d), (f) | `discharge-required` | one-constructor predicate proved for the positive family; no certificate field | atom equivalence and package transport | it concerns extraction of atoms, not cartesian universality |
| local regime | forward implication of (c), clause (f) | `discharge-required` | constructed by `Classification.lean`; no caller-supplied fixture | reverse extraction and canonical mate | it is the constructed opposite side of the stated equivalence |
| active forward-only witness | clause (e1) | `discharge-required` | explicit finite fixture and evaluation theorem | decide failure of the fixed condition and derive no regime | the fixture carries no no-regime certificate |
| active reverse witness | clauses (d6), (e2) | `discharge-required` | explicit strict-image-external fixture and independently constructed package | exercise condition, regime, nontrivial mate | the fixture carries no condition/regime certificate |
| inactive regression | clause (e3) | `discharge-required` | existing empty-fiber fixture plus new inactivity theorem | demonstrate exclusion from active success | emptiness tests scope and supplies no active conclusion |

The final report must cite the declaration body consuming every premise. None is
conclusion-equivalent: extraction reflection concerns atom selection, whereas a
regime contains cartesian package-level structure.

## Target anti-weakening rule

- The raw configuration contains no regime or package witness.
- The fixed condition has one constructor and no categorical conclusion.
- The theorem is an `↔`, not only the easy implication.
- Forward base change remains unconditional.
- Reverse base change is not claimed outside realized support.
- Empty fibers are inactive and cannot count as either firing witness.
- The positive witness lies outside the exact-comparison image.
- The negative witness is finite, active, and has a nontrivial pulled square.
- No clause reduces to `IsIso` of a supplied inverse or mate.

## Target route integrity gate

The completion report must trace:

1. raw configuration → compatible source → repointed base → forward pulled square;
2. fixed condition + actual package → atom equivalence → package transport →
   cartesian cleavage → mate;
3. regime + actual package → lifted source → reverse extraction;
4. pulled support → exact projection → base support → pulled cleavage;
5. positive/negative fixtures → fixed-condition decision → active stratum;
6. active context → the exact G-115 and G-116 imported declarations.

Presence without proof-body use does not discharge an obligation.

## Target theorem completion criteria

G-114 is complete only when clauses (a)–(f) are proved in Lean; the focused target
and required dependency DAG pass; no ResearchLean aggregate/full build is run; all
standard-axiom, placeholder, import-direction, Unicode, and diff scans pass; the
report records the final declaration map, premise ledger, certificate provenance,
proof-use routes, structure-field escape audit, and witness outputs; the report and
tracking Issue are synchronized; the standard fixed-head PR review and a fresh
completion-candidate `math-lean-review` return no major findings; PR CI is green
and merged; the final review packet is fixed; and `target-theorem-proved` is
recorded only then.

## Target failure policy

- A counterexample to any fixed clause gives `target-refuted` with an exact
  fixture and evaluation theorem.
- A missing semantic primitive required to state the condition or transport
  package structure gives `goal-defect`; do not weaken the target.
- An external dependency gives `target-blocked` only after the loop's prescribed
  repeated evidence.
- A revised GOAL is audited from scratch; revision-1 checkpoints are not
  revision-2 completion evidence.

## Revision history

Revision 1 asked for a global reverse regime over every refinement. A finite strict
witness showed extraction nonreflection, while an infinite empty-fiber fixture made
regime existence vacuous. The implementation branch correctly recorded that target
as `goal-defect`; it did not prove the claimed classification.

Revision 2 keeps the category and unconditional forward square, fixes one
realized-support geometric condition, separates active from inactive fibers, and
makes the resulting mate-bearing context the explicit supply contract for the rest
of Gr4.
