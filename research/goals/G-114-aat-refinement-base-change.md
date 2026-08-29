# G-114 — AAT Refinement Category and Realized-Support Base Change

- `id`: `G-114-aat-refinement-base-change`
- `status`: `active`
- `priority`: `high`
- `research mode`: `target-theorem`
- `tracking issue`: [#4239](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/issues/4239)
- `predecessors`: G-101, G-109, G-110, G-112
- `successors`: G-115, G-116
- `revision`: 2
- `source note`: [n1007](../../docs/note/n1007_aat_sakura_gr4_completion_design.md)

## Program context

G-112 established exact-bottom base change: an exact cospan has a selected pullback,
exact reindexing, and strong cartesian lifts. G-114 asks how this behaves under a
pointed endpoint refinement. Every refinement has a canonical forward pulled
square. Reverse package transport is stronger and exists exactly on the realized
part of the refinement.

Dependency anchors are G-109 final reviewed head `b5ca4630` for covariant
`coreFiberTransportObj`, G-110 final reviewed head `a1471483` for package
fiber-product/cartesian machinery, and G-112 final reviewed head `bf882573` for
exact-bottom pullback and reindexing. They are referenced, not modified.

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

Construct the unpointed refinement category, its pointed/package fibrational
realization over exact-bottom configurations, prove the canonical forward
refinement square, and classify reverse
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
`s₁ ⟶ b ⟵ s₂` and an unpointed
`RefinementDoctrineHom ρ : s₁' ⟶ s₁`. It contains no marked source, package,
regime, reverse lift, mate, or hypothesis implying the conclusion.

### Compatible sources and repointing

For `C : RefinementBCConfiguration`, `CompatibleSource C` contains
`x' : s₁'.Source` and `x₂ : s₂.Source` with the bottom equation
`f.sourceMap (ρ.sourceMap x') = g.sourceMap x₂`. For
`p : CompatibleSource C`, canonically repoint `s₁'` at `x'`, `s₁` at
`ρ.sourceMap x'`, `s₂` at `x₂`, and `b` at their common image. Define
`C.sourcePointAt p`, `C.targetPointAt p`,
`C.pullbackSourceAt p`, `C.pullbackTargetAt p`,
`C.baseRefinementAt p`, and `C.pulledRefinementAt p`. The two pullbacks and
the pulled refinement are generated from this repointed diagram; they are not
independent fixtures.

### Realized support

```lean
def RealizedAt (C : RefinementBCConfiguration) (p : CompatibleSource C) : Prop :=
  Nonempty (CoreFiber (C.targetPointAt p))
```

The exact spelling may follow G-112, but the predicate must mean existence of an
actual package over the target base atom. It may not be a configuration field.

### Fixed geometric condition

For a generated pointed refinement `r : X' ⟶ X`, define
`RealizedLocusExtractionReflecting r` with exactly one mathematical constructor:

> if `CoreFiber X` is inhabited, then for every `a : U.Atom`, extraction
> of `r.atomMap a` by `X.doctrine` at `X.source` implies extraction of
> `a` by `X'.doctrine` at `X'.source`.

Forward extraction is already supplied by refinement preservation. The condition
adds only reverse extraction on package-realized targets. Its statement mentions
no lift, cleavage, mate, equivalence, `IsIso`, or regime availability.

The configuration predicate is the derived all-compatible-source statement:

```lean
def ConfigurationRealizedLocusExtractionReflecting
    (C : RefinementBCConfiguration) : Prop :=
  ∀ p : CompatibleSource C,
    RealizedLocusExtractionReflecting (C.baseRefinementAt p)
```

This separation fixes the closure domain. Identity and composition are statements
about composable pointed refinement morphisms. Pulled-leg preservation compares
`C.baseRefinementAt p` with `C.pulledRefinementAt p`. No composition operation
on raw cospan configurations is asserted.

### Refinement package fibration

The cartesian language is not borrowed from the exact
`packageProjection : PackageTotalCategory U ⥤ ExtractionInstance U`. G-114 must construct
its refinement analogue explicitly:

1. `PointedRefinementObject U`, a wrapper around `ExtractionInstance U`, and
   `PointedRefinementCategory U` on that wrapper; using a wrapper is mandatory
   so the existing exact category instance on `ExtractionInstance U` is not
   shadowed. Its morphisms are `RefinementDoctrineHom` plus selected-source
   compatibility;
2. `RefinementPackageObject U`, a wrapper around `AATCorePackage U`, and
   `RefinementPackageTotalCategory U` on that wrapper; its morphisms contain a
   pointed refinement base map and a complete
   `SignedExactCoreReadingHom` upper map using the same Atom equivalence;
3. `refinementPackageProjection :
   RefinementPackageTotalCategory U ⥤ PointedRefinementCategory U`;
4. identity, composition, and projection laws;
5. exact-to-refinement comparison functors on both base and total categories,
   with a commuting comparison square to the reviewed exact
   `packageProjection`.

No cartesian lift, cleavage, factorization, mate, or reflection certificate is
stored in these category or morphism structures. A refinement cartesian lift uses
the existing `CategoryTheory.Functor.IsCartesian` /
`IsStronglyCartesian` interface relative to
`refinementPackageProjection`. G-114 must also construct, rather than assume,
the authored-source package and complete upper-reading hom from a target package
and selected-family equality.

### Regime and active context

`RefinementBCRegimeAt C p` consists of the base and pulled cartesian cleavages
for `refinementPackageProjection` along `C.baseRefinementAt p` and
`C.pulledRefinementAt p`. `RefinementBCRegime C` is their dependent family.
Exact reindexing, comparison maps, and mates are derived from G-112, the exact /
refinement projection comparison, and the two cleavages; they are not fields.

```lean
def Active (C : RefinementBCConfiguration) : Prop :=
  Nonempty (Sigma fun p : CompatibleSource C => CoreFiber (C.targetPointAt p))

def ActiveRegimeAvailable (C : RefinementBCConfiguration) : Prop :=
  Active C ∧ Nonempty (RefinementBCRegime C)
```

`ActiveRefinementBCContext` packages a configuration, compatible source, actual
target package, and the local regime produced by the classification theorem. It is
the sole G-114 interface supplied to G-115 and the refinement component of G-116.

## Target theorem

Prove **Refinement Category and Realized-Support Base-Change Stratification** with
all clauses below.

### (a) Refinement category and package fibration

1. Construct `RefinementObject U`, a wrapper around `ExtractionDoctrine U`,
   and the unpointed `RefinementCategory U` whose morphisms are
   `RefinementDoctrineHom`; prove its category laws. The wrapper is mandatory
   so the existing exact category instance is not shadowed.
2. Construct the unpointed exact-to-refinement functor
   `DoctrineCategory U ⥤ RefinementCategory U`.
3. Define identity and composition of pointed refinements on the wrapper category,
   prove its category laws, and prove compatibility with repointing.
4. Show that exact pointed morphisms embed functorially.
5. Construct `RefinementPackageTotalCategory`,
   `refinementPackageProjection`, and their category/functor laws.
6. Construct the exact-to-refinement base and total comparison functors and prove
   the projection square commutes.
7. Define refinement cartesian lifts, their factorization/uniqueness, and the
   cleavage interface relative to this projection.

### (b) Unconditional forward base change

For every raw configuration and compatible source, construct the mixed pulled
doctrine directly from the refined endpoint and the exact second leg, its exact
vertical projection, and the pulled refinement. Prove the square commutes and is
compatible with the G-112 exact-comparison image. No exact composite
`s₁' ⟶ b` and no package-support hypothesis may be assumed here.

### (c) Realized-support classification

First prove the local pointed-refinement theorem

```lean
Nonempty (RefinementCartesianCleavage r) ↔
  RealizedLocusExtractionReflecting r
```

The condition-to-cleavage direction must export the objectwise producer that,
for every actual target package, constructs the authored-source package, complete
upper hom, and strongly cartesian lift. This producer is the support transport
used in composition closure.

Then, for every raw configuration `C`, assemble base and pulled local results
and prove

```lean
Nonempty (RefinementBCRegime C) ↔
  ConfigurationRealizedLocusExtractionReflecting C
```

The forward proof must recover extraction reflection from an actual package and
the cartesian lift. The reverse proof must construct base and pulled cleavages and
include the support-transfer lemma

```lean
Nonempty (CoreFiber (C.pullbackTargetAt p)) →
  Nonempty (CoreFiber (C.targetPointAt p))
```

derived from the exact projection and the G-101/G-109 covariant
`coreFiberTransportObj` route, not from contravariant G-112 reindexing. Thus a
pulled realized point cannot evade the fixed condition at the base. Reverse
transport must be a lift for `refinementPackageProjection`, two-sided at the
complete upper-reading level, and cartesian—not merely a package map.

### (d) Condition qualification

Prove that `RealizedLocusExtractionReflecting` is invariant under pointed
refinement isomorphism, holds for identity pointed refinements, and is closed under
composition of pointed refinements. Prove separately that the derived
configuration predicate is preserved from each base refinement to its pulled
refinement, holds on the exact-comparison image, and is strictly broader than that
image by the active positive witness in clause (e). No equivalent condition may be
substituted without revising this GOAL from scratch.

For composition `X₀ ⟶ X₁ ⟶ X₂`, target support over `X₂` must be transported
to an actual package over `X₁` by the outer condition's authored-source package
producer before applying the inner condition. This generated package is proof data,
not an additional closure hypothesis.

### (e) Support-stratified nonvacuity

Provide three independent examples.

1. **Active forward-only witness.** A finite strict refinement with a nonempty
   target package fiber, failure of the fixed condition, and hence no regime.
   Nontriviality is the typed conjunction that the base source/target doctrines
   are unequal, the pulled source/target doctrines are unequal, and the condition
   failure supplies an explicit Atom whose selected-source extraction differs.
2. **Active reverse witness.** A nonidentity strict refinement outside the exact
   comparison image, with a nonempty target package fiber, nontrivial pulled
   square, the fixed condition, and a constructed regime. Fix a target package
   `Q` and Atom `a₀`; the exported mate component is required to satisfy the
   concrete observable
   `(mate.app Q).upper.atomEquiv a₀ ≠ a₀` (up to the final wrapper projections).
   The witness must therefore use a genuinely nonidentity Atom equivalence, not
   merely unequal doctrine wrappers.
3. **Inactive regression witness.** Construct an explicit infinite configuration
   (the `ExactBottomSumCarrier` / non-list-finite selected-family pattern is the
   fixed starting point) with empty target fibers. Prove it inactive and prove that
   total regime construction there cannot discharge either active witness
   obligation.

The first two witnesses must be distinct and must not derive support from a regime
fixture.

### (f) Gr4 supply theorem

Export a theorem constructing `ActiveRefinementBCContext` from a compatible
source, actual target package, and the fixed condition. Export the exact type of
the canonical base and pulled mates: their source/target functors are generated by
the exact `packageProjection` reindexing, the refinement projection cleavages,
and the commuting comparison square. G-115 and G-116 must import these
declarations rather than reconstructing reverse transport.

## Target theorem boundary

The target proves support-stratified base change for pointed endpoint refinements
of G-112 exact cospans. It does not assert reverse transport for every refinement.
It does not decide invertibility of upper-stage or Gr4 exchange mates; those are
G-115 and G-116 responsibilities. The carrier `U`, coefficient data, law
universe, site, and cover are fixed; carrier change, coefficient base change,
derived fiber products, and new cover topologies are excluded. The theorem is not
finite-only, but the active forward-only witness is finite; all other universe
parameters must elaborate in the existing G-112 universe discipline. Lean
artifacts live under
`ResearchLean/AG/DoctrineFiberProduct/RefinementBaseChange/`; accepted Lean
declarations are static evidence until premise, provenance, proof-use, nonvacuity,
review, CI, merge, and ledger gates also pass.

## Target proof artifacts

- `research/lean/ResearchLean/AG/DoctrineFiberProduct/RefinementBaseChange/Configuration.lean`
- `research/lean/ResearchLean/AG/DoctrineFiberProduct/RefinementBaseChange/Categories.lean`
- `research/lean/ResearchLean/AG/DoctrineFiberProduct/RefinementBaseChange/Projection.lean`
- `research/lean/ResearchLean/AG/DoctrineFiberProduct/RefinementBaseChange/Pullback.lean`
- `research/lean/ResearchLean/AG/DoctrineFiberProduct/RefinementBaseChange/RealizedSupport.lean`
- `research/lean/ResearchLean/AG/DoctrineFiberProduct/RefinementBaseChange/Regime.lean`
- `research/lean/ResearchLean/AG/DoctrineFiberProduct/RefinementBaseChange/Classification.lean`
- `research/lean/ResearchLean/AG/DoctrineFiberProduct/RefinementBaseChange/Witnesses.lean`
- `research/lean/ResearchLean/AG/DoctrineFiberProduct/RefinementBaseChange.lean`
- `research/reports/G-114-aat-refinement-base-change.md`

Existing names may be retained when their mathematical roles are unchanged. The
completion packet must give the exact final declaration map.

## Target proof strategy

1. Reuse G-112 exact cospans, selected pullbacks, reindexing, and strong lifts.
2. Define the unpointed refinement category/comparison functor, then pointed
   refinement composition and the refinement package total category/projection.
   Prove the exact-to-refinement comparison square.
3. Prove forward pullback functoriality for `s₁' ⟶ s₁`.
4. At a realized source, use the all-Atom reflection plus forward preservation to
   prove selected-family equality. Build a source package over the authored
   `s₁'` doctrine, transport all remaining upper-reading structure along
   `ρ.atomEquiv`, and prove the refinement-projection cartesian universal
   property.
5. Transport pulled support covariantly through exact projection using
   `coreFiberTransportObj`, then construct the pulled lift.
6. Assemble local constructions into the global regime and derive the mates via
   the comparison square and universal uniqueness.
7. Recover all-Atom reflection from a regime using an actual target package.
8. Prove closure and all three witnesses independently.

If step 4 fails because atom equivalence and selected-family equality do not
transport all package structure over the authored source doctrine, or if the new
projection cannot support the stated cartesian universal property,
revision 2 is mathematically refuted; the missing transport must not be added as a
configuration field.

## Target premise discharge policy

Every material premise must be a raw input above, a reviewed G-101/G-109/G-112
theorem, a declaration proved in the required artifacts, or witness-local data
constructed by its witness theorem. No completion theorem may assume the fixed
condition, regime, cleavage, mate, or package-equivalence conclusion as an opaque
fixture. The main classification is an equivalence: each direction constructs the
other side.

## Target material premise ledger

| premise | supports | role | provenance / discharge artifact | required proof-use | why not conclusion-equivalent |
| --- | --- | --- | --- | --- | --- |
| exact cospan | clauses (a)–(c) | `ambient-boundary` | fixed reviewed G-112 declaration; exact-head citation required | selected pullback and exact reindexing | it supplies the base square, not refinement reverse transport |
| unpointed refinement | clauses (a)–(e) | `ambient-boundary` | raw G-114 configuration field | repointing, forward square, and extraction preservation | it has only forward extraction |
| compatible source | clauses (b)–(f) | `ambient-boundary` | generated source index with bottom equations | repointing and local base selection | it contains no package-level lift |
| target package | clauses (c), (e), (f) | `direction-hypothesis` | active-context input or concrete witness constructed in `Witnesses.lean` | support firing, converse extraction, and mate evaluation | an object of the fiber is not a cleavage or mate |
| refinement package projection | clauses (a), (c), (f) | `discharge-required` | explicit categories, functor, exact comparison square, and laws in `Categories.lean` / `Projection.lean` | ambient for both cartesian factorization directions and mate generation | it defines the arena, not existence of a lift |
| fixed condition | condition-to-regime direction of (c), clauses (d), (f) | `direction-hypothesis` | one-constructor all-Atom predicate; each theorem must receive it only as the stated implication input | selected-family equality and construction of the opposite regime | it concerns extraction of atoms, not cartesian universality |
| local regime | regime-to-condition direction of (c), clause (f) | `direction-hypothesis` | received only as the stated implication input; condition-to-regime producer is separately proved | actual target lift, reverse extraction, and canonical mate | it is one side of the equivalence, not a hidden premise of its own producer |
| condition-to-regime producer | reverse implication of (c) | `discharge-required` | theorem body in `Classification.lean`; no caller-supplied cleavage | construct both base and pulled cartesian cleavages | it is the theorem to prove |
| regime-to-condition producer | forward implication of (c) | `discharge-required` | theorem body in `Classification.lean`; no caller-supplied reflection | derive all-Atom reflection from each realized target | it is the theorem to prove |
| active forward-only witness | clause (e1) | `discharge-required` | explicit finite fixture and evaluation theorem | decide failure of the fixed condition and derive no regime | the fixture carries no no-regime certificate |
| active reverse witness | clauses (d6), (e2) | `discharge-required` | explicit strict-image-external fixture and independently constructed package | exercise condition, regime, nontrivial mate | the fixture carries no condition/regime certificate |
| inactive regression | clause (e3) | `discharge-required` | explicit `ExactBottomSumCarrier`-based fixture, fiber-emptiness proof, and inactivity theorem in `Witnesses.lean` | demonstrate exclusion from active success | emptiness tests scope and supplies no active conclusion |

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
2. pointed refinement → refinement package projection → exact comparison square;
3. fixed all-Atom condition + actual package → selected-family equality →
   authored-source package → refinement cartesian cleavage → mate;
4. regime + actual package → lifted source → all-Atom reverse extraction;
5. pulled support → exact projection → covariant `coreFiberTransportObj` →
   base support → pulled cleavage;
6. positive/negative fixtures → fixed-condition decision → active stratum;
7. active context → the exact G-115 and G-116 imported declarations.

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
