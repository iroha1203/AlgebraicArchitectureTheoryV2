# G-aat-quality-surface-07 report

This report records proof-obligation evidence for the target theorem
`Law-Generated Conormal First-Order Descent Theorem`.

The fixed theorem statement and completion criteria live in
`research/goals/G-aat-quality-surface-07.md`. Runtime state lives in tracking
Issue #3246.

## Target Proof State

- status: target-proof-checkpoint
- latest reviewed cycle: 3
- completion candidate: no
- tracking Issue: #3246
- next obligation: prove connecting class zero iff actual global lift

## Cycle 1 — small generated cover and repository H1 checkpoint

- decision: approve
- result type: proof-checkpoint
- Lean file:
  `research/lean/ResearchLean/AG/QualitySurface/LawGeneratedConormalDescent.lean`
- checkpoint spine:
  - `SmallCanonicalTupleCover.TupleGeometry`
  - `SmallCanonicalTupleCover.FiniteComplex`
  - `SmallCanonicalTupleCover.Cover`
  - `SmallCanonicalTupleCover.complex`
  - `SmallCanonicalTupleCover.H1`
  - `SmallCanonicalTupleCover.additiveH1Class_eq_zero_iff`

### Checkpoint delta

The failed all-sieve presentation has been removed. A selected finite-poset
cover now generates its canonical tuple nerve and standard face-restriction
differential. That differential is bundled as the repository
`CoverRelativeCechComplex`, and the checkpoint exposes the repository
`AdditiveCechH1` and its zero-class iff degree-zero-coboundary theorem.

No section-specific cocycle or lift-effectivity theorem is present yet. This
cycle therefore establishes the small Čech target required by D0 but does not
discharge D0.

### Premise delta

- checkpoint: selected small generated cover realization, standard
  face-restriction differential, repository `AdditiveCechH1`, and its
  zero-class criterion.
- remaining: local-lift connecting cocycle, choice independence, zero iff
  actual global lift, lift-fiber torsor, law-generated `N / E / Q`, kernel
  comparison, objectwise exactness, generated-cover provenance, sheaf
  conditions, conormal
  instantiation, semantic representations, finite zero/nonzero witness pair,
  package theorem, and `H^1 = 0` corollary.

### Audits

- focused elaboration: pass
- module-wide standard-axiom assertion: pass
- placeholder / hidden Unicode / private-path scans: pass
- statement classification: proof-checkpoint; not D0 discharge
- certificate provenance: tuple geometry, faces, differential, and H1 are
  generated from the selected finite-poset geometry and obstruction sheaf
- proof use: the standard differential uses actual face restrictions and its
  square-zero theorem; no lift data are introduced in this checkpoint
- structure-field escape: none found
- route integrity: pass
- target-fitting / vacuity / one-way-as-equivalence / GOAL reinterpretation:
  none found

### Next obligation

Construct the local-lift difference as a cocycle of the generated repository
complex, prove choice independence, and prove that its `AdditiveCechH1` class
is zero exactly when an actual global lift exists. The reverse direction must
derive gluing from the generated-presieve sheaf API. Then construct from
law-witness input the ideal-power coefficient sequence supplying `N = I/I^2`,
`E = O/I^2`, `Q = O/I`, the projection and kernel comparison, objectwise
exactness, restriction naturality, and the required sheaf conditions.

## Cycle 2 — section-specific connecting class

- decision: approve
- result type: proof-checkpoint
- Lean file:
  `research/lean/ResearchLean/AG/QualitySurface/LawGeneratedConormalDescent.lean`
- checkpoint spine:
  - `SmallCanonicalTupleCover.LiftProblem`
  - `LiftProblem.map_differential`
  - `LiftProblem.baseSectionCochain_cocycle`
  - `LiftProblem.localLiftDifference`
  - `LiftProblem.localLiftDifference_cocycle`
  - `LiftProblem.connectingCocycle`
  - `LiftProblem.connectingClass`

### Checkpoint delta

Generic additive `N / E / Q`, objectwise kernel comparison, sheaf conditions,
a quotient section, and generator-indexed local lifts now generate a
kernel-valued degree-one cocycle on the Cycle 1 repository complex. The cocycle
proof is derived from naturality of the kernel map and the middle complex's
generated `d^1 d^0 = 0` theorem. Its class lies directly in repository
`AdditiveCechH1`.

### Premise delta

- checkpoint: section-specific local-lift difference, cocycle equation, and
  repository connecting class.
- remaining: choice independence, class zero iff actual global lift,
  generated-presieve gluing, lift-fiber torsor, law-generated coefficient
  sequence and exactness, conormal instantiation, semantic representations,
  finite zero/nonzero witness pair, package theorem, and `H^1 = 0` corollary.

### Audits

- focused elaboration: pass
- module-wide standard-axiom assertion: pass (47 declarations)
- placeholder / hidden Unicode / private-path scans: pass
- statement classification: proof-checkpoint; not D0 discharge
- certificate provenance: the cocycle is generated from explicit local lifts,
  the projection equation, objectwise kernel comparison, and standard
  differential naturality
- structure-field escape: no cocycle, cocycle equation, class, class zero, or
  global lift is supplied as an input field

### Next obligation

Generalize the generator local-lift choice, construct its chartwise kernel
change primitive, and prove equality of the resulting repository H1 classes
through `additiveH1Class_eq_iff_legacy_setoid`.

## Cycle 3 — local-lift choice independence

- decision: approve
- result type: proof-checkpoint
- Lean file:
  `research/lean/ResearchLean/AG/QualitySurface/LawGeneratedConormalDescent.lean`
- checkpoint spine:
  - `LiftProblem.GeneratorLocalLiftFamily`
  - `LiftProblem.localLiftDifferenceFor`
  - `LiftProblem.connectingCocycleFor`
  - `LiftProblem.connectingClassFor`
  - `LiftProblem.changePrimitive`
  - `LiftProblem.localLiftDifferenceFor_sub`
  - `LiftProblem.connectingClass_choice_independent`

### Checkpoint delta

Every explicit generator-local lift choice now generates its own repository
connecting class. The pointwise difference of two choices generates a
kernel-valued degree-zero primitive, and differential naturality proves that
the two overlap cocycles differ by its coboundary. The repository H1 setoid
therefore identifies their classes.

### Premise delta

- checkpoint: local-lift choice independence in repository `AdditiveCechH1`.
- remaining: class zero iff actual global lift, generated-presieve gluing,
  lift-fiber torsor, law-generated coefficient sequence and exactness,
  conormal instantiation, semantic representations, finite zero/nonzero
  witness pair, package theorem, and `H^1 = 0` corollary.

### Audits

- focused elaboration: pass
- module-wide standard-axiom assertion: pass (61 declarations)
- placeholder / hidden Unicode / private-path scans: pass
- certificate provenance: the change primitive is generated from the literal
  difference of two explicit local-lift choices
- structure-field escape: choice independence and the coboundary equation are
  proved, not supplied as fields

### Next obligation

Use the repository zero-class criterion to obtain a correction cochain, prove
the corrected chart family is compatible on the generated presieve, glue it
with the middle sheaf, and use quotient separatedness to fix its projection to
the original base section. Prove the reverse implication from an actual global
lift by constructing its chartwise kernel primitive.
