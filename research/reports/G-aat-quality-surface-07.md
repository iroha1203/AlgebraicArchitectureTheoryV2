# G-aat-quality-surface-07 report

This report records proof-obligation evidence for the target theorem
`Law-Generated Conormal First-Order Descent Theorem`.

The fixed theorem statement and completion criteria live in
`research/goals/G-aat-quality-surface-07.md`. Runtime state lives in tracking
Issue #3246.

## Target Proof State

- status: target-proof-checkpoint
- latest reviewed cycle: 5
- completion candidate: no
- tracking Issue: #3246
- next obligation: construct the law-generated ideal-power sheaf sequence

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

## Cycle 4 — actual global lift forces class zero

- decision: approve
- result type: proof-checkpoint
- Lean file:
  `research/lean/ResearchLean/AG/QualitySurface/LawGeneratedConormalDescent.lean`
- checkpoint spine:
  - `LiftProblem.GlobalLift`
  - `LiftProblem.globalRestrictionCochain`
  - `LiftProblem.globalRestrictionCochain_cocycle`
  - `LiftProblem.primitiveOfGlobal`
  - `LiftProblem.localLiftDifferenceFor_eq_d_primitiveOfGlobal`
  - `LiftProblem.connectingClassFor_eq_zero_of_globalLift`
  - `LiftProblem.connectingClassFor_eq_zero_of_nonempty_globalLift`

### Checkpoint delta

An actual global lift now generates its chart-restriction cochain. That cochain
is a zero-cocycle, and its literal difference from any explicit local-lift
choice generates a kernel-valued degree-zero primitive. The primitive exhibits
the section-specific connecting cocycle as a coboundary, so every actual global
lift forces the repository H1 class to be zero.

### Premise delta

- checkpoint: `Nonempty GlobalLift -> connectingClassFor L = 0`.
- remaining: the reverse implication from class zero to actual global lift,
  generated-presieve gluing, lift-fiber torsor, law-generated coefficient
  sequence and exactness, conormal instantiation, semantic representations,
  finite zero/nonzero witness pair, package theorem, and `H^1 = 0` corollary.

### Audits

- focused elaboration: pass
- module-wide standard-axiom assertion: pass (70 declarations)
- placeholder / hidden Unicode / private-path scans: pass
- statement classification: one direction of the primary equivalence as a
  proof-checkpoint; not D0 discharge
- certificate provenance: the primitive is generated from the literal
  local-minus-global restriction difference
- structure-field escape: global lift is the theorem antecedent; primitive,
  coboundary equation, and class-zero conclusion are constructed

### Next obligation

From a zero-class witness, construct the corrected local family, prove its
compatibility on the generated presieve through canonical pair overlaps, glue
it using the middle sheaf, and use quotient separatedness to prove that the
global middle section maps to the fixed base section.

## Cycle 5 — primary effectivity equivalence and lift-fiber torsor

- decision: approve
- result type: target-proof-checkpoint
- Lean file:
  `research/lean/ResearchLean/AG/QualitySurface/LawGeneratedConormalDescent.lean`
- checkpoint spine:
  - `LiftProblem.exists_correction_of_connectingClassFor_eq_zero`
  - `LiftProblem.correctedLocalLift_arrowsCompatible`
  - `LiftProblem.amalgamatedCorrectedLocalLift`
  - `LiftProblem.projection_amalgamatedCorrectedLocalLift`
  - `LiftProblem.connectingClassFor_eq_zero_iff_nonempty_globalLift`
  - `LiftProblem.kernelAction`
  - `LiftProblem.kernelVSub`
  - `LiftProblem.globalLiftFiber_simplyTransitive`
  - `LiftProblem.globalLiftFiberEquiv`

### Checkpoint delta

The repository zero-class criterion now yields a concrete kernel correction
cochain.  Subtracting its kernel image from the chosen local lifts gives a
degree-zero middle cochain with zero differential.  Canonical pair agreement
is transported to every common refinement by the overlap universal property,
producing an actual `Presieve.Arrows.Compatible` family on the selected cover.
The middle sheaf amalgamates that family.  Naturality of the projection and
separatedness of the quotient sheaf identify the projected amalgam with the
fixed quotient section.  This proves the primary generic equivalence
`connectingClassFor L = 0 ↔ Nonempty GlobalLift`.

Global kernel sections act on the actual-lift fiber.  The inverse difference
is constructed through the objectwise kernel comparison, and the action is
proved free and transitive as a Mathlib `AddTorsor`.  Thus the generic D0
effectivity and lift-fiber torsor are discharged without adding compatibility,
amalgamation, global-lift, or class-zero fields to `LiftProblem`.

### Premise delta

- discharged: generic connecting class, local-choice independence, zero iff
  actual global lift, generated-presieve gluing, quotient separatedness, and
  the nonempty lift-fiber torsor under `N(W)`.
- remaining: law-generated `I`, `O/I²`, `O/I`, `I/I²`; sheafified kernel
  comparison and exactness; `ConDef(W)` to the required degree-zero
  cohomology comparison; conormal instantiation; semantic representations;
  finite zero/nonzero witness pair; package theorem; and the `H¹ = 0`
  corollary.

### Audits

- focused elaboration: pass
- module-wide standard-axiom assertion: pass (100 declarations)
- placeholder / hidden Unicode / private-path scans: pass
- certificate provenance: the correction comes from the repository H1
  zero-class witness; compatibility is proved from actual canonical-pair
  restrictions and the overlap lifting property
- proof use: middle sheaf amalgamation and quotient separatedness are both
  used to construct and verify the actual global section
- structure-field escape: no correction, compatibility, amalgamation,
  global-lift, class-zero, action, freeness, or transitivity field was added
- target classification: D0 discharged; G-07 remains a proof checkpoint until
  D1--D3 and the final package are complete

### Next obligation

Construct from the law witness the raw ideal-power presheaves `O/I²` and
`O/I`, the conormal coefficient `I/I²`, their natural maps and objectwise
exactness, then sheafify canonically and prove the sheaf-level kernel
comparison used to instantiate this generic D0 theorem.
