# G-aat-quality-surface-07 report

This report records proof-obligation evidence for the target theorem
`Law-Generated Conormal First-Order Descent Theorem`.

The fixed theorem statement and completion criteria live in
`research/goals/G-aat-quality-surface-07.md`. Runtime state lives in tracking
Issue #3246.

## Target Proof State

- status: target-proof-checkpoint
- latest reviewed cycle: 16
- completion candidate: no
- tracking Issue: #3246
- next obligation: construct the finite Boolean-circle law-sensitive witness

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

## Cycle 6 — law-generated raw ideal-power sequence

- decision: approve
- result type: target-proof-checkpoint
- Lean file:
  `research/lean/ResearchLean/AG/QualitySurface/LawGeneratedIdealPowerSequence.lean`
- checkpoint spine:
  - `Raw.map_obstructionIdeal_sq_le`
  - `Raw.q1Coefficient`
  - `Raw.conormalCoefficient`
  - `Raw.projection`
  - `Raw.conormalInclusion`
  - `Raw.projection_inclusion_zero`
  - `Raw.projection_comp_inclusion`
  - `Raw.projectionAt_ker`
  - `Raw.conormalKernelEquiv`
  - `Raw.conormalInclusionAt_injective`
  - `Raw.projectionAt_surjective`

### Checkpoint delta

The existing law-equation witness core now generates the raw first-order
sequence without accepting any new geometric or effectivity field.  The
selected law witnesses generate `I`; its square is restriction-compatible;
and `O/I²`, `O/I`, and `I/I²` form additive presheaves.  The quotient
projection and conormal inclusion are natural transformations generated from
`Ideal.quotientMap` and `Ideal.mapCotangent`.

Objectwise, the projection kills the conormal inclusion.  Mathlib's canonical
cotangent ideal and quotient-factor kernel identify `I/I²` with the actual
kernel of `O/I² -> O/I`.  The conormal inclusion is injective and the quotient
projection is surjective.  These are theorem outputs from the law-witness core,
not supplied exactness or comparison fields.

### Premise delta

- discharged: raw law-generated `I`, `O/I²`, `O/I`, `I/I²`; restriction
  functoriality; projection and inclusion naturality; objectwise kernel
  comparison; objectwise inclusion injectivity and projection surjectivity.
- remaining: a law-generated ideal presheaf/subsheaf `I` with restriction
  provenance; canonical sheafification of the three additive presheaves;
  sheaf-level kernel comparison and exactness; `ConDef(W)` to degree-zero
  cohomology comparison; D0 instantiation; semantic representations; finite
  zero/nonzero witness pair; package theorem; and the `H¹ = 0` corollary.

### Audits

- focused elaboration: pass
- module-wide standard-axiom assertion: pass (26 declarations)
- supplied-field audit: no sheaf, exactness, kernel comparison, naturality, or
  effectivity field was added
- certificate provenance: every carrier and map is generated from
  `SemanticLawEquationWitnessIdealCore.obstructionIdeal`, `restrict`, and the
  existing restriction theorem
- target classification: raw D1 sequence checkpoint; G-07 remains a proof
  checkpoint until sheafification, D0 instantiation, D2, D3, and the final
  package are complete

### Next obligation

Construct the law-generated ideal presheaf/subsheaf `I` from the existing
objectwise ideals and restriction theorem.  Apply canonical AddCommGrp-valued
sheafification to the generated raw sequence, derive the sheaf-level kernel
comparison without accepting it as a field, and instantiate the generic D0
theorem on the selected finite-poset cover.

## Cycle 7 — categorical short exact sequence and conditional sheafification

- decision: approve
- result type: target-proof-checkpoint
- Lean file:
  `research/lean/ResearchLean/AG/QualitySurface/LawGeneratedIdealPowerShortExact.lean`
- checkpoint spine:
  - `Raw.shortComplex`
  - `Raw.conormalInclusion_mono`
  - `Raw.projection_epi`
  - `Raw.kernelElement`
  - `Raw.kernelLift`
  - `Raw.conormalInclusionIsKernel`
  - `Raw.shortComplex_exact`
  - `Raw.shortComplex_shortExact`
  - `Raw.sheafifiedShortComplex`
  - `Raw.sheafifiedShortComplex_shortExact`

### Checkpoint delta

The raw law-generated sequence is now a categorical `ShortComplex` of
`AddCommGrpCat`-valued presheaves.  Objectwise injectivity and surjectivity
generate categorical mono and epi instances.  The Cycle 6 kernel equivalence
constructs an explicit natural lift for every presheaf morphism killed by the
projection, proving that the conormal inclusion is the categorical kernel.
Consequently the raw sequence is `Exact` and `ShortExact` without accepting an
exactness or kernel certificate.

Under Mathlib's general sheafification availability class
`HasSheafify S.topology AddCommGrpCat`, `ShortComplex.ShortExact.map_of_exact`
sends the raw sequence through `presheafToSheaf` and proves the resulting sheaf
sequence short exact.  This theorem uses the canonical sheafification functor;
it does not accept selected sheaves or sheaf-condition fields.

### Premise delta

- discharged: categorical raw `ShortComplex`; presheaf-level mono, epi,
  categorical kernel, exactness, and short exactness.
- conditionally discharged: preservation of the generated short exact sequence
  by canonical AddCommGrp-valued sheafification, relative to
  `[HasSheafify S.topology AddCommGrpCat]`.
- remaining: a law-generated ideal presheaf/subsheaf `I` and its sheaf-level
  provenance; a concrete or imported canonical source of that `HasSheafify`
  instance for the selected AAT topology; unconditional sheafified sequence;
  the comparison to D0 coefficient sheaves; `ConDef(W)` to degree-zero
  cohomology comparison; semantic representations; finite zero/nonzero witness
  pair; package theorem; and the `H¹ = 0` corollary.

### Audits

- focused prerequisite elaboration: pass (Cycle 6 single file)
- focused Cycle 7 elaboration: pass
- module-wide standard-axiom assertion: pass (15 declarations)
- exactness provenance: `kernelLift` is generated pointwise by
  `Raw.conormalKernelEquiv` and its naturality is proved using the generated
  conormal inclusion and the input morphism's naturality
- supplied-field audit: no exactness, kernel, sheaf, or effectivity structure
  field was added
- sheafification availability audit: no arbitrary-AAT-site global instance of
  `HasSheafify S.topology AddCommGrpCat` was found; the theorem therefore keeps
  this typeclass visible and does not count it as discharged
- target classification: raw categorical D1 exactness is proved; sheafified
  exactness remains assumption-relative until the availability premise is
  constructed

### Next obligation

Construct the law-generated ideal presheaf/subsheaf `I` and retain its map into
the ambient observable presheaf through sheafification.  Provide a canonical
construction or reviewed Mathlib import yielding
`HasSheafify S.topology AddCommGrpCat` for the selected AAT topology.  Then
instantiate the sheafified short exact sequence unconditionally and connect it
to the generic D0 lift problem.

## Cycle 8 — law-generated additive ideal subpresheaf provenance

- decision: approve
- result type: target-proof-checkpoint
- Lean file:
  `research/lean/ResearchLean/AG/QualitySurface/LawGeneratedIdealSubpresheaf.lean`
- checkpoint spine:
  - `observableCoefficient`
  - `obstructionIdealRestrict`
  - `obstructionIdealCoefficient`
  - `obstructionIdealInclusion`
  - `obstructionIdealInclusion_mono`
  - `obstructionIdealSubobject`
  - `sheafifiedObstructionIdealInclusion`
  - `sheafifiedObstructionIdealInclusion_provenance`

### Checkpoint delta

The objectwise law-generated ideals now form an `AddCommGrpCat`-valued
presheaf.  Its restriction maps are constructed from `G.restrict` and
`G.map_obstructionIdeal_le`; identity and composition are proved from the raw
restriction laws.  The subtype inclusions assemble into a natural
transformation to the ambient observable presheaf, with categorical mono and
`Subobject` presentations generated from objectwise subtype injectivity.

Relative to `[HasSheafify S.topology AddCommGrpCat]`, canonical sheafification
maps this inclusion to a sheaf morphism.  The theorem
`sheafifiedObstructionIdealInclusion_provenance` is the canonical-unit
naturality square, so the sheafified morphism remains tied to the raw
law-generated inclusion rather than a supplied comparison map.

### Premise delta

- discharged: ambient observable additive presheaf; obstruction-ideal additive
  presheaf; restriction stability; natural ambient inclusion; mono and
  categorical subobject; canonical-unit provenance square.
- conditionally discharged: the induced morphism between additive
  sheafifications, relative to
  `[HasSheafify S.topology AddCommGrpCat]`.
- remaining: a concrete or imported canonical source of that `HasSheafify`
  instance for the selected AAT topology; sheafified ring action on the
  additive ideal object; stability under that action; a true ideal subsheaf of
  a ring sheaf; D0 comparison and instantiation; semantic representations;
  finite zero/nonzero witness pair; package theorem; and the `H¹ = 0`
  corollary.

The additive sheafification in this cycle is not called an ideal sheaf.
Additive sheafification alone does not construct or prove stability under a
sheafified ring action.  Those conditions remain undischarged and this cycle's
mono or provenance square is not completion evidence for them.

### Audits

- focused Cycle 8 elaboration: pass
- module-wide standard-axiom assertion: pass (9 declarations)
- construction provenance: every object and morphism is generated from
  `SemanticLawEquationWitnessIdealCore.Observable`, `obstructionIdeal`,
  `restrict`, and `map_obstructionIdeal_le`
- supplied-field audit: no ideal-presheaf, naturality, mono, subobject,
  sheafification comparison, ring-action, or ideal-subsheaf field was added
- sheafification availability audit: the same visible
  `[HasSheafify S.topology AddCommGrpCat]` premise as Cycle 7 remains
- target classification: additive subpresheaf and sheafification provenance
  are proved; true ideal-subsheaf structure and unconditional sheafification
  remain undischarged

### Next obligation

Construct the sheafified ambient ring action and prove stability of the
sheafified additive subobject, yielding the true ideal subsheaf required by
D1.  Provide the selected topology's canonical
`HasSheafify S.topology AddCommGrpCat` construction, combine Cycle 7's
sheafified short exact sequence with Cycle 8's inclusion provenance, and
instantiate the generic D0 lift problem.

## Cycle 9 — unconditional large-universe additive sheafification

- decision: approve
- result type: target-proof-checkpoint
- Lean file:
  `research/lean/ResearchLean/AG/QualitySurface/LawGeneratedIdealPowerLiftedSheafification.lean`
- checkpoint spine:
  - `liftPresheafFunctor`
  - `liftPresheafFunctor_additive`
  - `liftedShortComplex`
  - `liftedShortComplex_shortExact`
  - `sheafifiedShortComplex`
  - `sheafifiedShortComplex_shortExact`

### Checkpoint delta

The Cycle 7 raw short exact sequence is lifted objectwise from
`AddCommGrpCat.{u}` to `AddCommGrpCat.{u + 1}` using Mathlib's fully faithful
additive `uliftFunctor`.  Whiskering by that functor preserves finite limits
and finite colimits, so the lifted presheaf sequence remains short exact.

At coefficient universe `u + 1`, Mathlib's concrete sheafification instance is
available for every selected AAT site.  The lifted sequence is therefore sent
through `presheafToSheaf` without a `HasSheafify` theorem premise, and
`sheafifiedShortComplex_shortExact` proves that the resulting canonical
additive sheaf sequence is short exact.  No selected sheaf, sheaf condition,
kernel comparison, or exactness certificate is accepted.

### Premise delta

- discharged: objectwise coefficient universe lift; preservation of the raw
  short exact sequence by that lift; canonical
  `AddCommGrpCat.{u + 1}`-valued sheafification for arbitrary AAT sites; and
  short exactness of the resulting additive sheaf sequence.
- remaining: a large-coefficient adapter from the sheafified sequence to the
  generic D0 lift problem and its finite-cover cohomology surface; sheafified
  ambient ring action and stability of the additive ideal object; a true ideal
  subsheaf; semantic representations; finite zero/nonzero witness pair;
  package theorem; and the `H¹ = 0` corollary.

The sequence remains at coefficient universe `u + 1`; this cycle does not
assert a descent to `AddCommGrpCat.{u}`.  It also does not identify additive
sheafification with an ideal sheaf.  The true ideal-subsheaf structure and the
large-coefficient D0 comparison remain separate proof obligations.

### Audits

- focused Cycle 9 elaboration: pass
- module-wide standard-axiom assertion: pass (8 declarations)
- exactness provenance: the lifted complex is the image of Cycle 7's generated
  raw complex, and both short-exactness proofs use
  `ShortComplex.ShortExact.map_of_exact`
- sheafification availability: the `u + 1` concrete instance is inferred by
  Mathlib; no `HasSheafify` argument appears in the declarations
- supplied-field audit: no universe-lifted sequence, sheaf, sheaf condition,
  kernel comparison, exactness, ring-action, or ideal-subsheaf field was added
- target classification: unconditional additive D1 sheafification is proved;
  the D0 adapter and true ideal subsheaf remain unproved

### Next obligation

Generalize the generic D0 lift problem and its finite canonical-tuple
cohomology surface to a coefficient universe independent of the AAT site
universe, then instantiate it with the Cycle 9 sheafified short exact sequence.
Separately construct the sheafified ambient ring action and prove stability of
the additive ideal object before claiming a true ideal subsheaf.

## Cycle 10 — large-coefficient canonical-tuple additive H1

- decision: approve
- result type: target-proof-checkpoint
- Lean file:
  `research/lean/ResearchLean/AG/QualitySurface/LawGeneratedLargeCoefficientCech.lean`
- checkpoint spine:
  - `Tuple`
  - `overlapObject`
  - `face`
  - `faceHom`
  - `Cochain`
  - `faceRestriction`
  - `differential`
  - `d0`
  - `d1`
  - `d1_d0`
  - `threeTermComplex`
  - `H1`
  - `h1Class_isZero_iff`
  - `sheafThreeTermComplex`
  - `SheafH1`

### Checkpoint delta

The AAT site universe and additive coefficient universe are now independent on
the canonical finite tuple cover.  For any
`F : S.categoryᵒᵖ ⥤ AddCommGrpCat.{v}`, the coefficient-free overlap geometry
generates degree-zero, degree-one, and degree-two cochains and their finite
alternating face-restriction maps.

The proof of `d1_d0` uses the canonical two-coface simplex identities, rewrites
iterated restrictions as direct composite restrictions, and identifies the
two routes through the thin context category before signed cancellation.  The
result is packaged in the repository `Cohomology.AdditiveThreeTermComplex`, so
its additive `H¹` and the zero-class criterion are available in
`Type (max u v)` without identifying the coefficient universe with the site
universe.  Bundled additive sheaves enter through their underlying presheaves;
no sheaf condition is accepted by this construction.

### Premise delta

- discharged: large-coefficient canonical tuple cochains in degrees zero to
  two; generated face restrictions and alternating differentials; the
  differential-composition theorem; repository additive `H¹`; and the theorem
  that a represented class is zero exactly when it is a degree-zero
  coboundary.
- remaining: the large-coefficient D0 lift problem, connecting cocycle,
  choice-independence, zero-class/global-lift equivalence, and lift-fiber
  torsor; instantiation with Cycle 9's sheafified sequence; a true ideal
  subsheaf; semantic representations; finite zero/nonzero witness pair;
  package theorem; and the `H¹ = 0` corollary.

### Audits

- focused Cycle 10 elaboration: pass
- module-wide standard-axiom assertion: pass
- differential provenance: cofaces and overlap morphisms are generated from
  `FinitePosetCoverGeometry.canonicalTupleCoverGeometryFromOverlap`; no face,
  differential-composition, cocycle, or vanishing field is accepted
- universe audit: tuple geometry remains in the AAT site universe while
  section groups and additive `H¹` may live in an independent coefficient
  universe
- target classification: the large-coefficient Cech/H1 checkpoint is proved;
  the D0 theorem and its Cycle 9 instantiation remain unproved

### Next obligation

Port the generic D0 lift problem to bundled
`Sheaf S.topology AddCommGrpCat.{v}` coefficients, construct its objectwise
kernel comparison from the generated short exact sequence, and instantiate it
with Cycle 9.  Keep the sheafified ring action and true ideal-subsheaf proof as
separate D1 obligations.

## Cycle 11 — short-exact large connecting class

- decision: approve
- result type: target-proof-checkpoint
- Lean file:
  `research/lean/ResearchLean/AG/QualitySurface/LawGeneratedLargeConormalDescent.lean`
- checkpoint spine:
  - `sectionFunctor`
  - `sectionKernelIsLimit`
  - `sectionKernelIso`
  - `sectionKernelEquiv`
  - `sectionKernelEquiv_apply`
  - `LocalLiftData`
  - `LocalLiftData.map_differential`
  - `LocalLiftData.restrictionCochain_cocycle`
  - `LocalLiftData.localLiftDifferenceFor`
  - `LocalLiftData.localLiftDifferenceFor_cocycle`
  - `LocalLiftData.connectingClassFor`
  - `LocalLiftData.localLiftDifferenceFor_sub`
  - `LocalLiftData.connectingClass_choice_independent`

### Checkpoint delta

The Cycle 10 large-coefficient complex now receives the first half of generic
D0.  For a short exact complex of bundled additive sheaves at the concrete
coefficient universe used by Cycle 9, evaluation at each site object transports
the categorical kernel limit through `sheafToPresheaf` and evaluation.  The
resulting categorical kernel is identified with the concrete additive kernel,
so the sectionwise kernel equivalence is generated from `K.ShortExact` rather
than accepted as local-lift data.

`LocalLiftData geometry K` stores only the fixed quotient section, explicit
generator-local lifts, and the equations saying that they lift that same
section.  These inputs generate the overlap difference, its degree-one cocycle,
and the large additive connecting class.  Two explicit local-lift choices
differ by a generated degree-zero kernel primitive, and quotient soundness
proves that their connecting classes agree.

### Premise delta

- discharged in this checkpoint: sectionwise kernel comparison generated from
  categorical short exactness; large-coefficient cochain naturality; the
  local-lift connecting cocycle; and independence of the local-lift choice.
- remaining: class-zero iff actual global lift; selected-cover sheaf gluing;
  nonempty lift-fiber torsor and simple transitivity; direct Cycle 9
  specialization theorem; a true ideal subsheaf; semantic representations;
  finite zero/nonzero witness pair; package theorem; and the `H¹ = 0`
  corollary.

### Audits

- focused Cycle 11 elaboration: pass
- module-wide standard-axiom assertion: pass (48 declarations)
- certificate provenance: `sectionKernelEquiv` is built from
  `ShortComplex.ShortExact.fIsKernel`, preservation of the kernel limit under
  the underlying-presheaf and evaluation functors, and
  `AddCommGrpCat.kernelIsoKer`
- supplied-field audit: `LocalLiftData` contains no kernel comparison,
  exactness, cocycle, class-zero, compatible family, or global-lift field
- sectionwise-surjectivity audit: no sheaf epimorphism is interpreted as
  surjective on sections
- target classification: connecting-class construction and choice
  independence are proved; D0 effectivity is still unproved

### Next obligation

Use `h1Class_isZero_iff` to obtain the correction cochain, prove that corrected
local lifts form a compatible family on the selected generated cover, derive
their amalgamation from the bundled middle sheaf condition, and use quotient
separatedness to prove the primary `H1IsZero` iff actual-global-lift theorem.
Then construct the nonempty lift-fiber torsor and specialize the result to the
Cycle 9 law-generated sheafified short complex.

## Cycle 12 — large-coefficient D0 effectivity and lift-fiber torsor

- decision: approve
- result type: target-proof-checkpoint
- Lean file:
  `research/lean/ResearchLean/AG/QualitySurface/LawGeneratedLargeConormalDescent.lean`
- checkpoint spine:
  - `LocalLiftData.GlobalLift`
  - `LocalLiftData.connectingClassFor_isZero_of_globalLift`
  - `LocalLiftData.exists_correction_of_connectingClassFor_isZero`
  - `LocalLiftData.correctedLocalLift_arrowsCompatible`
  - `LocalLiftData.amalgamatedCorrectedLocalLift`
  - `LocalLiftData.projection_amalgamatedCorrectedLocalLift`
  - `LocalLiftData.connectingClassFor_isZero_iff_nonempty_globalLift`
  - `LocalLiftData.globalLiftAddTorsor`
  - `LocalLiftData.globalLiftFiber_simplyTransitive`
  - `LocalLiftData.lawGenerated_connectingClass_isZero_iff_nonempty_globalLift`

### Checkpoint delta

The large-coefficient connecting class now has the full section-specific D0
effectivity theorem. An actual global lift generates a kernel-valued
degree-zero primitive, hence an `H1IsZero` witness. Conversely, the repository
zero-class criterion produces a correction cochain. Its corrected local lifts
agree on canonical pairs and therefore on every common refinement. The middle
bundled sheaf amalgamates that compatible family, while quotient separatedness
proves that the amalgam projects to the original base section.

This proves
`H1IsZero (connectingClassFor hK L) ↔ Nonempty GlobalLift`. Global kernel
sections act freely and transitively on every nonempty lift fiber, producing a
Mathlib `AddTorsor`, an explicit simple-transitivity theorem, and an equivalence
after choosing one lift. The theorem is specialized directly to Cycle 9's
canonical law-generated sheafified short exact sequence.

### Premise delta

- discharged: large-coefficient class vanishing iff actual global lift;
  selected-cover sheaf gluing; quotient separatedness; nonempty lift-fiber
  torsor; and direct Cycle 9 law-generated specialization.
- remaining: a true law-generated ideal subsheaf with sheafified ambient ring
  action and stability; the required `ConDef(W)` to degree-zero cohomology
  comparison; semantic representations; a finite law-sensitive zero/nonzero
  witness pair; package theorem; and the global `H¹`-vanishing corollary.

### Audits

- focused Cycle 12 elaboration: pass
- module-wide standard-axiom assertion: pass (94 declarations)
- placeholder / hidden Unicode / private-path scans: pass
- statement review: the primary statement uses repository `H1IsZero` and an
  actual global section fiber, not a primitive or compatible-family predicate
- effectivity proof-use: pair agreement, arbitrary common refinement,
  `FamilyOfElements`, `amalgamate`, `valid_glue`, and quotient separatedness
  all occur in the proof chain
- provenance: sectionwise kernel comparison is generated from categorical
  short exactness; the law specialization supplies Cycle 9's generated
  `sheafifiedShortComplex_shortExact`
- supplied-field audit: `LocalLiftData` still contains only the base section,
  explicit local lifts, and their projection equations
- four independent review lanes: No major findings
- target classification: large-coefficient D0 and its law-sequence
  specialization are discharged; G-07 remains a proof checkpoint until the
  remaining D1--D3 artifacts and final package are complete

### Next obligation

Construct the law-generated coefficient as a true ideal object after
sheafification. The current `AddCommGrpCat` sheafification supplies only the
additive sequence, so the next construction must generate the ambient ring
action and ideal stability rather than accept either as input. Then identify
the resulting underlying additive kernel sheaf with the Cycle 9 first term and
construct the required degree-zero cohomology comparison.

## Cycle 13 — law-generated internal ring sheaves

- decision: approve
- result type: target-proof-checkpoint
- Lean file:
  `research/lean/ResearchLean/AG/QualitySurface/LawGeneratedRingSheaf.lean`
- checkpoint spine:
  - `LargeInt`
  - `LargeZMod`
  - `commRingObject`
  - `observableRingCoefficient`
  - `q1RingCoefficient`
  - `q0RingCoefficient`
  - `projectionRingCoefficient`
  - `q1RingPresheafObject`
  - `q0RingPresheafObject`
  - `projectionRingPresheaf`
  - `q1RingSheafObject`
  - `q0RingSheafObject`
  - `projectionRingSheaf`

### Checkpoint delta

The law-generated observable rings, `O/I²`, and `O/I` now form actual internal
commutative-ring coefficient functors in large-universe integer modules. The
construction lifts each raw commutative ring and restriction homomorphism
through `AlgCat` and the equivalence between algebra objects and internal
monoids, with commutativity proved from the original ring multiplication.

The q1-to-q0 projection is proved natural as a morphism of internal ring
coefficient functors. The functor-category commutative-monoid equivalence then
packages q1, q0, and their projection as internal ring presheaf objects.
Canonical monoidal sheafification transports the same objects and morphism to
internal commutative ring sheaves on the selected AAT site.

This cycle intentionally stops at ring sheaves and their projection. The
categorical kernel, its ambient action, ideal stability, and comparison with
Cycle 9's additive first term remain unproved and are not part of this
checkpoint claim.

### Premise delta

- discharged: law-generated q1/q0 ring-valued coefficient functors; universe
  lift with scalar compatibility; internal commutative ring presheaves;
  natural ring projection; monoidal sheafification of q1/q0 and the projection.
- remaining: the projection kernel as a true ideal object; the comparison with
  Cycle 9's additive conormal sheaf; the required degree-zero cohomology
  comparison; semantic representations; a finite law-sensitive zero/nonzero
  witness pair; package theorem; and the global `H¹`-vanishing corollary.

### Audits

- focused Cycle 13 elaboration: pass
- module-wide standard-axiom assertion: pass (24 declarations)
- placeholder / hidden Unicode / private-path scans: pass
- proof-use: q1/q0 functor laws reduce to the generated quotient restriction
  lemmas and `G.restrict_id` / `G.restrict_comp`; projection naturality reduces
  to the raw representative lemmas
- provenance: ring multiplication and commutativity come from the raw quotient
  rings; sheafified objects and projection are direct functorial images under
  canonical monoidal sheafification
- supplied-field audit: no ring object, action, ideal stability, kernel,
  exactness, or sheafification certificate is accepted as input
- public-claim correction: the module was renamed from the overbroad draft
  name to `LawGeneratedRingSheaf` before review approval
- four independent review lanes after the rename: No major findings
- target classification: the ring-sheaf prerequisite for the true conormal
  ideal is discharged; G-07 remains a proof checkpoint

### Next obligation

Take the categorical kernel of `projectionRingSheaf`, prove multiplication by
q1 preserves that kernel, and construct its internal module object without an
action or stability premise. Then compare the underlying additive kernel sheaf
with Cycle 9's `sheafifiedShortComplex G` first term by canonical
sheafification comparison and kernel uniqueness.

## Cycle 14 — true conormal ideal and selected-cover H0 comparison

- decision: approve
- result type: target-proof-checkpoint
- Lean files:
  - `research/lean/ResearchLean/AG/QualitySurface/LawGeneratedConormalIdealSheaf.lean`
  - `research/lean/ResearchLean/AG/QualitySurface/LawGeneratedLargeCoefficientH0.lean`
- checkpoint spine:
  - `moduleSheafMonoidalClosed`
  - `moduleSheafMonoidalPreadditive`
  - `conormalIdealCarrier`
  - `multiplication_kernel_annihilates`
  - `conormalIdealAction`
  - `conormalIdealModObj`
  - `conormalIdeal`
  - `conormalIdealInclusion`
  - `H0`
  - `baseSectionToH0`
  - `h0ToBaseSection`
  - `baseSectionsEquivH0`
  - `lawGeneratedConormalSectionsEquivH0`

### Checkpoint delta

The kernel of the Cycle 13 ring-sheaf projection now carries a generated
ambient q1 action. The sheaf category's tensor additivity is itself generated:
reflective monoidal closedness makes left tensoring a left adjoint, hence
additive, while braiding transfers additivity to right tensoring. This supplies
the tensor-zero fact needed to combine `IsMonHom.mul_hom` with the categorical
kernel equation.

Ambient multiplication therefore factors through the kernel by `kernel.lift`.
Cancelling the kernel inclusion reduces the action's unit and multiplication
laws to the internal ring laws. The resulting `ModObj` is bundled as a `Mod_`
ideal, with a module morphism into the regular q1 module and a theorem that its
underlying inclusion is killed by the q1-to-q0 projection. No action or
stability premise is accepted.

Independently, the large selected-cover degree-zero cohomology is fixed as
`ker d⁰`. Restriction sends an actual base section to this kernel. In the other
direction, a zero-cocycle gives canonical-pair agreement, compatibility on all
common refinements, and a sheaf amalgamation. Validity of that glue and
separatedness prove both inverse laws, yielding
`baseSectionsEquivH0`. Direct specialization to Cycle 9's first sheaf proves
the required additive `ConDef(W) ≃ Čech H⁰(U, ConDef)` comparison.

### Premise delta

- discharged: the Cycle 13 projection kernel as a true internal ideal object;
  generated ambient action and stability; module inclusion and projection-zero;
  selected-cover degree-zero cohomology; base-section/H0 additive equivalence;
  direct Cycle 9 additive-conormal specialization.
- remaining: an explicit comparison between the new internal-ring kernel
  carrier and Cycle 9's additive first sheaf; semantic representations; a
  finite law-sensitive zero/nonzero witness pair; package theorem; and the
  global `H¹`-vanishing corollary.

### Audits

- focused ideal elaboration: pass (19 declarations)
- focused H0 elaboration: pass (24 declarations)
- both module-wide standard-axiom assertions: pass
- placeholder / hidden Unicode / private-path scans: pass
- ideal proof-use: closed monoidal reflection, tensor additivity,
  `IsMonHom.mul_hom`, `kernel.condition`, `kernel.lift`, mono cancellation, and
  internal monoid laws all occur in the construction
- H0 proof-use: pair agreement, arbitrary common refinement,
  `FamilyOfElements`, `amalgamate`, `valid_glue`, and separatedness all occur in
  the two inverse proofs
- supplied-field audit: no action, stability, kernel comparison, compatible
  family, glue, or comparison inverse is accepted as input
- four independent review lanes: No major findings
- target classification: true conormal ideal and the selected-cover H0
  comparison are discharged; the explicit cross-construction kernel
  comparison and D2--D3 package obligations remain

### Next obligation

Construct the canonical isomorphism between the underlying additive sheaf of
the internal conormal ideal and Cycle 9's `sheafifiedShortComplex G` first
term. Compare q1 and q0 through sheafification composition, then obtain the
first-term isomorphism from the uniqueness of the two categorical kernels.

## Cycle 15 — canonical internal/additive conormal comparison

- decision: approve
- result type: target-proof-checkpoint
- Lean file:
  `research/lean/ResearchLean/AG/QualitySurface/LawGeneratedConormalComparison.lean`
- checkpoint spine:
  - `moduleForgetEquivalence`
  - `sheafificationComparison`
  - `q1SheafIso`
  - `q0SheafIso`
  - `projection_square`
  - `conormalSheafIso`
  - `conormalSheafIso_inclusion`
  - `shortComplexIso`
  - `internalUnderlyingShortExact`

### Checkpoint delta

Large integer modules are canonically equivalent to large additive
commutative groups by restriction of scalars along the lifted-integer ring
equivalence followed by the integer-module equivalence.  The induced
forgetful functor preserves sheafification.  The canonical
`sheafComposeNatIso` therefore compares the Cycle 9 additive sheafification
with the underlying additive sheaves of the Cycle 13 internal q1 and q0 ring
sheaves.  Naturality of that single comparison proves the projection square.

The first-term comparison is generated from categorical universal
properties.  Cycle 9 short exactness identifies its first term with the
kernel of its projection.  The projection square transports that kernel, and
preservation of kernels by the induced right-adjoint sheaf functor identifies
it with the underlying additive carrier of the Cycle 14 true conormal ideal.
The resulting inclusion square and q1/q0 comparisons form an isomorphism of
short complexes, transporting short exactness to the internal ideal sequence.

### Premise delta

- discharged: canonical q1/q0 sheafification comparison; projection
  naturality square; canonical internal/additive conormal kernel comparison;
  inclusion compatibility; short-complex comparison; underlying internal
  ideal short exactness.
- remaining: lawful-reading atlas and semantic first-order repair
  representation; a finite law-sensitive zero/nonzero witness pair; package
  theorem; and the global `H¹`-vanishing corollary.

### Audits

- focused comparison elaboration: pass (16 declarations)
- module-wide standard-axiom assertion: pass
- proof-use: the q1/q0 comparison is the canonical sheaf-composition natural
  isomorphism; the projection square is its naturality equation; the conormal
  comparison uses Cycle 9 kernel exactness, `kernel.mapIso`, and
  `PreservesKernel.iso`
- provenance: the module/additive equivalence comes from the lifted-integer
  ring equivalence and the integer-module/additive-group equivalence; no
  objectwise or selected comparison is supplied
- supplied-field audit: no sheafification comparison, projection square,
  kernel comparison, inclusion square, exactness, or inverse is accepted as
  input
- four independent review lanes: No major findings
- target classification: the law-generated ideal/quotient/kernel sheaves and
  exactness ledger item is discharged; D2 finite nonvacuity and D3 semantic
  representation remain

### Next obligation

Construct a lawful-reading atlas from patchwise raw readings whose overlap
differences are explicit finite combinations of required-law witnesses.
Generate q0 compatibility, actual sheaf amalgamation, and q1 local lifts from
that input, then use the Cycle 15 comparison to identify the internal semantic
repair fiber with the Cycle 12 actual global-lift fiber.

## Cycle 16 — explicit law-generated atlas and correction-primitive representation

- decision: approve
- result type: target-proof-checkpoint
- Lean file:
  `research/lean/ResearchLean/AG/QualitySurface/LawGeneratedSemanticFirstOrderRepair.lean`
- checkpoint spine:
  - `PatchReadingSource`
  - `DisplayedRequiredLaw`
  - `OverlapLawCombination`
  - `ExplicitLawGeneratedReadingAtlas`
  - `rawQ0_pair_compatible`
  - `additiveAtlasQ0Reading`
  - `internalAtlasQ0Reading`
  - `atlasQ0Comparison`
  - `toLocalLiftData`
  - `InternalFirstOrderLift`
  - `internalFirstOrderLiftEquiv`
  - `SemanticFirstOrderRepair`
  - `SemanticFirstOrderRepairEquiv`
  - `connectingClass_isZero_iff_nonempty_semanticFirstOrderRepair`

### Checkpoint delta

The checkpoint accepts an explicit patch-reading atlas.  Every pairwise
reading difference is displayed as a finite linear combination of selected
required-law violation witnesses indexed by actual Atom data.  This expansion
is a conditional local-relation input, not a discharged lawful-reading
constructor.  Given that explicit equation, generated-ideal containment sends
the difference to equality in `O/I`.

Those local quotient readings are extended to arbitrary common refinements
and amalgamated independently in two sheaves.  The first construction uses
Cycle 9's additive q0 sheafification; the second uses Cycle 13's internal q0
module sheaf.  The local sheafification-unit factorization and selected-cover
separatedness prove `atlasQ0Comparison`, identifying the two actual base
sections through Cycle 15's canonical q0 comparison.

The same raw local readings modulo `I²` generate q1 local lifts and therefore
the entire Cycle 12 `LocalLiftData` without a local-solvability certificate.
The internal q1 projection fiber is kept under the explicit name
`InternalFirstOrderLift`; Cycle 15 compares it with the additive global-lift
fiber.

`SemanticFirstOrderRepair` is defined independently as a kernel-valued Čech
zero-cochain whose coboundary is the generated local-lift difference.  Such a
correction primitive generates an actual global lift by correcting the local
q1 readings and using sheaf amalgamation.  Conversely, every actual global
lift generates its correction primitive.  Selected-cover separatedness and
the sectionwise kernel equivalence prove that these two constructions are
inverse.  Cycle 12 effectivity therefore identifies connecting-class zero
with existence of this correction-primitive representation.

### Premise delta

- discharged: explicit-atlas q0 compatibility; actual q0 sheaf effectivity;
  generated q1 local solvability; additive/internal q0 comparison;
  correction-primitive/global-lift equivalence; class-zero iff correction
  primitive existence.
- remaining: a constructor that derives the explicit overlap expansions from
  primitive semantic/law data; the same-cover/same-ambient-ring law-sensitive
  finite zero/nonzero witness pair; semantic repair specialization; torsor/H0
  transport; the final theorem package; and the global `H¹`-vanishing
  corollary.

### Audits

- focused atlas/correction elaboration: pass (115 declarations)
- module-wide standard-axiom assertion: pass
- proof-use: ideal membership uses required-law witness containment;
  common-refinement compatibility, `amalgamate`, `valid_glue`, separatedness,
  both Cycle 15 quotient comparisons, Cycle 12 correction/gluing, and the
  sectionwise kernel equivalence occur in the proof chain
- provenance: the overlap expansion is explicitly classified as input and
  exposes every coefficient, law, Atom, and raw equality; additive and
  internal base sections are independently generated before comparison;
  correction primitives contain no global section
- supplied-field audit: the pairwise finite expansion is an explicit
  conditional field and is not counted as lawful-reading discharge; no
  quotient section, compatible family, glue, local q1 lift, global lift,
  class-zero proof, comparison, inverse, or effectivity certificate is
  accepted as input
- four independent review lanes: No major findings
- target classification: explicit-atlas algebraic effectivity and the
  correction-primitive representation are discharged; primitive
  lawful-reading provenance remains

### Next obligation

Construct the explicit atlas from concrete semantic/law input on one finite
Boolean-circle AAT site.  Keep the site, cover, observable restriction functor,
and ambient ring fixed while changing only the law witness ideal.  The finite
constructor must discharge every overlap expansion by computation, then
produce an idempotent-law instance with zero conormal `H¹` and a square-zero-law
instance with an explicit nonzero period class in the current canonical tuple
complex.

## Cycle 17 — finite Boolean-circle AAT site and actual cover

- decision: approve
- result type: target-proof-checkpoint
- Lean file:
  `research/lean/ResearchLean/AG/QualitySurface/LawGeneratedBooleanCircleSite.lean`
- checkpoint spine:
  - `ContextIndex`
  - `contextPreorder`
  - `contextOverlap`
  - `coverageRequirements`
  - `site`
  - `cover`
  - `cover_patch_injective`
  - `cover_patch_ne_base`
  - `geometry`
  - `canonicalTupleGeometry`

### Checkpoint delta

The finite witness now has one coefficient-free AAT site.  Its selected
contexts are subsets of `Fin 3`, ordered by reverse inclusion, and overlap is
proved to be union.  Contexts outside this selected family retain identity
morphisms only.  Three distinct required Atom supports generate an actual
three-patch admissible cover by singleton contexts.

The finite-poset geometry uses that same site and cover.  Every ordered nerve
tuple is assigned the union of its chart indices, and the overlap-to-patch
morphisms are derived from singleton membership in that union.  The canonical
tuple geometry is therefore generated from the proved overlap operation rather
than from a separate combinatorial complex.  Patch injectivity and patch/base
inequality establish that the actual cover is nontrivial.

No ring, algebraic ring ideal, coefficient sheaf, cohomology class, or
vanishing statement is stored in the site data.  The coefficient-free cover
adequacy structure uses only the universal `True` witness predicate and its
trivial preservation proof; these fields do not construct or preserve either
later law-generated algebraic ideal profile.

### Premise delta

- discharged: a finite Boolean-lattice context preorder; union overlap with its
  universal property; an actual three-patch admissible AAT cover; distinct and
  non-base patches; and a canonical ordered-tuple geometry generated from that
  same cover.
- remaining: one fixed ambient finite ring and restriction functor; the two
  law-generated ideal profiles; raw conormal sheaves and sheafification
  comparison; the explicit zero/nonzero `H¹` pair; the primitive lawful-reading
  atlas constructor; semantic specialization; torsor/H0 transport; the final
  package theorem; and the global `H¹`-vanishing corollary.

### Audits

- focused site elaboration: pass (36 declarations)
- module-wide standard-axiom assertion: pass
- proof-use: cover admissibility uses three distinct required Atom supports;
  overlap universality uses reverse-inclusion/union; canonical tuple overlaps
  use the tuple image in the same Boolean lattice
- provenance: the site, cover, and overlap are independent of all later
  coefficient and ideal choices
- supplied-field audit: the only witness-ideal adequacy fields are the
  universal `True` predicate and trivial preservation proof; no algebraic ring
  ideal, coefficient sheaf, cocycle, class, or vanishing proof is accepted as
  input
- four independent review lanes after the report correction: No major findings
- target classification: the actual finite site/cover geometry is discharged;
  D2 is not yet discharged

### Next obligation

Define one fixed finite ambient ring presheaf and one restriction operation on
this site.  Instantiate two cores that differ only in their required-law
violation witness, prove the resulting idempotent and square-zero ideal
profiles, and connect their raw conormal presheaves to the current
sheafification construction.

## Cycle 18 — fixed finite ambient ring and two law cores

- decision: approve
- result type: target-proof-checkpoint
- Lean file:
  `research/lean/ResearchLean/AG/QualitySurface/LawGeneratedBooleanCircleLawCore.lean`
- checkpoint spine:
  - `AmbientRing`
  - `killEps`
  - `ambientRestrict`
  - `ambientRestrict_comp`
  - `generatorWitness`
  - `core`
  - `idempotentCore`
  - `squareZeroCore`
  - `idempotent_obstructionIdeal_sq`
  - `squareZero_obstructionIdeal_sq`
  - `idempotent_conormal_eq_zero`
  - `squareZeroConormalGenerator_ne_zero`

### Checkpoint delta

Both law instances now use one fixed finite ring
`ZMod 2 × TrivSqZeroExt (ZMod 2) (ZMod 2)` and one restriction operation.
The restriction is identity except on a nonidentity arrow whose source is the
selected cardinality-three context; there it applies `killEps`.  Identity and
composition laws are proved from the Boolean context order, and explicit
lemmas expose the identity and `killEps` cases.

The shared `core g` constructor takes only a law generator.  Its site,
observable ring, restriction maps, support Atom, and required law index do not
depend on `g`.  The two instances are `core e` and `core j`, where `e² = e`,
`j² = 0`, `j ≠ 0`, `killEps e = e`, and `killEps j = 0`.  Thus only the
violation-witness generator changes.

For the idempotent core, the generated obstruction ideal is `span {e}` and
its square is itself, so every raw conormal value is zero.  For the square-zero
core, the obstruction ideal has square zero.  It is `span {j}` below
cardinality three and zero at cardinality three.  The displayed raw conormal
generator below cardinality three is proved nonzero; the cardinality-three raw
conormal is proved zero.

### Premise delta

- discharged: fixed finite ambient ring; fixed functorial restriction;
  generator restriction compatibility; one common law-core constructor;
  same-site/same-ring/same-restriction provenance; idempotent and square-zero
  generated ideal profiles; raw idempotent conormal zero; raw square-zero
  conormal nonzero below cardinality three and zero at cardinality three.
- remaining: raw conormal presheaf sheafness and its sheafification comparison;
  canonical tuple overlap/profile formulas; explicit cocycle and period
  non-coboundary proof; the resulting sheafified zero/nonzero `H¹` pair;
  primitive lawful-reading atlas construction; semantic specialization;
  torsor/H0 transport; final package; and the global `H¹`-vanishing corollary.

### Audits

- focused law-core elaboration: pass (54 declarations)
- module-wide standard-axiom assertion: pass
- proof-use: restriction composition uses reverse-inclusion monotonicity and
  `killEps` idempotence; obstruction ideals are recovered from the generated
  required-law witness ideal; conormal claims use the computed ideal squares
- provenance: both cores are applications of the same `core g` constructor;
  no separate observable or restriction data is supplied to either instance
- supplied-field audit: no ideal equality, ideal-power result, conormal value,
  cocycle, class, or vanishing proof is accepted as a field
- four independent review lanes: No major findings
- target classification: the fixed-ring law-core and raw objectwise conormal
  profiles are discharged; the D2 sheafified `H¹` pair is not yet discharged

### Next obligation

Prove that the square-zero raw conormal presheaf is a sheaf on this generated
site and compare it canonically with its sheafification.  Compute its current
canonical tuple coefficient maps, construct the three-edge cocycle, and prove
non-coboundary by its nonzero period.  Transport that class through the
sheafification comparison, while the idempotent raw conormal zero result gives
the corresponding zero coefficient after the same comparison.
