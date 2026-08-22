import ResearchLean.AG.DoctrineFiberProduct.Schema
import ResearchLean.AG.DoctrineFiberProduct.SchemaWitnesses
import ResearchLean.AG.DoctrineFiberProduct.BCSchema
import ResearchLean.AG.DoctrineFiberProduct.BCSchemaWitnesses
import ResearchLean.AG.DoctrineFiberProduct.BCPastingSchema
import ResearchLean.AG.DoctrineFiberProduct.BCPastingSchemaWitnesses
import ResearchLean.AG.DoctrineFiberProduct.BCRelativeSchema
import ResearchLean.AG.DoctrineFiberProduct.BCRelativeSchemaWitnesses
import ResearchLean.AG.DoctrineFiberProduct.CartesianBranch
import ResearchLean.AG.DoctrineFiberProduct.CartesianRegimeSchema
import ResearchLean.AG.DoctrineFiberProduct.CartesianRegimeSchemaWitnesses
import ResearchLean.AG.DoctrineFiberProduct.CartesianTransport
import ResearchLean.AG.DoctrineFiberProduct.CartesianTarget
import ResearchLean.AG.DoctrineFiberProduct.CartesianTargetWitnesses
import ResearchLean.AG.DoctrineFiberProduct.FiniteCodeULift
import ResearchLean.AG.DoctrineFiberProduct.FiniteCodeULiftWitnesses
import ResearchLean.AG.DoctrineFiberProduct.FinitePackageULift
import ResearchLean.AG.DoctrineFiberProduct.FinitePackageULiftWitnesses
import ResearchLean.AG.DoctrineFiberProduct.FiniteEquationULift
import ResearchLean.AG.DoctrineFiberProduct.FiniteCorePackageULift
import ResearchLean.AG.DoctrineFiberProduct.FiniteEquationULiftWitnesses
import ResearchLean.AG.DoctrineFiberProduct.FiniteModelLiftComparison
import ResearchLean.AG.DoctrineFiberProduct.FiniteGeneratedLiftNaturality
import ResearchLean.AG.DoctrineFiberProduct.FiniteGeneratedFactorComparison
import ResearchLean.AG.DoctrineFiberProduct.FiniteGeneratedFactorFieldDescent
import ResearchLean.AG.DoctrineFiberProduct.FiniteGeneratedFactorFieldDescentWitnesses
import ResearchLean.AG.DoctrineFiberProduct.FiniteGeneratedObjectImageDescent
import ResearchLean.AG.DoctrineFiberProduct.FiniteGeneratedContextImageDescent
import ResearchLean.AG.DoctrineFiberProduct.FiniteGeneratedObjectContextImageWitnesses
import ResearchLean.AG.DoctrineFiberProduct.FiniteGeneratedContextImageFunctor
import ResearchLean.AG.DoctrineFiberProduct.FiniteGeneratedReflectedContextEquivalence
import ResearchLean.AG.DoctrineFiberProduct.FiniteGeneratedReflectedContextEquivalenceWitnesses
import ResearchLean.AG.DoctrineFiberProduct.FiniteGeneratedEquationIndexDescent
import ResearchLean.AG.DoctrineFiberProduct.FiniteGeneratedObservableEquivalenceDescent
import ResearchLean.AG.DoctrineFiberProduct.FiniteGeneratedEquationEquivalenceWitnesses
import ResearchLean.AG.DoctrineFiberProduct.FiniteGeneratedEquationRoleDescent
import ResearchLean.AG.DoctrineFiberProduct.FiniteGeneratedObservableNaturalityDescent
import ResearchLean.AG.DoctrineFiberProduct.FiniteGeneratedEquationGeneratorDescent
import ResearchLean.AG.DoctrineFiberProduct.FiniteGeneratedEquationTransportDescent
import ResearchLean.AG.DoctrineFiberProduct.FiniteGeneratedEquationTransportWitnesses
import ResearchLean.AG.DoctrineFiberProduct.FiniteGeneratedOperationMapDescent
import ResearchLean.AG.DoctrineFiberProduct.FiniteGeneratedInvariantSignatureMapDescent
import ResearchLean.AG.DoctrineFiberProduct.FiniteGeneratedUpperComputationalWitnesses
import ResearchLean.AG.DoctrineFiberProduct.FiniteGeneratedUpperStructuralLawDescent
import ResearchLean.AG.DoctrineFiberProduct.FiniteGeneratedDetectorLawDescent
import ResearchLean.AG.DoctrineFiberProduct.FiniteGeneratedOperationNaturalityDescent
import ResearchLean.AG.DoctrineFiberProduct.FiniteGeneratedInvariantSignatureLawDescent
import ResearchLean.AG.DoctrineFiberProduct.FiniteGeneratedUpperAssembly
import ResearchLean.AG.DoctrineFiberProduct.FiniteGeneratedUpperAssemblyWitnesses
import ResearchLean.AG.DoctrineFiberProduct.FiniteGeneratedUpperCompositionEquationDescent
import ResearchLean.AG.DoctrineFiberProduct.FiniteGeneratedEquationTransportCompositionDescent
import ResearchLean.AG.DoctrineFiberProduct.FiniteGeneratedContextEquivalenceCompositionDescent
import ResearchLean.AG.DoctrineFiberProduct.FiniteGeneratedObservableCompositionDescent
import ResearchLean.AG.DoctrineFiberProduct.FiniteGeneratedEquationTransportWholeCompositionDescent
import ResearchLean.AG.DoctrineFiberProduct.FiniteGeneratedUpperCompositionOperationSignatureDescent
import ResearchLean.AG.DoctrineFiberProduct.FiniteGeneratedPackageTotalHomAssembly
import ResearchLean.AG.DoctrineFiberProduct.FiniteGeneratedPackageTotalHomTriangle
import ResearchLean.AG.DoctrineFiberProduct.FiniteGeneratedPackageTotalHomTriangleWitnesses
import ResearchLean.AG.DoctrineFiberProduct.FiniteGeneratedReflectedUniversalProperty
import ResearchLean.AG.DoctrineFiberProduct.FiniteGeneratedReflectedUniversalPropertyWitnesses
import ResearchLean.AG.DoctrineFiberProduct.FiniteModelRealizationULift
import ResearchLean.AG.DoctrineFiberProduct.FiniteModelRealizationULiftWitnesses
import ResearchLean.AG.DoctrineFiberProduct.FiniteModelStrongLiftIsoTransport
import ResearchLean.AG.DoctrineFiberProduct.FiniteModelLift

/-!
# Doctrine fiber-product schema

Umbrella import for the G-110 finite presentation schema, its semantic decoders,
finite pullback closure, fixed Cart/BC condition languages, and finite witnesses.
It also exposes the F0b2 horizontal/vertical pasting constructors and the
one-field authored 2-cell table, together with the F0b2b discrete authored
support and relative-comparison producer signatures.
The F0c1 layer additionally fixes the carrier-global left-lift proposition,
qualified per-carrier right-regime and nondegenerate family interfaces, finite
counterexample endpoint types, and the branch-independent per-carrier regime
surface.  The F0c2a1 layer adds canonical cross-universe reindexing of the
complete finite cartesian code, decoder components, and Boolean evaluator.
The next two layers prove that canonical package transport is strongly
cartesian by a generated suffix factorization, inverse-reindex an arbitrary
target package without inverting the lower source map, and construct the
carrier-global left branch.  The finite witness layer additionally constructs
a branch-independent portfolio of actual lifts over pairwise nonisomorphic,
noninvertible arrows with nonisomorphic endpoints.  The branch layer fixes a
uniform conditional theorem-output surface, selects the single carrier-global
left artifact, and exports its sole per-carrier regime producer.  The current
finite-package foundation now rebases families, configurations, configuration
homs, finite-model reading components, and semantic configurations with exact
round-trip and graph laws.  The equation layer additionally rebases finite
circuit syntax, reconstructs the NoCycle equation and sound detector on every
lifted object, and assembles the complete lifted `CoreReading` and generated
`AATCorePackage`, with concrete cyclic and acyclic witnesses.  At that
foundation stage, complete cross-carrier hom retraction and ambient strong-lift
reflection for the separate `FiniteModelLift` obligation remained before K0.
The comparison layer records the
canonical vertical domain isomorphism between two strong lifts inside one
carrier.  The generated-lift naturality layer then consumes its inverse
triangle and proves endpoint, lower-map, upper-component, equation-semantic,
operation, invariant, and signature observations for the canonical finite
low/high package homs.  It also proves selected-target generated identity and
two-arrow composition coherence up to canonical vertical domain isomorphism,
fires both layers on a noninvertible concrete chain, and fixes the exact
component plus ambient-factorization output types for the next reflection
step.  These are observational and coherence theorem-outputs, not a
cross-carrier package functor or the still unproved ambient strong-lift
reflection.  The generated-factor comparison layer now applies the supplied
high universal property to every generated prefix, canonically normalizes its
factor, and identifies it with the named high inverse-package factor.  It also
constructs the corresponding low inverse-upper factor and records explicitly
that this low projection is independent of the supplied high lift.  Thus it is
a fail-closed proof-use checkpoint, not an ambient cartesianness reflection.
The field-descent layer then reads the actual normalized high factor directly
to reflect its exact-doctrine base, upper Atom map, object configuration, and
configuration map, and fires those fields on the concrete noninvertible
two-source chain.  The generated-image layer now also reflects both opaque
architecture-object values from that actual high image, lifts and reflects all
four context carriers and all three raw context-morphism maps on canonical
images, and proves restriction plus context-category full/faithful laws with
nontrivial finite witnesses.  The following layer constructs the generated-
domain Full/Faithful image functors and reflects the actual normalized high
context equivalence, including its forward and inverse objects and maps and all
four unit/counit components, with a concrete distinct-context restriction
witness.  The equation-equivalence layer then completes the generated-domain
equation-index image equivalences, reflects the actual high index equivalence,
constructs the equation-observable ring images, and reflects the actual high
observable equivalence at every canonical-image context.  Its concrete
noninvertible fixture fires both directions, while the proof-used conjugation
primitives are separately sensitive on finite swaps.  The complete equation-
transport layer now reflects the actual normalized high factor's role,
observable-naturality, violation-coordinate, and equation-residual laws and
assembles all seven fields of the generated low
`EquationSystemExactTransport`.  Its noninvertible fixture fires every field,
including distinct-context naturality, a nonzero violation coordinate, and
cyclic and acyclic residual values.  The next computational checkpoint reflects
the actual normalized high operation map, invariant-index map, signature-axis
map, and dependent coordinate equivalence through generated low/high image
equivalences, with all-value image and round-trip laws.  The following law
layer directly consumes all nine remaining structural, detector, operation,
invariant, and signature laws of that actual high factor and reflects them
through the generated images.  These laws and the earlier data producers are
then assembled into the exact eighteen-field generated low
`SignedExactCoreReadingHom`.  A single noninvertible selective-two fixture fires
every assembled projection, including distinct family and object controls,
accepted and rejected detector data, a nonidentity collapse operation, the
complete equation transport, and coordinate value `3`; rigid singleton and
constant laws are recorded without a sensitivity claim.  The next layer pairs
that upper with the reflected lower map to construct the generated low
`PackageTotalHom`, descends the supplied high factorization through all seven
computational upper fields to prove its exact composition triangle, and uses
it to factor every ambient low competitor with the required lift and
factorization laws.  The reflected universal-property layer then proves every
ambient candidate unique by inverse-package cancellation against that actual-
high-derived factor, assembles the exact generated component and universal-
property packets, derives Mathlib strong cartesianness without reusing the
existing low certificate, and returns the fixed reflected strong lift.  A
single noninvertible selective-two fixture fires the whole triangle, a concrete
ambient factor, arbitrary-candidate uniqueness, and the reflected lift.
At this stage the realization boundary needed by `FiniteModelLift` and the later
K0 obligation still remains.
The realization-ULift layer now also rebases every finite presentation to a
genuine high-universe `RealizableHom` and constructs the canonical
arrow-category isomorphism from the directly lifted low decoder arrow to that
rebased realization.  Its selective-two support-prefix witness remains
noninvertible in every universe and connects back to the reviewed generated
core arrow.  The completion layer transports every supplied strong lift on the
internally generated rebased endpoint back to the direct high semantic lift,
composes it with the canonical high completion tail, reflects that completed
lift through the generated universal property, and cancels the canonical low
tail.  It thereby constructs the original realized-prefix strong lift and the
one-way `FiniteModelLift` nonexistence transport for every realized input and
completion tail.  The selective-two fixture fires the data producer on an
actual high lift over low and high noninvertible bases; it does not assert an
inhabited right-branch no-lift premise.  K0 and the later target obligations
remain open.
-/
