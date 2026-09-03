# G-116 — Split Configuration Descent and Idempotent Beck–Chevalley Exactness

This report records proof-obligation deltas for the fixed active GOAL
`G-116-aat-idempotent-exchange-structure`.

## Cycle 1 — F0 / K1(b) package normalization idempotence

```yaml
ledger_type: target_cycle_result
goal: G-116-aat-idempotent-exchange-structure
cycle: 1
goal_blob_sha: 9b3a1157889b33d5b2ce279365f3bec9f6e3bed6
base_oid: bd0b824c8effbfdfe67cf85ae158622161d1601f
tracking_issue: 4345
report_path: research/reports/G-116-aat-idempotent-exchange-structure.md
selection:
  proof_state_ref: Issue #4345 active / F0 typing pending
  proof_dag_predecessors: [canonicalObjectNormalization_idempotent, canonicalObjectNormalizationEquationTransport, canonicalObjectNormalizationUpper, canonicalObjectNormalizationTotal]
  proof_obligation: Prove package idempotence (b), including named heterogeneous extensionality and the refl-trans equation-transport equality, through PackageTotalHom.ext and SignedExactCoreReadingHom.ext.
  selection_reason: Package idempotence is the stated unproved core and is consumed by the component projector and Karoubi image obligations.
  expected_result_type: proof-obligation-discharged
  lean_targets: [ResearchLean/AG/DoctrineFiberProduct/IdempotentExchangeNormalization.lean]
  risks: [object-map idempotence substituted for package equality, EquationSystemExactTransport HEq left unproved, operation cast composition hidden in proof irrelevance, nonstandard axioms]
  unchecked: [clauses (a), (c1), (c2), (d), (e1), (e2), (f), (g), (g2), (h)]
result:
  proposed_result_type: proof-obligation-discharged
  proof_obligation_delta: Clause (b) is proved at the total-category morphism level; the object, equation-transport, operation, invariant, axis, coordinate, upper, and lower data are included in the equality.
  completion_candidate: no
  lean_artifacts: [equationSystemExactTransport_hext, canonicalObjectNormalizationEquationTransport_comp_heq, cast_cast_heq_first, canonicalObjectNormalizationUpper_comp, canonicalObjectNormalizationTotal_comp]
  evidence: [focused elaboration exit 0, standard-axiom audit for all five declarations]
  claim_mapping:
    theorem_names: [canonicalObjectNormalizationEquationTransport_comp_heq, canonicalObjectNormalizationUpper_comp, canonicalObjectNormalizationTotal_comp]
    source_labels: [target theorem clause (b), target proof strategy F0 and K1]
    conjuncts: [heterogeneous equation-transport equality, signed-reading hom idempotence, package total hom idempotence]
    undischarged_assumptions: []
    acceptance_point: canonicalObjectNormalizationTotal_comp has the fixed universal quantification over P and admissible and concludes N_P composed with itself equals N_P without accepting idempotence as an argument or field.
    port_status: not-applicable
audits:
  premise_delta:
    discharged: [package idempotence (b) from canonicalObjectNormalization_idempotent and the definitions of the complete transport]
    remaining: [clauses (a), (c1), (c2), (d), (e1), (e2), (f), (g), (g2), (h)]
  certificate_provenance:
    discharged: [admissible supplies only the fixed reading laws used to construct N_P; idempotence is theorem-generated]
    unresolved: [cell projector provenance, fixture witness packet]
  proof_use:
    used: [canonicalObjectNormalization_idempotent, PackageTotalHom.ext, SignedExactCoreReadingHom.ext, canonicalObjectNormalizationEquationTransport]
    unused: [G-110 and G-113 reviewed artifacts]
  structure_field_escape: none-found
  route_integrity: pass
  target_fitting: none-found
  vacuity: none-found
  one_way_as_equivalence: none-found
  goal_or_report_reinterpretation: none-found
  validation_refs: [lake env lean ResearchLean/AG/DoctrineFiberProduct/IdempotentExchangeNormalization.lean — exit 0; axiom audit 5 declarations standard axioms only]
  blocking_findings: []
  next_obligation: K1(a) construct configuration descent at Type level, including the fixed-point equivalence, universal factorization, and quotient equivalence.
```

The three objects fixed by F0 remain distinct.  This cycle proves idempotence
of the package endomorphism `N_P`.  It does not identify `N_P` with a cell
component `E_c`, and it does not count the already known idempotence of the
object function `n_P` as the package-level result.

## Cycle 2 — K1(a) configuration descent

```yaml
ledger_type: target_cycle_result
goal: G-116-aat-idempotent-exchange-structure
cycle: 2
goal_blob_sha: 9b3a1157889b33d5b2ce279365f3bec9f6e3bed6
base_oid: b0524ca3f9a286398d880f8233b0fc7023bfd5e2
tracking_issue: 4345
report_path: research/reports/G-116-aat-idempotent-exchange-structure.md
selection:
  proof_state_ref: Issue #4345 and Cycle 1 merge b0524ca3f9a286398d880f8233b0fc7023bfd5e2
  proof_dag_predecessors: [canonicalObjectNormalization_configuration, canonicalObjectNormalization_selected, canonicalObjectNormalization_idempotent]
  proof_obligation: Construct the three Type-level configuration descent artifacts in clause (a): fixed-point equivalence, universal factorization, and configuration quotient equivalence.
  selection_reason: Clause (a) is the remaining K1 obligation and needs only the package-selected section and configuration projection, so it directly closes K1 without consuming later cell data.
  expected_result_type: proof-obligation-discharged
  lean_targets: [ResearchLean/AG/DoctrineFiberProduct/ConfigurationDescent.lean]
  risks: [fixed point supplied as an argument, factorization without uniqueness, quotient relation depending on P, dependent reading descent imported from the frontier, category-level quotient substituted for the Type quotient]
  unchecked: [clauses (c1), (c2), (d), (e1), (e2), (f), (g), (g2), (h)]
result:
  proposed_result_type: proof-obligation-discharged
  proof_obligation_delta: Clause (a) is proved at Type level by three constructions generated from the package object reading and the configuration projection.
  completion_candidate: no
  lean_artifacts: [CanonicalNormalizationFixed, canonicalNormalizationFixedEquiv, canonicalObjectNormalization_factorization_iff, architectureObjectConfigurationSetoid, architectureObjectConfigurationQuotientEquiv]
  evidence: [focused elaboration exit 0, standard-axiom audit for all five declarations]
  claim_mapping:
    theorem_names: [canonicalNormalizationFixedEquiv, canonicalObjectNormalization_factorization_iff, architectureObjectConfigurationQuotientEquiv]
    source_labels: [target theorem clause (a), target proof strategy K1]
    conjuncts: [Fix(n_P) equivalent to AtomConfiguration, normalization-invariant functions factor uniquely through configuration, quotient by equal configuration equivalent to AtomConfiguration]
    undischarged_assumptions: []
    acceptance_point: All three equivalences use the section selected by input package P and prove both inverse directions or uniqueness; no fixed point, factor, quotient representative, or dependent reading descent is accepted as a premise.
    port_status: not-applicable
audits:
  premise_delta:
    discharged: [configuration descent (a) from ObjectReading.configuration_eq and canonical normalization API]
    remaining: [clauses (c1), (c2), (d), (e1), (e2), (f), (g), (g2), (h)]
  certificate_provenance:
    discharged: [fixed points and quotient representatives are constructed canonically from P.reading.objectReading.object]
    unresolved: [cell projector provenance, fixture witness packet]
  proof_use:
    used: [canonicalObjectNormalization_selected, canonicalObjectNormalization_configuration, ObjectReading.configuration_eq, Quotient.sound]
    unused: [package idempotence (b), G-110 and G-113 reviewed artifacts]
  structure_field_escape: none-found
  route_integrity: pass
  target_fitting: none-found
  vacuity: none-found
  one_way_as_equivalence: none-found
  goal_or_report_reinterpretation: none-found
  validation_refs: [lake env lean ResearchLean/AG/DoctrineFiberProduct/ConfigurationDescent.lean — exit 0; axiom audit 5 declarations standard axioms only]
  blocking_findings: []
  next_obligation: K2(c1) prove idempotence and identity atom equivalence for every selected cell component E_c, preserving the selector gates and provenance route.
```

The fixed-point inverse and both quotient representatives are generated by the
object reading of the input package.  The factorization theorem quantifies over
an arbitrary target type and proves uniqueness by evaluating any competing
factor on the selected object.  No dependent operation or invariant descent,
and no category-level quotient, is included in this result.

## Cycle 3 — K2(c1) cell projector idempotence

```yaml
ledger_type: target_cycle_result
goal: G-116-aat-idempotent-exchange-structure
cycle: 3
goal_blob_sha: 9b3a1157889b33d5b2ce279365f3bec9f6e3bed6
base_oid: 3fa6b8f090c240b5033ce755721d595462e5b1e3
tracking_issue: 4345
report_path: research/reports/G-116-aat-idempotent-exchange-structure.md
selection:
  proof_state_ref: Issue #4345 and Cycle 2 merge 3fa6b8f090c240b5033ce755721d595462e5b1e3
  proof_dag_predecessors: [canonicalObjectNormalizationTotal_comp, authoredDiagnosticObjectCollapseComponentAtCochain_eq_id, authoredDiagnosticObjectCollapseComponentAtCochain_eq_canonical, authoredViaBaseDiagnosticObjectCollapseComponentAtCochain_eq_provenance, authoredDiagnosticObjectCollapseComparisonAtCochain_app, generatedAuthoredDiagnosticObjectCollapseComparison_replacement]
  proof_obligation: Prove clause (c1) for every input, cochain, and cell: E_c composed with itself equals E_c and its upper Atom equivalence is identity.
  selection_reason: The raw selector gates and provenance route already exist; package idempotence can now be transported functorially to the selected cell component.
  expected_result_type: proof-obligation-discharged
  lean_targets: [ResearchLean/AG/DoctrineFiberProduct/IdempotentExchangeCellProjector.lean]
  risks: [proving only the admissible firing branch, assuming a gate certificate, stopping at the raw support component, losing an equality through transport, omitting the Atom-equivalence conclusion]
  unchecked: [clauses (c2), (d), (e1), (e2), (f), (g), (g2), (h)]
result:
  proposed_result_type: proof-obligation-discharged
  proof_obligation_delta: Clause (c1) is proved for the complete selector and its two-stage transported via-base component, including identity of the upper Atom equivalence.
  completion_candidate: no
  lean_artifacts: [authoredSupportCanonicalNormalizationComponent_comp, authoredDiagnosticObjectCollapseComponentAtCochain_comp, authoredViaBaseDiagnosticObjectCollapseComponentAtCochain_comp, authoredViaBaseDiagnosticObjectCollapseComponentAtCochain_atomEquiv]
  evidence: [focused elaboration exit 0, standard-axiom audit for all four declarations]
  claim_mapping:
    theorem_names: [authoredViaBaseDiagnosticObjectCollapseComponentAtCochain_comp, authoredViaBaseDiagnosticObjectCollapseComponentAtCochain_atomEquiv]
    source_labels: [target theorem clause (c1), target proof strategy K2]
    conjuncts: [cell projector idempotence, identity upper Atom equivalence]
    undischarged_assumptions: []
    acceptance_point: The theorems quantify over every authored input, diagnostic cochain, and cell; the selector's three branches are discharged internally and the two functor maps preserve the package-level equality.
    port_status: not-applicable
audits:
  premise_delta:
    discharged: [projector idempotence and identity Atom equivalence (c1)]
    remaining: [clauses (c2), (d), (e1), (e2), (f), (g), (g2), (h)]
  certificate_provenance:
    discharged: [selector gates are decided inside the definition; normalization idempotence is theorem-generated; transport uses Functor.map_comp]
    unresolved: [fixture witness packet]
  proof_use:
    used: [canonicalObjectNormalizationTotal_comp, authoredDiagnosticObjectCollapseComponentAtCochain, authoredDiagnosticObjectCollapseComponentAtCochain_eq_id, authoredDiagnosticObjectCollapseComponentAtCochain_eq_canonical, Functor.map_comp, PackageTotalHom.atomEquiv_eq, CategoryTheory.IsHomLift.fac']
    referenced_existing_identifications: [authoredDiagnosticObjectCollapseComparisonAtCochain_app, authoredViaBaseDiagnosticObjectCollapseComponentAtCochain_eq_provenance, authoredViaBaseDiagnosticObjectCollapseComponentAtCochain_replacement, generatedAuthoredDiagnosticObjectCollapseComparison_replacement]
    unused: [G-110 and G-113 reviewed artifacts]
  structure_field_escape: none-found
  route_integrity: pass
  target_fitting: none-found
  vacuity: none-found
  one_way_as_equivalence: none-found
  goal_or_report_reinterpretation: none-found
  validation_refs: [lake env lean ResearchLean/AG/DoctrineFiberProduct/IdempotentExchangeCellProjector.lean — exit 0; axiom audit 4 declarations standard axioms only]
  blocking_findings: []
  next_obligation: K2(c2) prove naturality of canonical object normalization under arbitrary package total homs.
```

The component theorem covers the vanishing, admissible-firing, and
inadmissible branches of the selector.  The two transport functors preserve
the raw equality by `Functor.map_comp`.  The Atom-equivalence theorem reads the
identity lower map forced by the component's vertical core-fiber type through
the existing `PackageTotalHom.atomEquiv_eq` law.

## Cycle 4 — K2(c2) canonical normalization naturality

```yaml
ledger_type: target_cycle_result
goal: G-116-aat-idempotent-exchange-structure
cycle: 4
goal_blob_sha: 9b3a1157889b33d5b2ce279365f3bec9f6e3bed6
base_oid: 913ea9dc765fa77cc44230b004a866a18ab67465
tracking_issue: 4345
report_path: research/reports/G-116-aat-idempotent-exchange-structure.md
selection:
  proof_state_ref: Issue #4345 and Cycle 3 merge 913ea9dc765fa77cc44230b004a866a18ab67465
  proof_dag_predecessors: [SignedExactCoreReadingHom.object_formation_eq, SignedExactCoreReadingHom.configuration_eq, canonicalObjectNormalization]
  proof_obligation: Prove clause (c2), U(hom) composed with n_P equals n_Q composed with U(hom), for every package total hom.
  selection_reason: Both required equations are primitive laws of every complete exact upper hom, so the fixed object-map equality can be proved without additional hypotheses.
  expected_result_type: proof-obligation-discharged
  lean_targets: [ResearchLean/AG/DoctrineFiberProduct/CanonicalObjectNormalizationNaturality.lean]
  risks: [assuming admissibility, restricting to isomorphisms, reversing the composition equation, proving only a selected fixture, claiming a package-morphism equality]
  unchecked: [clauses (d), (e1), (e2), (f), (g), (g2), (h)]
result:
  proposed_result_type: proof-obligation-discharged
  proof_obligation_delta: Clause (c2) is proved pointwise and as the fixed function equality for arbitrary package total homs.
  completion_candidate: no
  lean_artifacts: [canonicalObjectNormalization_natural_apply, canonicalObjectNormalization_natural]
  evidence: [focused elaboration exit 0, standard-axiom audit for both declarations]
  claim_mapping:
    theorem_names: [canonicalObjectNormalization_natural_apply, canonicalObjectNormalization_natural]
    source_labels: [target theorem clause (c2), target proof strategy K2]
    conjuncts: [pointwise naturality, ArchitectureObject-valued function equality]
    undischarged_assumptions: []
    acceptance_point: The function equality quantifies over arbitrary P, Q, and PackageTotalHom P Q and uses no admissibility, isomorphism, or fixture premise.
    port_status: not-applicable
audits:
  premise_delta:
    discharged: [naturality of canonical object normalization (c2)]
    remaining: [clauses (d), (e1), (e2), (f), (g), (g2), (h)]
  certificate_provenance:
    discharged: [the equality is generated from object_formation_eq and configuration_eq]
    unresolved: [Karoubi image exactness, fixture witness packet]
  proof_use:
    used: [canonicalObjectNormalization, SignedExactCoreReadingHom.object_formation_eq, SignedExactCoreReadingHom.configuration_eq, Function.funext]
    unused: [admissibility, package idempotence, cell projector data, G-110 and G-113 reviewed artifacts]
  structure_field_escape: none-found
  route_integrity: pass
  target_fitting: none-found
  vacuity: none-found
  one_way_as_equivalence: none-found
  goal_or_report_reinterpretation: none-found
  validation_refs: [lake env lean ResearchLean/AG/DoctrineFiberProduct/CanonicalObjectNormalizationNaturality.lean — exit 0; axiom audit 2 declarations standard axioms only]
  blocking_findings: []
  next_obligation: K2(d) construct the fixed Karoubi image isomorphism from package and cell projector idempotence.
```

The pointwise proof unfolds the canonical normalization and rewrites exactly
with the two complete upper-hom laws.  Function extensionality packages that
calculation in the composition orientation fixed by clause (c2).

## Cycle 5 — K2(d) Karoubi image exactness

```yaml
ledger_type: target_cycle_result
goal: G-116-aat-idempotent-exchange-structure
cycle: 5
goal_blob_sha: 9b3a1157889b33d5b2ce279365f3bec9f6e3bed6
base_oid: 733da785fbd2a1a6faa3b45f27206a59d394bba9
tracking_issue: 4345
report_path: research/reports/G-116-aat-idempotent-exchange-structure.md
selection:
  proof_state_ref: Issue #4345 and Cycle 4 merge 733da785fbd2a1a6faa3b45f27206a59d394bba9
  proof_dag_predecessors: [authoredDiagnosticObjectCollapseComparisonAtCochain_app, authoredViaBaseDiagnosticObjectCollapseComponentAtCochain_comp, authoredSupportCanonicalMate_isIso, Mathlib.CategoryTheory.Idempotents.Karoubi]
  proof_obligation: Construct clause (d): beta_c as an isomorphism in the Karoubi envelope from (D_c, beta_c composed with inv alpha_c) to (V_c, E_c).
  selection_reason: Clause (c1) supplies the target idempotent and the component factorization conjugates it to the source idempotent.
  expected_result_type: proof-obligation-discharged
  lean_targets: [ResearchLean/AG/DoctrineFiberProduct/IdempotentExchangeKaroubiImage.lean]
  risks: [ill-typed source projector, proving only an abstract wrapper unrelated to beta_c, supplying a split as input, confusing raw IsIso with Karoubi IsIso, omitting inverse laws]
  unchecked: [clauses (e1), (e2), (f), (g), (g2), (h)]
result:
  proposed_result_type: proof-obligation-discharged
  proof_obligation_delta: Clause (d) is constructed with the literal source and target projectors and beta_c as the underlying forward Karoubi morphism.
  completion_candidate: no
  lean_artifacts: [authoredDiagnosticImageSourceKaroubi, authoredDiagnosticImageTargetKaroubi, authoredDiagnosticObjectCollapseKaroubiIso]
  evidence: [focused elaboration exit 0, standard-axiom audit for all three declarations]
  claim_mapping:
    theorem_names: [authoredDiagnosticObjectCollapseKaroubiIso]
    source_labels: [target theorem clause (d), target proof strategy K2]
    conjuncts: [source projector idempotence, target projector idempotence, Karoubi morphism compatibility, two inverse laws]
    undischarged_assumptions: []
    acceptance_point: The forward underlying morphism is the cochain-indexed authored diagnostic comparison component beta_c and the inverse is constructed as E_c composed with inv alpha_c for arbitrary input, cochain, and cell.
    port_status: not-applicable
audits:
  premise_delta:
    discharged: [Karoubi image exactness (d)]
    remaining: [clauses (e1), (e2), (f), (g), (g2), (h)]
  certificate_provenance:
    discharged: [both projectors and both inverse laws are theorem-generated from beta_c equals alpha_c composed with E_c, E_c idempotence, and the existing IsIso alpha_c instance]
    unresolved: [fixture witness packet]
  proof_use:
    used: [authoredDiagnosticObjectCollapseComparisonAtCochain_app, authoredViaBaseDiagnosticObjectCollapseComponentAtCochain_comp, authoredSupportCanonicalMate_isIso, component IsIso instance chain, IsIso.inv_hom_id_assoc, Karoubi.Hom.ext]
    unused: [a caller-supplied splitting, raw IsIso beta_c]
  structure_field_escape: none-found
  route_integrity: pass
  target_fitting: none-found
  vacuity: none-found
  one_way_as_equivalence: none-found
  goal_or_report_reinterpretation: none-found
  validation_refs: [lake env lean ResearchLean/AG/DoctrineFiberProduct/IdempotentExchangeKaroubiImage.lean — exit 0; axiom audit 3 declarations standard axioms only]
  blocking_findings: []
  next_obligation: K3(e1) construct two distinct architecture objects over every configuration.
```

The Karoubi source uses the literal projector `β_c ≫ inv α_c`, and the target
uses `E_c`.  The constructed isomorphism has underlying forward map `β_c` and
inverse `E_c ≫ inv α_c`; its compatibility and inverse laws use the fixed
component equation and cell-projector idempotence.

## Cycle 6 — K3(e1) distinct objects over every configuration

```yaml
ledger_type: target_cycle_result
goal: G-116-aat-idempotent-exchange-structure
cycle: 6
goal_blob_sha: 9b3a1157889b33d5b2ce279365f3bec9f6e3bed6
base_oid: d989ed401df317e451921912c295b3dc8f91b453
tracking_issue: 4345
report_path: research/reports/G-116-aat-idempotent-exchange-structure.md
selection:
  proof_state_ref: Issue #4345 and Cycle 5 merge d989ed401df317e451921912c295b3dc8f91b453
  proof_dag_predecessors: [ArchitectureObject, ULift, Equiv.cast, Fintype.card_congr]
  proof_obligation: Prove clause (e1) for every AtomCarrier U and every AtomConfiguration U by constructing two distinct ArchitectureObjects with that configuration.
  selection_reason: The general same-configuration witness is the first K3 obligation and supplies the witness that clause (e2) must consume rather than accept as a premise.
  expected_result_type: proof-obligation-discharged
  lean_targets: [ResearchLean/AG/DoctrineFiberProduct/DistinctArchitectureObjects.lean]
  risks: [proving only the finite fixture, fixing the carrier universe, assuming an existing object, changing only a value inside the same decoration type, accepting distinctness as a premise]
  unchecked: [clauses (e2), (f), (g), (g2), (h)]
result:
  proposed_result_type: proof-obligation-discharged
  proof_obligation_delta: Clause (e1) is proved uniformly by constructing unit- and Boolean-decorated architecture objects over the supplied configuration and deriving their inequality from the cardinalities of their StructureMaps types.
  completion_candidate: no
  lean_artifacts: [unitDecoratedArchitectureObject, boolDecoratedArchitectureObject, unitDecoratedArchitectureObject_ne_boolDecoratedArchitectureObject, exists_distinct_architectureObjects_over_configuration]
  evidence: [focused elaboration exit 0, targeted module build exit 0, standard-axiom audit for all four declarations]
  claim_mapping:
    theorem_names: [exists_distinct_architectureObjects_over_configuration]
    source_labels: [target theorem clause (e1), target proof strategy K3]
    conjuncts: [two ArchitectureObjects, object inequality, first configuration equality, second configuration equality]
    undischarged_assumptions: []
    acceptance_point: The theorem quantifies over an arbitrary universe-polymorphic carrier and supplied configuration; both witnesses are constructed internally and distinctness is proved rather than assumed.
    port_status: not-applicable
audits:
  premise_delta:
    discharged: [distinct objects lemma (e1)]
    remaining: [clauses (e2), (f), (g), (g2), (h)]
  certificate_provenance:
    discharged: [the witnesses use explicit ULift PUnit and ULift Bool decorations and their inequality follows from Fintype.card]
    unresolved: [internal split no-go, fixture witness packet]
  proof_use:
    used: [ArchitectureObject.StructureMaps, congrArg, Equiv.cast, Fintype.card_congr]
    unused: [admissibility, package idempotence, cell projector data]
  structure_field_escape: none-found
  route_integrity: pass
  target_fitting: none-found
  vacuity: none-found
  one_way_as_equivalence: none-found
  goal_or_report_reinterpretation: none-found
  validation_refs: [lake env lean ResearchLean/AG/DoctrineFiberProduct/DistinctArchitectureObjects.lean — exit 0; lake build ResearchLean.AG.DoctrineFiberProduct.DistinctArchitectureObjects — exit 0; axiom audit 4 declarations standard axioms only]
  blocking_findings: []
  next_obligation: K3(e2) prove that canonical package normalization has no internal split in the total category, using the general clause (e1) witness.
```

The construction changes only the decoration type while retaining the supplied
configuration literally.  Universe-polymorphism is preserved by lifting both
finite decoration types into the carrier universe.  The result supplies a
theorem-generated witness for clause (e2); no finite carrier or package data is
assumed.

## Cycle 7 — K3(e2) internal normalization split no-go

```yaml
ledger_type: target_cycle_result
goal: G-116-aat-idempotent-exchange-structure
cycle: 7
goal_blob_sha: 9b3a1157889b33d5b2ce279365f3bec9f6e3bed6
base_oid: bbfddc1f390883453bd4cfa95c9d204db8277ba2
tracking_issue: 4345
report_path: research/reports/G-116-aat-idempotent-exchange-structure.md
selection:
  proof_state_ref: Issue #4345 and Cycle 6 merge bbfddc1f390883453bd4cfa95c9d204db8277ba2
  proof_dag_predecessors: [canonicalObjectNormalization_natural_apply, exists_distinct_architectureObjects_over_configuration, PackageTotalHom.comp, PackageTotalHom.id, canonicalObjectNormalizationTotal]
  proof_obligation: Prove clause (e2) for arbitrary P Q adm r i in the package total category: not both i composed with r equals identity Q and r composed with i equals N_P.
  selection_reason: Clause (e1) now supplies the required same-configuration witness uniformly, while clause (c2) transports normalization across the proposed splitting maps.
  expected_result_type: proof-obligation-discharged
  lean_targets: [ResearchLean/AG/DoctrineFiberProduct/InternalNormalizationSplitNoGo.lean]
  risks: [accepting the distinct witness as a premise, restricting to CoreFiber or a fixture, proving only non-IsIso, reversing categorical composition, failing to use naturality, assuming normalization nonidentity]
  unchecked: [clauses (f), (g), (g2), (h)]
result:
  proposed_result_type: proof-obligation-discharged
  proof_obligation_delta: Clause (e2) is proved in the total category by showing any proposed split makes n_Q the identity, then contradicting the theorem-generated distinct same-configuration objects of Q.
  completion_candidate: no
  lean_artifacts: [packageTotalHom_objectMap_comp_apply, packageTotalHom_objectMap_id_apply, canonicalObjectNormalizationTotal_objectMap_apply, canonicalObjectNormalizationTotal_not_internal_split]
  evidence: [focused elaboration exit 0, standard-axiom audit for all five module declarations]
  claim_mapping:
    theorem_names: [canonicalObjectNormalizationTotal_not_internal_split]
    source_labels: [target theorem clause (e2), target proof strategy K3]
    conjuncts: [arbitrary total-category P and Q, admissibility of P, arbitrary r and i, retraction equality negated jointly with normalization equality]
    undischarged_assumptions: []
    acceptance_point: The theorem has exactly the fixed universal split-no-go signature; the same-configuration witness is constructed from clause (e1), and neither split impossibility nor normalization nonidentity is supplied as a premise.
    port_status: not-applicable
audits:
  premise_delta:
    discharged: [internal split no-go (e2)]
    remaining: [clauses (f), (g), (g2), (h)]
  certificate_provenance:
    discharged: [the two proposed split equalities are contradiction hypotheses; injectivity of i and identity of n_Q are derived; the final two objects come from clause (e1)]
    unresolved: [observable exactness, raw failure classification, transport identity-reflection classification, fixture conjunction packet]
  proof_use:
    used: [PackageTotalHom.comp, PackageTotalHom.id, canonicalObjectNormalizationTotal, canonicalObjectNormalization_natural_apply, exists_distinct_architectureObjects_over_configuration, canonicalObjectNormalization]
    unused: [finite-axis-fold witness, IsIso API, Karoubi image exactness]
  structure_field_escape: none-found
  route_integrity: pass
  target_fitting: none-found
  vacuity: none-found
  one_way_as_equivalence: none-found
  goal_or_report_reinterpretation: none-found
  validation_refs: [lake env lean ResearchLean/AG/DoctrineFiberProduct/InternalNormalizationSplitNoGo.lean — exit 0; axiom audit 5 declarations standard axioms only]
  blocking_findings: []
  next_obligation: K4(f) prove the fixed equation-residual and coordinate observable exactness equalities for every admissible firing cell.
```

The proof extracts the object-map equations of the two categorical equalities.
The retraction makes `i.upper.objectMap` injective.  Naturality of normalization
along `i`, followed by both split equations, makes every object of `Q` fixed by
`n_Q`.  Clause (e1) then provides two distinct objects over one explicitly
constructed configuration; normalization identifies them because it depends
only on configuration, yielding the contradiction.
