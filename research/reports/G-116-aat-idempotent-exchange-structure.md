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
  evidence: [canonical focused checker exit 0, targeted module build exit 0, standard-axiom audit for all four declarations, aggregate import registration]
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
  validation_refs: [research/lean/check_research_modules.sh --focused ResearchLean/AG/DoctrineFiberProduct/DistinctArchitectureObjects.lean — exit 0; lake build ResearchLean.AG.DoctrineFiberProduct.DistinctArchitectureObjects — exit 0; axiom audit 4 declarations standard axioms only; ResearchLean/AG/DoctrineFiberProduct.lean import registration]
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
  evidence: [canonical focused checker exit 0, standard-axiom audit passed, module manifest registration]
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
  validation_refs: [research/lean/check_research_modules.sh --focused ResearchLean/AG/DoctrineFiberProduct/InternalNormalizationSplitNoGo.lean — exit 0; standard-axiom audit passed; research-modules.txt registration]
  blocking_findings: []
  next_obligation: K4(f) prove the fixed equation-residual and coordinate observable exactness equalities for every admissible firing cell.
```

The proof extracts the object-map equations of the two categorical equalities.
The retraction makes `i.upper.objectMap` injective.  Naturality of normalization
along `i`, followed by both split equations, makes every object of `Q` fixed by
`n_Q`.  Clause (e1) then provides two distinct objects over one explicitly
constructed configuration; normalization identifies them because it depends
only on configuration, yielding the contradiction.

## Cycle 8 — K4(f) observable exactness

```yaml
ledger_type: target_cycle_result
goal: G-116-aat-idempotent-exchange-structure
cycle: 8
goal_blob_sha: 9b3a1157889b33d5b2ce279365f3bec9f6e3bed6
base_oid: 1414a4d0b34cfa2df97b1f66cf8b5ef369bbe621
tracking_issue: 4345
report_path: research/reports/G-116-aat-idempotent-exchange-structure.md
selection:
  proof_state_ref: Issue #4345 and Cycle 7 merge 1414a4d0b34cfa2df97b1f66cf8b5ef369bbe621
  proof_dag_predecessors: [CanonicalObjectNormalizationAdmissible.equationResidual_eq, CanonicalObjectNormalizationAdmissible.coordinate_eq, canonicalObjectNormalizationEquationTransport, coreFiberTransportMap_fac, selectedCoreFiberReindexFunctor_map_fac, strongCartesianLiftOfTarget, StrongCartesianLift.domainIso, authoredDiagnosticObjectCollapseComponentAtCochain_eq_canonical, authoredViaBaseDiagnosticObjectCollapseComponentAtCochain_eq_provenance, authoredDiagnosticObjectCollapseComparisonAtCochain_app]
  proof_obligation: Prove clause (f) at every admissible firing cell as literal same-context, same-index, same-Atom equation-residual equality and same-axis coordinate equality on E_c, then derive the corresponding beta_c and alpha_c equalities.
  selection_reason: Clauses (c1) and (e2) are complete; observable exactness is the first remaining K4 obligation and must use the selected readings rather than an arbitrary postcomposition function.
  expected_result_type: proof-obligation-discharged
  lean_targets: [ResearchLean/AG/DoctrineFiberProduct/IdempotentExchangeObservableExactness.lean]
  risks: [leaving equation or signature equivalence components in the conclusion, proving only identity-cell exactness, assuming transport preserves fields literally, accepting an upper inverse as caller data, replacing the selected readings with a generic function]
  unchecked: [clauses (g), (g2), (h)]
result:
  proposed_result_type: proof-obligation-discharged
  proof_obligation_delta: Clause (f) is proved for arbitrary input, cochain, and admissible firing cell. Both E_c equalities are literal on the transported package, and the beta_c versus alpha_c corollaries use their actual upper object maps.
  completion_candidate: no
  lean_artifacts:
    direct_proof_route: [SignedUpperInverseData.symm, coreFiberLift_upperInverseData, selectedCoreFiberCartesianLift_upperInverseData, coreFiberTransportMap_equationResidual, coreFiberTransportMap_coordinate, selectedCoreFiberReindexMap_equationResidual, selectedCoreFiberReindexMap_coordinate, authoredViaBaseDiagnosticObjectCollapseComponentAtCochain_equationResidual, authoredViaBaseDiagnosticObjectCollapseComponentAtCochain_coordinate, authoredDiagnosticObjectCollapseComparisonAtCochain_equationResidual, authoredDiagnosticObjectCollapseComparisonAtCochain_coordinate]
    supporting_api: [coreFiberTransportMap_upper_eq_conjugation, selectedCoreFiberReindexMap_upper_eq_conjugation, equationResidual_eq_of_upper_conjugation, coordinate_eq_of_upper_conjugation, strongCartesianLiftOfTarget_axisMap, signedExactCoreReadingHom_coordinate_eq_of_comp, authoredViaBaseDiagnosticObjectCollapseComponentAtCochain_axisMap]
  evidence: [canonical focused checker exit 0, standard-axiom audit passed, module manifest registration]
  claim_mapping:
    theorem_names: [authoredViaBaseDiagnosticObjectCollapseComponentAtCochain_equationResidual, authoredViaBaseDiagnosticObjectCollapseComponentAtCochain_coordinate, authoredDiagnosticObjectCollapseComparisonAtCochain_equationResidual, authoredDiagnosticObjectCollapseComparisonAtCochain_coordinate]
    source_labels: [target theorem clause (f), target proof strategy K4]
    conjuncts: [E_c same-context same-index same-Atom residual preservation, E_c same-axis coordinate preservation, beta_c and alpha_c residual agreement, beta_c and alpha_c coordinate agreement]
    undischarged_assumptions: []
    acceptance_point: The public theorems quantify over arbitrary input, cochain, cell, architecture object, and the literal transported reading indices. Their only branch premises are the fixed firing inequality and canonical-normalization admissibility.
    port_status: not-applicable
audits:
  premise_delta:
    discharged: [observable exactness (f)]
    remaining: [clauses (g), (g2), (h)]
  certificate_provenance:
    discharged: [canonical core transport inverse is generated by transportAlongUpperInverse; selected reindex inverse is generated by comparison with strongCartesianLiftOfTarget; the raw residual and coordinate equalities come from the supplied admissibility fields; canonicalObjectNormalizationEquationTransport is constructed from the admissibility fields inside canonicalObjectNormalizationTotal; authoredDiagnosticObjectCollapseComponentAtCochain_eq_canonical selects that total morphism; authoredViaBaseDiagnosticObjectCollapseComponentAtCochain_eq_provenance independently identifies the same direct via-base value with the provenance-indexed transport route and is recorded as route evidence rather than a direct dependency of the four new theorem bodies]
    unresolved: [raw failure classification, transport identity-reflection classification, fixture conjunction packet]
  proof_use:
    used: [coreFiberTransportMap_fac, selectedCoreFiberReindexFunctor_map_fac, StrongCartesianLift.domainIso_hom_fac, inverseCorePackageForward_comp_backward, inverseCorePackageBackward_comp_forward, authoredDiagnosticObjectCollapseComponentAtCochain_eq_canonical, CanonicalObjectNormalizationAdmissible.equationResidual_eq, CanonicalObjectNormalizationAdmissible.coordinate_eq, authoredDiagnosticObjectCollapseComparisonAtCochain_app]
    transitive_construction: [canonicalObjectNormalizationEquationTransport]
    route_evidence_not_direct_dependency: [authoredViaBaseDiagnosticObjectCollapseComponentAtCochain_eq_provenance]
    supporting_api_not_used_by_public_theorem_bodies: [strongCartesianLiftOfTarget_axisMap, signedExactCoreReadingHom_coordinate_eq_of_comp, authoredViaBaseDiagnosticObjectCollapseComponentAtCochain_axisMap]
    unused: [a generic q invariant, an assumed transport certificate, an identity-cell case]
  structure_field_escape: none-found
  route_integrity: pass
  target_fitting: none-found
  vacuity: none-found
  one_way_as_equivalence: none-found
  goal_or_report_reinterpretation: none-found
  validation_refs: [research/lean/check_research_modules.sh --focused ResearchLean/AG/DoctrineFiberProduct/IdempotentExchangeObservableExactness.lean — exit 0; standard-axiom audit passed; research-modules.txt registration]
  blocking_findings: []
  next_obligation: K4(g) prove the cellwise IsIso beta_c iff IsIso E_c iff E_c equals identity classification and the named finite-axis-fold comparison non-IsIso theorem.
```

The proof first extracts two-sided upper inverses for the canonical core lift
and the selected cartesian lift.  Their universal factor equations identify
both functorial images as literal conjugates of the raw support normalization.
Residual and coordinate invariance are stable under each conjugation because
the forward exact map is injective on the corresponding observable or
coordinate value and its inverse cancels on architecture objects.  The final
step specializes the raw equalities to the two admissibility fields and then
uses the actual component factorization `beta_c = alpha_c ≫ E_c`.

## Cycle 9 — K4(g) raw failure locus

```yaml
ledger_type: target_cycle_result
goal: G-116-aat-idempotent-exchange-structure
cycle: 9
goal_blob_sha: 9b3a1157889b33d5b2ce279365f3bec9f6e3bed6
base_oid: b492329a3a75edcbb79f2a20fb55c4185c266d41
tracking_issue: 4345
report_path: research/reports/G-116-aat-idempotent-exchange-structure.md
selection:
  proof_state_ref: Issue #4345 and Cycle 8 merge b492329a3a75edcbb79f2a20fb55c4185c266d41
  proof_dag_predecessors: [authoredDiagnosticObjectCollapseComparisonAtCochain_app, authoredViaBaseDiagnosticObjectCollapseComponentAtCochain_comp, isIso_comp_left_iff, NatTrans component IsIso instance, finiteAxisFold_viaBaseGeneratedObjectCollapseComponent_not_isIso, finiteAxisFold_initialRawDefect_second]
  proof_obligation: Prove the cellwise IsIso beta_c iff IsIso E_c iff E_c equals identity chain for arbitrary authored input, cochain, and cell, and prove the assumption-free named non-IsIso theorem for the whole generated finite-axis-fold comparison.
  selection_reason: Clause (f) is complete; clause (g) is the next fixed K4 obligation and isolates raw noninvertibility before the general transport identity-reflection classification.
  expected_result_type: proof-obligation-discharged
  lean_targets: [ResearchLean/AG/DoctrineFiberProduct/IdempotentExchangeRawFailureLocus.lean]
  risks: [confusing the whole natural transformation with one component, parsing an unparenthesized three-way biconditional incorrectly, accepting projector idempotence or fixture firing as caller data, proving only component noninvertibility for the fixture]
  unchecked: [clauses (g2), (h)]
result:
  proposed_result_type: proof-obligation-discharged
  proof_obligation_delta: Clause (g) is proved. The two cellwise biconditionals are named separately and packaged as a conjunction, their outer composite is named, and the fixed fixture's whole generated comparison is proved noninvertible without assumptions.
  completion_candidate: no
  lean_artifacts: [isIso_iff_eq_id_of_comp_self_eq_self, authoredDiagnosticObjectCollapseComparisonAtCochain_app_isIso_iff, authoredViaBaseDiagnosticObjectCollapseComponentAtCochain_isIso_iff_eq_id, authoredDiagnosticObjectCollapseAtCochain_rawFailureLocus, authoredDiagnosticObjectCollapseComparisonAtCochain_app_isIso_iff_eq_id, finiteAxisFold_generatedAuthoredDiagnosticObjectCollapseComparison_not_isIso]
  evidence: [canonical focused checker exit 0, standard-axiom audit passed, module manifest registration]
  claim_mapping:
    theorem_names: [authoredDiagnosticObjectCollapseAtCochain_rawFailureLocus, authoredDiagnosticObjectCollapseComparisonAtCochain_app_isIso_iff_eq_id, finiteAxisFold_generatedAuthoredDiagnosticObjectCollapseComparison_not_isIso]
    source_labels: [target theorem clause (g), target proof strategy K4]
    conjuncts: [cellwise IsIso beta_c iff IsIso E_c, cellwise IsIso E_c iff E_c equals identity, assumption-free whole generated finite-axis-fold comparison noninvertibility]
    undischarged_assumptions: []
    acceptance_point: The general theorems quantify over arbitrary input, cochain, and cell and invoke the previously proved idempotence internally. The fixture theorem fixes the generated cochain and second cell internally, discharges firing, and concludes noninvertibility of the whole natural transformation.
    port_status: not-applicable
audits:
  premise_delta:
    discharged: [raw failure locus and named non-IsIso beta (g)]
    remaining: [clauses (g2), (h)]
  certificate_provenance:
    discharged: [canonical mate component invertibility is an existing instance; projector idempotence is the reviewed clause (c1) theorem; fixture firing is derived from finiteAxisFold_initialRawDefect_second; fixture projector noninvertibility is the reviewed predecessor theorem]
    unresolved: [transport identity-reflection classification, fixture conjunction packet]
  proof_use:
    used: [authoredDiagnosticObjectCollapseComparisonAtCochain_app, isIso_comp_left_iff, authoredViaBaseDiagnosticObjectCollapseComponentAtCochain_comp, cancel_epi_id, generatedAuthoredDiagnosticObjectCollapseComparison_apply, NatTrans component IsIso instance, finiteAxisFold_initialRawDefect_second, finiteAxisFold_viaBaseGeneratedObjectCollapseComponent_not_isIso]
    unused: [observable exactness fields, an assumed idempotence certificate, an assumed firing certificate, a component-only replacement for the whole fixture theorem]
  structure_field_escape: none-found
  route_integrity: pass
  target_fitting: none-found
  vacuity: none-found
  one_way_as_equivalence: none-found
  goal_or_report_reinterpretation: none-found
  validation_refs: [research/lean/check_research_modules.sh --focused ResearchLean/AG/DoctrineFiberProduct/IdempotentExchangeRawFailureLocus.lean — exit 0; standard-axiom audit passed; research-modules.txt registration]
  blocking_findings: []
  next_obligation: K4(g2) decide and prove the fixed general transport identity-reflection classification, or prove its qualified concrete counterexample branch.
```

The comparison component factors as the invertible canonical mate component
followed by `E_c`, so left-composition by that isomorphism reflects and
preserves invertibility.  An invertible idempotent endomorphism is the identity
by epimorphic cancellation.  For the fixed finite axis-fold fixture, an
isomorphism of the whole generated comparison would make its second component,
and hence `E_second`, invertible; the internally discharged firing theorem and
the existing projector noninvertibility theorem contradict this.

## Cycle 10 — K4(g2) transport identity-reflection classification

```yaml
ledger_type: target_cycle_result
goal: G-116-aat-idempotent-exchange-structure
cycle: 10
goal_blob_sha: 9b3a1157889b33d5b2ce279365f3bec9f6e3bed6
base_oid: 2cb9cacb7e81920fee15d38052641027f4217e3d
tracking_issue: 4345
report_path: research/reports/G-116-aat-idempotent-exchange-structure.md
selection:
  proof_state_ref: Issue #4345 and Cycle 9 commit 2cb9cacb7e81920fee15d38052641027f4217e3d
  proof_dag_predecessors: [semanticGlobalTransport_isEquivalence, coreTransportReindexAdjunction, authoredViaBaseDiagnosticObjectCollapseComponentAtCochain_eq_provenance, exists_distinct_architectureObjects_over_configuration, authoredDiagnosticObjectCollapseComponentAtCochain_eq_id, authoredDiagnosticObjectCollapseComponentAtCochain_eq_canonical]
  proof_obligation: Decide the fixed positive-or-negative clause (g2), then prove the selected branch without using excluded-middle branch selection or restricting to the identity-presentation fixture.
  selection_reason: The positive branch holds generally because both stages of the provenance-indexed via-base route are equivalences and canonical normalization is noninjective for every package.
  expected_result_type: proof-obligation-discharged
  lean_targets: [ResearchLean/AG/DoctrineFiberProduct/IdempotentExchangeTransportIdentityClassification.lean]
  risks: [proving only the identity-presentation case, assuming faithfulness, treating noninjectivity as caller data, selecting a branch by Classical.em, proving only the raw selector statement without transport identity reflection]
  unchecked: [clause (h)]
result:
  proposed_result_type: proof-obligation-discharged
  proof_obligation_delta: Clause (g2) takes the positive branch. For every authored input, cochain, and cell, E_c is the identity exactly outside the simultaneous firing, admissible, noninjective selector branch.
  completion_candidate: no
  lean_artifacts: [selectedCoreFiberReindexFunctor_isEquivalence, bcProvenanceViaBaseRoute_isEquivalence, functor_map_eq_id_iff_of_faithful, iso_conjugate_eq_id_iff, authoredViaBaseDiagnosticObjectCollapseComponentAtCochain_eq_id_iff_raw, canonicalObjectNormalization_not_injective, authoredDiagnosticObjectCollapseComponentAtCochain_eq_id_iff, authoredViaBaseDiagnosticObjectCollapseComponentAtCochain_eq_id_iff]
  evidence: [canonical focused checker exit 0, standard-axiom audit passed, module manifest registration]
  claim_mapping:
    theorem_names: [authoredViaBaseDiagnosticObjectCollapseComponentAtCochain_eq_id_iff]
    source_labels: [target theorem clause (g2), target proof strategy K4]
    conjuncts: [arbitrary authored input, arbitrary cochain and cell, transported E_c identity, exact negation of firing-and-admissible-and-noninjective]
    undischarged_assumptions: []
    acceptance_point: The theorem has the fixed universal signature. Equivalence instances are derived from G-113 transport and the canonical adjunction; noninjectivity is constructed uniformly from the clause (e1) witness; the selector definition supplies all three cases.
    port_status: not-applicable
audits:
  premise_delta:
    discharged: [transport identity-reflection classification (g2)]
    remaining: [fixture conjunction packet (h)]
  certificate_provenance:
    discharged: [core transport equivalence comes from semanticGlobalTransport_isEquivalence; selected reindex equivalence follows from coreTransportReindexAdjunction and equivalence of its left adjoint; faithfulness is inferred from the composed equivalence; canonical-normalization noninjectivity is generated by exists_distinct_architectureObjects_over_configuration]
    unresolved: [fixture conjunction packet]
  proof_use:
    used: [semanticGlobalTransport_isEquivalence, coreTransportReindexAdjunction.isEquivalence_right_of_isEquivalence_left, authoredViaBaseDiagnosticObjectCollapseComponentAtCochain_eq_provenance, faithful map injectivity, isomorphism cancellation, exists_distinct_architectureObjects_over_configuration, canonicalObjectNormalization, selector identity and canonical branches]
    unused: [identity-presentation unitors, a caller-supplied injectivity decision, Classical.em as branch evidence]
  structure_field_escape: none-found
  route_integrity: pass
  target_fitting: none-found
  vacuity: none-found
  one_way_as_equivalence: none-found
  goal_or_report_reinterpretation: none-found
  validation_refs: [research/lean/check_research_modules.sh --focused ResearchLean/AG/DoctrineFiberProduct/IdempotentExchangeTransportIdentityClassification.lean — exit 0; axiom audit reports 8 declarations and standard axioms only; research-modules.txt registration]
  blocking_findings: []
  next_obligation: K5(h) package the fixed finite-axis-fold firing, admissibility, two distinct witness pairs, E_c nonidentity, beta_c noninvertibility, and literal transported residual equality in one theorem or structure.
```

The G-113 global transport theorem makes the canonical forward transport an
equivalence for every realized base map.  Its reviewed adjunction therefore
makes selected cartesian reindexing an equivalence as well, so their composite
faithfully reflects identity.  The provenance isomorphism reduces `E_c = 1` to
the raw selected endomorphism.  Its vanishing and inadmissible branches are the
identity, while its firing-and-admissible branch is canonical normalization;
the clause (e1) same-configuration pair proves that normalization is never
injective and hence cannot equal the identity.

## Cycle 11 — K5(h) finite witness packet

```yaml
ledger_type: target_cycle_result
goal: G-116-aat-idempotent-exchange-structure
cycle: 11
goal_blob_sha: 9b3a1157889b33d5b2ce279365f3bec9f6e3bed6
base_oid: 2cb9cacb7e81920fee15d38052641027f4217e3d
tracking_issue: 4345
report_path: research/reports/G-116-aat-idempotent-exchange-structure.md
selection:
  proof_state_ref: Cycle 10 and Cycle 11 were implemented atomically in commit 0e3e7638235e3c169eee3503bd00c1fc9af426a8, with 2cb9cacb7e81920fee15d38052641027f4217e3d as their shared pre-implementation snapshot; no intervening Git OID exists
  proof_dag_predecessors: [finiteAxisFold_initialRawDefect_second, finiteAxisFoldSwap_ne_one, finiteAxisFold_canonicalNormalizationAdmissibleAt, finiteAxisFoldUnitObject_ne_boolObject, finiteAxisFoldEraseObject_unit_eq_bool, transportAlongEquationSystemExact.equationResidual_eq, finiteAxisFold_viaBaseGeneratedObjectCollapseComponent_not_isIso, authoredDiagnosticObjectCollapseComparisonAtCochain_app_isIso_iff, authoredViaBaseDiagnosticObjectCollapseComponentAtCochain_equationResidual, authoredDiagnosticObjectCollapseComparisonAtCochain_equationResidual]
  proof_obligation: Package every clause (h) witness on the fixed finite-axis-fold datum, generated cochain, and second cell in one assumption-free theorem.
  selection_reason: Clause (h) is the sole remaining fixed mathematical obligation after the general transport identity-reflection theorem.
  expected_result_type: target-completion-candidate
  lean_targets: [ResearchLean/AG/DoctrineFiberProduct/IdempotentExchangeWitnessPacket.lean]
  risks: [moving firing or admissibility into theorem arguments, using the same object pair for noninjectivity and residual separation, using configuration projection as the separating reading, stating beta noninvertibility only for the whole natural transformation, checking residual preservation on the support package instead of the actual via-base package]
  unchecked: [fixed-head PR review, final four-lane math and Lean review, CI, merge, tracking synchronization]
result:
  proposed_result_type: target-completion-candidate
  proof_obligation_delta: Clause (h) is proved by one assumption-free conjunction theorem, so all fixed mathematical clauses (a) through (h), including (g2), now have Lean artifacts.
  completion_candidate: yes
  lean_artifacts: [finiteAxisFold_cyclic_configuration_ne_acyclic, finiteAxisFold_supportResidual_separates_cyclic_acyclic, finiteAxisFold_generatedCochain_second_ne_one, finiteAxisFold_idempotentExchange_witnessPacket]
  evidence: [canonical focused checker exit 0, standard-axiom audit passed, module manifest registration]
  claim_mapping:
    theorem_names: [finiteAxisFold_idempotentExchange_witnessPacket]
    source_labels: [target theorem clause (h), target proof strategy K5]
    conjuncts: [generated cochain firing at second, canonical-normalization admissibility, distinct same-configuration pair identified by normalization, distinct-configuration pair separated by the selected equation residual, E_second nonidentity, component beta_second noninvertibility, literal E_second residual preservation on P'_second, literal beta_second versus alpha_second residual equality on P'_second]
    undischarged_assumptions: []
    acceptance_point: The theorem has no arguments. It fixes the required datum, generated cochain, and second cell internally; the two object pairs have separate roles; the selected residual and both P'_second literal equalities are explicit theorem fields.
    port_status: not-applicable
audits:
  premise_delta:
    discharged: [fixture conjunction packet (h)]
    remaining: []
  certificate_provenance:
    discharged: [firing is computed from the initial raw defect and adjacent swap; admissibility is the reviewed finite canonical-normalization theorem; noninjectivity uses the unit and Boolean decorations; separation uses cyclic and acyclic configurations and transports the NoCycle residual through the exact equation transport; E and beta noninvertibility are derived from the selected firing component; P'_second equalities specialize the Cycle 8 universal theorems]
    unresolved: []
  proof_use:
    used: [finiteAxisFold_toTransportData, finiteAxisFold_initialRawDefect_second, finiteAxisFoldSwap_ne_one, finiteAxisFold_canonicalNormalizationAdmissibleAt, finiteAxisFoldUnitObject_ne_boolObject, finiteAxisFoldEraseObject_configuration, finiteCanonicalObjectNormalization_eq_erase, finiteAxisFoldEraseObject_unit_eq_bool, FiniteModel.object_hasCycleWitness, transportAlongEquationSystemExact.equationResidual_eq, observableEquiv injectivity, finiteAxisFold_viaBaseGeneratedObjectCollapseComponent_not_isIso, authoredDiagnosticObjectCollapseComparisonAtCochain_app_isIso_iff, authoredViaBaseDiagnosticObjectCollapseComponentAtCochain_equationResidual, authoredDiagnosticObjectCollapseComparisonAtCochain_equationResidual]
    unused: [configuration projection as a separating observable, coordinate and invariant readings that are constant on the fixture, a caller-supplied firing or admissibility certificate, whole-natural-transformation noninvertibility as a substitute for component beta_second]
  structure_field_escape: none-found
  route_integrity: pass
  target_fitting: none-found
  vacuity: none-found
  one_way_as_equivalence: none-found
  goal_or_report_reinterpretation: none-found
  validation_refs: [research/lean/check_research_modules.sh --focused ResearchLean/AG/DoctrineFiberProduct/IdempotentExchangeWitnessPacket.lean — exit 0; axiom audit reports 5 declarations and standard axioms only; research-modules.txt registration]
  blocking_findings: []
  next_obligation: Create the fixed-head implementation PR, run the standard PR review, then run the final four-lane math and Lean review and synchronize the completion ledger and tracking Issue after merge.
```

The noninjectivity pair changes only auxiliary object decoration over one Atom
configuration, while the separation pair uses cyclic and acyclic
configurations.  Exact equation transport carries their concrete NoCycle
residual difference into the fixed support package.  At the generated second
cell, firing and admissibility select the noninvertible normalization factor;
the packet records both its nonidentity and the comparison component's
noninvertibility.  It finally instantiates both Cycle 8 equation-residual
theorems on the actual via-base package `P'_second`.

## Cycle 12 — final-review API and ledger remediation

```yaml
ledger_type: target_cycle_result
goal: G-116-aat-idempotent-exchange-structure
cycle: 12
goal_blob_sha: 9b3a1157889b33d5b2ce279365f3bec9f6e3bed6
base_oid: 9af76250e27b537df58a7ee825e01617af63923a
tracking_issue: 4345
report_path: research/reports/G-116-aat-idempotent-exchange-structure.md
selection:
  proof_state_ref: First fixed-head completion review over 9af76250e27b537df58a7ee825e01617af63923a
  proof_dag_predecessors: [canonicalObjectNormalization, authoredDiagnosticObjectCollapseComponentAtCochain, bcProvenanceViaBaseRoute, canonicalObjectNormalization_natural_apply, authoredDiagnosticObjectCollapseComponentAtCochain_comp, canonicalObjectNormalizationTotal_not_internal_split, canonicalObjectNormalization_not_injective, authoredDiagnosticObjectCollapseComponentAtCochain_eq_id_iff]
  proof_obligation: Resolve the completion review's no-unfold API and Cycle 11 snapshot-provenance findings without changing any fixed target statement or conclusion.
  selection_reason: Lean B found two noncentral completion blockers after the central clauses (a) through (h) passed all four lanes.
  expected_result_type: target-completion-candidate
  lean_targets: [ResearchLean/AG/DoctrineFiberProduct/CanonicalObjectNormalizationAPI.lean, ResearchLean/AG/DoctrineFiberProduct/DiagnosticObjectCollapseSelectorAPI.lean, ResearchLean/AG/DoctrineFiberProduct/BCProvenanceViaBaseRouteAPI.lean, ResearchLean/AG/DoctrineFiberProduct/IdempotentExchangeCellProjector.lean, ResearchLean/AG/DoctrineFiberProduct/CanonicalObjectNormalizationNaturality.lean, ResearchLean/AG/DoctrineFiberProduct/InternalNormalizationSplitNoGo.lean, ResearchLean/AG/DoctrineFiberProduct/IdempotentExchangeTransportIdentityClassification.lean]
  artifact_targets: [ResearchLean/AG/DoctrineFiberProduct.lean, research-modules.txt, research/reports/G-116-aat-idempotent-exchange-structure.md]
  risks: [changing theorem signatures, hiding definitional expansion in downstream proofs, claiming an intervening commit that never existed]
  unchecked: [fresh standard fixed-head PR review, replacement final packet, four wholly fresh completion lanes, completion ledger, CI, merge, durable synchronization]
result:
  proposed_result_type: target-completion-candidate
  proof_obligation_delta: Downstream target proofs now use named evaluation, same-configuration, route-composition, and inadmissible-selector APIs from three lightweight definition-layer API modules; Cycle 11 explicitly records that Cycles 10 and 11 were implemented atomically and names both the shared pre-implementation snapshot and implementation commit.
  completion_candidate: yes
  implementation_oids: [a1113af14c495c562469d67119ad621ea30c0139, d8278a000037c8c894957574665eabbe80352342]
  lean_artifacts: [canonicalObjectNormalization_apply, canonicalObjectNormalization_eq_of_configuration_eq, bcProvenanceViaBaseRoute_eq, authoredDiagnosticObjectCollapseComponentAtCochain_eq_id_of_not_admissible]
  evidence: [seven named focused checks exit 0, each module's standard-axiom audit passed, aggregate and manifest registration, no target theorem signature or conclusion changed]
  claim_mapping:
    theorem_names: [canonicalObjectNormalization_natural_apply, canonicalObjectNormalizationTotal_not_internal_split, canonicalObjectNormalization_not_injective, authoredDiagnosticObjectCollapseComponentAtCochain_eq_id_iff]
    source_labels: [Lean quality standard no-unfold API, completion ledger reproducibility]
    conjuncts: [named downstream APIs, honest atomic-commit provenance]
    undischarged_assumptions: []
    acceptance_point: These are proof-route and ledger repairs only; clauses (a) through (h) retain their fixed statements.
    port_status: not-applicable
audits:
  premise_delta:
    discharged: [completion-review API and ledger findings]
    remaining: []
  certificate_provenance:
    discharged: [new API lemmas are definitional or derive from explicit configuration equality; no certificate is accepted from a caller]
    unresolved: []
  proof_use:
    used: [canonicalObjectNormalization_apply, canonicalObjectNormalization_eq_of_configuration_eq, bcProvenanceViaBaseRoute_eq, authoredDiagnosticObjectCollapseComponentAtCochain_eq_id_of_not_admissible]
    unused: [downstream unfold of canonicalObjectNormalization, downstream unfold of bcProvenanceViaBaseRoute, downstream selector simp]
  structure_field_escape: none-found
  route_integrity: pass
  target_fitting: none-found
  vacuity: none-found
  one_way_as_equivalence: none-found
  goal_or_report_reinterpretation: none-found
  validation_refs: [lake env lean ResearchLean/AG/DoctrineFiberProduct/CanonicalObjectNormalizationAPI.lean — exit 0, 2 declarations standard axioms only; lake env lean ResearchLean/AG/DoctrineFiberProduct/DiagnosticObjectCollapseSelectorAPI.lean — exit 0, 1 declaration standard axioms only; lake env lean ResearchLean/AG/DoctrineFiberProduct/BCProvenanceViaBaseRouteAPI.lean — exit 0, 1 declaration standard axioms only; lake env lean ResearchLean/AG/DoctrineFiberProduct/IdempotentExchangeCellProjector.lean — exit 0, 4 declarations standard axioms only; lake env lean ResearchLean/AG/DoctrineFiberProduct/CanonicalObjectNormalizationNaturality.lean — exit 0, 2 declarations standard axioms only; lake env lean ResearchLean/AG/DoctrineFiberProduct/InternalNormalizationSplitNoGo.lean — exit 0, 5 declarations standard axioms only; lake env lean ResearchLean/AG/DoctrineFiberProduct/IdempotentExchangeTransportIdentityClassification.lean — exit 0, 8 declarations standard axioms only]
  blocking_findings: []
  next_obligation: Refix the PR head, rerun the standard PR gate, publish a replacement same-head final packet, run four wholly fresh completion lanes, and only then emit the formal completion ledger and merge.
```

## Cycle 13 — arbitrary-carrier target surface and transport API closure

```yaml
ledger_type: target_cycle_result
goal: G-116-aat-idempotent-exchange-structure
cycle: 13
goal_blob_sha: 9b3a1157889b33d5b2ce279365f3bec9f6e3bed6
base_oid: 99987d36b6cb94b489f076f53c7742886cb3947d
tracking_issue: 4345
report_path: research/reports/G-116-aat-idempotent-exchange-structure.md
selection:
  proof_state_ref: Fresh standard four-lane review over 99987d36b6cb94b489f076f53c7742886cb3947d
  proof_dag_predecessors: [authoredDiagnosticObjectCollapseComponentAtCochain_comp, authoredViaBaseDiagnosticObjectCollapseComponentAtCochain_comp_of_raw_comp, authoredViaBaseDiagnosticObjectCollapseComponentAtCochain_comp, authoredDiagnosticObjectCollapseKaroubiIso, authoredViaBaseDiagnosticObjectCollapseComponentAtCochain_coordinate, authoredViaBaseDiagnosticObjectCollapseComponentAtCochain_equationResidual, authoredDiagnosticObjectCollapseComparisonAtCochain_coordinate, authoredDiagnosticObjectCollapseComparisonAtCochain_equationResidual, authoredDiagnosticObjectCollapseAtCochain_rawFailureLocus, authoredViaBaseDiagnosticObjectCollapseComponentAtCochain_eq_id_iff]
  proof_obligation: Expose clauses (c1), (d), (f), (g), and (g2) for every Atom carrier without a caller-supplied DecidableEq instance, and remove the remaining downstream unfolding of the via-base component definition.
  selection_reason: Math A identified the unclassified typeclass binder as a central anti-weakening risk, and Lean B found one remaining noncentral no-unfold violation.
  expected_result_type: target-completion-candidate
  lean_targets: [ResearchLean/AG/DoctrineFiberProduct/DiagnosticObjectCollapseSelectorAPI.lean, ResearchLean/AG/DoctrineFiberProduct/IdempotentExchangeCellProjector.lean, ResearchLean/AG/DoctrineFiberProduct/IdempotentExchangeUniversalTargets.lean]
  artifact_targets: [ResearchLean/AG/DoctrineFiberProduct.lean, research-modules.txt, research/reports/G-116-aat-idempotent-exchange-structure.md]
  risks: [changing the fixed target, changing fixture instance selection, leaving DecidableEq as a public target premise, moving producer unfolding into another downstream target]
  unchecked: [fresh standard fixed-head PR review, replacement final packet, four wholly fresh completion lanes, completion ledger, CI, merge, durable synchronization]
result:
  proposed_result_type: target-completion-candidate
  proof_obligation_delta: A lightweight producer-adjacent API now transports raw idempotence through the two functors without downstream unfolding. A new target-surface module internally selects Classical.decEq and restates all affected clauses with no DecidableEq binder, while the existing instance-parametric implementation and fixed finite fixture remain unchanged.
  completion_candidate: yes
  implementation_oids: [668c873e4ecfb9105896864e6f940983f229a72a]
  lean_artifacts: [authoredViaBaseDiagnosticObjectCollapseComponentAtCochain_comp_of_raw_comp, authoredViaBaseDiagnosticObjectCollapseComponentAtCochain_comp_universal, authoredViaBaseDiagnosticObjectCollapseComponentAtCochain_atomEquiv_universal, authoredDiagnosticObjectCollapseKaroubiIso_universal, authoredViaBaseDiagnosticObjectCollapseComponentAtCochain_coordinate_universal, authoredViaBaseDiagnosticObjectCollapseComponentAtCochain_equationResidual_universal, authoredDiagnosticObjectCollapseComparisonAtCochain_coordinate_universal, authoredDiagnosticObjectCollapseComparisonAtCochain_equationResidual_universal, authoredDiagnosticObjectCollapseAtCochain_rawFailureLocus_universal, authoredViaBaseDiagnosticObjectCollapseComponentAtCochain_eq_id_iff_universal]
  evidence: [three named focused checks exit 0, all three module-local standard-axiom audits pass, exact #check output shows every universal declaration quantifies only over U input cochain and cell before the GOAL-permitted direction hypotheses, fixed witness packet focused check remains exit 0, aggregate and manifest registration]
  claim_mapping:
    theorem_names: [authoredViaBaseDiagnosticObjectCollapseComponentAtCochain_comp_universal, authoredViaBaseDiagnosticObjectCollapseComponentAtCochain_atomEquiv_universal, authoredDiagnosticObjectCollapseKaroubiIso_universal, authoredViaBaseDiagnosticObjectCollapseComponentAtCochain_coordinate_universal, authoredViaBaseDiagnosticObjectCollapseComponentAtCochain_equationResidual_universal, authoredDiagnosticObjectCollapseComparisonAtCochain_coordinate_universal, authoredDiagnosticObjectCollapseComparisonAtCochain_equationResidual_universal, authoredDiagnosticObjectCollapseAtCochain_rawFailureLocus_universal, authoredViaBaseDiagnosticObjectCollapseComponentAtCochain_eq_id_iff_universal]
    source_labels: [G-116(c1), G-116(d), G-116(f), G-116(g), G-116(g2)]
    conjuncts: [arbitrary-carrier target signatures, internally selected classical decidable equality, unchanged mathematical conclusions, fixture independence]
    undischarged_assumptions: []
    acceptance_point: The fixed target is not weakened; each affected public target declaration has no DecidableEq binder, and the original proof-producing declarations remain available as implementation API.
    port_status: not-applicable
audits:
  premise_delta:
    discharged: [DecidableEq U.Atom is selected internally by the target surface and is no longer a caller premise]
    remaining: []
  certificate_provenance:
    discharged: [Classical.decEq is a canonical internal computational choice, not a proposition carrying any target conclusion; raw idempotence is theorem-generated before functorial transport]
    unresolved: []
  proof_use:
    used: [all nine universal target declarations directly reuse their proved instance-parametric declarations; authoredViaBaseDiagnosticObjectCollapseComponentAtCochain_comp uses the lightweight comp_of_raw_comp API and the raw idempotence theorem]
    unused: [downstream unfolding of authoredViaBaseDiagnosticObjectCollapseComponentAtCochain]
  structure_field_escape: none-found
  route_integrity: pass
  target_fitting: none-found
  vacuity: none-found
  one_way_as_equivalence: none-found
  goal_or_report_reinterpretation: none-found
  validation_refs: [lake env lean ResearchLean/AG/DoctrineFiberProduct/DiagnosticObjectCollapseSelectorAPI.lean — exit 0, 2 declarations standard axioms only; lake env lean ResearchLean/AG/DoctrineFiberProduct/IdempotentExchangeCellProjector.lean — exit 0, 4 declarations standard axioms only; lake env lean ResearchLean/AG/DoctrineFiberProduct/IdempotentExchangeUniversalTargets.lean — exit 0, 10 declarations standard axioms only; lake env lean ResearchLean/AG/DoctrineFiberProduct/IdempotentExchangeWitnessPacket.lean — exit 0, 5 declarations standard axioms only; lake env lean /private/tmp/G116UniversalSignatureCheck.lean — exit 0, no DecidableEq binder in any of the nine target declarations]
  blocking_findings: []
  next_obligation: Refix the PR head, rerun the standard PR gate, publish a replacement same-head final packet, run four wholly fresh completion lanes, and only then emit the formal completion ledger and merge.
```

## Cycle 14 — final target API boundary and dependency remediation

```yaml
ledger_type: target_cycle_result
goal: G-116-aat-idempotent-exchange-structure
cycle: 14
goal_blob_sha: 9b3a1157889b33d5b2ce279365f3bec9f6e3bed6
base_oid: 18938c328167421df4e34addd201384baa224373
tracking_issue: 4345
report_path: research/reports/G-116-aat-idempotent-exchange-structure.md
selection:
  proof_state_ref: Fresh standard four-lane review over 18938c328167421df4e34addd201384baa224373
  proof_dag_predecessors: [SignedExactCoreReadingHom.comp, SignedExactCoreReadingHom.refl, coreFiberLift, authoredDiagnosticImageSourceKaroubi, authoredDiagnosticImageTargetKaroubi, exists_distinct_architectureObjects_over_configuration]
  proof_obligation: Correct the Cycle 13 implementation OID, replace remaining target-surface constructor unfolding with named evaluation APIs, and remove the e1 witness module's unnecessary Karoubi dependency.
  selection_reason: All four lanes accepted the central mathematical claims; Lean B identified two additional noncentral API/dependency findings and all lanes identified the same ledger OID typo.
  expected_result_type: target-completion-candidate
  lean_targets: [ResearchLean/AG/DoctrineFiberProduct/SignedExactCoreReadingHomObjectMapAPI.lean, ResearchLean/AG/DoctrineFiberProduct/CoreFiberLiftAxisAPI.lean, ResearchLean/AG/DoctrineFiberProduct/DistinctArchitectureObjects.lean, ResearchLean/AG/DoctrineFiberProduct/InternalNormalizationSplitNoGo.lean, ResearchLean/AG/DoctrineFiberProduct/IdempotentExchangeKaroubiImage.lean, ResearchLean/AG/DoctrineFiberProduct/IdempotentExchangeObservableExactness.lean]
  artifact_targets: [ResearchLean/AG/DoctrineFiberProduct.lean, research-modules.txt, research/reports/G-116-aat-idempotent-exchange-structure.md]
  risks: [broad predecessor edits, changing target statements, losing c2 import for e2, moving unfolds without reducing dependency]
  unchecked: [fresh standard fixed-head PR review, replacement final packet, four wholly fresh completion lanes, completion ledger, CI, merge, durable synchronization]
result:
  proposed_result_type: target-completion-candidate
  proof_obligation_delta: Two lightweight owner-adjacent modules expose exact-reading object-map composition/identity and core-lift axis evaluation. Observable exactness and Karoubi image proofs consume named APIs. DistinctArchitectureObjects now imports ConfigurationDescent directly, while InternalNormalizationSplitNoGo imports naturality explicitly. The Cycle 13 implementation OID is corrected to the actual Git object.
  completion_candidate: yes
  implementation_oids: [b4a32b1786564c127ea24e85e4c516e47dda613e]
  lean_artifacts: [signedExactCoreReadingHom_comp_objectMap_apply, signedExactCoreReadingHom_refl_objectMap_apply, coreFiberLift_axisMap, authoredDiagnosticImageSourceKaroubi_p, authoredDiagnosticImageTargetKaroubi_p]
  evidence: [eight named focused checks exit 0, every changed module standard-axiom audit passes, target unfold pattern scan has no match, aggregate and manifest registration, exact import ownership]
  claim_mapping:
    theorem_names: [equationResidual_eq_of_upper_conjugation, coordinate_eq_of_upper_conjugation, coreFiberTransportMap_axisMap_of_eq, signedExactCoreReadingHom_coordinate_eq_of_comp, authoredDiagnosticObjectCollapseKaroubiIso, exists_distinct_architectureObjects_over_configuration, canonicalObjectNormalizationTotal_not_internal_split]
    source_labels: [Lean quality standard no-unfold API, dependency minimality, completion ledger reproducibility]
    conjuncts: [named object-map evaluation, named lift-axis evaluation, named Karoubi projectors, direct e1 dependency, explicit e2 naturality dependency]
    undischarged_assumptions: []
    acceptance_point: These are proof-route, import, and ledger repairs; every fixed target theorem statement and universal surface declaration is unchanged.
    port_status: not-applicable
audits:
  premise_delta:
    discharged: [remaining no-unfold/API findings, unnecessary Karoubi dependency, Cycle 13 OID typo]
    remaining: []
  certificate_provenance:
    discharged: [all new APIs are definitional evaluation equalities and carry no mathematical conclusion supplied by a caller]
    unresolved: []
  proof_use:
    used: [signedExactCoreReadingHom_comp_objectMap_apply, signedExactCoreReadingHom_refl_objectMap_apply, coreFiberLift_axisMap, authoredDiagnosticImageSourceKaroubi_p, authoredDiagnosticImageTargetKaroubi_p]
    unused: [target-surface unfolding of SignedExactCoreReadingHom.comp, SignedExactCoreReadingHom.refl, coreFiberLift, transportAlongHom, transportAlongUpper, authoredDiagnosticImageSourceKaroubi, authoredDiagnosticImageTargetKaroubi]
  structure_field_escape: none-found
  route_integrity: pass
  target_fitting: none-found
  vacuity: none-found
  one_way_as_equivalence: none-found
  goal_or_report_reinterpretation: none-found
  validation_refs: [lake env lean ResearchLean/AG/DoctrineFiberProduct/SignedExactCoreReadingHomObjectMapAPI.lean — exit 0, 2 declarations standard axioms only; lake env lean ResearchLean/AG/DoctrineFiberProduct/CoreFiberLiftAxisAPI.lean — exit 0, 1 declaration standard axioms only; lake env lean ResearchLean/AG/DoctrineFiberProduct/DistinctArchitectureObjects.lean — exit 0, 4 declarations standard axioms only; lake env lean ResearchLean/AG/DoctrineFiberProduct/InternalNormalizationSplitNoGo.lean — exit 0, 5 declarations standard axioms only; lake env lean ResearchLean/AG/DoctrineFiberProduct/IdempotentExchangeKaroubiImage.lean — exit 0, 5 declarations standard axioms only; lake env lean ResearchLean/AG/DoctrineFiberProduct/IdempotentExchangeObservableExactness.lean — exit 0, 36 declarations standard axioms only; lake env lean ResearchLean/AG/DoctrineFiberProduct/IdempotentExchangeUniversalTargets.lean — exit 0, 10 declarations standard axioms only; lake env lean ResearchLean/AG/DoctrineFiberProduct/IdempotentExchangeWitnessPacket.lean — exit 0, 5 declarations standard axioms only]
  blocking_findings: []
  next_obligation: Refix the PR head, rerun the standard PR gate, publish a replacement same-head final packet, run four wholly fresh completion lanes, and only then emit the formal completion ledger and merge.
```

## Cycle 15 — classification import and ledger exactness closure

```yaml
ledger_type: target_cycle_result
goal: G-116-aat-idempotent-exchange-structure
cycle: 15
goal_blob_sha: 9b3a1157889b33d5b2ce279365f3bec9f6e3bed6
base_oid: fed22056a6eaf9a159be037a7ba460121fb2dd67
tracking_issue: 4345
report_path: research/reports/G-116-aat-idempotent-exchange-structure.md
selection:
  proof_state_ref: Fresh standard four-lane review over fed22056a6eaf9a159be037a7ba460121fb2dd67
  proof_dag_predecessors: [DistinctArchitectureObjects, CanonicalObjectNormalizationAPI, DiagnosticObjectCollapseSelectorAPI, BCProvenanceViaBaseRouteAPI, TransportEquivalence]
  proof_obligation: Remove the classification module's unused raw-failure dependency and correct the two Cycle 14 declaration/evidence transcription errors.
  selection_reason: Lean B found the high-layer import; Math A and Lean A/B found the same nonexistent declaration name, and Math A/Lean A found the seven-versus-eight validation count mismatch.
  expected_result_type: target-completion-candidate
  lean_targets: [ResearchLean/AG/DoctrineFiberProduct/IdempotentExchangeTransportIdentityClassification.lean]
  artifact_targets: [research/reports/G-116-aat-idempotent-exchange-structure.md]
  risks: [losing a transitive producer API, changing g2 statement or proof, rewriting historical Cycle 14 facts]
  unchecked: [finding-limited direct response, replacement final packet, four wholly fresh completion lanes, completion ledger, CI, merge, durable synchronization]
result:
  proposed_result_type: target-completion-candidate
  proof_obligation_delta: Transport identity classification now imports the exact lower modules it uses rather than IdempotentExchangeRawFailureLocus. Cycle 14 names signedExactCoreReadingHom_coordinate_eq_of_comp and accurately records eight focused module checks.
  completion_candidate: yes
  implementation_oids: [0c4ea102f8035d8d5c33e1a83113478d3f361768]
  lean_artifacts: []
  evidence: [classification focused check exit 0 with 8 declarations standard axioms only, no target declaration change, exact direct imports, two cause-local Cycle 14 ledger corrections]
  claim_mapping:
    theorem_names: [authoredViaBaseDiagnosticObjectCollapseComponentAtCochain_eq_id_iff]
    source_labels: [G-116(g2), Lean quality dependency minimality, completion ledger reproducibility]
    conjuncts: [unchanged g2 positive classification, direct producer and API dependencies, exact historical declaration and validation references]
    undischarged_assumptions: []
    acceptance_point: The fixed target, proof body, and all mathematical conclusions are unchanged; only import ownership and ledger spelling/count are repaired.
    port_status: not-applicable
audits:
  premise_delta:
    discharged: [unused high-layer raw-failure import, nonexistent Cycle 14 declaration name, Cycle 14 validation count mismatch]
    remaining: []
  certificate_provenance:
    discharged: []
    unresolved: []
  proof_use:
    used: [canonicalObjectNormalization_eq_of_configuration_eq, authoredDiagnosticObjectCollapseComponentAtCochain_eq_id_of_not_admissible, bcProvenanceViaBaseRoute_eq, G-113 transport equivalence]
    unused: [IdempotentExchangeRawFailureLocus import]
  structure_field_escape: none-found
  route_integrity: pass
  target_fitting: none-found
  vacuity: none-found
  one_way_as_equivalence: none-found
  goal_or_report_reinterpretation: none-found
  validation_refs: [lake env lean ResearchLean/AG/DoctrineFiberProduct/IdempotentExchangeTransportIdentityClassification.lean — exit 0, 8 declarations standard axioms only; git diff --check — exit 0]
  blocking_findings: []
  next_obligation: Obtain the finding-limited direct response, publish the replacement same-head final packet, run four wholly fresh completion lanes, and only then emit the formal completion ledger and merge.
```

## Cycle 16 — fresh-source witness and scope closure

```yaml
ledger_type: target_cycle_result
goal: G-116-aat-idempotent-exchange-structure
cycle: 16
goal_blob_sha: 9b3a1157889b33d5b2ce279365f3bec9f6e3bed6
base_oid: 80307a3f4792c237474ded0ed699f1725aaeecb5
tracking_issue: 4345
report_path: research/reports/G-116-aat-idempotent-exchange-structure.md
selection:
  proof_state_ref: Fresh standard four-lane review over 80307a3f4792c237474ded0ed699f1725aaeecb5
  proof_dag_predecessors: [IdempotentExchangeRawFailureLocus, IdempotentExchangeTransportIdentityClassification, IdempotentExchangeObservableExactness, FiniteGeneratedEquationTransportWitnesses, DiagnosticObjectCollapseSelectorAPI]
  proof_obligation: Restore the witness packet's fresh-source declaration closure, remove remaining target unfold routes and unnecessary upper-layer imports, correct Cycle 6 registration provenance, and align n1008's Karoubi claim with the fixed GOAL boundary.
  selection_reason: Lean A/B found the witness import break and transitive import fragility; Lean B found remaining target unfolds; Math B found the Cycle 6 manifest overclaim and Karoubi minimality overclaim.
  expected_result_type: target-completion-candidate
  lean_targets: [ResearchLean/AG/DoctrineFiberProduct/DiagnosticObjectCollapseSelectorAPI.lean, ResearchLean/AG/DoctrineFiberProduct/CanonicalObjectNormalizationNaturality.lean, ResearchLean/AG/DoctrineFiberProduct/IdempotentExchangeKaroubiImage.lean, ResearchLean/AG/DoctrineFiberProduct/IdempotentExchangeObservableExactness.lean, ResearchLean/AG/DoctrineFiberProduct/IdempotentExchangeRawFailureLocus.lean, ResearchLean/AG/DoctrineFiberProduct/IdempotentExchangeTransportIdentityClassification.lean, ResearchLean/AG/DoctrineFiberProduct/IdempotentExchangeWitnessPacket.lean, ResearchLean/AG/DoctrineFiberProduct/IdempotentExchangeUniversalTargets.lean]
  artifact_targets: [docs/note/n1008_aat_idempotent_exchange_structure_program.md, research/reports/G-116-aat-idempotent-exchange-structure.md]
  risks: [stale olean false pass, losing witness theorem owners, changing fixed target claims, retroactively claiming a Cycle 6 manifest entry]
  unchecked: [fresh standard fixed-head PR review, replacement final packet, four wholly fresh completion lanes, completion ledger, CI, merge, durable synchronization]
result:
  proposed_result_type: target-completion-candidate
  proof_obligation_delta: WitnessPacket directly imports every theorem owner it uses and passes a fresh focused check. The classification object-map step, fixed swap nonidentity, and residual separation use named APIs. Naturality, Karoubi, Observable, and Witness imports are direct and minimal. n1008 now states only the explicit Karoubi isomorphism proved by clause (d), with universal/minimal completion and localization questions separated as later candidates. Cycle 6 records only its actual aggregate registration.
  completion_candidate: yes
  implementation_oids: [a25d9cb67afad7e18cbb7cbe8c66506c45c3d2a8]
  lean_artifacts: [canonicalObjectNormalization_eq_id_of_supportComponent_eq_id]
  evidence: [eight named focused checks exit 0 with standard-axiom audits, fresh WitnessPacket check after direct RawFailure and finite residual API imports, target no-unfold scan, exact direct-import closure, unchanged fixed GOAL blob]
  claim_mapping:
    theorem_names: [canonicalObjectNormalization_eq_id_of_supportComponent_eq_id, authoredDiagnosticObjectCollapseComponentAtCochain_eq_id_iff, finiteAxisFold_generatedAuthoredDiagnosticObjectCollapseComparison_not_isIso, finiteAxisFold_supportResidual_separates_cyclic_acyclic, finiteAxisFold_idempotentExchange_witnessPacket]
    source_labels: [G-116(g), G-116(g2), G-116(h), Lean quality no-unfold and dependency rules, GOAL Karoubi claim boundary]
    conjuncts: [fresh-source witness closure, named normalization object-map API, named swap nonidentity, named residual separation, explicit Karoubi iso scope]
    undischarged_assumptions: []
    acceptance_point: All fixed clauses retain their statements; the changes restore source-level proof routing and remove documentation and historical-ledger overclaims.
    port_status: not-applicable
audits:
  premise_delta:
    discharged: [fresh-source clause h import break, remaining target unfold routes, upper-layer transitive imports, Cycle 6 registration overclaim, Karoubi minimality overclaim]
    remaining: []
  certificate_provenance:
    discharged: [normalization identity follows from an explicit morphism equality through a producer-adjacent API; fixed swap and residual separation come from named proved fixture theorems]
    unresolved: []
  proof_use:
    used: [canonicalObjectNormalization_eq_id_of_supportComponent_eq_id, finiteAxisFoldSwap_ne_one, finiteSelectiveTwo_noCycleResidual_object_sensitive, authoredDiagnosticObjectCollapseComparisonAtCochain_app_isIso_iff]
    unused: [transitive theorem-owner imports, target-local unfolding of normalization objectMap, finite swap axis implementation, FiniteModel.noCycleResidual]
  structure_field_escape: none-found
  route_integrity: pass
  target_fitting: none-found
  vacuity: none-found
  one_way_as_equivalence: none-found
  goal_or_report_reinterpretation: none-found
  validation_refs: [lake env lean ResearchLean/AG/DoctrineFiberProduct/DiagnosticObjectCollapseSelectorAPI.lean — exit 0, 4 declarations standard axioms only; lake env lean ResearchLean/AG/DoctrineFiberProduct/CanonicalObjectNormalizationNaturality.lean — exit 0, 2 declarations standard axioms only; lake env lean ResearchLean/AG/DoctrineFiberProduct/IdempotentExchangeKaroubiImage.lean — exit 0, 5 declarations standard axioms only; lake env lean ResearchLean/AG/DoctrineFiberProduct/IdempotentExchangeObservableExactness.lean — exit 0, 36 declarations standard axioms only; lake env lean ResearchLean/AG/DoctrineFiberProduct/IdempotentExchangeRawFailureLocus.lean — exit 0, 7 declarations standard axioms only; lake env lean ResearchLean/AG/DoctrineFiberProduct/IdempotentExchangeTransportIdentityClassification.lean — exit 0, 8 declarations standard axioms only; lake env lean ResearchLean/AG/DoctrineFiberProduct/IdempotentExchangeWitnessPacket.lean — exit 0, 5 declarations standard axioms only; lake env lean ResearchLean/AG/DoctrineFiberProduct/IdempotentExchangeUniversalTargets.lean — exit 0, 10 declarations standard axioms only]
  blocking_findings: []
  next_obligation: Refix the PR head, rerun the standard PR gate, publish the replacement same-head final packet, run four wholly fresh completion lanes, and only then emit the formal completion ledger and merge.
```

## Cycle 17 — exact witness theorem-owner closure

```yaml
ledger_type: target_cycle_result
goal: G-116-aat-idempotent-exchange-structure
cycle: 17
goal_blob_sha: 9b3a1157889b33d5b2ce279365f3bec9f6e3bed6
base_oid: f00f8c704e21207f1980193cca94d4748e928577
tracking_issue: 4345
report_path: research/reports/G-116-aat-idempotent-exchange-structure.md
selection:
  proof_state_ref: Fresh standard four-lane review over f00f8c704e21207f1980193cca94d4748e928577
  proof_dag_predecessors: [Formal.AG.Examples.FiniteModel, BCDiagnosticAxisFoldComparisonWitnesses, BCDiagnosticPairwiseAxisFoldWitnesses, BCAuthoredObjectCollapse, BCAuthoredCanonicalObjectNormalizationWitnesses, BCAuthoredDiagnosticObjectCollapseProducerWitnesses, IdempotentExchangeRawFailureLocus, IdempotentExchangeObservableExactness, FiniteGeneratedEquationTransportWitnesses]
  proof_obligation: Make the Cycle 16 theorem-owner claim literal by importing every module that owns a theorem used by IdempotentExchangeWitnessPacket, and remove the unused classification umbrella import.
  selection_reason: Both fresh Lean lanes found that the witness elaborated through transitive theorem imports while Cycle 16 claimed exact direct ownership.
  expected_result_type: target-completion-candidate
  lean_targets: [ResearchLean/AG/DoctrineFiberProduct/IdempotentExchangeWitnessPacket.lean]
  artifact_targets: [research/reports/G-116-aat-idempotent-exchange-structure.md]
  risks: [retaining an unused umbrella import, omitting a theorem owner, confusing public theorem inventory with axiom-audit output count]
  unchecked: [finding-limited direct response, replacement final packet, four wholly fresh completion lanes, completion ledger, CI, merge, durable synchronization]
result:
  proposed_result_type: target-completion-candidate
  proof_obligation_delta: WitnessPacket now directly imports all six previously transitive theorem-owner modules, retains the three directly used target theorem modules, removes the unused IdempotentExchangeTransportIdentityClassification import, and passes focused source elaboration.
  completion_candidate: yes
  implementation_oids: [9a449e7b737e702249205e619516cfbc0779a535]
  lean_artifacts: []
  evidence: [WitnessPacket focused check exit 0 with 5 declarations standard axioms only, declaration-to-owner source scan, exact direct theorem-owner imports, unchanged fixed GOAL blob]
  claim_mapping:
    theorem_names: [finiteAxisFold_idempotentExchange_witnessPacket]
    source_labels: [G-116(h), Lean dependency ownership, Cycle 16 evidence correction]
    conjuncts: [unchanged fixed witness packet, direct theorem-owner closure, no unused classification umbrella]
    undischarged_assumptions: []
    acceptance_point: The clause h statement and proof term are unchanged; only its explicit source dependency closure and the evidence ledger are repaired.
    port_status: not-applicable
audits:
  premise_delta:
    discharged: [transitive theorem-owner imports in WitnessPacket]
    remaining: []
  certificate_provenance:
    discharged: []
    unresolved: []
  proof_use:
    used: [FiniteModel.object_hasCycleWitness, finiteAxisFold_toTransportData, finiteAxisFold_initialRawDefect_second, finiteAxisFoldSwap_ne_one, finiteAxisFoldEraseObject_configuration, finiteAxisFoldUnitObject_ne_boolObject, finiteAxisFoldEraseObject_unit_eq_bool, finiteCanonicalObjectNormalization_eq_erase, finiteAxisFold_canonicalNormalizationAdmissibleAt, finiteAxisFold_viaBaseGeneratedObjectCollapseComponent_not_isIso, finiteSelectiveTwo_noCycleResidual_object_sensitive, authoredDiagnosticObjectCollapseComparisonAtCochain_app_isIso_iff, authoredViaBaseDiagnosticObjectCollapseComponentAtCochain_equationResidual, authoredDiagnosticObjectCollapseComparisonAtCochain_equationResidual]
    unused: [IdempotentExchangeTransportIdentityClassification import]
  structure_field_escape: none-found
  route_integrity: pass
  target_fitting: none-found
  vacuity: none-found
  one_way_as_equivalence: none-found
  goal_or_report_reinterpretation: none-found
  validation_refs: [lake env lean ResearchLean/AG/DoctrineFiberProduct/IdempotentExchangeWitnessPacket.lean — exit 0, axiom audit raw output reports 5 namespace declarations standard axioms only; DiagnosticObjectCollapseSelectorAPI has three public theorem declarations while its axiom-audit macro raw output reports 4 namespace declarations]
  blocking_findings: []
  next_obligation: Obtain finding-limited direct responses for the Cycle 17 import fix and the exact-head PR body, then publish the replacement final packet and run four wholly fresh completion lanes.
```

## Cycle 18 — witness no-unfold API closure

```yaml
ledger_type: target_cycle_result
goal: G-116-aat-idempotent-exchange-structure
cycle: 18
goal_blob_sha: 9b3a1157889b33d5b2ce279365f3bec9f6e3bed6
base_oid: 072852ddc9963a7335ece163471d16d25703169a
tracking_issue: 4345
report_path: research/reports/G-116-aat-idempotent-exchange-structure.md
selection:
  proof_state_ref: Fresh full standard four-lane review over 072852ddc9963a7335ece163471d16d25703169a
  proof_dag_predecessors: [SchemaWitnesses, BCAuthoredObjectCollapse, IdempotentExchangeWitnessPacket]
  proof_obligation: Remove the remaining downstream unfolds of finite cycle, decoration configuration, and schema atom transport from clause h by adding and consuming owner-adjacent named APIs.
  selection_reason: Lean B found that the witness proof still unfolded externally owned definitions even though Cycle 16 claimed the target no-unfold route was closed.
  expected_result_type: target-completion-candidate
  lean_targets: [ResearchLean/AG/DoctrineFiberProduct/SchemaWitnesses.lean, ResearchLean/AG/DoctrineFiberProduct/BCAuthoredObjectCollapse.lean, ResearchLean/AG/DoctrineFiberProduct/IdempotentExchangeWitnessPacket.lean]
  artifact_targets: [research/reports/G-116-aat-idempotent-exchange-structure.md]
  risks: [moving external definition unfolds into the target proof, stale owner oleans, changing the fixed clause h conjunction]
  unchecked: [fresh full standard fixed-head PR review, schema-complete replacement final packet, four wholly fresh completion lanes, completion ledger, CI, merge, durable synchronization]
result:
  proposed_result_type: target-completion-candidate
  proof_obligation_delta: SchemaWitnesses now exposes identity Atom-equivalence and configuration-transport APIs; BCAuthoredObjectCollapse exposes both decoration configurations and configuration congruence for the finite cycle predicate; WitnessPacket consumes those named APIs and no longer unfolds the external definitions identified by review.
  completion_candidate: yes
  implementation_oids: [5daebba770203f1a9782e44bd7954a981a93b0ca]
  lean_artifacts: [finiteModelDoctrineFromFixture_atomEquiv, finiteModelDoctrineFromFixture_configuration_transport, finiteAxisFoldUnitObject_configuration, finiteAxisFoldBoolObject_configuration, finiteModel_hasDependencyCycle_iff_of_configuration_eq]
  evidence: [three named focused source checks, targeted dependency construction for SchemaWitnesses and BCAuthoredObjectCollapse, WitnessPacket exit 0 with 5 declarations standard axioms only, target no-unfold scan, unchanged fixed GOAL blob]
  claim_mapping:
    theorem_names: [finiteAxisFold_cyclic_configuration_ne_acyclic, finiteAxisFold_idempotentExchange_witnessPacket]
    source_labels: [G-116(h), Lean quality no-unfold rule]
    conjuncts: [cycle-based configuration separation, same-configuration decoration pair, transported separated configurations]
    undischarged_assumptions: []
    acceptance_point: Clause h retains the exact theorem signature and proof obligations while all externally owned implementation reductions move behind named source APIs.
    port_status: not-applicable
audits:
  premise_delta:
    discharged: [downstream finite cycle unfold, downstream decoration constructor unfold, downstream schema morphism unfold]
    remaining: []
  certificate_provenance:
    discharged: [cycle congruence follows from configuration equality; both decoration configurations and schema identity transport have named theorem producers]
    unresolved: []
  proof_use:
    used: [finiteModel_hasDependencyCycle_iff_of_configuration_eq, finiteAxisFoldUnitObject_configuration, finiteAxisFoldBoolObject_configuration, finiteModelDoctrineFromFixture_configuration_transport]
    unused: [target-local unfolding of FiniteModel.hasCycleWitness, FiniteModel.hasDependencyCycle, finiteAxisFoldUnitObject, finiteAxisFoldBoolObject, finiteModelDoctrineFromFixture]
  structure_field_escape: none-found
  route_integrity: pass
  target_fitting: none-found
  vacuity: none-found
  one_way_as_equivalence: none-found
  goal_or_report_reinterpretation: none-found
  validation_refs: [lake env lean ResearchLean/AG/DoctrineFiberProduct/SchemaWitnesses.lean — exit 0, 48 declarations standard axioms only; lake env lean ResearchLean/AG/DoctrineFiberProduct/BCAuthoredObjectCollapse.lean — exit 0, 24 declarations standard axioms only; lake env lean ResearchLean/AG/DoctrineFiberProduct/IdempotentExchangeWitnessPacket.lean — exit 0, 5 declarations standard axioms only; lake build ResearchLean.AG.DoctrineFiberProduct.SchemaWitnesses ResearchLean.AG.DoctrineFiberProduct.BCAuthoredObjectCollapse — targeted dependency construction only, exit 0; git diff --check — exit 0]
  blocking_findings: []
  next_obligation: Refix the PR head, repeat the full standard four-lane review, then emit a schema-complete replacement packet and run four wholly fresh completion lanes.
```

## Cycle 19 — cycle bridge and direct-owner closure

```yaml
ledger_type: target_cycle_result
goal: G-116-aat-idempotent-exchange-structure
cycle: 19
goal_blob_sha: 9b3a1157889b33d5b2ce279365f3bec9f6e3bed6
base_oid: 4b1602d8ff28b9f50422da31b92bff21cb2a8300
tracking_issue: 4345
report_path: research/reports/G-116-aat-idempotent-exchange-structure.md
selection:
  proof_state_ref: Fresh full standard four-lane review over 4b1602d8ff28b9f50422da31b92bff21cb2a8300
  proof_dag_predecessors: [AtomFoundation.Transport, SchemaWitnesses, BCAuthoredObjectCollapse, IdempotentExchangeWitnessPacket]
  proof_obligation: Eliminate the residual definitional reduction between hasCycleWitness and hasDependencyCycle, replace direct acyclic conjunction projection by a named fixture theorem, and directly import both new theorem owners used by the witness.
  selection_reason: Math B found that Cycle 18 still used definitional equality for the cyclic/acyclic facts; Lean B found two newly used theorem owners remained transitive imports.
  expected_result_type: target-completion-candidate
  lean_targets: [ResearchLean/AG/DoctrineFiberProduct/BCAuthoredObjectCollapse.lean, ResearchLean/AG/DoctrineFiberProduct/IdempotentExchangeWitnessPacket.lean]
  artifact_targets: [research/reports/G-116-aat-idempotent-exchange-structure.md]
  risks: [hiding an unfold behind exact-term conversion, adding a theorem without a direct owner import, changing clause h]
  unchecked: [fresh full standard fixed-head PR review, schema-complete replacement final packet, four wholly fresh completion lanes, completion ledger, CI, merge, durable synchronization]
result:
  proposed_result_type: target-completion-candidate
  proof_obligation_delta: BCAuthoredObjectCollapse now owns named cyclic and acyclic dependency-cycle facts. WitnessPacket uses those facts and the configuration-congruence theorem without reducing either external predicate, and directly imports AtomFoundation.Transport and SchemaWitnesses for the remaining named transport theorems.
  completion_candidate: yes
  implementation_oids: [17160a978abfb86ff344906857f55a9bf2ea7ca6]
  lean_artifacts: [finiteModel_object_hasDependencyCycle, finiteModel_acyclicObject_not_hasDependencyCycle]
  evidence: [BCAuthoredObjectCollapse exit 0 with 26 declarations standard axioms only, WitnessPacket exit 0 with 5 declarations standard axioms only, target no-unfold source inspection, direct theorem-owner imports, unchanged fixed GOAL blob]
  claim_mapping:
    theorem_names: [finiteAxisFold_cyclic_configuration_ne_acyclic, finiteAxisFold_idempotentExchange_witnessPacket]
    source_labels: [G-116(h), Lean quality no-unfold and import ownership rules]
    conjuncts: [named cyclic fact, named acyclic fact, configuration congruence, direct transport and schema owners]
    undischarged_assumptions: []
    acceptance_point: The fixed witness statement is unchanged; all cycle and transport reasoning in the target proof now consumes named theorems through direct imports.
    port_status: not-applicable
audits:
  premise_delta:
    discharged: [hasCycleWitness-to-hasDependencyCycle definitional conversion, direct projection from acyclic predicate body, transitive Transport theorem import, transitive SchemaWitnesses theorem import]
    remaining: []
  certificate_provenance:
    discharged: [cyclic and acyclic fixture facts have named source theorems]
    unresolved: []
  proof_use:
    used: [finiteModel_object_hasDependencyCycle, finiteModel_acyclicObject_not_hasDependencyCycle, finiteModel_hasDependencyCycle_iff_of_configuration_eq, transportArchitectureObject_configuration, finiteModelDoctrineFromFixture_configuration_transport]
    unused: [target-local reduction of FiniteModel.hasCycleWitness or FiniteModel.hasDependencyCycle]
  structure_field_escape: none-found
  route_integrity: pass
  target_fitting: none-found
  vacuity: none-found
  one_way_as_equivalence: none-found
  goal_or_report_reinterpretation: none-found
  validation_refs: [lake env lean ResearchLean/AG/DoctrineFiberProduct/BCAuthoredObjectCollapse.lean — exit 0, 26 declarations standard axioms only; lake env lean ResearchLean/AG/DoctrineFiberProduct/IdempotentExchangeWitnessPacket.lean — exit 0, 5 declarations standard axioms only; targeted dependency construction for BCAuthoredObjectCollapse — exit 0; git diff --check — exit 0]
  blocking_findings: []
  next_obligation: Refix the PR head and body, repeat the fresh full standard four-lane review, then publish a schema-complete replacement packet and run four wholly fresh completion lanes.
```
