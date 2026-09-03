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
    undischarged_assumptions: [all target clauses except (b)]
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
