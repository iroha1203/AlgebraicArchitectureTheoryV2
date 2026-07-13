# ArchSig Artifacts And Boundaries

ArchSig current artifacts are the v0.5.2 finite-poset-site ArchMap,
LawPolicy-selected measurement profile, measurement packet, compare report,
gate report, summary, insight report, viewer data, and run manifest.

| Artifact | Schema | Boundary |
| --- | --- | --- |
| ArchMap | `archmap/v0.5.2` | Source-grounded Atom observations, contexts, covers, declared sources, and fixed extraction doctrine. It does not select laws or assert global correctness. |
| LawPolicy | `law-policy/v0.5.2` | Selects evaluator manifests, laws, measurement profiles, policies, basis refs, and non-conclusions. |
| Normalized ArchMap | `normalized-archmap/v0.5.2` | Canonical finite-poset-site normalization for current analysis runs. |
| Measurement packet | `archsig-measurement-packet/v0.5.2` | Current AG measurement handoff. It carries structural verdicts, computed invariants, analytic readings, assumptions, and non-conclusions as bounded evidence. |
| Summary | `archsig-analysis-summary.json` | Conclusion-first compact reading surface for LLM and human review. |
| Insight report / brief | `archsig-insight-report.json`, `archsig-insight-brief.md` | Prioritized inspection queue and boundary digest derived from the measurement run. |
| Viewer data | `archsig-atom-viewer-data/v0.5.2` | Bounded ArchView projection. It adds no new structural verdict. |
| Run manifest | `archsig-run-manifest/v0.5.2` | Generated artifact list, input digests, validation result summary, claim boundary, and run metadata. |
| Comparison report | `archsig-comparison-report/v0.5.2` | Compares two current run directories and records verdict transitions, comparability, and change categories. |
| Gate report | `archsig-gate-report/v0.5.2` | Applies gate policy to a measurement packet and optional comparison report. This is the CI decision surface. |

FieldSig handoff uses `archsig-measurement-packet/v0.5.2`.
