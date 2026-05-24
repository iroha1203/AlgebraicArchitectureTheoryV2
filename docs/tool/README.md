# AAT Tooling Documentation

このディレクトリは、AAT の理論を実用 artifact、schema、workflow、検証境界へ落とす
tool 側の文書群である。

第一級理論本文は `docs/aat/mathematical_theory.md`, `docs/sft/aat_interface.md`,
`docs/sft/software_field_theory.md` に置く。tool 側文書は理論を参照してよいが、
理論本文は tool artifact、CI、PR、extractor、schema version に依存しない。

## 読む順序

1. [Tooling principles](principles.md)
2. [AIR](air.md)
3. [Claim boundary](claim_boundary.md)
4. [Signature artifacts](signature_artifacts.md)
5. [Reports](reports.md)
6. [Extraction](extraction.md)
7. [Workflows](workflows.md)
8. [Theorem precondition checks](theorem_preconditions.md)
9. [Repair suggestion](repair_suggestion.md)
10. [ArchMap PRD](archmap_prd.md)
11. [ArchSig / ArchMap PRD v2](archsig_archmap_prd_v2.md)
12. [ArchSig / ArchMap PRD v3](archsig_archmap_prd_v3.md)
13. [Schema compatibility](schema_compatibility.md)
14. [SoftwareField reconstruction protocol](software_field_reconstruction_protocol.md)
15. [SFT calibration and benchmark protocol](sft_calibration_benchmark.md)
16. [Examples](examples.md)
17. [Roadmap](roadmap.md)

## Tooling capability surface

Tooling docs は、実行できる command / artifact / workflow と、研究・校正・adapter gap を
分けて読む。ここでいう surface は website 向けの製品説明ではなく、tooling の現在の
観測能力と non-conclusion boundary を管理するための区分である。

| Surface | 主な文書 | 現在の tooling capability | Remaining gaps |
| --- | --- | --- | --- |
| ArchSig Core | `signature_artifacts.md`, `extraction.md`, `tools/archsig/README.md` | Lean / Python import graph scan、Sig0 validation、snapshot、signature diff。 | call graph、data dependency、dynamic import、plugin loading、framework semantics adapter。extractor completeness は主張しない。 |
| ArchSig Review | `air.md`, `reports.md`, `claim_boundary.md`, `theorem_preconditions.md`, `archmap_prd.md`, `archsig_archmap_prd_v2.md`, `archsig_archmap_prd_v3.md` | AIR、theorem precondition check、Feature Extension Report、policy decision、PR comment、baseline suppression、PR quality analysis。supplied JSON の ArchMap validation と AIR projection は実装済み。v2 PRD は ArchMap を AAT / SFT への準同型写像的 object として読み、LLM-readable output を product surface にする。v3 PRD は CI / PR quality analysis を ArchMap 主体の workflow として分離する。 | organization policy calibration、review workflow tuning、任意 invariant の自動判定。ArchMap validation pass は Lean theorem ではない。 |
| ArchSig SFT | `roadmap.md`, `workflows.md`, `software_field_reconstruction_protocol.md`, `sft_calibration_benchmark.md`, `ai_proposal_governance.md`, `archsig_archmap_prd_v2.md`, `archsig_archmap_prd_v3.md`, `tools/archsig/docs/artifacts-and-boundaries.md` | Markdown PRD / Spec / Issue / AI proposal、GitHub Issue JSON、AI proposal JSON から bounded forecast artifact と `ConsequenceEnvelope` を生成する pipeline。`SoftwareFieldEstimate` reconstruction、calibration / benchmark protocol、AI proposal governance は trace と observed refs の照合境界を定義する。v2 PRD は ArchMap-derived SFT input から `ForecastCone` / `ConsequenceEnvelope` を計算する方向を固定する。v3 PRD は `intentmap-v0` と `intent-archmap-alignment-v0` を validation し、`intent-forecast` で forecast cone へ接続する。 | real dataset calibration、framework semantics adapter。AI policy compliance や `ForecastCone` は point prediction / architecture lawfulness ではない。 |
| ArchSig Operational | `reports.md`, `workflows.md`, `software_field_reconstruction_protocol.md`, `sft_calibration_benchmark.md`, `tools/archsig/docs/operational-feedback.md` | PR history / feature / outcome dataset、B10 daily ledger、calibration、threshold、ownership、repair adoption、incident correlation、hypothesis refresh artifacts。 | 実 dataset での継続 calibration、private / missing data boundary、incident / rollback / MTTR との組織別運用接続。correlation は因果 theorem ではない。 |

## 文書の層

Tooling docs は、変化の速さごとに分ける。

| 層 | 文書 | 役割 |
| --- | --- | --- |
| Stable-ish spec | `air.md`, `claim_boundary.md`, `signature_artifacts.md`, `schema_compatibility.md` | artifact と claim boundary の中核 schema。 |
| Evolving design | `extraction.md`, `reports.md`, `workflows.md`, `theorem_preconditions.md`, `repair_suggestion.md`, `archmap_prd.md`, `archsig_archmap_prd_v2.md`, `archsig_archmap_prd_v3.md`, `software_field_reconstruction_protocol.md`, `sft_calibration_benchmark.md`, `examples.md` | command、report、検証、運用 flow。 |
| Mutable planning | `roadmap.md` | phase、standardization target、拡張候補。 |

## 第一級理論との関係

理論本文は [AAT 数学理論](../aat/mathematical_theory.md)、
[AAT / SFT Interface](../sft/aat_interface.md)、
[ソフトウェアの場の理論](../sft/software_field_theory.md) に置く。
tool 側の source of truth はこの `docs/tool/` 以下である。
旧 `docs/aat_v2_tooling_design.md` は archive に退避済みであり、現行入口としては使わない。

## 基本境界

- tool output は Lean theorem ではない。
- extractor output は `ComponentUniverse` と同一ではない。
- measured zero と unmeasured を混同しない。
- empirical correlation を formal claim に昇格しない。
- schema migration で non-conclusions、coverage、exactness boundary を落とさない。
