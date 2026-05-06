# AAT Tooling Documentation

このディレクトリは、AAT の理論を実用 artifact、schema、workflow、検証境界へ落とす
tool 側の文書群である。

数学理論の第一級本文は `docs/aat/` に置く。tool 側文書は理論を参照してよいが、
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
10. [Schema compatibility](schema_compatibility.md)
11. [Examples](examples.md)
12. [Roadmap](roadmap.md)

## 文書の層

Tooling docs は、変化の速さごとに分ける。

| 層 | 文書 | 役割 |
| --- | --- | --- |
| Stable-ish spec | `air.md`, `claim_boundary.md`, `signature_artifacts.md`, `schema_compatibility.md` | artifact と claim boundary の中核 schema。 |
| Evolving design | `extraction.md`, `reports.md`, `workflows.md`, `theorem_preconditions.md`, `repair_suggestion.md`, `examples.md` | command、report、検証、運用 flow。 |
| Mutable planning | `roadmap.md` | phase、standardization target、拡張候補。 |

## 旧入口との関係

旧 `docs/aat_v2_tooling_design.md` は、既存リンクと schema catalog のための薄い入口として残す。
本文の source of truth はこの `docs/tooling/` 以下である。

## 基本境界

- tool output は Lean theorem ではない。
- extractor output は `ComponentUniverse` と同一ではない。
- measured zero と unmeasured を混同しない。
- empirical correlation を formal claim に昇格しない。
- schema migration で non-conclusions、coverage、exactness boundary を落とさない。
