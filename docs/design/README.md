# 個別設計メモ

このディレクトリには、全体方針から切り出した個別 design / protocol 文書を置く。

## 文書一覧

| 文書 | 区分 | 用途 |
| --- | --- | --- |
| [Sig0 extractor v0 設計](sig0_extractor_design.md) | tooling design / empirical hypothesis | Lean module import graph から Signature v0 JSON を作る最小 extractor と、Lean `ComponentUniverse` との責務境界を整理する。 |
| [Signature 実証プロトコル](empirical_protocol.md) | empirical protocol | Signature と PR / issue / incident metadata を結合し、変更波及・レビューコスト・障害修正との関係を検証する手順を固定する。 |
| [ArchitectureSignature v1 後半戦まとめ](signature_v1_wrapup.md) | Lean schema / design decision | v0 互換軸、v1 core、optional extension axis の責務境界をまとめる。 |
| [relationComplexity 設計](relation_complexity_design.md) | tooling design / empirical hypothesis | 状態遷移代数層の複雑度を workflow observation として測る方針を整理する。 |
| [runtimePropagation 設計](runtime_propagation_design.md) | Lean executable metric / tooling boundary | 0/1 `RuntimeDependencyGraph` 上の propagation radius と runtime metadata の境界を整理する。 |
| [Projection soundness と exact projection の使い分け](projection_exact_soundness.md) | Lean bridge design | `ProjectionSound` で足りる主張と `ProjectionExact` が必要な refinement を分ける。 |
| [Observation bridge と projection bridge の関係](observation_projection_bridge.md) | Lean bridge design / future proof obligation | projection bridge と observation bridge を局所契約層で並列に扱う方針を整理する。 |
| [spectral radius bridge 設計](spectral_radius_bridge.md) | Lean bridge / empirical boundary | `rho(A)` の構造的 theorem と変更・障害コストの empirical claim を分離する。 |
