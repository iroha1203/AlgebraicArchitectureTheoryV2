# 研究の実装設計

GOALごとの構成・証明方針、依存関係、受入条件、既存宣言との対応を置く。
各設計は `research/designs/<goal-id>/README.md` を入口とし、詳細な対応表などを同じディレクトリに置く。

研究目的・固定target・完了条件は[GOAL](../goals/README.md)に従う。
設計には構成と検証条件を記し、進捗・判断・実行・査読の履歴はtracking IssueとPRに記録する。
証明された主張と宣言・前提・検証証拠の対応は、対応する `research/reports/<goal-id>.md` に置く。

| GOAL | 設計 | tracking Issue |
| --- | --- | --- |
| [G-124](../goals/G-124-aat-local-semantic-reconstruction.md) | [パートIII・IV：C–Eの実装設計](G-124-aat-local-semantic-reconstruction/README.md)、[再利用対応表](G-124-aat-local-semantic-reconstruction/reuse-map.md) | [#4711](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/issues/4711) |
