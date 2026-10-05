# 研究の実装設計

GOALごとの構成・証明方針、依存関係、受入条件、既存宣言との対応を置く。
各設計は `research/designs/<goal-id>/README.md` を入口とし、詳細な対応表などを同じディレクトリに置く。

設計時は既存の実装をまず精査し、接続部分・再利用部分・新規作成部分を整理する。

研究目的・固定target・完了条件は[GOAL](../goals/README.md)に従う。
設計には構成と検証条件を記し、進捗・判断・実行・査読の履歴はtracking IssueとPRに記録する。
証明された主張と宣言・前提・検証証拠の対応は、対応する `research/reports/<goal-id>.md` に置く。

| GOAL | 設計 | tracking Issue |
| --- | --- | --- |
| [G-133](../goals/G-133-aat-atlas-defect-composition.md) | [生成比較・欠損対象・依存関係](G-133-aat-atlas-defect-composition/README.md)、[再利用対応表](G-133-aat-atlas-defect-composition/reuse-map.md)、[台署名と普遍性](G-133-aat-atlas-defect-composition/support-signatures.md)、[指定例](G-133-aat-atlas-defect-composition/witnesses.md) | 未起票（draft） |
| [G-132](../goals/G-132-aat-visible-cycle-reflection.md) | [可視閉路・実比較・有限判定](G-132-aat-visible-cycle-reflection/README.md)、[再利用対応表](G-132-aat-visible-cycle-reflection/reuse-map.md)、[実被覆と指定例](G-132-aat-visible-cycle-reflection/witnesses.md) | [#5250](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/issues/5250) |
| [G-130](../goals/G-130-aat-relative-repair-composition.md) | [相対修復・全範囲合成・分類と再利用](G-130-aat-relative-repair-composition/README.md) | [#5132](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/issues/5132) |
| [G-131](../goals/G-131-aat-repair-observation-duality.md) | [実入力・観測・出力別最適値の対応](G-131-aat-repair-observation-duality/README.md) | [#5133](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/issues/5133) |
| [G-124](../goals/G-124-aat-local-semantic-reconstruction.md) | [パートIII・IV：C–Eの実装設計](G-124-aat-local-semantic-reconstruction/README.md)、[再利用対応表](G-124-aat-local-semantic-reconstruction/reuse-map.md) | [#4711](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/issues/4711) |
| [G-126](../goals/G-126-aat-operation-preserving-repair-quotients.md) | [A–Eの実装設計](G-126-aat-operation-preserving-repair-quotients/README.md)、[再利用対応表](G-126-aat-operation-preserving-repair-quotients/reuse-map.md)、[有限構成と費用](G-126-aat-operation-preserving-repair-quotients/finite-construction.md) | [#4945](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/issues/4945) |
| [G-127](../goals/G-127-aat-reversible-protocol-holonomy.md) | [A–Eの実装設計](G-127-aat-reversible-protocol-holonomy/README.md)、[再利用対応表](G-127-aat-reversible-protocol-holonomy/reuse-map.md) | [#4981](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/issues/4981) |
| [G-128](../goals/G-128-aat-minimal-compatibility-observations.md) | [A–Eの実装設計](G-128-aat-minimal-compatibility-observations/README.md)、[問い合わせと有限アルゴリズム](G-128-aat-minimal-compatibility-observations/query-and-greedy.md)、[再利用対応表](G-128-aat-minimal-compatibility-observations/reuse-map.md) | [#5075](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/issues/5075) |
| [G-129](../goals/G-129-aat-abelian-lifting-obstruction.md) | [A–Dの実装設計](G-129-aat-abelian-lifting-obstruction/README.md)、[3-cellと具体例](G-129-aat-abelian-lifting-obstruction/witnesses.md)、[再利用対応表](G-129-aat-abelian-lifting-obstruction/reuse-map.md) | [#5082](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/issues/5082) |
