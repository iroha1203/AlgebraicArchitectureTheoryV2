# 代数的アーキテクチャ論 V2

このリポジトリは、**Algebraic Architecture Theory V2** の Lean 形式化と研究ノートを管理するための独立リポジトリです。

## 大目標

本プロジェクトの中心主張は次の通りです。

> 設計原則は、アーキテクチャ不変量を保存・改善する操作である。
>
> アーキテクチャ品質は、不変量の破れを多軸シグネチャとして評価する。

ここでいう「設計原則」は、単なる経験則ではなく、依存構造・抽象化・観測可能な振る舞い・境界保存などの不変量に作用する操作として扱います。

また、品質評価は単一スコアに潰さず、循環、SCC、深さ、fanout、境界違反、抽象違反などの複数軸からなる `ArchitectureSignature` として扱います。

最終的には、アーキテクチャレビューを「感想」から「診断」に変える理論とツールを目指します。つまり、設計原則が守る不変量、コードベース上で破れている不変量、その破れと変更波及・障害修正・レビューコストの関係を説明できる状態を目標にします。詳細は [研究の最終ゴール](docs/research_goal.md) にまとめています。

## 研究方針

V2 では、次の三層を分けて進めます。

1. **構文的構造**
   - コンポーネントを頂点、依存関係を有向辺として表す。
   - `Walk`, `Reachable`, thin category, projection, observation を基礎概念にする。

2. **設計原則の分類**
   - SOLID, Layered Architecture, Clean Architecture などを、どの不変量を保証・保存・改善するかで分類する。
   - SOLID は局所契約層、Layered は大域構造層として扱い、役割を混同しない。

3. **定量評価**
   - 不変量の破れを `ArchitectureSignature` として多軸評価する。
   - 実証的な相関は Lean の定理ではなく、別途 empirical hypothesis（実証仮説）として扱う。

Lean では、定義が明確で全称命題として扱える構造的事実を証明します。現実コードベースにおける変更コストや障害修正時間との相関は、実証研究の仮説として分離します。

## フェーズ

現在のタスク管理は GitHub Issues / Milestones に移行しています。大まかな進行順は次の通りです。

1. **Finite Universe Bridge**
   - finite-list executable metrics（有限リスト上で実行可能な指標）を、証明付きの有限 universe（測定対象の有限集合）と接続する。
   - `ComponentUniverse` / `FiniteArchGraph` の役割分担を整理する。

2. **Path and Reachability Correctness**
   - `Walk` から `Path` / `SimpleWalk` を分離する。
   - 有限 universe 上で `Reachable` なら bounded path が存在することを証明する。
   - `hasCycleBool` と `HasClosedWalk` の有限 universe 上の対応を証明する。

3. **Cycle, SCC and Depth Correctness**
   - `sccSizeAt` と相互到達可能性の同値類を接続する。
   - acyclic finite graph 上の depth 指標を正当化する。

4. **Signature v0 Stabilization**
   - `ArchitectureSignature` v0 の各軸を安定化する。
   - `fanoutRisk` を `totalFanout` として扱い、`maxFanout` は将来の局所集中軸として分離する。

5. **Layering Equivalence**
   - `Acyclic + finite vertices -> StrictLayered` を証明する。
   - `Decomposable := StrictLayered` のもとで、分解可能性と非循環性の関係を整理する。

6. **Projection / Observation Invariants**
   - DIP, Strong DIP, projection exactness, representative stability の役割を整理する。
   - observation factorization と LSP の関係を発展させる。
   - SOLID を局所契約層として形式化し、それだけでは `Decomposable` が従わないことを明確にする。

7. **Path and Matrix Foundations**
   - adjacency matrix, nilpotence, DAG との bridge を作る。
   - spectral radius など解析的指標はこの後半フェーズで扱う。

8. **Empirical Signature Extraction**
   - 実コードベースから signature を抽出する tooling を検討する。
   - `ArchitectureSignature` と変更波及・レビューコスト・障害修正時間などの相関を検証する。

## 現在の Lean 形式化

初期形式化には、次の要素が含まれています。

- 依存グラフ `ArchGraph`
- walk と到達可能性 `Walk`, `Reachable`
- 到達可能性から作る thin component category
- strict layering, decomposability, acyclicity, finite propagation
- `Decomposable G := StrictLayered G`
- projection soundness / completeness / exactness
- representative stability と strong operational DIP
- observation, observation factorization, LSP compatibility
- SOLID 風局所条件だけでは decomposability が従わない反例
- `ArchitectureSignature` と componentwise risk order
- signature v0 の finite-list executable metrics（有限リスト上で実行可能な指標）
- executable metrics を `Walk` / `Reachable` に接続する proof-carrying finite component universe（証明付き有限測定 universe）

## 詳細ドキュメント

- [研究概要](docs/aat_v2_overview.md)
- [研究の最終ゴール](docs/research_goal.md)
- [設計原則の分類](docs/design_principle_classification.md)
- [証明義務と実証仮説](docs/proof_obligations.md)

## リポジトリ構成

- `Formal.lean`
  - Lean ライブラリの root module。
- `Formal/Arch`
  - 依存グラフ、到達可能性、層化、射影、観測、LSP、反例、signature などの Lean 定義と定理。
- `docs`
  - 研究概要、設計原則の分類、proof obligations、empirical hypotheses。
- `Main.lean`
  - 実行ターゲット `aatv2` の最小 entry point。
- `lakefile.toml`
  - Lake build 設定。
- `lean-toolchain`
  - Lean バージョン固定。

## Build

```bash
lake build
lake build Formal
lake exe aatv2
```

`lake exe aatv2` の出力は次の通りです。

```text
Algebraic Architecture Theory V2
```

## 証明と文書の扱い

- Lean ソースに `axiom`, `admit`, `sorry`, `unsafe` を導入しない。
- 未証明の主張は `docs/proof_obligations.md` または GitHub Issues に明示する。
- Lean で証明済みの主張、定義のみの概念、将来の証明義務、実証仮説を混同しない。
- `proof_obligations.md` は今後、GitHub Issues への索引としても使う。

## タスク管理

未解決課題は GitHub Issues で管理します。Issue は研究の依存構造に沿って milestone に割り当てます。

主な label:

- `type:definition`
- `type:lean-proof`
- `type:docs`
- `type:research-hypothesis`
- `type:tooling`
- `area:finite-universe`
- `area:reachability`
- `area:signature`
- `area:scc-depth`
- `area:layering`
- `area:projection-observation`
- `area:path-matrix`
- `area:empirical`
