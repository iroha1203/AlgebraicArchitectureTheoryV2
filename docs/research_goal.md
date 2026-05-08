# 研究の全体目標

この文書は、AAT v2 の全体目標と研究全体像を示す入口である。
数学的な定義と理論構成は [AAT](aat/README.md) と
[AAT 数学理論](aat/mathematical_theory.md) を source of truth とする。
要求、仕様、Issue、PR、組織、AI、運用、終焉を含む力学は
[SFT](sft/README.md) と [ソフトウェアの場の理論](sft/software_field_theory.md) に分離する。

## 一文で言うと

AAT v2 の目標は、機能追加によってソフトウェアアーキテクチャがどのように拡大し、
どの不変量を保存し、どの obstruction を導入するかを、証明・測定・仮定・実証を
分離して診断できる理論とツールチェーンを作ることである。

SFT はその上で、ソフトウェア進化を要求、仕様、Issue、PR、組織、AI、運用からの
force と field dynamics として扱う。

```text
AAT formalizes the local algebra of software change.
SFT studies the global field dynamics of software evolution.
```

## 中心的な見方

```text
AAT gives laws.
ArchSig measures state.
SFT predicts trajectories.
AI proposes operations.
Review / CI controls transitions.
```

AAT は、feature extension、operation、invariant、obstruction witness、
proof obligation、certificate を明示的に分ける。

SFT は、PRD、Spec、Issue、PR、review、CI、organization、AI agent、runtime feedback が
operation distribution と signature trajectory に与える作用を扱う。

## 全体構成

| 文書 | 役割 |
| --- | --- |
| [AAT](aat/README.md) | AAT の数学理論と Lean status の入口。 |
| [AAT 数学理論](aat/mathematical_theory.md) | `ArchitectureObject`, `FeatureExtension`, invariant, obstruction, signature, proof obligation, certificate, repair, path, diagram filling, analytic representation を整理する。 |
| [SFT](sft/README.md) | SFT の入口。 |
| [ソフトウェアの場の理論](sft/software_field_theory.md) | software field, force, forecast cone, dissipation, attractor engineering, organization field, AI control, lifecycle を整理する。 |
| [証明義務と実証仮説](aat/proof_obligations.md) | Lean status、未解決 proof obligation、empirical hypothesis の台帳。 |
| [Lean 定義・定理索引](aat/lean_theorem_index.md) | 現在 Lean に存在する主要な定義・定理の索引。 |

## 研究の層

| 層 | 扱うもの | 詳細 |
| --- | --- | --- |
| AAT | architecture extension、operation、invariant、obstruction witness、proof obligation、certificate | [AAT 数学理論](aat/mathematical_theory.md) |
| Lean 形式化 | 前提を明示できる構造的命題、finite universe、graph / walk / reachability、lawfulness bridge | [証明義務と実証仮説](aat/proof_obligations.md), [Lean 定義・定理索引](aat/lean_theorem_index.md) |
| ArchSig / Tooling | AIR、extractor、Signature artifact、Feature Extension Report、theorem precondition checker、CI integration | [AAT Tooling Documentation](tooling/README.md), [ArchSig tooling index](design/archsig_tooling_index.md) |
| SFT | PRD force、forecast cone、operation distribution、signature trajectory、dissipation、organization field、AI control | [ソフトウェアの場の理論](sft/software_field_theory.md) |
| 実証研究 | Signature や report と、変更波及、レビューコスト、incident scope、障害修正コストとの関係 | [Signature 実証プロトコル](design/empirical_protocol.md), `docs/empirical/` |

## 研究が答えたい問い

- この feature addition は、既存 architecture を lawful に拡大しているか。
- 既存構造は拡大後にも埋め込まれているか。
- 新機能差分は既存構造から split して取り出せるか。
- split しない場合、どの obstruction witness が妨げているか。
- どの不変量が保存され、どの不変量が破れたか。
- この PRD / Spec / Issue はどの operation distribution を誘導するか。
- PR は予測された signature delta と一致したか。
- review / CI / policy は raw force をどこで拒否・射影・減衰したか。
- AI agent は安全な operation support と certificate boundary の中で動いているか。

## Architecture Signature の位置づけ

`ArchitectureSignature` は、アーキテクチャ品質を単一スコアへ潰すためのものではない。
分解可能性、依存伝播、境界健全性、抽象化、観測可能性、状態遷移、実行時依存、
実証的コストなどを分けて読むための多軸診断 artifact である。

ArchSig は、AAT 的観測量を抽出し、SFT 的予測・制御に渡す計測層である。

```text
codebase / PR
  -> signature axes
  -> obstruction witnesses
  -> proof obligation status
  -> forecast / control feedback
```

## 設計原則の読み方

AAT v2 では、SOLID、Layered / Clean Architecture、Event Sourcing、Saga、
Circuit Breaker、Replicated Log などを、同じ階層の万能原理として扱わない。

- SOLID: 局所契約層。
- Layered / Clean Architecture: 大域構造層。
- Event Sourcing / Saga / CRUD: 状態遷移代数層。
- Circuit Breaker / Replicated Log: 実行時依存・分散収束層。

詳細な分類は [AAT 数学理論](aat/mathematical_theory.md#16-設計原則) に置く。

## Lean と実証の分担

Lean では、定義が明確で全称命題として扱える構造的事実を証明する。
graph、walk、reachability、projection、observation、lawfulness bridge、
finite universe 上の executable metric と theorem の接続などである。

一方、実コード extractor の完全性、Signature と変更コストの相関、runtime exposure と
incident scope の関係、relation complexity と運用リスクの関係、forecast cone の精度、
organization field や AI agent policy の効果は、実証研究または tooling boundary の問題として扱う。

どの主張が `proved`、`defined only`、`future proof obligation`、
`empirical hypothesis` なのかは、[証明義務と実証仮説](aat/proof_obligations.md) を参照する。

## 読む順序

1. [AAT](aat/README.md)
2. [AAT 数学理論](aat/mathematical_theory.md)
3. [SFT](sft/README.md)
4. [ソフトウェアの場の理論](sft/software_field_theory.md)
5. [証明義務と実証仮説](aat/proof_obligations.md)
6. [Lean 定義・定理索引](aat/lean_theorem_index.md)
7. 必要に応じて [個別設計メモ](design/README.md), [PRD 一覧](prd/README.md), `docs/empirical/`
