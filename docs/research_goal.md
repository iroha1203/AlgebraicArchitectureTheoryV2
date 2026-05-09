# 研究の全体目標

この文書は、AAT v2 の研究プログラム全体を読むための入口である。
数学的な第一級本文は、次の 3 文書に固定する。

1. [AAT 数学理論](aat/mathematical_theory.md)
2. [AAT / SFT Interface](sft/aat_interface.md)
3. [ソフトウェアの場の理論](sft/software_field_theory.md)

この 3 文書は、研究上の source of truth として扱う。
Lean 実装 status、proof obligation、tooling schema、empirical protocol、PRD、旧草案は
補助文書として分離する。

## 一文で言うと

AAT v2 の目標は、設計原則を「アーキテクチャ不変量を保存・改善する操作」として扱い、
品質を単一スコアではなく、不変量の破れを示す多軸シグネチャとして診断する理論と
ツールチェーンを作ることである。

SFT はその上で、要求、仕様、Issue、PR、review、CI、組織、AI、運用 feedback、
lifecycle decision が、到達可能な architecture future をどう変えるかを扱う。

```text
AAT formalizes the local algebra of software architecture.
AAT / SFT Interface fixes the one-way boundary.
SFT makes software evolution computable.
```

## 第一級文書

| 文書 | 役割 |
| --- | --- |
| [AAT 数学理論](aat/mathematical_theory.md) | `ArchitectureObject`, operation, invariant, obstruction witness, signature, theorem boundary, repair, path, diagram filling, analytic representation を整理する数学本文。 |
| [AAT / SFT Interface](sft/aat_interface.md) | SFT が AAT から借りる概念、片方向依存、禁止される読み替えを固定する境界文書。 |
| [ソフトウェアの場の理論](sft/software_field_theory.md) | PRD / Spec / Issue / PR / Review / CI / organization / AI / lifecycle を field, force, trajectory, control として扱う計算理論。 |

補助入口として、[docs README](README.md)、[AAT directory README](aat/README.md)、
[SFT directory README](sft/README.md) を置く。ただし、理論本文そのものは上の 3 文書である。

## 層の分担

```text
AAT gives laws.
ArchSig measures state.
SFT predicts trajectories.
AI proposes operations.
Review / CI controls transitions.
```

| 層 | 扱うもの | 主な文書 |
| --- | --- | --- |
| AAT | architecture object、operation、invariant、obstruction witness、signature、theorem boundary、non-conclusions | [AAT 数学理論](aat/mathematical_theory.md) |
| Interface | AAT theorem を SFT 側でどう読めるか、何を読んではいけないか | [AAT / SFT Interface](sft/aat_interface.md) |
| SFT | field model、ArtifactMediatedChange、ForecastCone、ConsequenceEnvelope、governance intervention、FieldUpdate | [ソフトウェアの場の理論](sft/software_field_theory.md) |
| Lean 形式化 | 実装済み API、証明済み定理、defined only な構造、future proof obligation | [証明義務と実証仮説](aat/proof_obligations.md), [Lean 定義・定理索引](aat/lean_theorem_index.md) |
| Tooling / ArchSig | AIR、extractor、Signature artifact、Feature Extension Report、claim boundary、workflow | [AAT Tooling Documentation](tool/README.md) |
| Empirical | Signature / report と review cost、incident scope、変更波及、AI shortcut との関係 | `docs/empirical/` |

## 研究が答えたい問い

- この architecture operation は、選択された invariant を保存しているか。
- 破れているなら、どの obstruction witness がそれを示しているか。
- その破れはどの ArchitectureSignature axis に現れるか。
- AAT theorem boundary の下で何を結論でき、何を non-conclusion として残すべきか。
- AAT の局所主張を、SFT の forecast / governance 側でどう安全に使えるか。
- この PRD / Spec / Issue はどの operation support と policy を誘導するか。
- 生成された ConsequenceEnvelope は、どの architecture region と signature axis を含むか。
- Review / CI / policy は shortcut をどこで拒否・射影・減衰し、field memory をどう更新するか。
- AI agent の proposal support は、bounded field model と theorem boundary の中に収まっているか。

## Architecture Signature の位置づけ

`ArchitectureSignature` は、アーキテクチャ品質を単一スコアへ潰すためのものではない。
分解可能性、依存伝播、境界健全性、抽象化、観測可能性、状態遷移、実行時依存、
実証的コストなどを分けて読むための多軸診断 artifact である。

ArchSig は、AAT 的観測量を抽出し、SFT 的予測・制御に渡す計測層である。

```text
codebase / PR
  -> signature axes
  -> obstruction witnesses
  -> theorem boundary status
  -> ForecastCone / ConsequenceEnvelope boundary
  -> governance feedback
```

## 設計原則の読み方

AAT v2 では、SOLID、Layered / Clean Architecture、Event Sourcing、Saga、
Circuit Breaker、Replicated Log などを、同じ階層の万能原理として扱わない。

- SOLID: 局所契約層。
- Layered / Clean Architecture: 大域構造層。
- Event Sourcing / Saga / CRUD: 状態遷移代数層。
- Circuit Breaker / Replicated Log: 実行時依存・分散収束層。

設計原則は、それがどの invariant、operation、observation、theorem boundary、
governance intervention に対応するかを明示して読む。

## Lean と実証の分担

Lean では、定義が明確で全称命題として扱える構造的事実を証明する。
graph、walk、reachability、projection、observation、lawfulness bridge、
finite universe 上の executable metric と theorem の接続などである。

一方、実コード extractor の完全性、Signature と変更コストの相関、runtime exposure と
incident scope の関係、relation complexity と運用リスクの関係、ForecastCone の精度、
organization field や AI agent policy の効果は、実証研究または tooling boundary の問題として扱う。

どの主張が `proved`、`defined only`、`future proof obligation`、
`empirical hypothesis` なのかは、[証明義務と実証仮説](aat/proof_obligations.md) を参照する。

## 読む順序

1. [AAT 数学理論](aat/mathematical_theory.md)
2. [AAT / SFT Interface](sft/aat_interface.md)
3. [ソフトウェアの場の理論](sft/software_field_theory.md)
4. [証明義務と実証仮説](aat/proof_obligations.md)
5. [Lean 定義・定理索引](aat/lean_theorem_index.md)
6. 必要に応じて [AAT Tooling Documentation](tool/README.md), `docs/empirical/`
