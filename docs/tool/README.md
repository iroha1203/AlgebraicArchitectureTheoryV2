# Tool Docs

`docs/tool/` は ArchSig v0.6.0・ArchView・FieldSig の製品コンセプト、仕様（contract）、編集ガイドラインを扱い、各ツールが何を入力して何を計算・生成するかを定める（AAT の数学的主張は [理論本文](../aat/algebraic_geometric_theory/README.md) にある）。

## ArchSig v0.6.0 の入口

- [Tooling 編集ガイドライン](guideline.md): ツールの責務範囲、設計・Rust 品質・肥大化停止線、テストと代表規模ベンチマークの規律。
- [ArchSig v0.6.0 製品コンセプト](archsig_v0_6_0_concept.md): AI Agent SKILL を通して AAT の構造を解析する、AI ネイティブなアーキテクチャ計算基盤の製品像と設計原則。
- [ArchSig v0.6.0 I/O 仕様](archsig_v0_6_0_io/README.md): Atom 定義・Law・ArchMap・問い・計算範囲・実行・型付き結果の実装要件。
- [Atom と Law のエンジン設計](archsig_atom_law_engine/README.md): 計算核の設計判断と具体例。
- [ArchSig v0.6.0 実装 README](../../tools/archsig_v0.6.0/README.md): クレート構成、ビルド、CLI 実行、観測補助、テスト手順。
- [同梱観測 SKILL](../../tools/archsig_v0.6.0/skills/archsig-observe/SKILL.md): 実コードから Atom 定義・Law・ArchMap を構成し、CLI 計算へ接続する製品 SKILL。

## ツール構成

| ツール | 責務 | 主な入口・実装 |
| --- | --- | --- |
| ArchSig（v0.6.0） | 共通の Atom 定義・Law・ArchMap と問いから、対象・操作・対応・局所構造・診断・修復候補・必要観測を計算する | `tools/archsig_v0.6.0/`、[I/O 仕様](archsig_v0_6_0_io/README.md) |
| ArchView | ArchMap の Atom 構造を可視化し、ArchSig の分析結果を重ねてソース参照へ接続する | `tools/archview/`、[ArchView README](../../tools/archview/README.md) |
| FieldSig | ArchSig の計測出力と開発ワークフローの証拠を、SFT の進化計測入力として読む | `tools/fieldsig/`、[FieldSig README](../../tools/fieldsig/README.md) |

## ArchView

ArchView は、ArchMap だけでコードベース理解を成立させる Atom-native Architecture Atlas であり、次の3責務を持つ。

1. ArchMap の Atom / Context / Cover からアーキテクチャ構造を理解できる形にする。
2. ArchSig が供給した分析結果を同じ幾何上のオーバーレイとして表示する。
3. finding の支持 Atom からソース参照を解決し、file / symbol / line へ到達させる。

ArchView は構造判定・関係・ソース記号・修復提案を独自に生成せず、AAT 構造解析の判定・結論には ArchSig の計算結果を用いる。
現行実装と再構築の差は [ArchView README](../../tools/archview/README.md) に置く。

## Sources of truth

| 領域 | 参照先 |
| --- | --- |
| Tooling 編集規律・品質・検証 | [guideline.md](guideline.md) |
| ArchSig v0.6.0 仕様 | [ArchSig v0.6.0 I/O 仕様](archsig_v0_6_0_io/README.md) |
| ArchSig v0.6.0 実装 | [実装 README](../../tools/archsig_v0.6.0/README.md)、`tools/archsig_v0.6.0/` と同ワークスペースの tests |
| ArchView | [tools/archview/README.md](../../tools/archview/README.md) と UI / E2E tests |
| FieldSig | [tools/fieldsig/README.md](../../tools/fieldsig/README.md)、serialized schema、tests |

PRD や設計ノートを恒久仕様として参照しない。実装済み仕様は現行仕様書・ソース・テスト・フィクスチャへ置く。
