# SFT 編集ガイドライン

この文書は、`docs/sft` と、SFT に関連する Lean およびツールの連携部分を編集するときの作業方針を定める。

> 注記（2026-07-04）: SFT v2 の全面改訂が進行中である。`software_field_theory.md` は v2
> （P3: 序・第I〜IV部・第VI部・第IX〜X部・付録が完成済み、第V・VII・VIII部は予告）であり、
> `aat_interface.md`・本ガイドライン・README は P5 で v2 へ更新する。
> 以下の記述のうち `ForecastCone` や `ConsequenceEnvelope` などの旧語彙に関する規律は、
> v1 の FieldSig 資産にのみ適用する。

## 位置づけ

- SFT は、場として捉えたソフトウェア進化（field-shaped software evolution）の計算理論である。
- SFT は、AAT の architecture object、operation、不変量、obstruction witness、signature、
  および定理の適用範囲を、観測量・制約・制御入力として利用する。
- SFT は AAT の数学的な核の上に構築し、AAT → SFT の片方向依存を保つ。
- AAT の理論本体の所在は
  [AGENTS.md「基礎概念」](../../AGENTS.md#基礎概念)にある。
  実成果物の測定対象・観測方法・観測条件は SFT・ArchSig・実証データの側で定める。
- `docs/sft/software_field_theory.md` が SFT 本文であり、`docs/sft/aat_interface.md` が
  AAT / SFT 間のインタフェースを定める。
- `docs/sft/software_field_theory.md` と `docs/sft/aat_interface.md` は SFT とその接続の根幹文書であり、
  保護対象である。更新条件は [Workflow guideline](../workflow/guideline.md) の
  「保護対象(3条件)」に従う。
- SFT の恒久情報は、現行の本文、インタフェース文書、台帳、成果物仕様に置く。

## claim discipline

- `ForecastCone`、`ConsequenceEnvelope`、変更提案の集計、組織場、AI ガバナンスは、
  明示された計算可能な核と主張範囲のもとで扱う。
- 予測、確率、因果的な解釈、安全性、および CI・テスト・人間レビューとの関係は、
  明示されたモデル、データセット、運用成果物に紐づけて扱う。
- 実証データセット、運用フィードバック、キャリブレーション資料においては、
  相関・観測・仮説と因果に関する定理を明確に区別する。
- Lean の定理として主張できる範囲は AAT / Lean 側に置く。SFT の文書で定理に触れる場合は、
  AAT 数学本文と対応する `Formal/` の宣言を確認する。
- ArchSig / FieldSig のレポートは、選んだ入力（観測と法・方程式）から導かれる肯定的な結論として読む。
- レビューやタスク整理では、SFT 文書が定義した成果物、型つきの結論、アクセサ定理、
  キャリブレーション手順を完了条件とする
  （判定範囲は [Workflow guideline](../workflow/guideline.md#完了レビューの判定範囲) に従う）。

## 編集方針

- SFT 固有の語彙（特に field、force、attractor、basin、`ForecastCone`、`ConsequenceEnvelope`）は、
  計算可能な定義へ結びつけて丁寧に説明する。
- AAT・ArchSig・FieldSig それぞれの役割と分担を明確に保つ。
- AI エージェントやレビュー・CI は、場を制御する介入・成果物として位置づける。
- SFT 本文は理論・仕様の記述に集中し、外部記事や公開向けの説明は `website/` または `outreach/` 側で扱う。

## 検証

ドキュメントのみの変更でも、AAT の定理状態、ツールスキーマ、website の公開文面への影響を確認する。
PR 前の共通チェックは [Workflow guideline](../workflow/guideline.md) の「PR 前の共通確認」に従う。

Lean ソースや FieldSig の挙動に触れた場合は、変更範囲に応じて単一ファイル確認、対象モジュールの
ビルド、必要な監査を選ぶ（Lean build の必須規則は
[AAT guideline](../aat/guideline.md) の「Lean build 運用(hard rule)」にある）。

```bash
lake env lean <target-file>
lake build <module>
cargo test --manifest-path tools/fieldsig/Cargo.toml
```
