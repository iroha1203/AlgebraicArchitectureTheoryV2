# SFT 編集ガイドライン

この文書は `docs/sft` と SFT 関連 Lean / tooling 境界を編集するときの作業方針をまとめる。

> 注記(2026-07-04): SFT v2 全面改訂が進行中である。`software_field_theory.md` は v2
> (P3: 序・第I〜IV部・第VI部・第IX〜X部・付録が完全。第V/VII/VIII部は予告)であり、
> `aat_interface.md`・本ガイドライン・README は P5 で v2 化する。
> 設計の正典は [SFT v2 理論骨格ノート](../note/sft_development_spacetime_dynamics_skeleton.md)。
> 以下の記述のうち ForecastCone / ConsequenceEnvelope 等の旧語彙に関する規律は、
> v1 資産(archive、凍結された `Formal/Arch/Evolution/`、FieldSig)にのみ適用する。

## 位置づけ

- SFT は field-shaped software evolution の計算理論である。
- SFT は AAT の architecture object、operation、invariant、obstruction witness、signature、theorem boundary / non-conclusions を観測量・制約・制御入力として使う。
- SFT は AAT の数学的核を置き換えない。AAT から SFT への依存は片方向として保つ。
- AAT は Atom を公理とする純粋数学理論であり、測定境界は SFT / ArchSig / empirical artifact 側にある。
  SFT 側でも、AAT の外部にある観測限界を AAT の未完了 theorem として扱わない。
- `docs/sft/software_field_theory.md` は SFT 本文、`docs/sft/aat_interface.md` は AAT / SFT 境界の source of truth である。
- `docs/sft/software_field_theory.md` と `docs/sft/aat_interface.md` は SFT / interface の根幹文書である。ユーザーの明示的な指示なしに更新しない。
- 文書 lifecycle は [repository documentation guideline](../guideline.md) に従う。SFT の恒久情報は
  現行本文、interface、台帳、artifact contract に置く。

## claim discipline

- ForecastCone、ConsequenceEnvelope、proposal accounting、organization field、AI governance は、明示された computable core と claim boundary の下で扱う。
- forecast、probability、causal reading、safety、CI/Test/human review との関係は、明示された model /
  dataset / operational artifact に相対化して扱う。
- empirical dataset、operational feedback、calibration artifact は、相関・観測・仮説を因果 theorem と混同しない。
- Lean theorem claim として読める範囲は AAT / Lean 側に置く。SFT docs で theorem claim に触れる場合は、AAT数学本文と対応する `Formal/` declaration を確認する。
- ArchSig / FieldSig 由来の report は、選ばれた evidence contract の中で語れる肯定的な conclusion として読む。
  語れない外側を一般的な non-conclusion や残タスクとして増幅しない。
- レビューやタスク整理では、SFT 文書が定義した artifact、typed conclusion、accessor theorem、
  calibration step だけを完了条件にする。現実の未来全体や因果全体を、未完了タスクとして持ち出さない。

## 編集方針

- SFT 固有語彙は、危険さと魅力のある研究語彙として丁寧に定義する。特に field、force、attractor、basin、ForecastCone、ConsequenceEnvelope は計算可能な読みへ接続する。
- AAT / ArchSig / FieldSig の境界を曖昧にしない。
- AI agent や review / CI を完全性の証明として扱わず、field を制御する artifact / intervention として扱う。
- outreach や website 向けの説明を SFT 本文へ混ぜない。公開コピーは `website/` または `outreach/` 側で扱う。

## 検証

docs-only 変更でも、AAT theorem status、tool schema、website copy への影響を確認する。

```bash
git diff --check
rg -nP "[\x{200B}-\x{200F}\x{202A}-\x{202E}\x{2066}-\x{2069}]" <changed-files>
```

Lean source や FieldSig behavior に触れた場合は、変更範囲に応じて次も実行する。

```bash
lake build
cargo test --manifest-path tools/fieldsig/Cargo.toml
```
