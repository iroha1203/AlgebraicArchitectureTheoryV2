# SFT 編集ガイドライン

この文書は `docs/sft` と SFT 関連 Lean / tooling 境界を編集するときの作業方針をまとめる。

## 位置づけ

- SFT は field-shaped software evolution の計算理論である。
- SFT は AAT の architecture object、operation、invariant、obstruction witness、signature、theorem boundary / non-conclusions を観測量・制約・制御入力として使う。
- SFT は AAT の数学的核を置き換えない。AAT から SFT への依存は片方向として保つ。
- `docs/sft/software_field_theory.md` は SFT 本文、`docs/sft/aat_interface.md` は AAT / SFT 境界の source of truth である。
- `docs/sft/software_field_theory.md` と `docs/sft/aat_interface.md` は SFT / interface の根幹文書である。ユーザーの明示的な指示なしに更新しない。

## claim discipline

- ForecastCone、ConsequenceEnvelope、proposal accounting、organization field、AI governance は、明示された computable core と claim boundary の下で扱う。
- forecast correctness、probability、causal correctness、global safety、CI/Test/human review の置換を主張しない。
- empirical dataset、operational feedback、calibration artifact は、相関・観測・仮説を因果 theorem と混同しない。
- Lean theorem claim として読める範囲は AAT / Lean 側に置く。SFT docs で theorem boundary に触れる場合は、対応する `docs/aat/proof_obligations.md` や `docs/aat/lean_theorem_index.md` も確認する。

## 編集方針

- SFT 固有語彙は、危険さと魅力のある研究語彙として丁寧に定義する。特に field、force、attractor、basin、ForecastCone、ConsequenceEnvelope は計算可能な読みへ接続する。
- AAT / ArchSig / FieldSig の境界を曖昧にしない。
- AI agent や review / CI を完全性の証明として扱わず、field を制御する artifact / intervention として扱う。
- outreach や website 向けの説明を SFT 本文へ混ぜない。公開コピーは `website/` または `docs/outreach/` 側で扱う。

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
