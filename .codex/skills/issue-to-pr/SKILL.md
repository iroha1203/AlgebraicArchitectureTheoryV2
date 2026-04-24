---
name: issue-to-pr
description: GitHub Issue を起点に実装・検証・PR 作成まで進める。Use when the user asks Codex to handle a specific issue number, says "Issue #N を対応して", "次の Issue を選んで", "issue-to-pr", or wants an issue selected automatically and completed through a pull request.
---

# Issue to PR

GitHub Issue を起点に、タスク選定から Pull Request 作成まで進める。
このリポジトリでは、応答・コミット・PR・Issue 操作は日本語で行う。

## 入力の扱い

- Issue 番号が指定された場合は、その Issue を対象にする。
- Issue 番号がない場合は、open Issue を確認し、次の優先順で選ぶ。
  1. `priority:blocking` かつ `status:ready`
  2. milestone の依存順が早いもの
  3. 後続 Issue をブロックしているもの
  4. `status:needs-design` より `status:ready`
- 前提 Issue が完了していて着手可能なら、必要に応じて `status:blocked` を外し、`status:ready` を付ける。

## 標準手順

1. `main` を最新化する。
   - `git switch main`
   - `git pull --ff-only`
2. Issue を確認する。
   - 指定あり: `gh issue view <number>`
   - 指定なし: `gh issue list --state open`
3. 対応方針を短く説明する。
4. 専用ブランチを切る。
   - 例: `issue-6-bounded-path`
5. 実装する。
   - 既存の設計と命名を優先する。
   - Lean 定義は小さく保ち、対応関係は theorem として育てる。
   - `axiom`, `admit`, `sorry`, `unsafe` は明示的な相談なしに導入しない。
6. 必要に応じて `docs/proof_obligations.md` を更新する。
   - Lean status を `proved`, `defined only`, `future proof obligation`, `empirical hypothesis` に分ける。
   - Issue 番号や残る proof obligation を明確にする。
7. 検証する。
   - Lean 変更あり: `lake build`
   - PR 前: `git diff --check`
   - PR 前: hidden / bidirectional Unicode scan
   - 必要に応じて `axiom|admit|sorry|unsafe` scan
8. 日本語でコミットする。
9. ブランチを push する。
10. 日本語で PR を作成する。
    - 本文に概要、変更内容、確認結果を書く。
    - 対象 Issue は `Closes #N` で閉じる。
11. `gh pr checks --watch` で CI を確認する。
12. 最後に PR URL、主な変更、確認結果を日本語で報告する。

## このリポジトリ固有の注意

- `Decomposable G := StrictLayered G` を維持する。
- acyclicity, finite propagation, nilpotence, spectral conditions は定義に混ぜず、別 theorem または future proof obligation として扱う。
- `ComponentCategory` は thin category として path count / walk length を忘れる。
- 定量指標は `Walk`, `Path`, adjacency matrix, future free-category construction 側で扱う。
- executable metrics は有限な測定 universe 上の計算として定義し、graph-level facts との接続は別 theorem として証明する。
- `ComponentUniverse` は proof-carrying measurement universe として扱い、実コードベース抽出器の完全性を直接主張しない。
- Architecture Signature は単一スコアではなく、多軸診断として扱う。

## hidden Unicode scan

必要に応じて対象範囲を絞って実行する。

```bash
LC_ALL=C rg -n "[\x{200B}\x{200C}\x{200D}\x{200E}\x{200F}\x{202A}\x{202B}\x{202C}\x{202D}\x{202E}\x{2066}\x{2067}\x{2068}\x{2069}\x{FEFF}]" Formal docs README.md AGENTS.md .codex
```

## PR 本文テンプレート

```markdown
## 概要

Issue #N に対応しました。

## 変更内容

- ...

## 確認

- `lake build` 成功
- `git diff --check` 成功
- hidden / bidirectional Unicode scan で検出なし

Closes #N
```
