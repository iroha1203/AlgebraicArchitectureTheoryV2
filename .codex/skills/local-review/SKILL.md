---
name: local-review
description: ローカル差分、作業ブランチ、PR前のセルフレビューを、対象分野ひとつに絞って複数観点から行う。Use when the user asks Codex to review current local changes, staged or unstaged diffs, a commit range, a branch before opening a PR, or says "$local-review". This skill defaults to multi-agent review across four domain-specific perspectives unless the user explicitly asks for single-agent or sequential review.
---

# Local Review

現在のローカル作業を、対象分野ひとつに絞ってレビューする。GitHub PR 番号起点のレビューは `$review-pr` を使い、この skill は未コミット差分、作業ブランチ、PR 前確認、指定コミット範囲のセルフレビューを担当する。

## 基本方針

- ユーザーへの報告は日本語で行う。
- コードレビュー姿勢を取る。バグ、仕様未達、claim boundary の逸脱、テスト不足、docs drift、セキュリティや運用上のリスクを先に出す。
- Findings first で書く。重大な指摘がない場合は、無理に finding を作らず「重大な指摘なし」と明記する。
- coverage を明示する。読んだ範囲、読んでいない範囲、実行した検証、実行できなかった検証を分ける。
- 公開物に入る可能性がある code、fixture、docs、schema catalog、website、release asset、tool output contract では、個人名、ローカル絶対パス、private/internal 風の fixture 値、作業環境固有名の混入を必ず finding 候補として確認する。
- 既存の未コミット変更はユーザー変更として扱い、勝手に戻さない。破壊的操作をしない。
- AAT / Lean / ArchSig / FieldSig / Website の責務を混同しない。AAT / SFT の protected source docs は、明示依頼なしに編集しない。

## 入力と初期確認

1. 対象範囲を決める。
   - 明示されたファイル、commit range、branch、staged diff、unstaged diff を優先する。
   - 指定がなければ現在の作業ツリーと `main...HEAD` を見る。
2. 先にローカル状態を確認する。
   - `git status --short --branch`
   - `git diff --stat`
   - `git diff --name-only`
   - `git ls-files --others --exclude-standard`
   - 必要なら `git diff --cached --stat`、`git diff main...HEAD --stat`、`git diff main...HEAD --name-only`
3. PR 番号だけをレビュー対象にする依頼なら、この skill ではなく `$review-pr` を使う。

## 分野判定

ユーザーが分野を指定した場合はそれを優先する。指定がない場合は changed files から次のいずれかを選ぶ。

- AAT / Lean: `Formal/`, `Formal.lean`, `Main.lean`, `docs/aat/`, Lean theorem index、proof obligations。
- Tooling / ArchSig / FieldSig: `tools/archsig/`, `tools/fieldsig/`, `docs/tool/`, ArchSig / FieldSig 固有 skill bundle、tool workflows。
- Website / Manual: `website/`, `docs/website/`, public manual surface、static route / asset changes。
- Docs / SFT / Research Notes: `docs/sft/`, `docs/note/`, `.codex/skills/` の一般的な workflow instruction、PRD、research note、task ledger、cross-domain docs。

複数分野が混ざる場合でも、レビュー対象をひとつの主分野に寄せる。どれが主分野か判断できない場合だけ、短く確認する。

## 分野別 profile

4観点の詳細は `references/domain-review-profiles.md` を読む。各分野は必ず次の比率にする。

- リポジトリ固有ルール: 2観点
- 一般的なタスクレビュー観点: 2観点

## Multi-Agent Default

`$local-review` では、ユーザーが「並列なし」「単独レビュー」「sequential」と明示しない限り、multi-agent review をデフォルトにする。multi-agent tool が使えない環境では、同じ4観点を親 Codex が順番に確認する。

multi-agent を使う場合:

1. 親 Codex が対象範囲、主分野、changed files、diff stat を先に把握する。
2. 選ばれた分野 profile の4観点を、4つの sub-agent に分ける。
3. 各 sub-agent には担当観点、対象範囲、必要な raw context、出力形式だけを渡す。期待 finding や親の結論を渡さない。
4. 各 sub-agent は担当観点を主責務にする。ただし、担当観点から自然に見える横断的な suspicious signal は報告してよい。
5. 親 Codex は待機中に別角度の確認を進め、sub-agent 結果を統合する。複数観点で重なった finding はノイズではなく、信頼度や優先度の補強材料として扱う。
6. 親 Codex が重複、矛盾、過剰 claim、coverage gap を整理する。

## Sub-Agent Prompt 形式

sub-agent への依頼は、次の形を使う。
sub-agent はこの単一観点用形式だけに従う。下の「報告形式」は親 Codex が4観点を統合するときの形式であり、sub-agent が未担当の観点を補完してはいけない。

```text
Use the local-review skill context. Review only the assigned perspective.
Domain: <AAT / Lean | Tooling / ArchSig / FieldSig | Website / Manual | Docs / SFT / Research Notes>
Perspective: <profile perspective name>
Target: <files, diff range, or working tree scope>

Report in Japanese:
1. Findings, ordered by severity, with file/line references when available.
2. Evidence checked.
3. Tests or commands that should be run for this perspective.
4. Coverage limits.

Do not edit files. Stay anchored in the assigned perspective. If a sensitive local path, private/internal-looking fixture value, personal name, or machine-specific workspace identifier is visible, report it even if privacy is not the assigned perspective. Do not perform a full review of the other perspective or infer conclusions outside your evidence.
```

## 検証の選び方

変更範囲に応じて検証を選ぶ。

- Lean 変更: `lake build`
- ArchSig 変更: `cargo test --manifest-path tools/archsig/Cargo.toml`
- FieldSig 変更: `cargo test --manifest-path tools/fieldsig/Cargo.toml`
- Website 変更: local static preview と Playwright / link / asset / title / layout checks
- 共通: `git diff --check`
- 共通 hidden / bidi scan: `rg -nP "[\x{200B}-\x{200F}\x{202A}-\x{202E}\x{2066}-\x{2069}]" <changed-files>`
- 共通 privacy / local-path scan: changed files と public / release surface に対して `rg -n "(\\/Users\\/|\\/home\\/|C:\\\\Users\\\\|Documents\\/|HelloLean|nakahata|private\\/internal|\\/private\\/internal|\\.codex|AlgebraicArchitectureTheoryV2)" <changed-files>` を目安に確認する。正当な public asset 名などの false positive は根拠付きで除外してよい。
- Tooling / release 変更では、runtime output / schema catalog / fixtures に repo-local docs path や読めない source-of-truth path が出ていないか確認し、必要なら `aat-theory:*` や `archsig-contract:*` のような安定 ID を求める。
- Lean placeholder scan: `rg -n "\b(axiom|admit|sorry|unsafe)\b" Formal docs`

実行できない検証は、理由と残リスクとして報告する。

## 親 Codex の報告形式

1. 判定: `Needs changes`, `No major findings`, `Blocked / cannot determine`
2. Findings: 重大度順。各 finding は根拠、影響、必要な修正を含める。
3. 観点別まとめ: 4観点それぞれの確認結果。
4. 実行した検証: コマンドと結果。
5. Coverage / residual risk: 読んだ範囲、未確認範囲、未実行検証。
