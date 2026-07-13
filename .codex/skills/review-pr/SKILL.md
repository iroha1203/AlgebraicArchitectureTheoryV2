---
name: review-pr
description: 実装完了後の最終スナップショットを対象に、GitHub PR番号を受け取り、Issue・CI・変更責務を確認し、対応する敵対レビューSKILLへ委譲してマージ可否を統合し、監査コメントを投稿する。"$review-pr PR-number"、最終PRレビュー、マージ可否判定で使う。
---

# Review PR

GitHub PR のマージゲート。紐づく Issue の受け入れ要件・CI 状態の照合は本体で
行い、**内容レビューは分野別の敵対レビュー SKILL へ渡す**。

## 必須契約

`.codex/skills/_shared/review-protocol.md` と
`.codex/skills/_shared/refutation-checklist.md` を読み、委譲結果の資格、
fail-closed、反証試行、証拠資格、統合出力を適用する。

## 基本方針

- **実装者の自己申告を証拠から除外する。** PR 本文の「証明した定理」
  リスト、「セルフレビュー実施済み」チェック、台帳・checklist の記載は
  監査対象であって証拠ではない。claim mapping はレビュー側で**独立に
  再構築**し、PR 本文の申告(conjunct 対応表を含む)と**突合**する。
- PR ブランチの checkout が必要な場合は一時 worktree
  (`/tmp/aat-review-pr-<PR>`)を使う。
- 処置種別の降格を含む PR は、PRD の降格許容リストと照合する。許可外の
  降格は `Needs changes` とし、ユーザー判断事項として報告する(PRD が正)。
- 分野別レビューが未実行、実行不能、または資格条件を満たさない場合、
  本体が内容レビューを肩代わりして `No major findings` / `Mergeable` を
  合成してはならない。結果は `Blocked / cannot determine` とする。

## 手順

1. 作業ツリーと PR メタデータを確認する。
   - `git status --short --branch`
   - `gh pr view <PR> --json number,title,state,isDraft,author,baseRefName,headRefName,headRefOid,mergeStateStatus,reviewDecision,body,url,files,commits,labels,closingIssuesReferences`
   - `gh pr checks <PR>`
   - `gh pr diff <PR> --name-only`

2. 紐づく Issue を読む。
   - `closingIssuesReferences` と PR 本文の `Closes #N` を確認する。
   - 明示的な Issue がなければ「紐づく Issue 不明」としてレビュー上の
     リスクにする。
   - Issue の `受け入れ要件`、タスク型宣言、source of truth ポインタ
     (PRD 節番号・本文ラベル・移植元 theorem 名)を抜き出す。
     現行フォーム導入前のIssueでは`完了条件`を同じ契約として読む。
     `[doc]` title prefixはタスク型`docs`の宣言として扱う。
     タスク型が「移植」の PR では、移植元 theorem 名を委譲先に渡す。

3. **分野判定と委譲(このゲートの中心)。**
   changed files から分野を判定し、対応する分野別レビュー SKILL を実行する。
   分野判定はファイルパスの集合では
   なく責務で行う(各分野は自分の claim に隣接する docs を所有する):

   | 分野 | 対象 | 委譲先 |
   | --- | --- | --- |
   | AAT / Lean / 数学claim | `Formal/`、数学本文、研究GOAL、固定statement、数学claim、および Lean 実装変更に伴う `docs/aat/` 台帳整合 | `$math-lean-review` |
   | Tooling | `tools/`、`docs/tool/`、schema catalog | `$tool-review` |
   | Website | `website/`、`docs/website/` | `$website-review` |
   | Docs / governance | docs-onlyの`docs/aat/`台帳、`docs/sft/`、非数学的な`docs/note/`、PRD、README、`AGENTS.md`、`.codex/skills/`、文章主体のIssue / PR template、cross-domain docs | `$docs-review`(レビューモード) |

   - **Lean 実装(`Formal/`)を触る PR は、差分の大きさを問わず(1行でも)
     `$math-lean-review` の正式判定を必須とする。** `$math-lean-review`
     が合格を返さない限り `Mergeable` を出せない。
   - Lean 実装+`docs/aat/` 台帳更新の PR は math-lean-review のみで
     足りる(statement と台帳の一致は一体で監査する)。
   - Lean 実装を含まない `docs/aat/` 台帳更新だけの PR は docs-only として
     `$docs-review` に渡す。
   - 数学本文、研究GOAL、固定statement、数学claimを変更するPRは、Lean差分の
     有無にかかわらず `$math-lean-review` に渡す。
   - 真の分野横断(例: Lean + SFT 本文)は該当する複数分野で実行する。
   - 既知分野へ分類できないprose / governance差分は`$docs-review`へ渡す。
   - 委譲結果の資格と起動不能時の処理は共有契約を適用する。

4. 本体で照合する(委譲と並行してよい)。
   - Issue 受け入れ要件と diff の照合(条件文言と実体の対応)。
   - CI 状態(`gh pr checks`)。
   - checklist §6 の横断機械 scan(hidden/bidi、privacy / local-path、
     `git diff --check`)。
   - 必要なら統括エージェントが一時 worktree で `lake build` / cargo test を実行する。
     `lake build` は1回に限り、サブエージェントに委譲しない。

5. 統合判定する。
   - **委譲先判定の写像(合格の定義)**:
     - `math-lean-review`: 合格 = `No major findings`、または
       `Minor issues` かつ全 finding が中心 claim に触れない場合
       (その finding は監査コメントに残し、対応要否を明記する)。
       `Major revisions` / `Reject` / `Blocked` は不合格。
     - `tool-review` / `website-review` / `docs-review`:
       合格 = `No major findings` のみ。`Needs changes` / `Blocked` は不合格。
     - いずれの分野も、初回正式レビューがfindingを出した場合は、全findingの解消と
       共有契約に従う有資格な修正後確認(直接対応)が監査記録に揃った状態を
       合格と同等に扱う。資格喪失時は、該当分野の正式レビュー再実行の結果だけを
       合格判定に使う。
   - **Mergeable**: 委譲した全分野レビューが上記の意味で合格
     (Lean 系は math-lean-review の合格を含む)、Issue受け入れ要件を満たし、
     CI / 必要なローカル検証が通り、重大な未対応がない。
   - **Needs changes**: 委譲先の不合格、受け入れ要件未達、テスト不足、
     docs drift、CI failure がある。
   - **Blocked / cannot determine**: PR head を取得できない、CI 未完了、
     紐づく Issue 不明、サブエージェント起動不能、分野別レビュー未実施、
     必要な検証が実行できない。
   - **Needs changes 後の修正確認**: 修正後の確認は共有契約の
     「レビューバッチと修正後確認」に従う(直接対応の資格条件と確認subagentの
     検査義務は同節が正本)。有資格な直接対応は、finding限定の単一subagent確認と
     既存監査コメントへの追記で再判定し、分野別レビュー SKILL の全観点を
     再委譲しない。資格喪失時は最終スナップショットを固定し直し、資格喪失が
     生じた分野に限って手順3の委譲を再実行する(findingが出ておらず修正も
     及んでいない分野の合格結果は維持する)。

6. **監査コメントを PR に投稿する(マージ前提条件)。**
   マージ手順に進む前に、次を含むレビュー監査コメントを PR へ投稿する。
   投稿が存在しない PR はマージ手順に進めない。
   - 統合判定
   - 分野別レビューの結論、finding、反証試行、coverage limits。
     これらを取得できない分野はレビュー未完了として扱い、`Mergeable`
     として統合しない。
   - 共有契約を満たす反証試行記録
   - Issue 受け入れ要件の照合結果(満たした / 未達)
   - 実行した検証(コマンドと結果)、coverage / 残リスク
   共有契約の資格条件を満たさない監査コメントは、後続のフル
   レビューで「レビュー未実施」として扱われる。
   投稿は `gh pr comment <PR> --body-file <監査コメント本文>` などで行い、
   投稿 URL または投稿成功をユーザー報告に含める。コメント投稿に失敗した
   場合は、レビュー判定自体が良好でも `Blocked / cannot determine` とし、
   `Mergeable` として扱わない。

## 報告形式

ユーザーへの報告は共有契約の構成で出し、監査コメントのURLを添える。
