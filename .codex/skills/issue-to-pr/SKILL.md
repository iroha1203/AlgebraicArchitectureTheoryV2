---
name: issue-to-pr
description: GitHub Issueを指定または優先順から選び、タスク型とsource of truthを確定して実装・検証・commit・push・PR作成・CI確認まで進める。"$issue-to-pr"、"Issue番号を対応して"、"次のIssueを選んでPRまで"で使う。PRのマージやPRD全体の反復にはreview-pr / prd-loopを使う。
---

# Issue to PR

GitHub Issue を起点に、タスク選定から Pull Request 作成まで進める。

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
2. Issue を確認し、**タスク型を確定する**。
   - 指定あり: `gh issue view <number>`
   - 指定なし: `gh issue list --state open`
   - Issue 本文の `タスク型`(新規実装 / 修正 / 移植(Research→本体) /
     docs)を読む。宣言が無い場合は自分で判定し、対応方針の説明に含める。
     Research 由来の theorem・受理成果を本体化する作業を含むなら移植型。
     現行docsフォームの`[doc]` title prefixはタスク型`docs`の宣言として扱う。
   - **移植型の規律**(通常の修正と規律が反転する):
     - 最小差分ヒューリスティクスを無効化する。「既存ファイル周辺で
       安く直す」より「移植元の構成を崩さない」を優先する。
     - 実装前に移植元 statement(Issue の `移植元 theorem` /
       `docs/aat/research_evidence_index.md` / `rg` での Research 検索)を
       実読し、結論一覧(conjuncts)と本体 statement の**対応表**を作る。
       この対応表は PR 本文の必須節にする(レビュー側が独立再構築した
       mapping との突合対象になる)。
     - **Research 下限原則**: Research 側の statement が本体実装の下限。
       本体 statement が下限より弱い形になる場合、その PR で close せず、
       実装で回避もせず、停止して理由を報告する。scope・台帳注記で
       弱化を正当化しない(scopeを書く資格条件は
       `.codex/skills/_shared/refutation-checklist.md` §4)。
     - **移植 ≠ import(依存 repackage の禁止)**: 本体
       (`Formal/AG` 本線・`Formal.lean` 配線)から `ResearchLean.AG` を
       import してはならない(import 方向は Research → 本体のみ可)。
       移植とは構成を本体内で再構成する蒸留であり、Research module を
       import して再導出する形は移植として扱われず、math-lean-review の
       Research import方向検査で hard fail になる。下限到達に Research の巨大 route の
       書き直しが必要で1 PR に収まらない場合は、import で近道せず、
       分解計画を報告して停止する。
   - 選択されたIssue Formのrequired fieldをすべて作業入力として扱う。
   - 実装Issueとdocs Issueの両方で`期待する成果物`を必須deliverableとして追跡する。
   - `現状の課題`、`解決方針`、`期待する成果物`、`受け入れ要件`の対応を確認する。
   - 各受け入れ要件について、実装箇所と確認証拠の対応表を作る。この対応表は
     実装中のチェックリストとPR本文の`受け入れ要件への対応`に使う。
   - 受け入れ要件が曖昧、成果物より弱い、または成果物の存在やbuild / testの
     通過だけで閉じられる場合は、最小解釈で実装を開始しない。Issueの課題、
     解決方針、source of truthから要件を具体化し、Issueへ反映してから実装する。
     意味の変わる補強が必要ならユーザー判断を求める。
   - required fieldまたは受け入れ要件を満たせない、または計画変更が必要なら、
     実装を開始しない。理由と代替範囲についてユーザー承認を得て、Issue本文を
     先に改訂する。未達要件をPR本文の注記だけで対象外へ移さない。
   - 実装依頼 Issue で「docs 修正だけでは完了しない」と明示されている場合、文書更新だけの PR にしない。Issue の範囲が実装不能または設計不足なら、実装せずに不足点を報告する。
   - ドキュメント修正 Issue では `備考` に示された source of truth と受け入れ要件の
     整合条件を確認し、実装変更が必要なら勝手に範囲を広げず、別 Issue 化または
     ユーザー確認を優先する。
3. 対応方針を短く説明する。
4. 専用ブランチを切る。
   - 例: `issue-6-bounded-path`
5. 実装する。
   - 既存の設計と命名を優先する。
   - 受け入れ要件ごとに実装箇所と確認証拠を追跡し、すべての完了を必須とする。
   - Issue の `備考` に明示された対象外に反する変更は入れない。
   - Lean 定義は小さく保ち、対応関係は theorem として育てる。
   - `axiom`, `admit`, `sorry`, `unsafe` は明示的な相談なしに導入しない。
   - **instance ペア規律**: 新規の Prop 述語・certificate 構造を導入する
     ときは、満たす instance と満たさない instance の両方を同じ PR で
     提供する(意味レベルの空虚化 — subsingleton 等式型・
     proof-irrelevance 恒真・answer-encoding — への一次防衛線。
     片方が作れない場合は理由を PR 本文に明記する)。
   - **CI gate の変更はユーザー判断事項**: CI workflow への gate の追加・
     削除・revert を PR 単独で行わない。必要な場合は Issue / PR 本文で
     ユーザー決定を明示し、決定が無ければ `status:blocked` にする。
6. 必要に応じて `docs/aat/proof_obligations.md` と `docs/aat/lean_theorem_index.md` を更新する。
   - Lean status は `docs/aat/guideline.md` の現行 status discipline に従う。
     `unported (Research-proved)` を別statusへ置換して完了扱いしない。
   - Issue 番号や残る proof obligation を明確にする。
7. 検証する。
   - Lean 変更あり: 統括エージェントが `lake build` を1回だけ実行する。
     サブエージェントに委譲しない。
   - Rust tooling 変更あり: `cargo test --manifest-path tools/archsig/Cargo.toml`
   - website 変更あり: `python3 -m http.server 8000 --directory website` などで静的 preview を確認する。
   - Issue の`受け入れ要件`に示された検証証拠を優先する。
   - PR 前の共通scanは`AGENTS.md`と
     `.codex/skills/_shared/refutation-checklist.md` §6に従う。
8. PR 作成前にローカル自己点検を行う。
   - 対象は現在のローカル差分、staged / unstaged diff、必要に応じて `main...HEAD` とする。
   - Issue scope、期待する成果物、検証結果、PR 本文に書く claim が diff と一致しているかを点検する。
   - obvious な未達・テスト不足・docs drift・PR 本文の過大 claim があれば、PR 作成前に修正する。
9. 日本語でコミットする。
10. ブランチを push する。
11. 日本語で PR を作成する。
    - `.github/pull_request_template.md` に沿って本文を書く。
    - 概要、証明した定理、編集したドキュメント、実施したテスト、チェックリストを埋める。
    - Issue の各`受け入れ要件`に対して、対応内容と確認証拠を
      `受け入れ要件への対応`の表で確認できるようにする。
    - ユーザー承認を得てIssue本文を先に改訂した計画変更は、PR本文にも
      変更した成果物・変更理由・追加Issueの有無を記録する。
    - ローカル自己点検の結果を、実施したテストまたは残リスク欄に簡潔に反映する。
    - 移植型では、移植元 conjunct 対応表(手順2)を PR 本文の独立した節として入れる。
    - 定理追加や docs 更新がない欄は `なし` と明記する。
    - 受け入れ要件をすべて満たした場合だけ、対象Issueを`Closes #N`で閉じる。
      未達要件が残るPRに`Closes #N`を記載しない。
12. `gh pr checks --watch` で CI を確認する。
13. 最後に PR URL、主な変更、確認結果を日本語で報告する。

## このリポジトリ固有の注意

- `Decomposable G := StrictLayered G` を維持する。
- acyclicity, finite propagation, nilpotence, spectral conditions は定義に混ぜず、別 theorem または future proof obligation として扱う。
- `ComponentCategory` は thin category として path count / walk length を忘れる。
- 定量指標は `Walk`, `Path`, adjacency matrix, future free-category construction 側で扱う。
- executable metrics は有限な測定 universe 上の計算として定義し、graph-level facts との接続は別 theorem として証明する。
- `ComponentUniverse` は proof-carrying measurement universe として扱い、実コードベース抽出器の完全性を直接主張しない。
- Architecture Signature は単一スコアではなく、多軸診断として扱う。

## PR 本文テンプレート

`.github/pull_request_template.md`を正本とし、対象Issueを`Closes #N`で含める。
