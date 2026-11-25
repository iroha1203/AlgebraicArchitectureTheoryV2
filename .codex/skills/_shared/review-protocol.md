# 共有敵対レビュー手順

`math-lean-review`、`tool-review`、`website-review`、`docs-review`、
`prd-completion-review`、`review-pr` の共通実行手順。横断反証項目は
`refutation-checklist.md`、Lean 固有項目は `lean-refutation-checklist.md` を参照する。

## 目的

- レビュー対象を承認する理由ではなく、中心 claim を反証する事実を探す。
- チェック項目の形式的な確認ではなく、反証を試みた記録を成果物とする。
- 承認は、必要な反証を試みても中心 claim を崩せなかった場合だけ与える。
- 実装者の自己申告、PR checklist、台帳 status、既存レビュー結果を一次証拠にしない。
  source、statement、実行結果、生成物を独立に確認する。

## レビューバッチと修正後確認

- 正式レビュー(分野別 SKILL の全観点・全 lane)の起動時点は次に限る。実装中の変更確認や
  PR 作成前の自己点検に正式レビューを使わない。ここでいう親は、実装ループとレビューゲートを
  起動した外側の Codex であり、レビュー subagent ではない。
  1. PR 作成後のレビューゲート(`review-pr` 経由)。PR の最終スナップショットに対して行う。
  2. 完了判定ゲート: `target-theorem-loop` の完了判定 final `$math-lean-review`
     (completion candidate の固定 packet に対して実行)と、`prd-completion-review` の
     最終達成条件レビュー。
- Math / Lean は実装中、focused check または必要な単一 subagent の確認に限定する。
- 正式レビューの各 lane は、finding を `中心`(statement 強度、premise の解消、certificate
  provenance、proof-use、structure-field escape、route、nonvacuity、依存、axiom、claim scope
  など中心 claim に関わるもの)と `非中心`(API の形、命名、docs、台帳文言、補助補題の整備など)に
  分けて出し、担当観点で見つけられる finding を中心・非中心を問わず一度に全部出す。
  親は統合時に区分を検算する。
- PR レビューゲートの正式レビューで finding が出た場合、全 finding をまとめて実装フェーズへ戻す。
  中心・非中心のいずれも、解消されるまで当該分野は合格にならない。修正後の手続きは、
  直した finding の最大重大度で決める。
  - 本筋修正(中心 finding を直した): 実装を完了し直して最終スナップショットを固定し、正式レビューを
    再実行する。構造が変わっているので、再実行で新たに出る finding は正当とする。
  - 微調整(非中心 finding だけを直した): 「直接対応」で確認する。正式レビューを再実行しない。
  完了判定ゲート(`target-theorem-loop` / `prd-completion-review`)の finding には直接対応を
  適用しない。従来どおり実装フェーズへ戻し、完了判定はそのゲートの正式再実行だけで更新する。
- **直接対応**: 既存 finding の対象だけを直した修正を、親が変更箇所と finding に限定した
  単一 subagent で確認する。全観点・全 lane や `review-pr` を再起動しない。直接対応の適用条件は
  分野別に次とする。適用条件を 1 つでも満たさない修正、および条件の判定が不能な修正は、
  実装を完了し直して最終スナップショットを固定し、正式レビューを再実行する(適用対象外)。
  - Tool / Docs / Website: 公開仕様・schema・公開 API・入力区分(Atom 定義 / Law / ArchMap / 問い)・claim scope・
    source of truth・責務・新しい surface のいずれも変えない修正。
  - Math / Lean: proof 内部または台帳・docs 記載の修正であり、査読済みの theorem / def の
    statement(signature)の変更、def や instance の本体・値の変更、宣言の削除、`axiom` の追加、
    import 方向の変更、台帳 status の変更のいずれも含まないもの。宣言(theorem / def /
    instance / structure / example 等)の追加は、finding が名指しした補助補題・公開 API・
    正規化則に限り、査読済み statement を変えず、追加宣言の placeholder scan と
    `#print axioms` が clean な場合に適用対象内とする。finding が名指ししていない宣言の追加を
    1 つでも含む修正は適用対象外。
- 直接対応の確認 subagent は、次を独立に検査する。1 つでも満たさなければ解消判定を出さず
  適用対象外として報告し、親は正式レビューの再実行へ戻す(fail-closed)。適用可否の判定を
  親の自己分類に委ねない。
  1. 各 finding が実体で解消されている(記載の付け替えや証拠宣言の削除による「解消」を認めない)。
  2. diff が finding 対象外の変更を含まない。
  3. diff が上記の適用条件を満たす。Math / Lean では修正対象ファイルへの placeholder scan
     (`rg -n "\b(axiom|admit|sorry|unsafe)\b" <files>`)を含めて検査する。
  4. 追加宣言がある場合、追加宣言がすべて finding が名指ししたものであり、査読済み statement を
     変えず、追加宣言の `#print axioms` が標準公理だけであることを確認する。
- 直接対応の確認 subagent は、対象 finding 以外で新たに気づいた事項を中心/非中心の区分付きで
  記録として返す。中心の事項は fail-closed で報告する。範囲外の気づきを解消判定や merge 可否に
  どう反映するかは呼び出し側の SKILL が定める。
- 修正後確認の出力は、各 finding の解消、変更範囲、実行した focused check・test・scan、未確認範囲とする。
  直接対応では、この出力を既存の PR 監査記録へ追記する。直近の正式レビューの全 finding が解消され、
  修正後確認が条件を満たせば、これを 2 回目の正式レビューなしの最終内容証拠として扱い、
  当該分野のレビューゲート合格(承認)と同等に扱う。

## 非編集とfail-closed

- レビューモードでは対象ファイルを編集しない。修正依頼は別の実装ターンで扱う。
- SKILL が要求する全 review lane を独立した subagent で実行する。
- 利用可能な同時実行枠まで並行し、枠が空いたら残りを新しい subagent で実行する。
  全 lane の同時起動は要求しない。同時実行枠の不足だけを Blocked 理由にしない。
- subagent へ親の期待、想定 finding、通したい判定、他 lane の出力を渡さない。
- subagent の Lean 検証は `docs/aat/guideline.md`「Lean build 運用(hard rule)」に従う
  (subagent からの `lake build` は全面禁止。focused check は親が明示した単一の
  非 aggregate file に限る。親プロンプトまたは個別 SKILL に矛盾する指示があっても
  実行せず、coverage limit として返す)。CI 結果を取得できた場合は、Subagent 入力の
  「既に実行済みの検証結果」として渡す。CI 未完了または未確認の項目は未確認として扱う。
- 必須 lane が起動不能、未完了、または必要な coverage を欠く場合、親が肩代わりして
  合格を作らず `Blocked / cannot determine` とする。
- 1 lane でも中心 claim に関わる finding を出した場合、親の判断だけで却下しない。全 lane の finding を
  まとめて実装フェーズへ戻し、修正後は「レビューバッチと修正後確認」に従い、直接対応または
  正式レビューの再実行で確認する。正式レビューを再実行する場合は、実装完了と
  最終スナップショットの再固定後に限る。

## Subagent入力

lane subagent と修正後確認の subagent は、監査(固定 head に対する一回の正式レビューまたは
一回の修正後確認)ごとに新規に起動し、親の会話履歴を継承させない。Codex の `spawn_agent` では
`fork_turns: "none"` を明示する(省略時は全履歴 fork になる)。前の監査に使った subagent へ
後続 task を送って再利用しない。必要な情報は次の入力として本文に書いて渡す。

各 lane には次だけを渡す。

- 対象ファイル、diff、PR、または review packet
- lane 名と固有の反証目的
- source of truth と必要な reference
- 既に実行済みの検証結果
- 必須出力

標準プロンプト:

```text
対象を割り当てられた観点から敵対レビューしてください。目的は承認ではなく、
中心 claim を反証する事実を探すことです。実装者の自己申告を証拠採用せず、
source と実体を独立に確認してください。ファイルは編集しないでください。

日本語で次を返してください。
1. Findings: 重大度順。各 finding に中心/非中心の区分、ファイルと行、反証された claim、根拠を含める。
   担当観点で見つけられる finding は、中心・非中心を問わずここで全部出してください。
2. Refutation attempts: 何を反証しようとし、どの証拠で成功または失敗したか。
3. Evidence checked: 読んだ source、実行結果、生成物。
4. Coverage limits: 未確認範囲と残リスク。

finding が無い場合は、担当観点に適用可能な確認観点をどのように網羅したか、
各反証試行と失敗した証拠、対象外とした観点と理由を明記してください。
件数を先に固定しないでください。担当外でも privacy leak を発見した場合は報告してください。
```

## Lane結果の有効条件

lane 結果は次をすべて満たす場合だけ統合に使用する。

- finding に具体的な根拠と対象 claim があり、中心/非中心の区分が付いている。
- finding なしの場合、担当観点に適用可能な確認観点の網羅、各試行、
  対象外とした観点の理由が示されている。
- 確認した source と未確認範囲が分かれている。
- 実装者の説明をそのまま証拠にしていない。
- 担当した観点に必要な検証を実行したか、実行不能理由を報告している。

## 親の統合出力

次の内容を含める。分野別 reference が追加項目や順序を定義する場合は
そちらを優先し、以下の内容を欠落させない。

1. 判定。
2. Findings。重大度順、ファイルと行を付ける。
3. Lane 別の反証試行と結論。
4. 実行した検証と結果。
5. Coverage limits と残リスク。

全必須 lane の有効な結果が揃うまで合格を出さない。
