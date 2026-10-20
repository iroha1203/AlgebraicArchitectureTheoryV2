# PRD Completion Review lanes

要件査読A/Bと実装・検証査読A/Bの4本を、同じ合格基準を持つ重複独立査読として実行する。
A/Bを主査と補助に分けない。各laneがPRD全文から条件を独立抽出し、累積実体を確認する。
親の条件リスト、会話履歴、期待結論、他laneの出力、前の監査結果を渡さない。
新規起動と履歴を渡さない方法は共有review protocolの「Subagent入力」に従う。

## Lane定義

### 要件査読 A / B

- PRDの問い、全達成条件、拘束条件、requirement matrix、must-not-remainを全文から抽出する。
  抽出の範囲と除外規則は[標準手順2](../SKILL.md#標準手順)に従う。
- 各条件と一次証拠の強さ・範囲を照合し、部分実装、許可外の降格、記載のみの充足、
  欠落した条件群、PRD外の要求混入を探す。ACとは別に問いの回答を判定する。

### 実装・検証査読 A / B

- 要件査読と同じ抽出を独立に行い、全条件をコード、宣言、schema、fixture、test、docs、
  必要なGitHub状態へ追う。名前や台帳のstatusだけで充足扱いしない。
- assertion内容、負系、未接続surface、旧構造・旧挙動の残存、検証の再現性を確認する。
  Lean要件ではstatement、依存、仮定放電、axiom等の該当する反証項目も適用する。

## 全lane共通の合格基準

各laneは重点の違いにかかわらず、要件充足、欠落・反例、検証再現性、scope・状態整合の
全観点を確認する。theoremRefの実在と主張方向、public artifactのprivacyも対象とする。
条件群の深掘りは同じlane内で順次行う。抽出専用・深掘りの追加laneは起動しない。
全数を実読できない条件群はsamplingで充足扱いせず、条件IDと理由を付けて未確認とする。

## Lane入力

- 固定したPRDパス・内容hashと全文、対象commit。作業ツリー差分を含む場合は対象の内容hash。
- lane名と反証目的、適用guidelineと必要なreference。
- 累積実体への参照、実行済みの検証コマンド・結果と対象snapshot。
- tracking Issue / PR番号は証拠検索の索引としてのみ渡す。
- 一次証拠規則。台帳、Issue、PR本文、tracking checklistは監査対象とする。

## 追加出力

共有review protocolの出力に加え、各laneは次を返す。

1. 独立抽出した全条件・拘束条件・requirement matrix・must-not-remainと除外理由。
   PRDにIDがなければ、節・原文引用で親が対応を照合できる形にする。
2. 条件ごとの推奨status:
   `満たした` / `未達` / `未確認` / `PRD欠陥` / `範囲外`。
3. 一次証拠。testを使う場合はassertion内容を含める。
4. 問いに対するアウトカム判定。
5. 確認した条件と未確認の条件・実体・検証、その理由。

## 親の報告

1. 総合判定:
   `達成済み` / `未達あり` / `未確認あり` / `PRD欠陥あり` /
   `範囲限定レビュー`。
2. PRDの「問い」に対するアウトカム判定。
3. Scoreboard。
4. 条件別レビュー表。独立抽出の差分と解消根拠を含む。
5. Findings。
6. Lane別の反証試行・判定と、親による一次証拠の再判定。
7. 実行した検証、対象commit・PRD内容hash・必要な実体hash。
8. Coverage limits。
9. 次アクション案。実装は行わない。

`達成済み`には4本すべてと親の全必須項目の確認を要求する。未完了lane、未解消finding、
抽出の不一致、必要なcoverageの不足が残る場合は完了にしない。

`prd-loop`の最終レビュー、またはtracking Issueがある単独レビューでは、
1〜8をtracking Issueへコメントする。投稿不能でも一次証拠に基づく判定は返し、
`tracking Issue未同期`として報告する。`prd-loop`側のclose操作は同期まで停止する。
