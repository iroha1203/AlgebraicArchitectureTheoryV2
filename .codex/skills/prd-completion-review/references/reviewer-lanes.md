# PRD Completion Review lanes

## 横断4観点

1. **要件充足**
   - 各条件を直接満たす一次証拠を確認する。
   - 似た概念、部分実装、名前だけの対応を充足扱いしていないか疑う。
2. **欠落・反例**
   - edge case、未接続surface、docs drift、fixture不足、negative path不足を探す。
   - 条件の達成が別の未確認前提に依存していないか確認する。
3. **検証再現性**
   - acceptance test、ローカル検証、CI、GitHub状態が条件を覆うか確認する。
   - test名ではなくassertion内容を読む。
4. **scope・状態整合**
   - PRD外の巨大claim、分野責務の混同、statusと実体の不一致を探す。
   - theoremRefの実在と主張方向、public artifactのprivacyを確認する。

条件が多い場合は、固定件数を閾値にせず、横断4観点だけでは一次証拠を
実読できない条件群ごとに深掘りlaneを追加する。

## 独立抽出lane

横断laneとは別に1本実行する。親が抽出した条件、拘束条件、requirement matrix、
tracking Issueを渡さず、PRD全文だけから次を抽出する。

1. 達成条件。
2. 採否規律・中心方針・非主張などの拘束条件。
3. must-not-remain。別PRDへ明示的に残した項目と除外理由を含む。

親の抽出との差分をfindingとして返し、差分を解消してから統合する。

## Lane入力

- PRDパスと全文。
- 親が抽出した条件、拘束条件、must-not-remain。独立抽出laneには渡さない。
- 担当観点と担当条件。
- 対象のraw artifactと既に実行した検証。
- 一次証拠規則。台帳、Issue、PR本文、tracking checklistは監査対象とする。
- 横断laneは親が渡した条件を再scope・置換・省略しない。条件リスト自体が
  誤っている場合は、独自の条件集合へ差し替えずfindingとして返す。

## 追加出力

共有review protocolの出力に加え、各laneは次を返す。

1. 確認した条件ID。
2. 条件ごとの推奨status:
   `満たした` / `未達` / `未確認` / `PRD欠陥` / `範囲外`。
3. 一次証拠。testを使う場合はassertion内容を含める。
4. 親の条件抽出に対するfinding。

## 親の報告

1. 総合判定:
   `達成済み` / `未達あり` / `未確認あり` / `PRD欠陥あり` /
   `範囲限定レビュー`。
2. PRDの「問い」に対するアウトカム判定。
3. Scoreboard。
4. 条件別レビュー表。
5. Findings。
6. Lane別の反証試行。
7. 実行した検証。
8. Coverage limits。
9. 次アクション案。実装は行わない。

`prd-loop`の最終レビュー、またはtracking Issueがある単独レビューでは、
1〜8をtracking Issueへコメントする。投稿不能でも一次証拠に基づく判定は返し、
`tracking Issue未同期`として報告する。`prd-loop`側のclose操作は同期まで停止する。
