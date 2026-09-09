# Target GOAL Card Contract

`target-theorem`カードの適用版を特定し、内容をループ・査読の入力へ読み取る手順。
新規カードの記載基準は[GOALカードの型](../../../../research/goals/README.md#goal-カードの型)にある。

## 適用版の特定

1. カードの初出履歴と、上記記載基準のmainへの導入履歴を確認し、新規・既存を判別する。
   カード内に新しい形式識別fieldを追加しない。
2. 新規カードではactive化時に、GOALの固定commitと、共通基準を読むcommit・pathを
   tracking Issueへ記録する。draftの記載点検では作業中の版を使う。
   targetが参照する既存宣言の解決commitもactive化時に記録する。原則はGOALの固定commitとし、
   別版を参照する宣言はcommit・path・宣言名を特定する。実装時の参照版変更で指示対象や要求が
   変わる場合は、人間の判断と変更箇所をIssueへ記録してから適用する。
   再開時は記録した版を`git show <commit>:<path>`などで読み、参照先の共通基準も同じ
   commitから解決する。版変更は人間の判断と変更箇所をIssueへ記録してから適用する。
3. 既存カードは人間が固定した内容と従来の適用版で読む。版は既存のtracking Issue・
   report・Git履歴から復元し、本変更のためのカード追記・移行・再監査は行わない。
   旧形式の項目一覧はcommit `d481b4e9f76b107b54e6d58fc7551416821bd701`の
   `research/goals/README.md`と本ファイルで参照できる。既存の明示判断があればそれを優先する。
4. 適用版を特定できない場合は、その不足を報告する。新形式へ自動変換したり、
   新しい必須項目の欠如を既存カードの欠陥としたりしない。

## 内容の読み取り

新規カードの5項目から次の監査入力を抽出する。旧形式では右欄の従来fieldを読む。
field名の有無ではなく、該当内容と参照先を確認する。

| 監査入力 | 新規カードでの所在 | 旧形式での所在 |
| --- | --- | --- |
| id・mode・起動資格 | 基本情報 | `id`、`research mode`、`status` |
| 研究目的と既存成果との差 | 研究目的 | `research aim`、`core tension`、`rival` |
| statement・対象の制限 | 固定target | `target theorem`、`claim boundary`、`target theorem boundary` |
| 成果物・完了判定 | 完了条件と参照するtarget条項 | `target proof artifacts`、`target theorem completion criteria` |
| material premise・構成・使用先 | 前提・構成台帳と参照するtarget条項 | `target premise discharge policy`、`target material premise ledger` |
| 固有の生成経路・許容結果 | 固定target・台帳・完了条件の該当箇所 | `target route integrity gate`、`target anti-weakening rule`、`target failure policy` |

新規カードの台帳roleは、入力として保持するものを`ambient-boundary`、一般定理の仮定を
`direction-hypothesis`、構成・放電義務を`discharge-required`として監査へ渡す。
結論との循環の懸念は`conclusion-equivalent-risk`として確認事項を抽出する。
同じ前提の経路別roleと、構成から主結論までの接続を保持する。

## 共通基準の参照適用

下表の基準を、上で特定した版から読む。新規カードはこの節を参照すれば共通基準を
適用でき、監査や停止規則の本文をカードに転記する必要はない。

| 判定 | 参照先 |
| --- | --- |
| statement一致・前提放電・anti-weakening・provenance・route・非空虚性 | [acceptance基準](acceptance-contract.md) |
| 実装PRの標準レビュー、独立4査読による完了判定、停止処理 | [ループのPR gate・Completion・停止条件](../SKILL.md#pr-gate) |
| final packet・report／Issueとの対応 | [completion ledger](completion-ledger.md) |
| 独立した数学・Lean査読 | [math-lean-review](../../math-lean-review/SKILL.md)とそこから参照する共有基準 |

監査へ渡すときはGOALと共通基準のcommit・pathおよび該当条項を添える。
final packetの`completion_criteria`にはカード固有の条件と適用版付き共通基準の参照を
含める。completion証拠の取得方法を人間判断で変更した場合は、targetの変更ではないこと、
承認Issue/comment、依存trustの範囲をpacketのdependency policyへ固定する。
既存packetの必須項目や正式ゲートは維持する。

## 欠陥判定

起動資格としてactiveかつtarget-theoremであることを確認する。新規カードの内容は
記載基準に従い、特に次の場合はproof obligationの選定へ進まない。

- 入力・量化・構成義務・結論を特定できない、または研究目的との接続が不明。
- 成果物と達成条件が不明で、SCOREやPR mergeだけで完了になっている。
- 台帳から入力・一般定理の仮定・放電義務を区別できず、provenanceや使用先を追えない。
- 結論相当の仮定を入力に移した疑いがあるのに、その確認事項が特定されていない。
- 必要なwitnessの評価対象・同時成立条件、証明と反証の扱いを特定できない。
- 共通基準への参照が解決できない、正式ゲートの省略を指示している、または必要な監査を実行できない。

新規カードで旧fieldの独立節、SCORE用stub、任意のproof strategyがないことは欠陥ではない。
既存カードの点検は「適用版の特定」に従い、新規の記載基準で再判定しない。
欠陥を見つけたらカードを編集せず、具体的な不足と改訂案をtracking Issueへ記録する。
