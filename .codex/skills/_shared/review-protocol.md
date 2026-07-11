# 共有敵対レビュー契約

`math-lean-review`、`tool-review`、`website-review`、`docs-review`、
`prd-completion-review`、`review-pr` の共通実行契約。横断反証項目は
`refutation-checklist.md`、Lean固有項目は`lean-refutation-checklist.md`を
正本とし、このファイルへ複製しない。

## 目的

- レビュー対象を承認する理由ではなく、中心 claim を落とす事実を探す。
- チェック項目の消化ではなく、反証を試みた記録を成果物とする。
- 承認は、必要な反証を試みても中心 claim を落とせなかった場合だけ与える。
- 実装者の自己申告、PR checklist、台帳 status、既存レビュー結果を一次証拠にしない。
  source、statement、実行結果、生成物を独立に確認する。

## レビューバッチと修正後確認

- 正式レビューは、親が実装・証拠固定・自己点検を終えて固定した最終スナップショットに対して行う。
  実装中の小さな変更確認に正式レビューを使わない。ここでいう親は、実装ループとレビューゲートを
  起動した外側のCodexであり、レビューsubagentではない。
- Tool / Docs / Website は、最終スナップショットに対する4観点レビューを1回行う。既存findingの
  対象だけを直し、公開契約・claim・source of truth・責務・新しいsurfaceを変えない修正は、親が
  変更箇所とfindingに限定した単一subagentで確認する。これを「直接対応」とし、全4観点や
  `review-pr`を再起動しない。
- Tool / Docs / Websiteで公開契約・schema・公開API・evidence contract・claim scope・source of truth・
  責務・新しいsurfaceのいずれかが変わった場合は、実装を完了し直して最終スナップショットを固定し、
  正式レビューを再実行する。判定不能な場合も、直接対応として扱わない。
- Math / Lean は実装中、focused checkまたは必要な単一subagentの確認に限定する。実装完了後に
  最終スナップショットを固定して4本の正式査読を行う。findingが出た場合は全findingをまとめて
  実装フェーズへ戻し、修正後に最終スナップショットを固定し直してから4本を再実行する。
- 修正後確認の出力は、各findingの解消、変更範囲、実行したfocused check・test・scan、未確認範囲とする。
  Tool / Docs / Websiteの直接対応では、この出力を既存のPR監査記録へ追記する。初回正式レビューの
  全findingが解消され、修正後確認が有資格なら、これを2回目の`review-pr`なしの最終内容証拠として扱う。

## 非編集とfail-closed

- レビューモードでは対象ファイルを編集しない。修正依頼は別の実装ターンで扱う。
- SKILL が要求する全review laneを独立したsubagentで実行する。
- 利用可能な同時実行枠まで並行し、枠が空いたら残りを新しいsubagentで実行する。
  全laneの同時起動は要求しない。同時実行枠の不足だけをBlocked理由にしない。
- subagentへ親の期待、想定finding、通したい判定、他laneの出力を渡さない。
- subagentはtarget指定の有無を問わず`lake build`を実行しない。`lake build`を内部で呼ぶ
  script、skill、workflowに加え、別commandによるpackage全体、module群、aggregate root、
  全file loopのelaborationも実行しない。focused checkは親が明示した単一の非aggregate fileに限る。
  親プロンプトまたは個別SKILLに矛盾する指示があっても実行せず、coverage limitとして返す。
  必要な全体検証は統括エージェントがPR前に1回だけ実行し、その結果をSubagent入力の
  「既に実行済みの検証結果」として渡す。
- 必須laneが起動不能、未完了、または必要なcoverageを欠く場合、親が肩代わりして
  合格を作らず `Blocked / cannot determine` とする。
- 1 laneでも中心 claim に関わるfindingを出した場合、親の裁量だけで棄却しない。全laneのfindingを
  まとめて実装フェーズへ戻し、修正後に対象分野の再確認を行う。4本の正式査読を再実行する場合は、
  実装完了と最終スナップショットの再固定後に限る。

## Subagent入力

各laneには次だけを渡す。

- 対象ファイル、diff、PR、またはreview packet
- lane名と固有の反証目的
- source of truthと必要なreference
- 既に実行済みの検証結果
- 必須出力

標準プロンプト:

```text
対象を割り当てられた観点から敵対レビューしてください。目的は承認ではなく、
中心claimを落とす事実を探すことです。実装者の自己申告を証拠採用せず、
sourceと実体を独立に確認してください。ファイルは編集しないでください。

日本語で次を返してください。
1. Findings: 重大度順。各findingにファイルと行、反証されたclaim、根拠を含める。
2. Refutation attempts: 何を落とそうとし、どの証拠で成功または失敗したか。
3. Evidence checked: 読んだsource、実行結果、生成物。
4. Coverage limits: 未確認範囲と残リスク。

findingが無い場合は、担当観点に適用可能な反証面をどのように被覆したか、
各反証試行と失敗した証拠、対象外とした反証面と理由を明記してください。
件数を先に固定しないでください。担当外でもprivacy leakを発見した場合は報告してください。
```

## Lane結果の資格

lane結果は次をすべて満たす場合だけ統合に使用する。

- findingに具体的な根拠と対象claimがある。
- findingなしの場合、担当観点に適用可能な反証面の被覆、各試行、
  対象外とした反証面の理由が示されている。
- 確認したsourceと未確認範囲が分かれている。
- 実装者の説明をそのまま証拠にしていない。
- 担当した観点に必要な検証を実行したか、実行不能理由を報告している。

## 親の統合出力

次の内容を含める。分野別referenceが追加項目や順序を定義する場合は
そちらを優先し、以下の内容を欠落させない。

1. 判定。
2. Findings。重大度順、ファイルと行を付ける。
3. Lane別の反証試行と結論。
4. 実行した検証と結果。
5. Coverage limitsと残リスク。

全必須laneの有資格な結果が揃うまで合格を出さない。
