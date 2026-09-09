# Completion生成器の回帰確認

## 実例から取り出した検証対象

G-118は監査事故のサンプルとして使う。全451宣言の再監査を、この生成器の完了条件にはしない。
出典は[PR #4403のpacket撤回](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/pull/4403#issuecomment-5557020461)、
[標準監査](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/pull/4403#issuecomment-5556939163)、
[最終監査](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/pull/4403#issuecomment-5557145097)。

撤回時の`generatedQualifiedComparisonRelation_iff_inputConditions`は、実際には
`generatedQualifiedComparisonRelation_iff_difference_mem`と
`mem_generatedPulledComparisonKernel_iff_inputConditions`を直接使う。
`qualifiedComparisonSubgroup`だけをpredecessorにした記載が実proof bodyと不一致だった。
小さい`CompletionFixture.inputCharacterization`では、必要十分条件を二つの方向の定理から
作る形を保持する。`differenceCriterion`と`kernelInputCriterion`が直接参照されることを
実Lean抽出と独立期待集合で検査する。G-118固有のgeometry・群・transportは省いている。

選んだ撤回本文、入力packetコメント本文のSHA-256、抽出範囲、旧新routingは
[サンプルmanifest](../scripts/fixtures/g118-sample.json)に固定した。
packetコメントのdigestは取得したUTF-8本文のhashであり、生成packetの中心証拠digestとは区別する。

中心`T`とfull `Γ`の誤った同一視、代表宣言への過大なdirection割当は、機械的な到達だけでは
判定できない意味上の事例である。[overclaim.json](../scripts/fixtures/overclaim.json)は
任意のnについての必要十分条件を、`positive 0`だけを証明する`identityMember`へ過大に
割り当てた具体的サンプルである。schemaが受理したことを数学的合格と扱わず、PRの独立査読で
誤った対応をvetoできるか確認する。unit testはそのfindingを入力にしたroutingだけを検査する。

## 旧手順と新手順の比較

下表の回数は、一件のfinding修正後に要求される追加のfull 4-lane batch数である。
G-118全工程の総実行回数や時間短縮の実測値ではない。旧手順は変更前の共有review protocolの
「完了判定には直接対応を適用しない」という規定による。新手順の比較は再現用fixtureである。

| 事例 | 旧手順の追加full batch | 新手順の追加full batch | 新手順の確認 |
| --- | --- | --- | --- |
| G-118由来の誤った中心predecessor | 1 | 1 | fresh 4査読。本文不変でも降格しない |
| 中心route / direction overclaimという意味上のfinding | 1 | 1 | 有資格な中心findingを入力してfreshへ送る |
| 4査読後の補助ref修正、中心データ不変 | 1 | 0 | 新規独立確認者によるdirect recheck |
| 投稿前enum型検査の失敗 | 0 | 0 | 投稿を止めて修正。まだ査読を起動しない |
| 4査読後の補助欄（`auxiliary`）の表示修正、中心データ不変 | 1 | 0 | 型再検査と独立direct recheck |
| 放電の唯一のrefを補助refと自己申告 | 1 | 1 | 中心gateのfindingを降格しない |

0-batchの修正範囲は`auxiliary.notes`と`auxiliary.refs`に限る。生成器・抽出器・対応表や
中心証拠を変更する修正は、表示を目的としていてもこの経路に含めない。

G-118の撤回記録と最終監査からは、訂正後にfresh 4査読が実施されたことを確認できる。
撤回前batchの各lane完了数や、投稿前の内部試行総数は、この比較の実測値として数えない。

## 再現手順

```bash
python3 .codex/skills/target-theorem-loop/scripts/test_completion_packet.py
python3 .codex/skills/target-theorem-loop/scripts/integration_completion.py
```

後者はコミット済みsourceの明示的な小さいleafを個別に実行し、全Research buildを呼ばない。
追加の2 leafは同一namespaceを別cacheへ出力し、先のcacheに未記録の古いmoduleを残す。
環境変数にもそのcacheを設定したままcollectと再抽出を行い、focused owner overlayが
同名の古いowner artifactより優先されることを検証する。
生成物・stdout/stderr・receipt・packet・結果は`.tmp/completion/integration/`に保存する。
期待参照はfixtureのsourceから独立に定め、直接参照、private補助定理経由、型のみの参照、
`simp`参照、標準公理、再生成一致、手編集拒否を検査する。
外部packageとrepo-local runtime importを持つcanaryでも、選択ownerだけをfocused elaborationし、
runtime依存をsource-build済みと主張せず抽出できることを検査する。
全宣言の型・値のconstant集合をLean標準走査と照合するほか、全Expr constructorの
literal ASTから独立に定めた参照集合・site・位置を完全一致で検査する。
全type参照を削除するmutation、余分な参照、元lane確認者の再利用も拒否する。
test名とassertionを検証証拠とし、過去のG-118完了判定を更新しない。

意味上のサンプルの独立査読結果と、このPRの固定headでの実行結果はPR監査記録へ残す。
generatorのtest成功を、その独立査読の代替としない。
