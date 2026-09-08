# Completion packet生成と検査

version 2では、固定sourceとJSON対応表からpacketを生成する。
入出力のfield・enum・未知field・重複keyの検査は
[`completion_packet.py`](../scripts/completion_packet.py)の`validate_map`、`material`、
`validate_bundle`、`validate_packet`に集約する。対応表の最小例は
[`mapping.json`](../scripts/fixtures/mapping.json)にある。JSONは標準ライブラリだけで
読み書きできる形式として選んだ。YAMLの暗黙型変換は使わない。

## 固定入力と実行

対応表を対象PRへcommitしてから、repo rootで次を実行する。
`$packet`は`python3 .codex/skills/target-theorem-loop/scripts/completion_packet.py`を表す。
各コマンドは失敗時に非零で終了する。古い成功出力の有無で成功を判定しない。

```text
$packet check --source <単一leaf.lean> --module <owner> --out .tmp/completion/cache
$packet collect --mapping <対応表.json> --receipt <owner.receipt.json> --out .tmp/completion/bundle.json
$packet render --bundle .tmp/completion/bundle.json --packet .tmp/completion/packet.json
$packet validate --bundle .tmp/completion/bundle.json --packet .tmp/completion/packet.json
```

`check`は明示された単一leafだけを`lean -o`でelaborateする。`lean`は対象toolchainの
実行ファイルを使い、必要なpackage search pathは親が`LEAN_PATH`または`lake env`で設定する。
`--deps`で見つけたtoolchain外のimportには、同じhead/source/oleanを結ぶ
`--dependency-receipt <file>`を要求する。既存cacheを無条件で信用せず、証拠のない依存は
親が必要なmoduleに限って確認する。`check`を全Research moduleのloopへ使わない。
外部packageのreceiptは、そのGit作業領域内で同じcheckを実行し、同領域内に保存する。
親repoへ渡す際はpackageのrepo相対位置・commit・source/blobも再検算する。
subagentの実行制限は[AAT guideline](../../../../docs/aat/guideline.md)に従う。

`collect`は複数の`--receipt`を受け取り、選んだownerの宣言をLeanから抽出する。
`--base`で比較元commitを指定でき、省略時はその時点の`origin/main`をcommitへ解決して固定する。
型・値・owner・private名・公理・参照位置を記録する。`validate`はGitと実行出力を検算し、
対象oleanから再抽出してbundleと一致することを確認する。全sourceのGit blob一覧は
入力整合のための読取りであり、全moduleのelaborationではない。
receiptはコマンド実行証拠なので手で作成・編集しない。第三者査読はreceiptとsourceを
照合し、必要な対象だけを独立に再実行する。

各宣言の型・値ごとの全constant名は、独立したLean標準`Expr.getUsedConstants`でも収集する。
独自の位置付き走査の全件集合と照合し、欠落も余分な参照も拒否する。projection名は
`Expr.const`と別のmetadataなので、この集合比較から分ける。全Expr constructorを持つ
literal ASTのfixtureでは、参照名・site・位置をPythonの手書き期待値と完全一致で検査する。

対象source、GOAL、report、対応表、extractorは固定headに存在する必要がある。
未コミット変更・head/blob不一致・出力欠落・未知version・抽出不能は投稿不可。
toolchain外の依存がreceiptで解決できなければ、対象を勝手に縮小せず未確認を報告する。

## 対応表と数学判断

- `criteria`と`claims`はGOALの全completion criteriaに対応させる。各claimはGOAL内の
  literal quote、方向、複数のexact declaration名、中心node、必須routeを持つ。
- `premises`はGOALの全material premise行を列挙する。roleの申告だけで放電と判定しない。
  discharge-requiredには放電宣言と実際のconsumerを対応させ、値の経路を要求する。
- `evidence`には現行15 gate全ての宣言参照を置く。artifact sync等のコマンド・文書証拠は
  bundleのsource/receiptと併せて読む。宣言参照だけでgateをpassにしない。
- `direction_coverage`は各claimへ複数のexact refと型を添えて生成する。同じ宣言を複数claimへ
  割り当てる場合は、そのstatementが全てを支えることを査読する。

機械検査は登録済みcriteriaの欠落、空ref、未解決ref、型不正等を拒否する。
GOAL全体からのcriterion/premiseの選び落とし、statementより広いclaim、量化の弱化、
結論を仮定・certificate fieldへ移した実装は、独立4査読がsourceに基づいて判定する。
対応表を唯一の査読対象リストにせず、GOAL全体から逆照合する。

## acceptance spineと抽出グラフ

`dependency_dag`はtarget acceptance spineである。各conjunct、全discharge-required、
certificate生成元、必須route、固定decision、非空虚性の中心nodeを含める。
`core.gate_evidence`の宣言も必須nodeとなる。edgeは消費側から参照先へ向ける。

指定ownerの型と値にあるconstant参照を自動列挙し、外部宣言は型/owner付き終端にする。
生成器は選択node間の到達を計算し、directは1 hop、viaは補助宣言経由の経路として
全hopを出力する。必須routeを証拠なしにdirect扱いできない。外部終端を越える必須routeは、
必要なownerを追加して再収集するまで未確認である。

definitionやprivate補助宣言は経路に含める。`simp`は最終証明項に残る参照を抽出する。
型・binder型の参照、projectionは別siteとして残し、型参照だけのhopをproof-use経路にしない。
term部分の参照も数学的な必要性を保証しない。未使用let値や型を引数として渡す式を
実質的なproof-useと誤認しないよう、Lean査読が値の実体を確認する。

初期実装は小さい到達経路を安定順で出力し、全pathを列挙しない。中心nodeの巡回は
`cannot determine`として拒否する。巡回を黙って削除してDAGを作らない。
自動抽出の全constant参照はbundleに保持するが、全補助edgeの手作業再構成は通常査読の
必須責務にしない。falseな中心edge、中心predecessorの欠落は常にblockingである。

## 投稿と修正後確認

generatorはネットワークへ書き込まない。親は同一headの標準PR監査とacceptance検査の合格を
確認してから、`validate`成功後のpacketとbundleをPRコメントへ投稿する。
一つのコメントに収まらないデータは分割し、各partのSHA-256と順序を別manifestへ置く。
投稿本文を再取得し、ローカル生成物との一致を確認してから最終4査読を起動する。
取得不能・不一致はその版を無効とし、投稿成功と扱わない。GitHub URLだけを不変性の証拠にしない。
公開前に絶対path・private識別子のscanを行う。

packetを直接編集しない。補助説明や補助リンクは`render --auxiliary <json>`の
`notes`文字列と`refs`配列で与える。中心refはこの欄へ移せない。
修正後の`route --old <packet> --new <packet> --review <review.json>`は次工程を返すだけで、
合格判定を作らない。直接確認の資格・独立確認者・finding解消は
[共有review protocol](../../_shared/review-protocol.md)で判断する。

source、対応表、中心証拠のdigestと補助欄以外の実データが全て不変な場合に限り、
packet-only findingを直接確認へ送る。中心gateに属するfindingは、自己申告がpacket-onlyでも
fresh 4査読へ送る。schemaの意味や抽出結果を変える修正も再収集・fresh 4査読を要求する。
未知versionの旧packetを暗黙変換しない。過去の完了結果に遡及適用しない。

`ledger --bundle <bundle> --packet <packet> --review <review> --gates <gates> --out <ledger>`は
4 laneと全gateを検査する。直接確認を使う場合は`--old-packet`と`--recheck`を追加する。
review/gates/recheckは独立査読・親の統合判断を構造化した入力であり、generatorが作成する
数学判断ではない。schemaは実装の`route_findings`/`ledger`、例は対応するtestを参照する。

review入力は`packet_digest`、`implementer`、4つの`lanes`、`lane_evidence`、`findings`を持つ。
各laneには別のreviewer ID、全gateの`checked_gates`、空の`unchecked_central_claim`、
レビュー本文の`ref: {path, sha256}`を要求する。refのpathはrepo相対の保存済み本文とし、
CLIは実ファイルをhashして解決する。GitHubコメントは取得した本文を保存して参照する。
gates入力は15 gateとroot/標準PR/acceptance判定、全`completed_criteria`、全`premise_status`、
同一headの`stage_evidence`を持つ。discharge-requiredに`discharged`以外は許可しない。
recheckにも保存済み確認本文のrefを付ける。これらのIDやhashは本文の真偽を保証する署名では
ないため、親はレビューを実際に独立起動し、結果との一致を確認して入力を作る。
実装者を元laneに含む入力、直接確認者を元laneから再利用する入力、実装者IDの付替えは拒否する。

## 検証

```bash
python3 .codex/skills/target-theorem-loop/scripts/test_completion_packet.py
```

抽出器の統合試験は同梱`CompletionFixture.lean`を単一leafとして上記check/collect/render/validateで
処理する。期待する独立参照は`inputCharacterization → differenceCriterion, kernelInputCriterion`、
private helper経由の到達、型参照のみの`typedOnly`、`simp`参照である。
一般fixtureとG-118由来のサンプル比較は[回帰記録](completion-regression.md)を参照する。
