# Completion packet生成と検査

version 3では、固定sourceとJSON対応表からpacketを生成する。
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
実行ファイルを使う。生成器はsourceに最も近い`lake-manifest.json`から`lake env`を解決し、
呼出元の任意`LEAN_PATH`をfocused checkや抽出に使わない。
receiptは選択ownerの固定head、source blob、exact command、出力olean、stdout/stderr、
Elanが対象toolchainへ解決したLean/Lake実行artifact（shimではない）のhashとversion、
最寄りの`lake-manifest.json` blobを結ぶ。check、抽出、validate時の再抽出は、いずれも
その解決済みLeanを絶対pathで実行する。

runtime importはこのfocused elaborationの実行環境であり、数学claimの証拠ではない。
外部packageや非選択moduleについてsourceからoleanを生成したとは主張しない。
全importのreceipt、全artifact hash、推移closureの列挙、content-addressed registryを要求しない。
`check`を全Research moduleのloopへ使わず、対応表で選んだownerだけに実行する。
subagentの実行制限は[AAT guideline](../../../../docs/aat/guideline.md)に従う。

`collect`は複数の`--receipt`を受け取り、選んだownerの宣言をLeanから抽出する。
選択ownerのartifactだけを一時overlayの先頭へ置き、依存はsourceのmanifestから解決した
Lake環境から読む。同一ownerの異なるdigestは拒否する。rootとResearchのように複数の
Lake packageからownerを選ぶ場合は、各receiptのmanifest由来`LEAN_PATH`を結合するが、
Lean toolchain artifactが一致しない混在は拒否する。
manifestやtoolchainが変わればvalidateを失敗させる。runtime dependency artifactの同一性や
source-build provenanceは保証範囲に含めず、その限定をpacketと最終査読で明示する。
`--base`で比較元commitを指定でき、省略時はその時点の`origin/main`をcommitへ解決して固定する。
型・値・owner・private名・公理・参照位置に加え、宣言種別・universe parameter一覧・
読みやすい型表示・source位置を記録する。位置を環境から取得できない場合は`source_range: null`
とし、取得不能を明示する。`validate`はGitと実行出力を検算し、
対象oleanから再抽出してbundleと一致することを確認する。全sourceのGit blob一覧は
入力整合のための読取りであり、全moduleのelaborationではない。
receiptはコマンド実行証拠なので手で作成・編集しない。第三者査読は選択ownerのreceiptと
sourceを照合し、必要な対象だけを独立に再実行する。

byte一致を要求する再生成は、同じ保存済みbundleと補助入力からのrenderを指す。
check/collectの再実行では、head、`--base`の解決commit、platformを含むLean version、
toolchain artifactのhash、出力先のrepo相対pathや実行記録もpacket digestへ影響する。
同じ環境での再実行だけではdigest一致を保証しない。別環境の検証では`result: pass`と
検査内容を確認し、元のpacketとの同一性を示す場合はこれらの入力も照合する。
元bundleの`validate`は、現在のsource snapshot・toolchain・artifactが記録と異なれば
失敗する。この不一致を無視して承認しない。

各宣言の型・値ごとの全constant名は、独立したLean標準`Expr.getUsedConstants`でも収集する。
独自の位置付き走査の全件集合と照合し、欠落も余分な参照も拒否する。projection名は
`Expr.const`と別のmetadataなので、この集合比較から分ける。全Expr constructorを持つ
literal ASTのfixtureでは、参照名・site・位置をPythonの手書き期待値と完全一致で検査する。

対象source、GOAL、report、対応表、extractorは固定headに存在する必要がある。
未コミット変更・head/blob不一致・出力欠落・未知version・抽出不能は投稿不可。
対応表の`fixed_goal`はtarget固定時のcommit/path/blobを持つ。現在のGOAL blobはlifecycle状態の
追跡用に別記し、claim quoteとtarget判定は固定版本文から解決する。
version 2 packet/receiptをversion 3へ暗黙変換しない。

## 対応表と数学判断

- `criteria`と`claims`はGOALの全completion criteriaに対応させる。各claimはGOAL内の
  literal quote、方向、複数のexact declaration名、中心node、必須routeを持つ。
- `premises`はGOALの全material premise行を列挙する。roleの申告だけで放電と判定しない。
  discharge-requiredには放電宣言と実際のconsumerを対応させ、値の経路を要求する。
  一行の`declarations × consumed_by`の全組を検査する。消費先ごとに異なる宣言が担当する
  場合は、対応する組だけを持つ別行に分け、同じGOAL quoteと別IDで役割を明示する。
- `evidence`には現行15 gate全ての宣言参照を置く。artifact sync等のコマンド・文書証拠は
  bundleのsource/receiptと併せて読む。宣言参照だけでgateをpassにしない。
- `direction_coverage`は各claimへ複数のexact refと型を添えて生成する。同じ宣言を複数claimへ
  割り当てる場合は、そのstatementが全てを支えることを査読する。
- 外部packageの定理をmaterial predecessorとして使う場合だけ、`external_predecessors`へ
  exact declaration、owner、GOAL quote、consumerを登録する。生成器は選択ownerの値からの
  到達と抽出された型を固定し、owner名に対応するtracked Lean sourceがrepo内にないことを
  検査する。同一repoのterminalをexternalと申告してfocused receiptを回避できない。
  4本査読はそのstatementと数学的使用を直接確認する。

機械検査は登録済みcriteriaの欠落、空ref、未解決ref、型不正等を拒否する。
GOAL全体からのcriterion/premiseの選び落とし、statementより広いclaim、量化の弱化、
結論を仮定・certificate fieldへ移した実装は、独立4査読がsourceに基づいて判定する。
対応表を唯一の査読対象リストにせず、GOAL全体から逆照合する。

## acceptance spineと抽出グラフ

`dependency_dag`はtarget acceptance spineである。各conjunct、全discharge-required、
certificate生成元、必須route、固定decision、非空虚性の中心nodeを含める。
`core.gate_evidence`の宣言も必須nodeとなる。edgeは消費側から参照先へ向ける。

指定ownerの型と値にあるconstant参照を自動列挙し、非選択宣言は型/owner付き終端にする。
生成器は選択node間の到達を計算し、directは1 hop、viaは補助宣言経由の経路として
全hopを出力する。必須routeを証拠なしにdirect扱いできない。同一repoのmaterial predecessorを
越える必須routeは、必要なownerを追加して再収集するまで未確認である。外部packageの定理を
material predecessorとして使う場合はexact declarationとstatementを4本査読が直接確認する。
runtime importの存在だけをpremise dischargeやproof-useに数えない。

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
未知versionの旧packetを暗黙変換しない。version 2以前のpacketや過去の完了結果に遡及適用しない。

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
python3 .codex/skills/target-theorem-loop/scripts/integration_completion.py --case fixture
```

抽出器の統合試験は同梱`CompletionFixture.lean`を単一leafとして上記check/collect/render/validateで
処理する。期待する独立参照は`inputCharacterization → differenceCriterion, kernelInputCriterion`、
private helper経由の到達、型参照のみの`typedOnly`、`simp`参照である。
統合scriptは`--case`で必ず一つのleaf/caseだけを選び、一回の実行で複数leafを順次
elaborateしない。`--case external`の`CompletionExternalFixture.lean`はLake解決した外部packageと
repo-local runtime importを持つ単一leaf canaryであり、推移closureのelaborationやartifact
registryなしにfocused ownerを抽出できること、およびrepo-local/external owner分類を確認する。
`reference`、`shadow-a`、`shadow-b`、`repo-predecessor`も必要な対象を個別に指定して実行する。
一般fixtureとG-118由来のサンプル比較は[回帰記録](completion-regression.md)を参照する。
