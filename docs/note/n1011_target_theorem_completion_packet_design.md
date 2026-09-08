# Target theorem completion packetの機械生成設計

対象: [Issue #4404](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/issues/4404)

この文書は、固定targetの完了監査を支えるpacket生成器と修正後確認の設計案である。
実装前の検討用メモとして、入出力、判断の担当、検証方法、既存手順への反映先を示す。
現行の完了判定は既存skillに従う。新方式の適用開始は、実装と検証を含む変更のレビュー後とする。

実装の入出力と実行手順は[completion generation](../../.codex/skills/target-theorem-loop/references/completion-generation.md)にある。
初期実装は標準ライブラリで扱えるJSON対応表を採用し、中心nodeの巡回は未確認として拒否する。
以下のYAML模式例とSCC凝縮は設計上の表現であり、初期CLIの対応形式・機能とは区別する。

## 1. 設計判断

手書きpacketを、次の三つの入力から機械生成する方式へ変更する。

1. GitとLeanから抽出した固定sourceの事実。
2. GOALの各claim、material premise、中心宣言を対応させる小さな手書きの対応表。
3. 対象を固定して実行した検証結果。

この三つから査読前packetを生成する。独立査読者の判定記録は後段のledger生成で
初めて入力する。packetを作るために、そのpacketの査読結果を要求する循環を作らない。

事実の転記・列挙・整形は生成器が担当し、claim対応の妥当性、中心証拠の十分性、
premiseの放電、非空虚性は独立数学/Lean査読が担当する。
生成の成功だけでは、数学ゲートのpassも`target-theorem-proved`も出さない。

新方式でも、固定GOALとの一致、statement strength、全material premise、certificate
provenance、proof-use、structure-field escape、route integrity、nonvacuity、全方向、
definition unfolding、dependency DAG、axiom/placeholder、artifact sync、regressionの
各判定欄を保持する。標準PRレビューと最終4査読の責務も分けたまま保持する。

## 2. 現行入力と反映先

| 現行ファイル | 実装時に反映する責務 |
| --- | --- |
| [completion-ledger.md](../../.codex/skills/target-theorem-loop/references/completion-ledger.md) | packet/ledgerの入出力、生成物への参照、schema version |
| [target-theorem-loop](../../.codex/skills/target-theorem-loop/SKILL.md) | 生成・投稿前検証・最終レビュー・修正後確認・merge後同期の呼出順 |
| [math-lean-review](../../.codex/skills/math-lean-review/SKILL.md) | 生成物とsourceの独立照合、完了時の直接確認への参照 |
| [reviewer-lanes.md](../../.codex/skills/math-lean-review/references/reviewer-lanes.md) | 4本の独立性と中心claimのcoverage、抽出事実の検算 |
| [review-protocol.md](../../.codex/skills/_shared/review-protocol.md) | finding分類、直接確認の資格、既存レビューを有効とする条件 |
| [AAT guideline](../aat/guideline.md) | 既存のfocused検証・Research全体build禁止を適用 |

共有review protocolの「完了判定には直接対応を適用しない」という現行規定と、
math-lean-review側の同規定を同じ実装変更で整合させる。変更対象はtarget-theoremの
packet-only確認に限定し、prd-completion-reviewの再実行条件は維持する。
分類・資格の本文は共有review protocolへ集約し、個別skillから参照する。
この設計メモを実装後の恒久仕様として参照する構成にはしない。

## 3. 成果物の配置と処理順

以下の新規パスと処理名は提案であり、実装時に具体的なCLIへ対応させる。

| 成果物 | 提案配置 | 編集方法 |
| --- | --- | --- |
| GOAL別対応表 | `research/completion/<goal-id>.yaml` | 手書き。固定headでレビュー |
| schema・schema説明 | `.codex/skills/target-theorem-loop/references/` | 実装と一緒にレビュー |
| Python生成器・validator・fixture | `.codex/skills/target-theorem-loop/scripts/` | 通常の実装レビュー |
| Lean抽出器 | `research/lean/ResearchLean/Tools/CompletionAudit.lean` | targeted検証と数学/Leanレビュー |
| 実行中の抽出結果とpacket | `.tmp/completion/<run-id>/` | 生成専用、Gitに追加しない |
| 確定packet・検証bundle・査読・ledger | PRコメントと保持方針を明示したartifact | digest付きで固定し、過去版を上書きしない |

対応表には宣言名とclaimの関係を置く。Git blobや監査件数、抽出edge、コマンドの
成功結果、最終verdictは手入力しない。GOAL本文は変更せず、runtime stateも追加しない。

処理は次の順序に分ける。

```text
固定source + 対応表
  → collect: Git / Lean事実と実行証拠
  → validate: schema / snapshot / ref / graph検査
  → render: canonical packetと読みやすいPR本文
  → publish-check: 標準PR監査・acceptance検査・head・artifactの確認
  → publish: packet投稿と再取得による一致確認
  → 最終4査読
  → ledger: 4査読と必要な修正後確認を統合
  → merge → GOAL/report/index/Issue同期
```

投稿前のローカル生成と検査は何回でもできる。正式レビューの起動回数とは分ける。
投稿は生成器から分離し、実行主体が投稿の権限と既存レビューの条件を確認して行う。
validator失敗時は投稿処理へ進めず、以前の成功出力を今回の成功として再利用しない。
collectは標準PR監査前にも行える。publish-checkは、同じheadの標準PR監査と
[acceptance検査](../../.codex/skills/target-theorem-loop/references/acceptance-contract.md)が
合格していることを確認する。投稿後の再取得が不一致ならその版を無効として記録し、
最終査読を起動しない。

## 4. 固定sourceと再現性

### 4.1 入力snapshot

生成器は次を固定する。

- 対象リポジトリ、base/head commit、GOAL pathとblob、対応表のblob。
- 対象owner modulesおよびそのimport依存のsource/blob一覧。
- Lean toolchain、Lake manifest、外部依存revision、抽出器・生成器・schemaのdigest。
- reportの参照節とblob、標準PR監査の対象headと取得本文digest。

過去head由来の検証サンプルに新しい抽出器を適用する場合、対象headとツールのrevisionを別欄に置く。
抽出器は別namespaceから対象をimportし、対象sourceを差し替えない。Lean versionが
異なる場合の比較は同一snapshot扱いにせず、互換性の検証結果を別途要求する。

対象と依存sourceに未コミット差分があれば確定生成を拒否する。無関係な作業を戻すことは
せず、固定commitを隔離した作業領域で処理できるようにする。import依存が含むmoduleを
黙って省略しない。解決不能・外部依存不明は検証失敗とする。

既存`.olean`はsource一致を推測して信用しない。対象snapshot、依存、toolchain、
build設定とartifact digestを結ぶ再利用可能な検証記録がある場合だけ使う。
記録がなければ親が必要な依存に限って構築し、対象ownerをfocused検証する。
全Research moduleの走査からbuild対象を自動拡大する操作やaggregate importは設けない。

### 4.2 digestの分離

- `source_digest`: 対象・import依存・toolchain・抽出器を含むsource snapshot。
- `claim_map_digest`: claim、premise、中心宣言、必要な証拠の対応表。
- `core_evidence_digest`: 抽出事実、中心経路、必要検証のscopeと結果の構造化データ。
- `packet_digest`: 投稿用packetのcanonical bytes。

直接確認では`source_digest`、`claim_map_digest`、`core_evidence_digest`の一致を要求する。
修正した`packet_digest`は変わってよく、旧値と新値を記録する。前者三つの一致も、
非中心判定の十分条件にはしない。
中心の情報を補助欄へ移して比較を回避できないよう、未知fieldはschemaで拒否し、
どのfieldを各digestへ含めるかをschema versionごとに固定する。

中心データは対応表と収集結果から作り、表示用packetから逆算しない。補助リンク・説明文は
生成時の補助入力として別に保存し、packetとともにdigestを付ける。これらを証明・放電の
唯一の参照先にすることは認めない。対応表のblobが変わる修正はheadも変わるため、
この設計の直接確認対象から外れる。schema型修正の直接確認は、収集済み中心データが
正しく、表示層だけに誤りがあった場合に限る。旧中心データを確定できない場合は資格外とする。

canonical JSONはUTF-8、key順・集合のsort・配列の順序意味を固定する。
同一の収集済み入力からの再生成はbyte一致を要求する。実行時刻・所要時間・一時path・
投稿URLは別の実行記録へ置き、同一入力の再生成を壊さないようにする。
コマンド再実行は別の実行証拠を作る。ログ自体のbyte一致を数学的同一性と混同しない。
stdout/stderrを別ファイルで保存してそれぞれhashし、実行記録から両方を参照する。
packet自身のdigestや投稿後URLは外側のmanifestに置き、自己参照hashを作らない。

## 5. Leanから抽出する事実

既存の[MigrationAudit.lean](../../research/lean/ResearchLean/Tools/MigrationAudit.lean)は、
owner moduleによる宣言列挙、`ConstantInfo`の型・値、`collectAxioms`の抽出を実装している。
この方式を参考に、完了監査用の抽出器を分離して作る。移動前後の名前を同一視する既存の
名前正規化は転用せず、完全修飾名とprivate/generated名を正確に保存する。

各宣言について次を取得する。

- 完全修飾名、owner module、対応source/blob、宣言種別、universe parameters。
- 型の構造化表現とdigest、読みやすい型表示、取得可能な値の構造化表現とdigest。
- 型中のconstant参照、値中のconstant参照、projection参照を区別した一覧。
- 公理の推移的集合。標準公理の許容基準は既存監査と一致させる。
- private、生成補助宣言、値の取得不能、source位置の取得可否。

名前・owner・型を正確に解決できない必須宣言は失敗とする。値の取得不能を依存ゼロに
変換しない。中心経路の抽出に必要なら`cannot-determine`として止める。
pretty-printer出力だけからstatement同一性を判定しない。

値の式全体を走査すると、binderの型や引数中のconstantも含まれる。
したがって「値に出現した」は構文上の事実であり、数学的に必要なproof-useを保証しない。
式中の位置を保存し、型由来か、application/let等のどの位置かを検算できるようにする。
`simp`が実際の証明項へ残した参照は抽出するが、探索時に試しただけの補題までは含めない。
sourceに書かれたtactic名や実行時call graphを復元することは要求しない。

## 6. dependency_dagの意味

### 6.1 自動抽出グラフとacceptance spine

自動抽出グラフは、指定された宣言集合とその依存を、上記の式出現規則で収集したものとする。
scope、探索を終える外部依存、取得不能を明記する。source snapshotでは全import依存の
整合を確認するが、全import moduleの全宣言を展開することは要求しない。中心宣言と
要求証拠を始点として指定owner内の到達宣言を抽出し、外部宣言への参照は名前・型・owner・
blobを持つ終端として記録する。必須routeが終端を越える場合は、必要部分へ抽出scopeを
広げてから検査する。途中打切りを到達不能と断定せず、未確認として拒否する。
これは指定scopeでのconstant参照であり、数学的な最小依存集合ではない。definitionとtype-only参照も保持し、描画時の省略と
収集時の欠落を区別する。巡回がある場合はSCCとして保持する。

packetの`dependency_dag`は、このグラフから生成するtarget acceptance spineとする。
対応表が選ぶ中心宣言には次を含める。

1. 各target conjunct・方向を担うacceptance宣言。
2. 各discharge-required premiseを放電し、acceptance側が消費する宣言。
3. certificate生成、必須route、非空虚性、固定decisionの中心となる宣言。
4. それらの接続に必要な中心predecessor。

選択したnode間の到達関係は機械抽出から計算し、次の選択nodeに至る経路を生成する。
人はedgeの実在を手入力しない。非選択nodeを経由する接続には、全ての直接hopを
確認できる経路証拠を添える。表示には安定した順序で選んだ代表経路を使い、元の到達
部分グラフへリンクする。全pathの列挙は行わず、node/edgeを一度ずつ保存する。
SCCがあれば凝縮DAGと内部node/edgeを保持する。

距離の区分と参照位置の区分を別fieldにする。

- 距離: `direct`は一つのhop、`via`は一つ以上の補助宣言を経由する複数hop。
- 参照位置: 宣言の型、値のbinder型、値のterm部分、projectionを区別する。
  型にだけ現れるものは`type-reference`として保持し、放電やproof-useの根拠にしない。

`via`の各hopにも参照位置を付ける。値のterm部分に出現することも、数学的に必要な
proof-useの十分条件にはならない。例えば使用されないlet値や型を引数として渡す式は、
構文的到達があっても中心証拠として十分かを査読者が確認する。

edgeの向きは「消費側 → 参照先」に固定する。`direct`と`via`の表示を取り違えた場合は
検査失敗とする。中心proof-use routeは各hopに値の参照を要求し、途中のhopが
`type-reference`だけで成立する経路は拒否する。型参照は別の型・仮定監査に保持する。
definitionは値から辿れる場合に経路へ含める。定義展開の意味が必要な箇所は査読で実読する。

### 6.2 完全性の担当

validatorは、対応表に書かれた必須node、経路到達、経路内のhop、要求scopeと収集完了記録の
一致を検査する。同じ抽出器の再実行だけでは抽出器自身の欠落bugを否定できない。
小さいfixtureの期待参照集合をsourceと照合して独立に定め、抽出器の全件結果と比較する。
最終Lean査読でも中心宣言の型・値・公理・経路をsourceへ戻って検算する。
GOALの自然言語から全ての中心predecessorを自動発見したとは主張しない。
4査読はGOALと証明を独立に読み、対応表がtarget conjunctや中心predecessorを落として
いないか確認する。未登録の中心predecessorを発見した場合も中心findingとして扱う。

補助constantの手作業による全列挙は通常の査読責務から外す。一方、中心経路に疑いがあれば
査読者は元の抽出グラフとsourceへ戻って調べる。生成器の選択だけで査読範囲を限定しない。

## 7. claim・premise対応表

対応表の概形は次とする。以下はschema設計用の模式例であり、G-118の実データではない。

```yaml
schema_version: 2
goal: G-example
claims:
  - id: B1.input_characterization
    goal_ref: {section: target theorem, item: B1}
    direction: iff
    declarations:
      - name: Example.inputCharacterization
        covers: [forward, reverse]
    central_declarations:
      - Example.differenceCriterion
      - Example.kernelInputCriterion
    required_routes:
      - from: Example.inputCharacterization
        to: Example.differenceCriterion
        allow: [direct, via]
      - from: Example.inputCharacterization
        to: Example.kernelInputCriterion
        allow: [direct, via]
premises:
  - id: example_input_transport
    goal_ref: {section: target material premise ledger, item: input_transport}
    role: discharge-required
    discharge_declarations: [Example.inputTransport]
    consumed_by: [Example.inputCharacterization]
```

実schemaではnonvacuity、certificateの生成元・field-content、definition unfolding、
固定decision、検証対象moduleを対応表の別欄に置く。全claim/criterion/premiseの
索引をGOAL本文と照合し、その照合自体を査読記録に残す。

`direction_coverage`はこの対応表から生成する。各claimに一つ以上のexact declaration ref、
その型、担当する方向・部分claimを表示する。一つの宣言が複数claimを担う指定は、
そのstatementが本当に全てを含む場合に認める。複合claimは部分claimへ分けて割り当てる。
validatorは空欄・重複・未解決名・未対応の登録済みclaimを拒否する。statementより広いclaim、
量化の違い、結論相当の仮定を含むものは数学査読で拒否する。

premiseの役割は対応表への申告であり、validator成功で放電済みに変換しない。
packetでは申告と実際の抽出証拠を併記し、review/ledgerで初めて査読済みstatusを付ける。
最終4査読用の入力に、前回の数学verdictや「全放電済み」という期待を与えない。
標準PR監査の合格は起動条件の確認記録として保持し、GOAL成立の証拠とは分離する。

## 8. findingと修正後確認

### 8.1 分類

| 事象 | 分類 | 処置 |
| --- | --- | --- |
| 誤った中心edge、中心predecessor欠落、type-only経路をproof-use扱い | central completion finding | 修正後fresh 4査読 |
| claimの過大割当、premise未放電、certificateへの結論移動 | central completion finding | 修正後fresh 4査読 |
| 非空虚性・固定decision・axiom・route・claim statusの変更 | central completion finding | 修正後fresh 4査読 |
| enumの値型、整形、補助参照の表現だけを直し中心証拠不変 | packet-only non-central findingの候補 | 資格ある直接確認 |
| source/head/blob不一致、古い`.olean`、抽出欠落、生成器の証拠抽出bug | integrity failure、中心への影響は未確定 | 投稿停止。既存レビューの根拠不明ならfresh 4査読 |
| 補助refと申告したが唯一の放電証拠だった | central completion finding | 降格を拒否、fresh 4査読 |

投稿前に機械検査で落ちた入力は、まだ始めていない正式レビューの「再実行」に数えない。
投稿後もすべてのfindingを記録し、未解消のまま完了にしない。

### 8.2 直接確認の資格

最終4査読をすべて実施済みで、中心の未確認・vetoがなく、残るfindingがpacket-onlyに
限られる場合だけ、直接確認でその4査読の結果を最終packetへ接続できる。
まだ実施していないlaneを直接確認で代替しない。

必要条件は次の全てとする。

1. 対象head、GOAL、Lean sourceと依存、toolchain、claim/premise対応、中心経路が不変。
2. 証拠抽出・schema意味・検証scope・公理基準・statusの判定規則が不変。
3. 各修正が既存findingと対応し、中心証拠の削除や未確認の非中心欄への移動を含まない。
4. 再生成と全機械検査が成功し、必要なdigest比較および入力/生成物の実diffを提示できる。
5. 実装者以外の新規確認subagentが、資格と解消をsourceに照らして確認する。
   元findingの根拠、旧/new入力、対象source、検証結果を渡し、修正者の分類を結論として渡さない。

判定不能、資格外の差分、新しい中心findingはfresh 4査読へ戻す。新しい非中心findingは
記録して直接確認の対象へ追加し、未解消のものがあれば完了を保留する。
最終監査では、通常cycleの「範囲外の非中心findingをmerge後へ引き継ぐ」規定を適用しない。
中心修正の正式再実行は既存cycleの回数制限に従い、上限後は次cycleへ戻す。

確認記録には、旧/new packet digest、4 laneの元記録、finding ID、変更field、
不変性の証拠、検査結果、確認者の資格判定を持たせる。
単一の修正後確認ではfindingの解消と資格を確認し、元laneのverdictを保持する。
最終ledgerは「元4査読 + 有資格の修正後確認」を参照して全findingの解消を判定する。
これを満たした場合にのみ、各laneの有効な承認と統合`No major findings`を記録できる。

## 9. validator・レビュー・ledgerの責務分担

validatorは次を機械検査する。

- 必須field、enumと値型、未知field、重複key、schema version。
- head/blob/ref、owner、宣言種別、型/値digest、依存snapshotの整合。
- 登録済みclaim/premiseの未対応、宣言refの欠落、重複、方向schema。
- 抽出scope、必須node、direct/via/type区分、経路hop、SCC/凝縮DAG。
- コマンドの引数配列、作業directory、scope、exit code、出力artifact/hash。
- 公理・placeholder等の機械判定、全要求gateの記録欄と証拠欄。
- 投稿対象headの再確認、artifactを再取得したdigestとmanifestの一致。

数学の真偽、意味上のstatement strength、premise役割の妥当性、非空虚性、
証明の中心経路の十分性、自然言語claimの完全性は4査読が判定する。
sourceのconstant参照を、これらの自動判定へ置き換えない。

ledger生成器は、固定対象・packet・独立レビュー・修正後確認の参照を照合する。
全ゲートpass、全laneの有効な承認、中心未確認なし、全finding解消、root recheckを
確認してから完了ledgerを生成する。生成器自身は査読者やrootの判断を作成しない。
merge後の文書同期は別のheadで記録し、証明判定のheadを差し替えない。
査読前packetのartifact syncはGOAL・report・Issueが同じcandidateを指すことを、
完了ledgerではその一致と未解消findingの有無を、merge後同期ではterminal記録を確認する。
最終レビュー前にGOALやIssueの完了statusを要求しない。

機械判定と意味の判定は、gateごとに次の証拠へ分ける。実装では現行ledgerの全gate名を
この一覧へ対応させ、欠落をschema testで拒否する。

| gateの対象 | 機械が確認するもの | 査読・統合で確認するもの |
| --- | --- | --- |
| GOAL・statement・全方向 | 固定ref、型、claim対応の形式 | 量化・強さ・全条項と両方向の充足 |
| premise・certificate・field escape | 宣言/型/生成元/消費先のref | 全放電、結論相当の入力への移動なし |
| proof-use・route・DAG・definition | 抽出参照、経路、定義実体 | 中心経路の正確性・十分性 |
| nonvacuity・regression | witness/decisionと実行証拠の存在 | 必要な正負例、固定入力上の実際の成立 |
| axiom・placeholder | 固定scopeの抽出/scan結果 | scopeの十分性、公理基準との一致 |
| artifact sync | head/digest/refと段階の整合 | claim statusの妥当性、未解消findingなし |

GitHubコメントは編集できるため、URLだけを不変性の根拠にしない。取得本文digestと
packet manifestを一緒に保存する。大きい抽出結果は保持方針を明示したartifactへ分離し、PR本文には
検算に必要な索引とhashを載せる。分割投稿では全partのdigestと順序をmanifestに記録する。
初期実装では、通常のPRコメントに収まるmanifestと分割データを使う経路を必須とする。
大きいbinary等に別保存先が必要な場合は、保存先・保持期限・取得方法をmanifestへ記録する。
査読/ledger生成時に必要なデータを取得できない場合は保留する。自動失効するCI artifactを
唯一の長期証拠にせず、検証手順から再取得・再生成できるsourceも固定する。
公開bundleにはrepo相対pathを使い、実行環境の絶対path等は投稿前に検査する。

## 10. 一般的な回帰fixtureとG-118の検証サンプル

検証は小さい一般的なfixtureを中心に行い、G-118を実際の監査事故に基づくサンプルの
一つとして使う。誤りの種類と中心証拠への影響を保つ範囲で、必要な宣言・対応表・
findingを抽出する。G-118全体の再生成や再監査は完了条件に含めない。
サンプルの出典はhead `a661c341e9880eaa16d00b12c18bad5b915756b6`、GOAL blob
`64d9ec2cd1b771c929db043752fc8c477eddcf6f`と、[最終packet](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/pull/4403#issuecomment-5557101743)、
[最終4査読](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/pull/4403#issuecomment-5557145097)、
[完了ledger](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/pull/4403#issuecomment-5557153114)とする。
使用する出典の取得本文digestと、サンプルへ抽出した範囲をfixture manifestへ固定する。
簡略化したfixtureには、実例から保った関係と省略した要素を記録する。
G-118の宣言数やmodule数を、新方式の試験規模や合格条件にはしない。

| fixture | 必須の期待結果 |
| --- | --- |
| 小さい固定sourceと正しい対応表からの生成 | 抽出からpacket生成・検証まで成功し、同一入力で再生成が一致 |
| `iff_inputConditions`のpredecessorを`qualifiedComparisonSubgroup`だけに置換 | 必須中心経路の欠落を拒否。直接参照の偽装も拒否 |
| 中心`T`だけからfull `Γ`が得られると割当 | 中心route finding、fresh 4査読 |
| 型にしか現れない参照、未使用let値の参照を中心proof-useへ割当 | 型由来は機械検査で拒否。term出現だけの過大評価は意味の査読でveto |
| 必須中心nodeを対応表から削除 | 登録済み要件の欠落はvalidatorで拒否。要件ごと削除した場合はGOAL対照レビューでveto |
| C1t/C2や射影・核・torsorを不足する代表宣言にまとめる | direction overclaimとしてレビューでveto |
| 正しい複数宣言へのclaim割当 | 参照検査を通し、statement coverageをレビュー |
| `structure_field_escape`/`route_integrity`の値型不一致 | 投稿前schema検査で拒否。意味不変の修正にfull restartを要求しない |
| 必須証拠が別途存在する補助refの欠落 | integrity finding。投稿後は不変性確認と直接確認で解消 |
| 唯一の放電ref欠落を「補助」と申告 | central finding。直接確認の資格なし |
| 古いhead/blob/`.olean`、未知schema、抽出不能 | 投稿拒否、失敗を空集合やpassにしない |
| 生成器の抽出規則を変えて同じpacketを主張 | digest/入力差分で既存レビューの流用を拒否 |
| 4 laneのうち1本未完了、期限切れartifact、未解消finding | ledger生成を拒否 |
| 整形のみの修正と、対応表blobを変える修正 | 前者は中心digest不変を検証して直接確認、後者はfresh 4査読 |
| 中心digestを復元できない旧packet、旧schemaの完了記録 | 直接確認へ流用しない。歴史的な完了結果はその版の証拠として保持 |
| canonical再生成・packetの手編集・分割part欠落 | 同一入力はbyte一致。手編集・part欠落は拒否 |

機械検査fixture、レビュー判断fixture、routingの状態遷移fixtureを分離する。
自然言語overclaimをvalidatorが自動検出したようなmock testは作らない。
意味上のfixtureは、具体的な誤った対応表と対応するsourceを独立査読者へ渡してvetoを確認する。
routing fixtureではその有資格なfindingを入力にして、fresh/直接確認/保留の遷移を検証する。
LLM査読は決定的なunit testにしない。意味上のfixtureは導入時の独立確認として結果を固定し、
通常の回帰実行ではschema・抽出・生成・状態遷移の決定的な検証を行う。

## 11. 旧手順との比較と実装順

G-118の[撤回記録](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/pull/4403#issuecomment-5557020461)は、
Lean本文不変でも中心predecessorが誤っていた実例として使う。
変更分類は「packetだけ」というファイル範囲ではなく、失われた証拠の役割で判定する。

比較記録には、イベントID、入力packet digest、finding、実際の旧手順、提案手順での
処置、full 4-lane batch数、直接確認数を持たせる。標準PR監査とcompletion監査を
別集計し、投稿前lint、途中で中断したbatch、完了したbatchを区別する。
コメント時刻だけから実行回数や所要時間を推定しない。追跡不能な回数は不明とし、
サンプルに対する新方式の判定結果を歴史的実績として書かない。
比較範囲は選んだ監査事例に固定し、G-118全工程の再実行回数の復元を要求しない。

実装は次の順序とする。

1. 小さいLean fixtureで宣言owner・型/値・direct/type/projection・private/generated・
   `simp`・取得不能の抽出を検証し、scopeとserializerを固定する。
2. 対応表schema、抽出結果schema、生成器、投稿前validator、canonical再生成を実装する。
3. 必須中心routeの照合、direction grouping、snapshotと検証artifactの整合を実装する。
4. 共有review protocol、2 skill、reviewer lanes、completion-ledgerを同じ変更で整合させる。
   field説明はschema側へ集約し、skillには呼出順と判断の参照だけを置く。
5. 一般的なfixtureとG-118由来の検証サンプルを実行し、選んだ監査事例の旧/新routing比較を記録する。
6. 実装PRの内容レビュー、必要な検証とCIを経て適用開始を記録する。

切替はschema version単位で行う。旧packetから新packetへの暗黙変換や、過去の完了GOALへの
遡及適用は行わない。新方式で最終監査を開始するcandidateは、対応表と抽出結果を新schemaで
揃える。fixture導入前やgenerator未実装の段階では、現行skillの完了手順を維持する。

新しい恒久CI jobは追加しない。検証は対象を固定したローカル手順として実装する。
subagentのLean実行は既存guidelineの制限に従い、抽出器を口実にbuildを委譲しない。

完了条件は、全fixtureの期待結果、G-118由来の監査事例比較、同一入力の再生成一致、必須gateの保持、
既存手順との衝突解消、失敗時の投稿/ledger拒否、中心/非中心の独立分類確認が揃うこととする。
抽出器が中心証拠を取得できない、対応表の十分性を確認できない、または必要なartifactを
再取得できない場合は、その具体的な失敗を残して新方式の適用を保留する。
