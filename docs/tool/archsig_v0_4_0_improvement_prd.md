# ArchSig v0.4.0 改善 PRD — measured_zero 純度 / 行レベル assumption 依存 / 境界の機械可読化 / ArchMap atom 語彙 lint

## 問い

この PRD のすべての要求は、次の問いに仕える。

```text
問い:
  v0.4.0 の AG measurement path が「肯定的に言い切る」と決めた三つの継ぎ目 ——
  ゼロの根拠・violated の波及・沈黙の表現 —— を、
  新しい測定を一切足さずに、契約の内側でより正確に言い切れるか?
```

v0.4.0 は H^1 を語れるようにした release である。本改善は、その言い切りが
依拠する packet 出力契約(structuralVerdict / analyticReading / assumptions /
nonConclusions)と、その手前にある入力 ArchMap 契約の継ぎ目を締め直す。主問いには、
次の従う問いが続く。

```text
ゼロは「測ったゼロ」か「測れなかったゼロ」か —— 区別して言い切れるか?      (R1)
violated は packet 全体を潰すのか、依存 verdict 行だけを潰すのか?          (R2)
沈黙は、どの結論に従属し、なぜ語れないのか —— 機械可読に言い切れるか?      (R3)
atom は AAT が公理として定義した種別の語彙に属するか —— 語彙外を弾けるか?  (R4)
```

各要求の採否は、この問いで読む。新しい invariant・verdict・推測を導入する変更、
結論幅を広げる変更、沈黙を forecast / proof にすり替える変更は、それ自体に
価値があっても本 release に入れない。三要求はいずれも「既に packet 内に局所的に
存在する事実」を、正確に・型付きで・conclusion-first に表へ出すことに限定する。

この改善の上位には、v0.4.0 から続くプロジェクトの問いがある:
「AG 本文の finite measurement geometry は、実際のコードベースに当たる道具として
本当に動くか?」。v0.4.0 がその最初の答えだったとすれば、本 PRD は
**その答えを安心して使える状態に固める** hardening の位置づけである。

## 中心方針

v0.4.0 が計測の数学的基盤を AG 本文へ載せ替える release だったのに対し、本改善は
v0.4.0 が敷いた契約 —— packet 出力契約と入力 ArchMap 契約 —— の
**健全性と表現の継ぎ目を締め直す hardening release** とする。新しい
evaluator・invariant・verdict 値は足さない。四要求はいずれも次の原則に従う。

```text
既に契約内に局所的に存在する事実を、
  正確に   (R1: ゼロの素性)
  局所的に (R2: violated の帰属)
  型付きで (R3: 沈黙の構造)
  語彙内で (R4: 入力 atom 種別)
conclusion-first に表へ出す / 受け入れる。新しい測定・推測・外界検証は導入しない。
```

互換性方針: 本改善は AG measurement path(`archmap/v2` + `measurement-profile/v1`
-> `archsig-measurement-packet/v1`)に閉じる。legacy v1 structural path
(`archmap/v1` + `law-policy/v1`)は変更しない。packet schema へのフィールド追加
(R2 / R3)と atom-kind 語彙 artifact の新設(R4)は後方互換(既定値・compat view・
additive)を保ち、既存 fixture を回帰させない。ただし R4 の語彙 conformance は、
公理外 atom を **意図的に** fail-closed で弾く(これは互換性破壊ではなく契約の明示化)。

本 release は v0.4 系の hardening point-release(例: v0.4.1)として降ろす。

> Provenance: 本 PRD の三要求は、ArchSig 改善 idea の多角生成 + 境界規律審査
> (idea-forge)で得た 27 生存案から、互いに直交し全て境界クリーンな三本として
> 選定した。クラスタ・代表案・淘汰理由は `.tmp/archsig_idea_forge_digest.md` を参照。

## 背景

三つの継ぎ目は、いずれも現行コードに具体的な裏付けがある(行番号は調査時点)。

- **ゼロの非対称(R1)**: `selected_cover_contexts` が空のとき、cech の
  `edge_cochain_is_coboundary`(`ag_measurement.rs:5795-5819`)は空入力でループせず
  `true` を返し、H^1 が自動で `measured_zero` に化ける
  (`ag_measurement.rs:3689-3703`)。一方 laplacian / tor / square-free は同じ
  空入力を `not_computed` に落としている(`ag_measurement.rs:726-746`)。cech だけが
  非対称に取り残され、profile author が cover を絞った結果が静かに SAFE ゲートへ
  化けうる。`measured_zero` が CI 緑条件になりうる v0.4.0 で、これは最も静かな
  偽陽性である。
- **violated の粗い波及(R2)**: CBI ledger は violated を記録するが、packet は
  「どの verdict 行がどの assumption に依存するか」を encode していない。
  `insight_boundary_digest`(`ag_measurement.rs:1896` の `blocking = violated +
  not_computed`)と packet 全体 fail-fast(`ag_measurement.rs:6401-6411` 系)が、
  無関係 evaluator の violated を独立 measured_zero まで巻き添えにする。v0.4.0 で
  6 evaluator(cech / square-free / tor / laplacian / period / transfer)が同一
  packet に共存するのが常態化し、巻き添えが日常的に起きる。各 evaluator は既に
  theorem_ref 付き assumption と verdict を同一スコープで共産しているため、依存辺は
  新規 authoring なしに既存配線への backreference で張れる。
- **沈黙の文字列性(R3)**: 非結論は `non_conclusions: Vec<String>`
  (`src/schema/measurement.rs:16`)として平坦な文字列で出ており、どの結論を
  qualify するか・なぜ語れないかが型で表現されていない。summary / viewer の
  conclusion-first 規律は脆い文字列ヒューリスティックに依存する。v0.4.0 で
  `reading_id` / `structuralVerdictRef` が安定したため、境界を id で scope に
  紐づける土台が初めて成立した。
- **atom 種別の野放し(R4)**: ArchMap v2 の atom は `kind` / `subject` / `axis` が
  いずれも freeform な `String`(`src/schema/archmap.rs:47-51`)で、AAT 数学本文が
  公理として定義する atom 種別の語彙に属するかを検査する経路が無い。語彙外の任意
  文字列を atom として書き込め、それが measurement まで素通りする。AAT は Atom を
  公理とする純粋数学であり、その「公理的に定義された種別の語彙」を機械可読な
  artifact contract として宣言し、入力時に lint する境界が空白になっている。

四者は独立だが合流点を持つ: R1 が生む `empty_selected_scope` と R2 が生む
`violated_assumption` の波及は、いずれも R3 の BoundaryStatement の `kind` として
表に出る。R4 は入力境界側で同じ語彙規律を担い、R3 の `out_of_selected_vocabulary`
kind と対をなす。R3 を schema 基盤、R1 / R2 / R4 をその供給源・適用先として設計する。

## アウトカム

本改善の完了時にユーザー(コードベースを計測するアーキテクチャ責任者)が得る
成果を、ユースケースとして定義する。各ユースケースは要求 ID への対応を持つ。

### UC1. 「ゼロ」を信頼してマージできる(R1)

空スコープ由来の見せかけゼロが `not_computed`(reason: `empty_selected_scope`)
として分離され、緑 SAFE ゲートに化けない。cech が laplacian と同じ空ガード規律で
揃い、構造 evaluator 全体でゼロの素性が一貫する。

### UC2. violated が出ても、依存しない結論が生き残る(R2)

violated assumption の波及が、それに依存する verdict 行だけに局所化される。
無関係な measured 結論(特に H^1 ゼロ)が boundary に巻き込まれず、conclusion-first
を保つ。依存を宣言しない行は従来どおり保守的 fallback に倒れ、安全側が default。

### UC3. 沈黙を型で扱える(R3)

沈黙・非結論が「何を語らないか(`kind`)・どの結論に従属するか(`scopeRefs`)・
なぜ語れないか(`reason`)」を持つ機械可読 qualifier になる。後段(viewer #2082 /
FieldSig handoff / self-audit)が文字列を再解釈せず型で扱え、非結論の主役化が
schema validation で構造的に防がれる。

### UC4. ArchMap に公理外の atom が入らない(R4)

AAT 数学本文が公理として定義した atom 種別の語彙に属さない `kind` を持つ atom が、
入力時に lint で弾かれる。著者は measurement を回す前(`archmap` lint)に、あるいは
遅くとも `analyze` の入力 validation で、語彙外 atom を atom id・違反 token つきで
知らされ、公理外の種別が measurement へ素通りしない。

### ユースケース横断の共通アウトカム

新しい測定を一切足さずに、packet の「言い切り」の正確さ(R1)・局所性(R2)・
表現(R3)と、入力 ArchMap の語彙健全性(R4)が一段上がる。blocked / unmeasured /
not_computed と measured_zero の区別は、本改善でむしろ強化される。

## 設計原則: 既存事実の正確な表出に閉じる

- **新規測定ゼロ**: 本改善は invariant・verdict 値・evaluator を追加しない。
  R1 は空判定、R2 は既存共産物への backreference、R3 は既存非結論の typed 化に閉じる。
- **推測・補完の禁止**: 依存辺(R2)も境界(R3)も、ArchSig が推測・発明・補完
  しない。evaluator が同一 measurement 内で既に共産した theorem_ref / 既存結論 id
  への syntactic 参照のみを使う。
- **未宣言は保守 fallback**: 依存を宣言しない verdict は packet-level の保守扱いに
  戻す(楽観禁止)。宙に浮いた境界は schema validation で reject する。
- **measured_zero へ潰さない**: R1 / R2 はいずれも measured を measured_zero へ
  昇格する経路を作らない。blocked / unmeasured / not_applicable を別状態として
  保つ。
- **conclusion-first 維持**: 散文 surface は SAFE_WITHIN_POLICY 等の肯定的結論を
  主役に保ち、境界・非結論を qualifier として従属させる。
- **境界規律**: 結論は profile / cover / evidence contract 相対に閉じる。source
  真実・semantic correctness・global safety・zero curvature・Rust↔Lean 対応・Lean
  theorem discharge は要求しない。FieldSig 領分(forecast / governance /
  longitudinal / calibration)に踏み込まない。
- **語彙境界の外在化(R4)**: AAT は Atom を公理とする純粋数学のまま保ち、「公理的に
  定義された種別の語彙」は AAT 内部の判定ではなく ArchMap 側の artifact contract
  (語彙 artifact)として外在化する。linter は宣言語彙への構文 membership のみを検査し、
  ある種別を公理に加えるべきかや atom が source を正しく観測しているかには沈黙する。

## 要求

### R0. 本 release を v0.4 系 hardening release として定義する

- 新規測定を伴わない、packet 出力契約と入力 ArchMap 契約の健全性・表現改善に限定した
  release とする。
- スコープを AG measurement path に閉じ、legacy v1 structural path を変更しない。
- 優先順位を R1(ゼロ純度)-> R4(入力語彙 lint)-> R3(境界 schema 基盤)->
  R2(行レベル依存)の順で定義する。R1 と R4 は独立した fail-closed gate で先に立てやすい
  (R4 は入力側、R1 は出力側)。R3 を R2 の前に置くのは、R1 / R2 / R4 の出力が R3 の
  `kind` に合流するためである(R2 の実装が R3 の typed boundary に書けると最も綺麗に噛む)。

### R1. vacuous-zero ガード: 空スコープ由来の measured_zero を not_computed に分離する

- cech evaluator(`ag.cech-obstruction@1`)に scope-nonemptiness 前提を導入する。
  `selected_cover_contexts` が空(cover 未発見 / 空 context_ids)、または観測対象の
  1-skeleton(`cech_edges` を含む)が一つも実体化しないとき、`measured_zero` では
  なく `not_computed`(reason: `empty_selected_scope`)を返す。これは laplacian の
  `cells.is_empty()` / `edges.is_empty()` 早期 return と同型のガードを cech へ
  対称化するものである。
- 同パターンを全構造 evaluator で点検し統一する。既に空を `not_computed` に落として
  いる laplacian / tor / square-free は現状維持とする。
- 空スコープを CBI ledger に「U-adequate cover で非空 1-skeleton が選択される」
  evaluator-relative precondition の `violated` として記録する。これにより当該 cech
  verdict は R2 の経路で `not_computed` に落ちる(R1 と R2 の合流点)。
- `reason` 文言は contract 内事実(非空を期待したが空だった)に限定し、cover 選択への
  規範判断・批判・author 意図の推測を含めない。
- viewer / summary surface で空スコープ `not_computed` を緑(SAFE)ではなく blocker
  として表示し、conclusion-first を崩さない。

### R2. 行レベル assumption 依存: violated の波及を依存 verdict 行に局所化する

- `AgStructuralVerdictV1` に `dependsOnAssumptions: Vec<String>`(各要素は packet 内に
  実在する `AgAssumptionLedgerEntryV1.theorem_ref` への参照)を追加する。各 evaluator
  が同一 measurement 内で既に共産している assumption の theorem_ref を verdict 行へ
  機械配線する(新規の数学判定は無い)。
- packet 後処理に単一 propagation pass を入れる。status==`violated` の assumption に
  `dependsOnAssumptions` で繋がる verdict 行のみ `not_computed` に正規化し、reason に
  `depends_on violated <theorem_ref>` を記録する。依存しない measured 行はそのまま
  保持する。
- packet 全体 fail-fast を、「verdict が measured_* かつ `dependsOnAssumptions` に
  violated 行を含む」場合に限定発火するよう締め直す(現状 `ag_measurement.rs:6401-6411`
  系の粗い packet-level 発火を精緻化)。
- 依存を宣言しない(`dependsOnAssumptions` が空の)verdict は、従来どおり packet-level
  の保守 fallback に戻す。未宣言 = 沈黙として扱い、依存を補完しない(楽観禁止、
  安全側 default)。辺の宣言漏れで真の依存がすり抜けうるが、これは「未宣言=沈黙」
  規律に沿った soundness のトレードオフであり、巻き添えを増やす方向の粗さではない。
- `insight_boundary_digest` / summary の boundary 表示を依存グラフ駆動へ更新する。
  既存の packet-level violatedCount / blockingCount は温存しつつ、「この measured 行は
  当該 violation の依存外で生存している」を行ローカルに明示する。CBI 三値
  (checked / assumed / violated)と conclusion-first を保つ。

### R3. BoundaryStatement v1: 非結論を機械可読 qualifier に格上げする

- `archsig-boundary-statement/v1` schema と Rust 型
  `BoundaryStatementV1 { id, kind, scopeRefs, reason, text }` を `src/schema/` に
  新設する。`kind` は ArchSig が実際に出力している沈黙状態のみを列挙する 6 値:
  `silence_by_design` / `out_of_selected_vocabulary` / `unmeasured_support` /
  `violated_assumption` / `blocked_method` / `not_applicable`。
- packet の `non_conclusions: Vec<String>`(`src/schema/measurement.rs:16`)を
  `boundaryStatements: Vec<BoundaryStatementV1>` に格上げする。後方互換のため旧文字列を
  各 statement の `text` に自動移送し、シリアライズ時に旧 `nonConclusions` 文字列 view も
  併記する compat レイヤを残す。
- 非結論を出力している既存箇所(`ag_measurement.rs` / `main.rs` の
  nonClaims / nonConclusions、`reports/pr_review.rs`、`archsig_analysis_packet.rs` の
  REQUIRED_NON_CONCLUSIONS、`schema/analysis_packet.rs` の各 `non_conclusions`)を
  typed builder 経由の生成に置換する。
- scopeRefs validation: 各 statement は既存 id へ解決可能でなければならない。解決先は
  `AgAnalyticReadingV1.reading_id`、structural verdict ハンドル、analysis-packet 内の
  conclusion id。scopeRefs が空、または未解決の境界は schema validation で reject する。
- R1 の `empty_selected_scope` は `kind=blocked_method`(または専用 reason)として、
  R2 の violated 波及は `kind=violated_assumption` として、いずれも対応する
  `not_computed` verdict に scopeRefs で従属して表れる。`blocked_method` /
  `unmeasured_support` / `not_applicable` は measured_zero に潰さず別 kind として
  明示分離する。

### R4. ArchMap Linter: 公理外 atom 種別を入力時に弾く

- AAT 数学本文が公理として定義する atom 種別を、機械可読な **atom-kind 語彙 artifact**
  (`aat-atom-vocabulary/v1`)として宣言する。各語彙 entry は許可される
  `kind` token と、AAT 数学本文の定義箇所への provenance ref(`doctrineRef` /
  `theoremRef`)を持つ。この artifact は AAT 公理そのものではなく、公理の
  **artifact-side projection(authoring contract)** である。
- ArchMap v2 validation に atom-kind 語彙 conformance check を追加する。各 atom の
  `kind`(`axis` / `subject` token も対象に含めうる)が、ArchMap の宣言
  する extraction n / doctrine から解決した語彙集合に **構文的に属するか** を検査し、
  語彙外 token を持つ atom を lint error として弾く。現状 `kind` / `subject` / `axis`
  が freeform `String`(`src/schema/archmap.rs:47-51`)である点を、宣言語彙への構文
  membership で締める。
- この check を二つの surface で共有する。(a) `analyze` の入力 validation 段で
  fail-closed に弾き、公理外 atom を measurement へ素通りさせない(enforcement パス)。
  (b) `archmap` サブコマンドの lint として、measurement なしの
  authoring dry-run で著者へ早期に返す(authoring feedback パス、idea-forge #18 / #20
  の C8 系)。
- 出力は conclusion-first・肯定形を主役にする。語彙内なら
  `ATOMS_WITHIN_DECLARED_VOCABULARY` を主結論とし、語彙外 atom はその atom id・違反
  token・期待語彙 ref を持つ concrete な lint error として最小限に列挙する(非結論一覧を
  主役化しない)。
- 境界ガード: linter は **token 語彙 conformance のみ**を検査し、atom が source code を
  正しく観測しているか(semantic correctness)は検査しない —— それは ArchMap author /
  extractor の責務である。語彙の補完・推測・拡張をせず、語彙外は弾く(語彙を増やすのは
  doctrine / 数学本文 author の宣言行為であり、linter は沈黙して弾くのみ)。Lean 対応 /
  theorem discharge を要求せず、語彙 artifact は provenance ref 付きの token 契約であって
  AAT 公理の証明ではない。AAT 本文は純粋数学のまま保ち、種別語彙の境界を ArchMap 側の
  artifact contract として外在化する。lint error の reason は「宣言語彙に属さない token」
  という contract 内事実に限定する。

## スコープ

この PRD のスコープは次である。

- R0-R3 の要求。
- `archsig-measurement-packet/v1` への後方互換なフィールド追加
  (`dependsOnAssumptions`、必要なら `verdict_id`、`boundaryStatements`)。
- cech evaluator の空ガード対称化と、構造 evaluator 横断の空ガード点検。
- violated 波及の行レベル propagation pass と packet-level fail-fast の限定発火化。
- `archsig-boundary-statement/v1` schema と typed builder / validator。
- atom-kind 語彙 artifact(`aat-atom-vocabulary/v1`)の新設と、extraction n / doctrine
  からの解決、ArchMap v2 validation への語彙 conformance check、`analyze` 入力段の
  fail-closed enforcement、`archmap` lint surface(authoring dry-run)。
- summary / pr-review / viewer-data surface の追従(conclusion-first 維持)。
- fixtures(空スコープ / 巻き添え非発生 / 宙に浮いた境界 reject / 公理外 atom reject)と
  `docs/tool/`(README、guideline、analysis packet 説明)の更新。

実装設計で具体化するものは次である。

- 依存辺の向きと参照粒度、独立性肯定表示・degree hook の採否。
- scopeRefs の structural verdict ハンドル方式と `verdict_id` 追加の有無。
- compat view の寿命、reason コードの粒度、R1 の横断点検範囲。
- 語彙 artifact の置き場 / provenance ref 形式、語彙 check の対象(kind / axis / subject)、
  R4 の enforcement 強度。

## Non-Goals

この PRD は次を目標にしない。

- 新しい evaluator / invariant / verdict 値 / 測定の追加。
- 依存辺・境界の推測 / 補完 / 自動発見(宣言・既存共産物への参照のみ)。
- H^2 以上の evaluator 本体の実装。R2 は degree hook を残すに留め、higher-cohomology
  の実装は別 PRD とする。
- source 真実 / semantic correctness / global safety / zero curvature / universal
  atom truth の主張。
- 沈黙 -> forecast / proof の変換。FieldSig 領分(forecast / governance /
  longitudinal / calibration)の取り込み。FieldSig は handoff consumer としてのみ
  言及する。
- viewer #2082 の描画変更。R3 は schema の供給までで、viewer はその consumer。
- legacy v1 structural path(`archmap/v1` + `law-policy/v1`)の変更、migration
  tooling の提供。
- ArchMap author / LawPolicy author / evaluator registry 責務の本体吸収。
- ArchMap atom が source code を正しく観測しているかの semantic correctness 検査
  (R4 は token 語彙 conformance のみ。観測の正しさは ArchMap author / extractor の責務)。
- ある種別を AAT 公理に加えるべきかの判断(doctrine / 数学本文 author の責務。linter は
  語彙外を弾くのみで、語彙の拡張・補完・推測をしない)。
- atom-kind 語彙 artifact を AAT 公理の証明や Lean 台帳と同一視すること(provenance ref
  付きの token 契約であり、theorem discharge を要求しない)。AAT 数学本文(保護ファイル)
  自体の改変は本 PRD に含めない。
- Lean 形式化との接続 / theorem discharge / Rust↔Lean 対応。

## Acceptance Criteria / 完了条件

- 問いが冒頭に立てられ、各要求の採否を問いで読む規律が明記されている。
- 本 release が新規測定を伴わない hardening release であり、AG path に閉じ legacy v1
  path を変更しない方針が明記されている。
- ユーザー目線のアウトカムがユースケース(UC1-UC3)として定義され、各ユースケースが
  要求 ID への対応を持つ。
- **(R1)** `selected_cover_contexts` が空、または 1-skeleton が不実体化する profile で
  `ag.cech-obstruction@1` の structural verdict が `measured_zero` ではなく
  `not_computed`(reason に `empty_selected_scope` を含む)になり、非空かつ obstruction
  不在のときは従来どおり真の `measured_zero`、obstruction 存在時は `measured_nonzero`
  が維持される(既存テスト非回帰)。
- **(R1)** 空スコープ時に CBI ledger へ当該 precondition が `violated` として記録され、
  reason 文言が contract 内事実に限定され cover 選択への提案 / 批判 / author 意図推測を
  含まないことが文言テストで固定される。viewer / summary で空スコープ `not_computed` が
  blocker として描画される。
- **(R2)** ある evaluator が violated + not_computed を出し、別 evaluator が独立に
  `measured_zero` を出す fixture で、`measured_zero` 行が `not_computed` に降格されず
  保持される(無関係 violated の巻き添えが起きない)。
- **(R2)** measured_* verdict が `dependsOnAssumptions` で violated 行を参照する fixture
  で、その verdict のみ単一 propagation pass で `not_computed` に正規化され、reason が
  `depends_on violated <theorem_ref>` を含む。`dependsOnAssumptions` 未宣言の verdict は
  violated 共存下でも measured_* のまま保持される(沈黙の保全)。
- **(R2)** 締め直した fail-fast が「measured_* かつ dependsOn に violated を含む」場合
  のみ fail し、`dependsOnAssumptions` を持たない既存 packet が従来結論を回帰なく出す
  (serde 後方互換、既定空 Vec)。
- **(R3)** 既存 `non_conclusions` の全文字列が `boundaryStatements` の typed entry として
  再現され、各 `text` が旧文字列と一致し、旧 `nonConclusions` 文字列 view が compat
  レイヤから併出される(回帰テスト)。
- **(R3)** scopeRefs が空、または既存 id に解決しない BoundaryStatement を validator が
  reject する。`kind` が 6 値に限定され、source 真実 / global safety 等を含む statement が
  型 / validation で拒否される。
- **(R3)** violated assumption を含む測定で `kind=violated_assumption` の境界が当該
  `not_computed` verdict に scopeRefs で解決し、`blocked_method` / `unmeasured_support` /
  `not_applicable` が別 kind として現れ、いずれも `measured_zero` に潰されない。
- **(R4)** AAT 公理外の `kind` token を持つ atom を含む ArchMap v2 を `analyze` に通すと
  入力 validation が fail-closed で reject し、measurement へ素通りしない。語彙内 atom のみ
  の ArchMap は従来どおり通る。
- **(R4)** `archmap` lint surface が measurement なしで同じ語彙 conformance を検査し、語彙外
  atom を atom id・違反 token・期待語彙 ref つきの concrete な lint error として返し、語彙内
  なら `ATOMS_WITHIN_DECLARED_VOCABULARY` を conclusion-first に出す。
- **(R4)** atom-kind 語彙 artifact が許可 kind token と AAT 数学本文への provenance ref を
  持ち、ArchMap の extraction n / doctrine から解決される。lint error の reason が「宣言語彙に
  属さない token」に限定され、種別を公理に加えるべきかの規範判断 / semantic correctness 主張を
  含まないことを文言テストで固定する。
- summary / pr-review surface が conclusion-first(肯定的結論を主役、境界を qualifier に
  従属)を保つことを golden 出力で確認する。
- `cargo test --manifest-path tools/archsig/Cargo.toml` が緑で、schema fixture /
  golden packet が新フィールドを反映して更新され、`git diff --check` と hidden Unicode
  scan が clean である。
