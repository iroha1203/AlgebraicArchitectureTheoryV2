# ArchSig v0.5.0 再設計ノート — 代数幾何 AAT 単一 path への純化と SAGA の現場接続

- 日付: 2026-07-04(同日改訂・いずれもユーザー決定: 版数体系を単一契約版数 v0.5.0 に統一 — §8 裁定7 /
  後方互換の全面不採用 — §8 裁定10 / SAGA Stage 3 を 0.5.x に組み込み、v0.6.0 は SAGA 以後の研究成果用に予約 — §9 /
  方針⑦の連携先を ArchMap → ArchView に訂正 — §5 / スコープ案A 確定 — §10 / LawPolicy 案4 確定 + 発展追随の拡張規律 — §4)
- 改訂 2026-07-05(ユーザー決定): ArchView は計測束縛の内側で表現を最大化する「攻めた幾何表現」へ /
  Three.js は repo に vendor せず release bundle への packaging 時注入 — いずれも §6
- 位置づけ: 調査と設計のみ。PRD は未着手(切り方の候補を §10 に置く)。
- 設計プロセス: 8 領域の並列読解 → 6 次元の並列設計 → 3 レンズ敵対査読(境界規律 / 理論忠実性 / 実現可能性、計 80 指摘を検証・反映)→ 完全性監査。
- 次元別の詳細設計(schema フィールド・CLI・削除リストの全文)は [docs/note/archsig_v0_5_0/](archsig_v0_5_0/) の 6 文書。
  6 文書間で食い違う箇所は本ノート §8 の統合裁定を正とする。
- AAT 数学本文(`docs/aat/algebraic_geometric_theory/`)が正であり、本ノートはそれに相対化される。

## 問い

**v0.5.0 は何を約束する版か。** 答え: 古典 AAT の名残を持たず、代数幾何 AAT だけを地盤とする単一計測 path
`archmap + 選択された制度 → archsig-measurement-packet` を確立し、その上に SAGA 定理(第X部)の最初の現場計測を立てる版である。
版数もこの版で一本化する: 全 artifact は単一契約版数 `<name>/v0.5.0` を名乗る(§8 裁定7)。

採否の判定規律(全設計要素に適用する 3 問):

- **Q1(経路)**: AG 計測 path の計算に寄与するか。
- **Q2(理論 anchor)**: AG 本文に定義・定理番号で anchor できるか。古典語彙(signature axes / zero-reflecting distance / witness completeness 型同値定理)しか anchor がないものは入れない。
- **Q3(境界)**: 三層責務(観測 = ArchMap / 制度選択 = LawPolicy / 計算 = ArchSig)と境界の一括払い哲学に適合するか。

## 目標アウトカム

v0.5.0 系列(v0.5.0 出荷 + 0.5.x 追補。v0.6.0 は SAGA 以後の研究成果用に予約 — §9)で到達する姿を
5 つのアウトカムとして固定する(2026-07-04 ユーザー決定)。PRD 化の際は各 PRD の受け入れ条件を
このアウトカムに遡って接続する。各アウトカムは無制限 claim ではなく、選ばれた入力 contract の
内側での能力として読む(境界規律)。

| # | アウトカム | 実現する設計 | 到達時期(スコープ案A 前提) |
| --- | --- | --- | --- |
| O1 | **レガシーが破棄され、シンプルで使いやすい計測器になる** | §2 三段階削除(src 77%)+ 単一 AG path、裁定7 単一契約版数、裁定10 互換ゼロ、gate/compare の CI 面(§5) | v0.5.0 で完結 |
| O2 | **SAGA 定理など、AAT の強力な理論を現場に接続できる** | §3 診断の階段 + SAGA evaluator 3 種 + 境界定理 guardrail + 肯定的結論への翻訳規律 | v0.5.0 で入口(descent、Stage 1)、0.5.x で完結(comparison / grounded 10 結論) |
| O3 | **ArchMap を Agent SKILL で再現性高く生成できる** | §7 決定的 worklist + 二重抽出突合 + coverage ledger + 監査 5 check + 語彙カタログ突合 lint | v0.5.0(M1-M2)、抽出 corpus による実測は 0.5.x(M3) |
| O4 | **Law ポリシーが AAT の求める law を表現できるようになる** | §4 案4: law-equation-surface(方程式・witness 変数・defect tie の宣言 — 原則11.6「述語は方程式を決めない」への回答) | v0.5.0 で基盤(Stage 1)、0.5.x で law surface 本体(Stage 2) |
| O5 | **ArchView によって幾何らしい可視化ができる** | §6 幾何対象台帳 G1-G10 + SAGA ビュー + viewer data の一級 contract 化(§5) | v0.5.0 で既測フィールドの描画解禁(V-A)、0.5.x で幾何再設計本体 |

## 0. 要約

v0.4.0 の実態は docs の「2 path」記述より悪く、**三世代 + 孤児の四層構造**である(src 66.5 千行の実測):

| 世代 | 実体 | 行数 | 到達性 |
| --- | --- | ---: | --- |
| v0(dead) | analysis packet builder、全部入り LawPolicy DSL | ≈35,000 | CLI 不達(unit test のみ) |
| 孤児 | `src/reports/` ほか | ≈5,000 | コンパイルすらされない |
| v1(legacy) | typed evaluator + architecture distance + pr-review | ≈11,000 | 現行 runtime だが predicate 5 語制約で実用記述力なし |
| AG(current) | archmap/v2 + measurement-profile → measurement-packet、`ag.*` evaluator 11 種 | ≈13,000 | 現行一次。v0/v1 とコード独立 |

v0.5.0 は約 51,000 行(src の 77%)を三段階で削除し、残る AG path を純化・増築する。ユーザー方針 8 項と設計の対応:

| # | 方針 | 主担当 §(詳細文書) |
| --- | --- | --- |
| ① | 古典 AAT レガシー破棄 | §2([design_legacy-triage](archsig_v0_5_0/design_legacy-triage.md)) |
| ② | AG 分析の充実 | §3([design_ag-measurement](archsig_v0_5_0/design_ag-measurement.md)) |
| ③ | SAGA 定理の現場接続 | §3(同上、§6 の SAGA ビューも) |
| ④ | 境界の一括払い(観測境界は ArchMap と LawPolicy へ) | §4 / §7 を貫く規律。各節の境界整合に明記 |
| ⑤ | ArchMap 検出精度を Agent SKILL で | §7([design_archmap-skill](archsig_v0_5_0/design_archmap-skill.md)) |
| ⑥ | LawPolicy 再設計の複数案 | §4([design_lawpolicy](archsig_v0_5_0/design_lawpolicy.md)、4 案 + 比較 + 推奨) |
| ⑦ | 出力 artifact 再設計(CI / ArchView 連携)※当初指示の「ArchMap 連携」は誤りとユーザー訂正(2026-07-04) | §5([design_artifacts](archsig_v0_5_0/design_artifacts.md)) |
| ⑧ | ArchView の幾何らしい可視化 | §6([design_archview](archsig_v0_5_0/design_archview.md)) |

**すぐ直すべき既知の破損**(v0.5.0 を待たない): CLAUDE.md / AGENTS.md の検証コマンド例(`archsig analyze` の
`tests/fixtures/minimal/` 参照)は v0 fixture を指しており、現時点で既に
`--input must have schemaVersion archmap/v1` で fail する(実行確認済み)。
`ag_measurement/archmap_v2.json + law_policy_ag.json` への差し替え(analyze 成功を確認済み)を先行 PR にしてよい。

## 1. 調査で確定した現状(設計の前提事実)

1. **判定語の残滓は v0/v1 ではなく AG path 自身にある。** 責務憲章が「破損の現状そのもの」と名指しした
   `predicate:"mismatch"` 系の判定混入は v2 fixture 側で起き、観測純化 PRD(R1-R4)の hard error で回復済み。
   残るのは registry の `ag.*` manifest の判定語 predicate 3 件(`coherence.legacy-coherence-token` /
   `boundary-residue.legacy-boundary-token` / `section-factorization.legacy-section-token`)と、
   判定語 atom を消費する最後のコード `legacy-counting-invariant` invariant(有効入力では恒常 vacuous)。
2. **v0/v1 削除の境界的意義は別軸にある。** v0 LawPolicy DSL(obstructionCircuitDefinitions 等の手書き)は
   憲章「LawPolicy が書かないもの」への層越境。v1 pr-review の authored `archmap-delta-v0` は
   差分計算という計算責務の観測者への転嫁。削除はこの二つの境界回復として書ける。
3. **SKILL の版数ねじれ。** archmap-creater は v2 一次だが archsig-reader / archsig-pr-reviewer は v1 前提で、
   creater → reader → pr-review のループが v2 で閉じていない。
4. **SAGA(第X部)の計測はゼロ。** 理論側は 2026-07-03 に全連鎖 Lean proved。受け皿様式
   (evaluator + profile 検証 + assumption 定理参照の 3 点セット)は既にあるのに、第X部対応 evaluator が 1 つもない。
5. **ArchView は「計測前進・可視化後退」。** packet に実在して描かれていないフィールドが多数
   (locusField / periodStokes.meters / H² coherence — H² は投影・parse 済みで描画だけが沈黙)。
6. **artifact 表記の三様化。** `x/v1` と `x-v1`、`schema` と `schemaVersion` キーの混在。run manifest は 3 様式。
   v0.5.0 契約基盤では Cargo.toml も `0.5.0` へ揃える。

## 2. 設計次元1: 古典 AAT レガシーの破棄

詳細: [design_legacy-triage.md](archsig_v0_5_0/design_legacy-triage.md)(削除対象の完全リスト、PR 分割、リスク表)。

- **三値 triage**(DELETE / KEEP / REPLACE)を Q1-Q3 で判定。REPLACE に該当するのは PR review 機能のみ
  (後継は §8 裁定1 の `archsig compare` + `archsig gate`)。
- **削除は 3 フェーズ**: (A) 孤児 ≈5k 行 → (B) v0 dead ≈35k 行 + fixture 10 系統 + FieldSig の v0 受理 →
  (C) v1 path ≈11k 行 + pr-review + `--strict-distance` + skills/docs/CI 同期。
  各フェーズ末で CI green。FieldSig の v1 `--analysis-packet` 受理削除は lean.yml の v1 e2e 区間削除と
  **同一 PR** で行う(先に消すと CI が恒常 fail する二重依存があるため)。
- **第 1 世代計測ファミリ(monodromy / ACTS spectrum / homotopy Stokes / Part IV distance)は AG 語彙へ移植しない。**
  理論的核は AG 本文と既存 `ag.*` evaluator 11 種に吸収済み(boundary holonomy → `ag.boundary-residue@1`、
  spectrum → `ag.sheaf-laplacian@1` proxy、Stokes → `ag.period-stokes@1`)。後継が無いのは
  transport data 不在時に沈黙が正しい領域だけである。
- **互換の扱い**: 受理・変換レイヤも専用 removal error も作らない(§8 裁定10)。旧 schema は
  一般 validation fail に落ちる(エラー文言に現行契約名を含める程度)。告知は README の移行表 1 枚のみ。
  schema catalog に legacy エントリを持たない(過去 schema の正本は git tag v0.4.0)。
- **残存ドリフト掃除**(v0/v1 削除とは独立の、観測純化の仕上げ): registry の判定語 predicate 3 件を
  中立語彙へ同期し、`legacy-counting-invariant` invariant を代替なしで廃止する。
- 削除後の単一 path 構成と、`ag_measurement.rs`(11,840 行)のモジュール分割
  (evaluator trait + 1 ファイル 1 evaluator)は同文書 §3.6。

## 3. 設計次元2: AG 計測の充実と SAGA 定理の現場接続

詳細: [design_ag-measurement.md](archsig_v0_5_0/design_ag-measurement.md)(evaluator 仕様、packet 表現、翻訳規律の全文)。

核は第X部の問い「local repairs may each succeed. Do they glue to a global repair?」を、
選ばれた有限入力の内部で、CI が読める肯定的結論として判定できるようにすること。

- **診断の階段** = SAGA の supplied / generated 規律(part_10 §1)をそのまま artifact contract 境界にする:
  - (A) 観測(archmap/v2)→ residual 生値
  - (B) + `archsig-repair-plan/v1`(新 artifact: charts / overlaps / repair primitives / residual / supp)
    → 境界所属 r∈B¹。**r∉B¹ ⇒ 貼り合わない は無条件**(定理3.4(i))
  - (B') + faithfulness 基盤(complete-support 宣言 = 定理3.5 regime、または supplied data)
    → `REPAIR_GLUES_WITHIN_SELECTED_COMPLEX`(肯定的 descent)
  - (C) + triple / additive 係数 / true sheaf certificate → class 水準(Z¹/B¹、定理4.8)
  - (D) + incidence bridge + H¹ comparison data → SAGA 比較・非零 class 転送(定理7.2 / 7.4)
  - (E) + law-equation 面(§4 の law surface)→ 10 結論 packet(定理7.5、law-dependent 1-3 / law-independent 4-10 の
    分割を artifact の一次構造にする)
- **新 evaluator**: `ag.saga-descent@1`(層 B/C)、`ag.saga-comparison@1`(層 D)、`ag.saga-grounded@1`(層 E、0.5.x)。
  既存の `ag.cech-obstruction` は @2 で concrete class support + nerve topology + 定理12.4 の 3 前提検査を持つ。
  `ag.square-free-repair@1` は実装済みのため summary token `REPAIR_TARGETS_IDENTIFIED` の追加のみ(版上げしない)。
- **guardrail(境界定理の強制)**: 定理8.4 / 8.5 / 6.4「比較可能性はデータである」を schema・validator・CLI の三層で強制。
  comparison data は写像水準のフィールドしか持たず(結論を格納しない、定義7.1)、refinement は粗→細の片方向のみ
  (命題4.10。逆方向は定理8.5 の反例で遮断)、供給なしの cross-run class 同一視は構造的に不可能にする。
- **理論忠実性の要点**(査読で確定): 「law が守られている」は law-check 生値検査
  (law surface の holdsCriterion による chart-local 検査)からのみ生成し、interpretation 零 / H⁰ 零からは生成しない
  (系11.5: 消滅と同値なのは law の成立ではなく defect の ideal 所属)。H¹ 語彙を law 充足の言葉に翻訳しない
  (定理8.1 / 8.2: law は H⁰ で働き、H¹ の内容は cover の幾何から来る)。
- **エンジニア向け翻訳規律 7 項**: 主文は選ばれた profile 内側の肯定形、非零は concrete support / class で名指す、
  沈黙は「次に何を供給すれば語れるか」1 行、「証明する」は theoremRef 付き定理帰属文のみ、等(同文書 §3.8)。
- fixture は Lean proved 面と数値ロックで接続する(circle nerve は Lean witness の 3 辺形が一次 fixture。
  本文 worked example の 2 頂点形とは別 witness として帰属を書き分ける)。Rust と Lean の対応は contract として要求しない。

## 4. 設計次元3: LawPolicy 再設計 — 案4 で確定(ユーザー決定 2026-07-04)

詳細: [design_lawpolicy.md](archsig_v0_5_0/design_lawpolicy.md)(各案の schema 全文、binding 対応規則、Stage 計画)。

設計問題は G-06「law は方程式である」(原則11.6: 述語は方程式を決めない。方程式が無ければ係数も cohomology も無い)
を受けて、**方程式をどこに置くか**に帰着する。

| 案 | 思想 | 評価 |
| --- | --- | --- |
| 案1 Selector 純化 | 方程式は registry 焼き込みのまま、掃除と非対称解消のみ | 移行最小だが SAGA 層 E の政策記述力が得られず、law を足すたび Rust 実装追加 |
| 案2 方程式一級化(LawPolicy 内) | `laws[]` に witness 方程式を宣言 | 記述力は得るが単一文書が肥大し、defect source の入力欄が無く単体では層 E 未達 |
| 案3 統合(LawPolicy ⊕ profile) | 1 文書 1 引数 | **非推奨**。誤結論時の責任切り分け(憲章の機能条件)を弱め、政策変更と計測変更が単一 fingerprint に混ざる |
| **案4 政策バンドル層化 ★推奨** | `law-policy/v2`(selector)+ `law-equation-surface/v1`(方程式面)+ `measurement-profile/v2`(計測手段)+ 任意の bundle manifest | supplied / generated 境界を artifact contract 境界に写す。LawPolicy の selector 性格と三層分離を保存したまま方程式を一級化。component 単位 fingerprint が CI 比較の台紙になる |

**案4(政策バンドル層化)で確定**(ユーザー決定 2026-07-04。案1〜3 は比較記録として保持)。要点:

- `law-equation-surface/v1` が持つもの: `laws[]`(conditionType 6 型 enum、closed-equational のみ ideal 意味論、
  witnessVariables + ArchMap 生値語彙への binding、forbiddenSupportGenerators)、`skeleton`、`defectSources`
  (chart-local law-defect tie の宣言)、`quotientSheafCondition`(theorem / assumed / not-selected の三相)。
  結論相当フィールドは schema 水準で禁止(判定語 hard error の政策文書版)。
- §3 の holdsCriterion(law 充足の生値評価意味論)は **law surface の laws[] 側に置く**(§8 裁定3)。
- `measurement-profile/v2`: 独立ファイル化、witnessFamily を law surface へ移設(P4 解消)、
  有限上限 7 定数の finiteBounds 昇格(registry hard cap 以下への引き下げのみ可)、diagnosticCeiling
  (診断階段の要求上限宣言)。
- 縮退は「`lawSurfaceRef` を持たない政策文書 = v0.4.0 相当 contract の明示選択」であり、
  CLI フラグ省略を引き金にした fallback は存在しない(fail-closed 規律)。
- 移行は Stage 1(掃除 + 対称化 = 案1 と同一作業)→ Stage 2(law surface 新設 + 二経路の方程式移行)→
  Stage 3(SAGA 層 E 入口)。案4 を選んでも案1 の作業は無駄にならない。

### 発展追随の拡張規律(ユーザー要件 2026-07-04)

案4 は SAGA 専用の規格にしない。**AAT の高度な数学を最大限に活かし、今後の理論の発展
(例: GOAL G-03 の relation atom と他 atom の mix、G-04 系の non-abelian H¹ / conormal 係数)に
schema の骨格を変えずに追随できること**を設計要件とする。記述の難易度は agent SKILL で吸収する
(schema は人間の手書きしやすさより表現力を優先してよい)。

1. **拡張点は 3 箇所に限定する**: (i) law surface の宣言語彙(conditionType enum / binding kind /
   生成元代数)、(ii) evaluator registry(理論 anchor 付き)、(iii) profile の enum
   (coefficient / zeroPredicate / diagnosticCeiling の段)。**3 artifact 分割と supplied / generated 境界
   という骨格は変えず、語彙だけが育つ**。単一契約版数(裁定7)+ 互換ゼロ(裁定10)の下では、
   enum 追加はそのリリースの契約更新として扱えばよく、互換機構は不要。
2. **binding は生値座標への汎用セレクタとして規格化する**: Stage 2 の 2 形(square-free の変数名照合 /
   cech の edge 宣言)を特例ではなく **binding kind の registry**(kind ごとに解決規則と検証を定義)として
   実装する。witnessVariables は **atom kind を横断して混成できる** — 1 つの law の変数集合に
   relation atom 由来の変数と capability / semantic 由来の変数を混ぜられる。これが G-03 の
   relation atom mix の受け皿になる。binding kind と評価器の乖離は語彙カタログ突合 lint(次元6)が
   CI で検出する。拡張例(binding kind `relation-edge` は将来、理論の定理と共に registry に追加される想定):

   ```json
   { "lawId": "law:order-flow-consistency", "conditionType": "closed-equational",
     "witnessVariables": [
       { "variable": "r_calls",
         "binding": { "kind": "relation-edge", "axis": "static", "predicate": "calls" } },
       { "variable": "x_shared_state",
         "binding": { "kind": "support", "axis": "square-free", "predicate": "support" } } ],
     "forbiddenSupportGenerators": [ { "support": ["r_calls", "x_shared_state"] } ] }
   ```

3. **生成元代数は変数の出自に依存させない**: forbiddenSupportGenerators は「宣言された変数上の
   square-free monomial」であり、変数がどの kind の atom に束縛されるかに依存しない。
   したがって kind を mix しても係数生成の計算可能クラス(F₂ Boolean + 有限上限)は不変のまま使える。
   より高い係数(conormal I_U/I_U²、non-abelian 係数)は profile の coefficient enum の拡張点として
   予約だけ置き、理論側の定理が揃うまで有効化しない(G-04 の入口。それまでは沈黙)。
4. **有効化の条件は理論の定理**: 新しい conditionType / binding kind / coefficient の有効化は、
   既存様式「evaluator + profile 検証 + assumption 定理参照」の 3 点セットと theorem anchor(問い Q2)が
   揃ってからに限る。G-03 は幅の探索 GOAL であり成果を先取りした schema は切らない —
   確保するのは**容量**(mix を表現できる binding / 変数 / 生成元の一般形)であって、成果の予約ではない。
5. **記述難易度の吸収先は SKILL**: law surface の authoring は law-policy-creater(新規作成のみ、裁定10)と
   良悪対例集が担う。表現力のための語彙増に対して、SKILL 側の対例集と lint を同じ PR で育てることを
   語彙追加の完了条件にする。

## 5. 設計次元4: 出力 artifact の再設計 — CI 連携・ArchView 連携

詳細: [design_artifacts.md](archsig_v0_5_0/design_artifacts.md)(schema 全文、digest 仕様、gate/compare の validation 規則)。
※ユーザー訂正(2026-07-04): 方針⑦の連携先は ArchMap ではなく **ArchView**。詳細文書の「ArchMap authoring loop を
第二の消費者とする」枠組みはこの訂正で読み替え、artifact 体系の一級消費者は CI・ArchView・FieldSig の三者とする。

- **命名・版数統一**: schema 識別子は `<artifact-name>/v0.5.0` の単一契約版数(§8 裁定7。viewer data も
  例外なく同一 cut-over)、トップレベルキーは `schema` に全廃一本化。全 artifact に `toolVersion` +
  `inputDigests`(canonical JSON sha256)。runId は入力 digest からの決定的導出
  (同一入力 → byte 同一出力。golden / CI キャッシュの基盤)。
- **measurement packet 新形(`archsig-measurement-packet/v0.5.0`)**: 6 区画を保持したまま、行安定 id、`target` ブロック(どの cover のどの class を測ったかの
  構造化 = 原則4.4 の concrete class 規律)、`scopeSize`(measured_zero 純度の機械検証 — vacuous zero を schema 水準で排除)、
  行レベル assumption 依存の id 解決、computedInvariants の typed 化(closed kind 語彙)、
  `claimStatus: certified|candidate` と `fidelity: faithful|proxy` の型区別、`suppliedData[]` 台帳
  (supplied / generated 規律の artifact 化)。profile 区画は既存 MeasurementProfileV1 の解決済み埋め込みで凍結し、
  **LawPolicy 再設計の完了を待たない**。
- **CI 連携 = 計測と合否の分離**: `archsig analyze` は計測(verdict を exit code に埋めない)、
  **`archsig gate`** が制度的判断。gate-policy/v1(CI 管理者が author)は verdict 5 値 + violated-assumption 依存の
  全写像を明示必須(fail-closed)とし、非終端 verdict への plain pass は schema 水準で不可能
  (`pass_with_boundary` / `block` の 2 値制限 — unmeasured を黙って pass に丸める制度は選べない)。
  写像語彙に `fail` は無い(unknown は failure ではない)。丸めの痕跡は gate-report の appliedMapping に全行残る。
- **PR review 後継 = `archsig compare`**(§8 裁定1): base / head 両 ArchMap の二重計測 + 比較可能性の 3 段階
  (identical / verdict-row / class-transport)。verdict-row 水準は profileFingerprint + siteCoverDigest の一致で
  機械判定し、遷移は「記録の並記」であって class の同一性を主張しない(conclusionCode も
  `…_RECORDED_AFTER_CHANGE` 系の record 水準名)。class-transport は `measurement-comparison/v1` 供給 +
  kind 別 license(refinement は粗→細片方向のみ)+ 適合条件検査の下でのみ。
- **ArchView 連携 = viewer data を一級の出力 artifact として contract 化**: viewer data は
  「packet + normalized archmap の純射影」という位置づけを schema で固定し、v0.5.0 の単一契約版数
  cut-over に含める(裁定7)。全幾何要素は `drivenBy` で packet 内の verdict / invariant / reading を指し、
  **packet に対応物の無い幾何要素は viewer data validation で fail**(「計測=主・可視化=従」を
  nonClaims 文字列から実行可能検査へ昇格)。verdict 相当値は literal / boolean コピー禁止・ref のみ
  (§6 の contract 規律と同一物 — 契約の定義は本次元、投影の設計は次元5 が持つ)。packet に実在して
  viewer contract で沈黙しているフィールド群(locusField / periodStokes.meters / H² coherence 等)の
  投影解禁も本次元と次元5 の共同作業として台帳化する。
- **ArchMap authoring への frontier(`archsig-observation-frontier`)は方針⑦の要求から外れたため補助機能に降格**
  (0.5.x・任意): unmeasured / blocked verdict を「次に必要な生観測の形」に変換する authoring 層宛て
  artifact として設計は保持する(次元6 の complete-first ループ支援)。実装するかは 0.5.x で
  SKILL 側の必要に応じて判断。設計規律(`silence_by_design` から entry を作らない、
  disposition 分類は authoring 層の所有)はそのまま。
- **FieldSig handoff v2**: 行レベル propagation 採用(violated assumption は依存行だけに影響)、
  受理は atomic 切替(fieldsig は非配布で受益者不在のため両受理窓・dual-emit を設けない)。

## 6. 設計次元5: ArchView 再設計 — 幾何らしい可視化

詳細: [design_archview.md](archsig_v0_5_0/design_archview.md)(幾何対象の台帳 G1-G10、SAGA ビュー画面設計、contract v3)。

- **描くべき幾何対象の台帳(G1-G10)**: すべて「計測 artifact のどのフィールドを投影するか」を宣言してから描く
  (対応表なしの視覚要素は追加しない)。主なもの:
  - G1 site の poset(Hasse 配置、有向 restriction 矢印)
  - G3 nerve topology(b₁ capacity 閉路、`b1 = 面込み複体の Betti 数` を contract invariant 化)
  - G4 1-cochain の値・向き・**holonomy 蓄積リング**(閉路を一周して「1 残る」が文字通り見える)
  - G5 descent の運動(局所 section パネルの接合。**融合 sheet は effectivity verdict 参照時のみ** —
    class 零だけでは大域 section を語らない、原則4.4 逆向き)
  - G6 lawful locus 盆地(measured_zero が画面の「地」)+ minimal repair hitting sets の弦束
  - G8 H² coherence 膜(既存フィールドの描画解禁のみ。artifact 変更ゼロ)
- **structure レーン新設**(5 レーン目): verdict を持たない computed invariant(cover の形、poset 順序、b₁ 容量)を
  低輝度で描き、**structure レーンのフィールドから verdict レーンの表示を点けない**を規律化
  (例: forest フラグでは H¹=0 バッジは点かない。バッジは計測側が定理12.4 の 3 前提を検査して emit した
  measured_zero 行への ref でのみ点く)。
- **SAGA ビュー(旗艦シーン)**: H⁰ 床(law 依存結論 = chart ごとの interpretation ランプ、Λ/K 二層の alias 衛星)/
  H¹ 中間帯(repair cover nerve + residual チャージ + 吸収アニメ)/ comparison bridge(supplied 時のみ)/
  10 結論 ladder(law-dependent 1-3 と law-independent 4-10 の 2 段)/ supplied-layers ゲージ
  (「なぜ結論がここまでか」を入力側の責務として表示 — 境界の一括払いの可視化)。
- **contract 規律**: verdict 相当値はすべて packet への ref(literal / boolean コピー禁止、presence は ref 解決可能性)。
  sequence manifest にも同じ規律(supplied manifest に verdict literal を置けない)。
  verdictRef は既存安定形式 `structuralVerdict/{evaluator}/{law}/{method_status}` に統一。
- 既存 viewer PRD 3 本(insight viewer / gluing geometry #2082 / M+V 統合 #2217)の吸収・破棄判断は
  同文書 §3.8 の表で確定。**3 本とも docs/archive へ移動**(ユーザー決定 2026-07-05。本設計が正)。

### 攻めた幾何表現(ユーザー指示 2026-07-05)

ユーザー方針: **Three.js を使う以上、幾何らしいリッチな見た目へ振り切ってよい**。
ただし規律は不変 — リッチにするのは**表現**であって**主張**ではない。全視覚要素の計測フィールド束縛
(drivenBy)、verdict 非生成、沈黙 = 霧/frosted、決定論レンダリングはそのまま維持し、
その内側で視覚資源を最大化する。0.5.x の ArchView 再設計本体(V-B/V-C)は G1-G10 を次の水準へ引き上げる:

- **section を本物の面として描く**: 各 chart の局所 section を fresnel ガラスの曲面シートで描き、
  descent 成立時は辺に沿って**メッシュが実際に溶接される**(頂点マージ + seam glow の消灯)。
  唯一の大域 section は環境反射を持つ 1 枚の連続曲面 + 呼吸リング(∃! の冠)。
- **nerve を本物の単体複体として描く**: 頂点球・辺チューブ・充填された半透明 2-単体。
  b₁ capacity 閉路は押し出しチューブ、実測非零 class の support 閉路だけが
  **shader の方向フロー(cocycle の向きが流れとして見える)+ bloom** で点灯する。
- **holonomy を粒子で描く**: 選択閉路を粒子流が一周し、蓄積値のぶんだけ**リングが物理的に閉じない**
  (段差 + 値ラベル)。擬円周 golden example の「一周して 1 残る」が運動として見える。
- **lawful locus を地形として描く**: locusField を displacement map による実 terrain にし、
  measured_zero 盆地は静かな平地(画面の「地」)、curvature 起伏は lavender の山脈、
  blockedRegions は霧の谷。カメラ fly-through を guided tour に接続。
- **poset を結晶層として描く**: posetDepth の地層 + restriction 方向の光の流れ。
  Λ/K alias は component 核の周りを軌道する instanced 衛星(trail 付き)。
- **SAGA ビューの演出**: H⁰ 床 → H¹ 中間帯 → comparison bridge の staged カメラ振付、
  descent snap は吸収の物理感のある easing、10 結論 ladder の点灯は ref 解決の順に波及。
- **技法**: UnrealBloom に加え、custom GLSL(フロー場・fresnel・SDF 膜)、depth-of-field による
  シーン焦点、選択 outline pass、InstancedMesh + trail。すべて決定論(乱数なし、振付は実測値の純関数)。

見た目の派手さと claim の慎ましさを両立させる原則は一つ: **強い視覚効果ほど強い計測に束縛する**
(bloom は measured_nonzero の class support だけ、溶接は effectivity verdict だけ、
冠は SAGA の uniqueGlobalSection 行だけ)。装飾のための装飾は structure レーンの低輝度に留める。

### 配布方式(ユーザー決定 2026-07-05: repo に vendor を置かない)

- **リポジトリ**: 現行どおり CDN importmap(Three.js r0.164.1 に pin)。vendor ディレクトリ(±1.3MB)は
  git に入れない。開発・repo 内利用はオンライン前提でよい。
- **release bundle**: `archsig-release.yml` が packaging 時に pin した版を取得し、
  **SHA256 checksum 検証の上で** `archview/vendor/` に配置、importmap の参照先を `./vendor/` に
  書き換えてから同梱する(packaging 時変換であり build 導入ではない)。配布物は offline で動く。
- no-build 単一 HTML・決定論は不変。archview 詳細文書 §3.7-2 の「repo 内 vendor 同梱」はこの方式に読み替える。

## 7. 設計次元6: ArchMap 抽出 Agent SKILL — 漏れなく・再現性高く

詳細: [design_archmap-skill.md](archsig_v0_5_0/design_archmap-skill.md)(新 4 schema、authoring CLI 3 面、9 段階 Workflow)。

中核原則: **機械層(列挙・ハッシュ・突合・参照整合)と読解層(atom の生成・採否・意味付け)を分離し、
機械層を決定的にし、読解層を二重化して突合する。** 観測の主観(意味の読み取り)は守り、機械化しない。

- **再現性の底 = `archsig scope-manifest`**: 同一ツリー・同一 spec からビット同一の worklist
  (byte 辞書順 + sha256 + git revision 記録)。author 追加証拠は `--add-evidence` で spec の一部として記録・再現。
- **二重抽出 + 突合 = `archsig extraction-diff`**: pass A / B が独立に読解した candidate packet を
  正規化キー(atom-match-key@1)で機械突合。unmatched は「見落とし検出のキュー」であり、
  裁定は必ず該当 source の再読解で行う(多数決・類似度マージ・自動採択は禁止)。
  判定語 lint と semantic object lint は候補段階で前倒し適用。
- **網羅性の bounded claim = coverage ledger**: 「選択スコープ内の走査記録」(worklist と 1:1)。
  extraction completeness は主張しない。スコープ判断も一括払いの対象で、pass 実行中の sub-agent に
  out-of-scope 判断を分散させない(scope manifest 更新 + ユーザー再承認への round-trip)。
- **監査の機械化 = `archsig archmap` の authoring フラグ**: sources 解決 / provenance closure /
  ledger-worklist 1:1 / read-before-cite / revision 記録の 5 check。自己申告ゲートの一部が機械検証に昇格。
  肯定的結論 `AUTHORING_SURVEY_TRACEABLE_WITHIN_SCOPE` を先頭に。
- **語彙カタログ(W4 対応)**: kind / axis / predicate の 3 層を分離し、axis 表は `ag_measurement.rs` の
  実フィルタから機械採録(AG 経路が読む axis と記述用 axis を別列で区別)。axis × predicate の AG 消費対応表 +
  CI 突合 lint で「AG 経路が読まない atom の量産」を防ぐ。新 axis の導入は authoring run 内で行わず
  doctrine / registry 側への escalation。
- **alias 保存規律(SAGA 接続の観測側要件)**: 同一 subject に相異なる use-evidence があれば semantic atom を
  別々に保持する(第X部の Λ/K 二層 = faithfulness 判定の核心を観測側で潰さない)。
  semantic kind は object 必須規約 + lint で意味差をキーに載せる。
- ArchMap 本体(archmap/v2)の schema は**変更しない**。新設 4 artifact はすべて authoring workspace の
  sibling であり、計測経路(analyze)は一切読まない。

## 8. 統合裁定 — 6 設計間の衝突の解決

完全性監査が 6 設計間の衝突・接続漏れ 17 件を特定した。本節の裁定が正であり、
次元別文書の該当記述は本節に従って読み替える。

### 裁定1: PR review 後継は `archsig compare` + `archsig gate` に一本化(v0.5.0)

- 衝突: legacy-triage は「pr-review v2(base/after 二重計測 + ArchSig 計算の archmap-diff)を v0.5.0 で新設」、
  artifacts は「観測層 authored の archmap-delta + compare を 0.5.x」、ag-measurement は「compare は次版」。
- 裁定: **コマンド名は `compare` と `gate`**(pr-review の名は v1 と共に消す)。中身は両設計の合成:
  base / head 両 ArchMap の二重計測(legacy-triage)、比較可能性 3 段階と record 水準 conclusionCode(artifacts)。
  **v0.5.0 では identical / verdict-row 水準まで**を出荷し(比較 data 不要・理論的に安全)、
  class-transport 水準(measurement-comparison/v1 + kind 別 license)は 0.5.x(ag-measurement Stage 3 と同期)。
  これで PR review 機能の空白は生じない(v1 pr-review の実用価値は predicate 5 語制約でほぼ理論値)。
- **ArchMap 差分の責務**: 二つの supplied ArchMap の差分計算は観測ではなく計算であり、
  `compare` が `archmap-diff/v1` を**計算して出力**する(cover 変更検出と deltaRefs の機械的交差に使う)。
  観測層 authored の `archmap-delta/v1` + `delta-apply` は「head ArchMap を作る authoring 手段」であり
  別物として 0.5.x の任意最適化に置く。v0.5.0 の head ArchMap は archmap-creater の増分モード
  (scope-manifest `--baseline`)で作る。cover が変わった行は `cover_changed_between_runs` boundary を付し
  gate の合否から除外する(legacy-triage の最小契約を comparison-report の語彙で実現)。

### 裁定2: CI 合否機構は gate に一本化。strict 系フラグは全廃

- 衝突: `--strict` 改名(legacy-triage)vs strict carve-out(ag-measurement)vs gate 体系 + strict 廃止(artifacts)。
- 裁定: **gate 体系を採る**(計測と制度的判断の分離が三層責務の CI 版として最も筋が良い)。
  `--strict-distance` は廃止し、`--strict` への改名も行わない。
  ag-measurement が確定した silence_by_design carve-out(repair-plan 不供給の not_computed 等、
  語彙内の入力不足による非終端行を合否の分母から外す)は、gate-policy の rule に
  **`boundaryKindOverrides`**(例: `{ "silence_by_design": "pass_with_boundary" }`、写像先は同じ 2 値制限)を
  追加して表現する。carve-out は pass への丸めではなく、boundary 付きで通した痕跡が appliedMapping に残る。

### 裁定3: SAGA 層 E データの置き場は law-equation-surface/v1(案4)に一本化

- 衝突: ag-measurement は lawEquation ブロック(holdsCriterion / quotientSheafCondition 込み)を
  measurement-profile 側に、lawpolicy 案4 は law-equation-surface/v1 に置き witnessFamily を profile から削除。
- 裁定: **案4 に従う**。law の方程式面・witness 変数・binding・defect tie(defectSources)・holdsCriterion・
  quotientSheafCondition はすべて law surface の所有(law 側データであることは定義11.3 の violation coordinates
  帰属から自然)。measurement-profile/v2 は計測手段(cover / 係数 enum に `generated:quotient-of-witness-ideal` を追加 /
  finiteBounds / diagnosticCeiling)に徹する。ag-measurement の §3.2 は「置き場が law surface に変わるだけで
  フィールド意味論は同一」と読み替える。
- 付随: ag-measurement が宣言した blocking 依存「policy 行ごとの profileRef 化」は、
  **law-policy/v2 に `policies[].profileRef`(任意、文書水準 measurementProfileRef の override)を予約**して受領する。
  v0.5.0 runtime は単一 profile / run のままとし、measured residual は二 run 構成(`--residual-packet`)を正式経路、
  単一 run 化は予約フィールドの有効化として 0.5.x 以降。

### 裁定4: SAGA supplied 層の供給 artifact は `archsig-repair-plan/v1` に統一

- 衝突: ag-measurement は repair-plan/v1 を完全設計、lawpolicy は同成分を「repair-proposal/v1(未決・供給者未定)」と別名で保留。
- 裁定: **repair-plan/v1**(ag-measurement §3.1 の設計)が正。repair primitives は観測でも政策でもなく
  修理提案者の contract であり ArchMap に置かない(lawpolicy の境界確定はそのまま生きる)。
  lawpolicy 未決事項 1・3 の供給者は repair-plan/v1(層 B/C/D)+ law surface(層 E)で解消。
  authoring は repair-plan authoring SKILL(§8 裁定8)。

### 裁定5: 比較系 artifact の名称と役割の一本化

- **within-run**(SAGA 定義7.1: semantic 複体 ↔ Čech 複体の比較 data)= repair-plan/v1 内の `comparison` ブロック。
- **cross-run**(refinement / refactor-morphism / identity)= `measurement-comparison/v1`(artifacts §3.3.3)。
  ag-measurement の standalone `refinement-comparison/v1` / `h1-comparison-data/v1` はこの 2 つに吸収。
- fingerprint の健全性要件(ag-measurement §3.7: identity 自動採用は参照名一致でなく正規化複体表示の同一性を
  witness すること)は、artifacts の **siteCoverDigest**(contexts / covers / 導出 nerve のみから計算)が満たす。
  identity 自動採用条件 = profileFingerprint 一致 ∧ siteCoverDigest 一致、で両設計は合流する。

### 裁定6: verdict 行参照は既存安定形式、conclusionCode は単一 registry

- verdict ref は実装済みの安定形式 `structuralVerdict/{evaluator}/{law}/{method_status}` を正とし、
  artifacts 案の新 verdictId 形式は導入しない。compare / gate の行対応は (evaluator, law, target) の組で取る。
- summary conclusionCode / token は **Rust 単一 const registry + schema catalog + fixture lock** の三点固定
  (artifacts の機構)に、ag-measurement の token 集合(`REPAIR_GLUES_WITHIN_SELECTED_COMPLEX` /
  `MEASURED_NONGLUING_RESIDUAL`(層B)/ `MEASURED_NONGLUING_RESIDUAL_CLASS`(層C)/
  `COVER_SHAPE_EXCLUDES_GLUING_OBSTRUCTION` 等 — claim boundary を綴りに焼き込んだ側)を収載して統一する。
  artifacts の予約名 `REPAIR_GLUES_UNDER_PROFILE`、archview の `MEASURED_REPAIR_GLUES_UNDER_PROFILE` は
  この registry 綴りに読み替える。

### 裁定7: 版数体系の統一 — 単一契約版数 v0.5.0(ユーザー決定 2026-07-04)

個別 artifact に独立の版数(archmap/v2、law-policy/v2、summary/v3、…)を振る体系は廃止し、
**システム全体で版数は一つ — ArchSig のリリース版数 — に統一する**。

- **schema 文字列**: すべて `<artifact-name>/v0.5.0` 形式。「この artifact は ArchSig v0.5.0 の
  artifact contract に適合する」という宣言であり、artifact 個別の `v2` / `v3` は消える。
  例: `archmap/v0.5.0`、`law-policy/v0.5.0`、`archsig-measurement-packet/v0.5.0`、
  `archsig-atom-viewer-data/v0.5.0`。
- **出力**: ArchSig は常に自分のリリース版数で emit する(schema 版数と `toolVersion` は常に一致)。
- **入力(authored artifact)の受理規則**: **現行リリース版数との完全一致のみ受理**(fail-closed。
  エラーが現行版数を名指す)。受理範囲・互換窓のような機構は作らない(裁定10)。
  形が変わっていないリリースをまたぐときの authored ファイル更新は版数文字列の書き換えだけであり、
  機械的(sed 一発、または SKILL が更新時に行う)。この単純さを互換機構より優先する。
- **evaluator id も `@N` を落とす**: `ag.cech-obstruction@1` → `ag.cech-obstruction`。
  evaluator はコンパイル内蔵であり、計算の実体は toolVersion が一意に決める(`@1` は toolVersion と
  二重の版数だった)。挙動変更は release note と catalog に記録し、packet の `toolVersion` が
  監査可能性を担う。`compare` は両 run の toolVersion を記録し、不一致時は boundary statement を付す
  (identical 水準は toolVersion 一致も要求)。verdict ref(裁定6)は
  `structuralVerdict/{evaluator}/{law}/{method_status}` の evaluator segment から `@N` が消えるだけで形式は同じ。
- **統一の対象外(意図的 carve-out)**:
  - `doctrine:aat-canonical@1` — 抽出 doctrine の版はツールのリリースではなく語彙意味論の事件であり、
    独立版数を保つ(A8 の相対化の錨、観測純化 PRD の固定定数)。
  - ユーザーが自分の文書に振る instance id(`policy:shop-backend@1` 等)— author の所有物であり規約しない。
  - fingerprint / digest — 内容の同一性判定は版数でなくハッシュが担う(裁定5)。
- **viewer data の例外は廃止**: v0.5.0 の単一 cut-over に viewer data も含める
  (`schema` キー + `archsig-atom-viewer-data/v0.5.0`)。ArchView は同リリースで受理文字列を更新し、
  **現行 schema のみ受理**する(旧版の併記受理はしない — viewer data は analyze の出力であり、
  古い artifact は再実行で再生成すればよい。幾何再設計自体は 0.5.x のまま)。
- **読み替え規則**: 本ノートおよび次元別 6 文書中の `<name>/vN`・`<name>-vN`・evaluator `@N`・
  `atom-match-key@1` 等の仕様 id は、すべて本裁定の統一形式(`…/v0.5.0`)に読み替える
  (次元別文書は改稿しない。本裁定が正)。0.5.x で新設される artifact(law-equation-surface、
  observation-frontier 等)は初出リリースの版数を `since` として同じ体系に入る。

### 裁定8: SKILL 群の受け皿を明示する

散在していた SKILL 作業を次の 5 本に確定する(いずれも既存 4 SKILL の書式慣行に従う):

1. **archmap-creater 再設計**(§7 の主題。M1-M2 が v0.5.0)
2. **law-policy-creater 改稿**: 新契約(law-policy / measurement-profile)での**新規作成のみ**を扱う。
   旧フォーマットの読み取り・移行・バックフィルは SKILL の責務に含めない(裁定10)。
   Rust の `migrate` コマンドも作らない。旧 law-policy を持つ利用者は、リポジトリの規約・設計文書から
   通常の authoring として書き直す(それが SKILL の本来の仕事)。lawpolicy §6 の移行ツール記述は削除として読む。
3. **archsig-reader v2 native 化**(summary v3 / packet v2 / gate-report の読解順)
4. **archsig-pr-reviewer 後継**: compare + gate の報告を人間語へ翻訳(PR コメント生成は ArchSig 本体の責務にしない)
5. **repair-plan-creater 新設**(v0.5.0 は complete-support mode 限定の最小形。
   SAGA 現場接続の実運用に必須のためオーナー不在を解消する)

gate-policy は SKILL を新設しない(starter テンプレート + docs/tool の authoring ガイド。
law の選択と CI 制度の選択を混ぜない)。

### 裁定9: 相互先送り 2 件の決着

- **ArchMap の鮮度**: archmap/v2 本体は変更しない。鮮度は (a) authoring 側 scope-manifest の revision 記録、
  (b) 計測側 packet / manifest の `inputDigests.archmap`(ArchSig が読み込み時に計算)で持つ。
  entry 単位の鮮度検証は将来課題として明示保留。
- **語彙 manifest**: 初版は archmap-creater の vocabulary-catalog(references 文書 + 機械可読抜粋 fixture +
  CI 突合 lint)。registry manifest への昇格(law surface binding 検証との共有、新 axis escalation の受け皿)は
  0.5.x に LawPolicy Stage 2 と同時に判断する。lawpolicy リスク表の「manifest 一元化」前提はこの段階計画に読み替える。

### 裁定10: 後方互換の全面不採用(ユーザー決定 2026-07-04)

ArchSig は v0.x であり、後方互換は維持しない。互換のための機構を**一切作らない**ことを設計原則にする。
次元別文書に残る互換メカニズムはすべて削除として読む:

- **専用 removal error を作らない**(legacy-triage §3.5 の時限措置は不採用)。旧 schema は一般
  validation fail に一本化(エラー文言に現行契約名を含める程度)。README の移行表 1 枚だけを残す。
- **受理窓・互換範囲を作らない**(裁定7 の受理規則は現行版数の完全一致のみ)。
- **ArchView / FieldSig は現行 schema のみ受理**。旧出力 artifact の graceful degradation・新旧併記受理・
  後方互換テストは作らない(出力は analyze 再実行で再生成できる)。dual-emit も無し(既定どおり)。
- **SKILL は旧フォーマットのバックフィルをサポートしない**: law-policy-creater は新規作成のみ(裁定8)、
  archmap-creater に v1 読み取り・変換の条項を置かない、archsig-reader / pr-reviewer 後継も
  現行 artifact のみを読む。
- catalog の deprecated エントリ掲載(1 release)も不要 — catalog は現行 artifact のみを列挙する。

根拠: 互換の受益者が存在しない(fieldsig は非配布、packet の消費者は monorepo 内に閉じ、
authored artifact は SKILL で再作成できる)。互換を「維持しようとして複雑化する」コストだけが残るため、
根拠のない互換性維持はしないという AGENTS.md の規律をそのまま適用する。

## 9. 統合ロードマップ(単一フェーズ体系)

6 文書の独立フェーズ体系(Phase A-F / V-A〜C / M1-M4 / Stage 1-3 ×2)を単一の依存順序に統合する。
各 P の末尾で `cargo test`(archsig + fieldsig)と CI が green であることを完了条件とする。

| P | 内容 | 由来 | 主な順序制約 |
| --- | --- | --- | --- |
| P0 | 孤児 3 点削除 + CLAUDE.md / AGENTS.md の analyze 例差し替え(既に fail している) | 次元1 A | なし。即着手可 |
| P1 | v0 dead 一式 + fixture 10 系統 + schema-catalog legacy + FieldSig **v0** 受理削除 | 次元1 B | P0 |
| P2 | 命名・版数統一(schema キー / 単一契約版数 `<name>/v0.5.0`、viewer data 含む + ArchView 受理文字列の最小パッチ)+ run-manifest 単一様式 + schema catalog / 入力受理の完全一致規則 + digest 基盤(sha2 / canonical JSON / 決定的 runId)+ Cargo 0.5.0 | 次元4 A + 裁定7 | P1。tests/cli.rs 断言 150+ 箇所は機械置換で独立 PR |
| P3 | measurement packet 新形(profile 埋め込み凍結)+ summary / insight 新形 + packet validation + FieldSig 新 packet 受理・行レベル propagation + lean.yml handoff 更新 | 次元4 B | P2 |
| P4 | `archsig gate`(gate-policy / gate-report / exit code 体系)+ `archsig compare`(identical / verdict-row + 計算 archmap-diff)+ lean.yml push 側 e2e を analyze+gate 形へ | 次元4 C + 裁定1/2 | P3。v1 削除(P5)の受け皿を先に立てる |
| P5 | v1 path 一式削除(typed evaluator / pr-review / --strict-distance。専用 removal error は作らない — 裁定10)+ **lean.yml v1 区間削除 + FieldSig v1 受理削除(同一 PR)** | 次元1 C | P4 |
| P6 | skills 改稿(reader / pr-reviewer 後継 / creater の v1 条項削除 / law-policy-creater)+ docs 改稿・archive 移動 + 残存ドリフト掃除(registry 判定語 3 件 + legacy-counting-invariant 廃止)+ 拡大 rg 残存検査 | 次元1 C-3 | P5 |
| P7 | law-policy / measurement-profile の新形(Stage 1: basisLedger / finiteBounds / 独立ファイル化 / lawSurfaceRef・policies[].profileRef 予約)+ CLI `--law-policy` 改名 | 次元3 Stage 1 | P3(schema catalog)。P5 と同一マイルストーン |
| P8 | SAGA Stage 1: repair-plan/v1 + `repair-plan` コマンド(`--residual-packet` 込み)+ `ag.saga-descent@1`(complete-support regime)+ `ag.cech-obstruction@2` + `REPAIR_TARGETS_IDENTIFIED` + Lean witness fixture ロック | 次元2 Stage 1 | P3 / P7 |
| P9 | archmap-creater M1-M2: references 再編 + candidate packet schema 化 + authoring CLI 3 面(scope-manifest / extraction-diff / archmap 監査)+ 層1 lint(語彙カタログ突合含む) | 次元6 | P2(digest 基盤を共有) |
| 0.5.x | LawPolicy Stage 2(law-equation-surface / bundle / fingerprint)、SAGA Stage 2(saga-comparison / supplied faithfulness / 出力語彙 lint / gate boundaryKindOverrides)+ **Stage 3(saga-grounded 10 結論 packet / harmonic-debt / refactor-transport)**、compare の class-transport、archmap-delta + delta-apply、observation-frontier(任意、次元6 支援)、ArchView V-A〜V-C、extraction corpus M3、SKILL M4 | 各次元 | v0.5.0 出荷後。SAGA の現場接続は 0.5.x 系列で完結させる |
| v0.6.0 | **予約**: SAGA からさらに先へ進んだ研究成果の取り込み(例: G-04 系 — non-abelian H¹ / stacky descent、conormal 係数 I_U/I_U² の読み)。v0.5.x までの計画項目をここへ送らない | 理論側の進展待ち | 0.5.x |

同一作業の重複計上(FieldSig 受理削除、legacy-counting-invariant 廃止、registry 掃除、CLAUDE.md 例、schema catalog 改訂)は
上表の P に一意に帰属させた。

## 10. v0.5.0 スコープ — 案A で確定(ユーザー決定 2026-07-04)

**採択: 案A。v0.5.0 = P0〜P9 全部**(レガシー全破棄 + 基盤 + gate / compare + LawPolicy Stage 1 +
SAGA Stage 1 + SKILL M1-M2)。目標アウトカム O2 / O4 / O5 の完結は 0.5.x 追補(§9 のとおり)。
以下は選択時の比較記録として残す。

1. **案A(採択): v0.5.0 = P0〜P9 全部。**
   レガシー全破棄 + 基盤 + gate / compare + LawPolicy Stage 1 + SAGA Stage 1 + SKILL M1-M2。
   「単一 path の確立 + SAGA の最初の計測 + CI 合否面 + 抽出再現性の底」が一版で揃い、8 方針すべてに実体が入る。
   リスクは規模(PR 十数本)だが、P 間の依存は直列に切ってあり、各 P で CI green を保てる。
2. **案B(薄い v0.5.0): v0.5.0 = P0〜P6。**
   破棄と基盤と CI 面まで。P7〜P9 は 0.5.x へ。最速で「古典レガシーゼロ」を宣言できるが、
   「AG 分析の充実」「SAGA 接続」の実体が版名に対して空になる。
3. **案C(厚い v0.5.0): 案A + LawPolicy Stage 2 + SAGA Stage 2 + ArchView V-A/V-B。**
   全次元が一版に結合する。監査が警告したとおり、どれか一つの遅延が全体を止める構造になるため非推奨。

## 11. ユーザー確認事項・未決事項

**ユーザー確認が必要(本設計の外側の判断)**:

1. ~~スコープの選択~~ → **案A で確定**(§10、2026-07-04)。
2. ~~Lean guardrail 3 本の処遇~~ → **決定**(2026-07-05): 削除する
   (`Formal/Arch/Signature/{MonodromyMeasurement,CurvatureTransferSpectrum,HomotopyHolonomyStokes}.lean`。
   Formal.lean の import 3 行除去 + classical index 該当節に archive 注記、lake build green を確認)。
   背景: ユーザーは **Formal/Arch 全体を近日中に archive する意向**であり、古典塔9ファイルの棚卸しは
   その別件に吸収される(本設計のスコープには含めない)。Rust 側の削除は Lean 側の作業を待たない。
3. ~~第 1 世代理論ノート 4 本の archive 移動~~ → **決定**(2026-07-05): docs/archive へ移動する(P6 で実施)。
4. ~~viewer PRD 3 本の扱い~~ → **決定**(2026-07-05): superseded 追記ではなく **docs/archive へ移動**する。
   本設計(統合ノート + design_archview)が正。M+V 統合 PRD の M 側は v0.4.0 で実装済みのため
   PRD は歴史記録として archive で問題ない(実装の正は現行コードと docs/tool)。
5. ~~Three.js vendor の配置~~ → **決定**(§6、2026-07-05): repo は CDN pin のまま、release bundle のみ
   packaging 時に checksum 検証付きで vendor 注入。

**設計内の未決(PRD 化時に確定)**: 各次元文書の §6 参照。主なもの —
restrictsTo の正準方向の一文定義(次元6)、`ag.saga-descent@1` の層 B/C 分割判断(次元2)、
basisLedger の path 実在検査の深さ(次元3)、SARIF 変換器の要否(次元4)、
viewerVisualScenes 12→9 語彙の registry 更新(次元5)。

**PRD 化の切り方(候補)**: ロードマップの P 群単位で 4 本に分けるのが自然 —
(i) レガシー破棄 P0-P2・P5-P6、(ii) artifact / CI 基盤 P3-P4、(iii) LawPolicy + SAGA Stage 1 P7-P8、
(iv) ArchMap SKILL P9。各 PRD の「問い」候補は着手時に複数提示する。
