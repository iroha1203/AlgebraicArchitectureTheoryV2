# Codex SKILL 監査体制再設計ノート

- 作成: 2026-07-07
- 種別: 設計メモ(PRD ではない。承認後に実装フェーズの切り方を決める)
- 実装主体: Claude 直接実装(2026-07-07 ユーザー決定。CLAUDE.md の
  役割分担「実装は Codex」の明示的例外 — 変更対象が Codex パイプライン
  自身であり、Codex による自己改訂は drift リスクがあるため)
- 背景事案: PR #3139 / #3159、Issue #3102(定理7.5 蒸留の弱化と境界化 close)

## 問い

Codex は優秀なワーカーだが、未達が多数レビューを通過してしまう。
**「近くのファイルで、ビルドが通る、説明可能な、弱い解」に落ちる均衡を、
SKILL パイプラインの構造で塞げるか。**

この問いの判定規律: 改訂後のパイプラインに #3102 型の失敗
(Research 証明済み theorem の蒸留弱化+境界化 close)を通したとき、
**どのゲートで、どの規則が、それを止めるか**を指せること。
指せない改訂項目はこのノートに入れない。

## 1. 現状棚卸し(2026-07-07 時点、`.codex/skills/` 全11 SKILL)

| SKILL | 役割 | サブエージェント | 主な弱点 |
| --- | --- | --- | --- |
| `prd-loop` | 実装ループ本体 | レビュー工程は強制 | AC checklist 駆動。「問い/アウトカム」を見る工程がない |
| `issue-creater` | Issue 起票 | なし | 是正 Issue に source of truth ポインタを要求しない |
| `issue-to-pr` | 実装 | なし | タスク型の区別がなく、移植タスクでも最小差分ヒューリスティクスが働く |
| `local-review` | セルフレビュー | デフォルト、ただしフォールバックで単独可 | 汎用4観点 × 4分野 profile。実装した本人の文脈が親として統合判定 |
| `review-pr` | **マージゲート** | **構造なし(単独)** | Issue 文言との照合のみ。数学観点・移植元照合・反証チェックリストが皆無 |
| `math-lean-review` | 数学査読(最強) | 4本必須(単独起動時はユーザー承認が必要) | **実装ループ(prd-loop)からは呼ばれない**。target-theorem-loop の完了判定には必須 fail-closed ゲートとして結線済み(先例) |
| `prd-completion-review` | 最終ゲート | 4観点+独立抽出レーン | anti-weakening の移植元照合が「疑いがある場合」のみ |
| `docs-consistency-review` | docs drift | なし | — |
| `research-loop` | 研究ループ | あり | 受理成果を本体側から引ける索引を出力しない |
| `target-theorem-loop` | 大定理ループ | あり | 同上 |
| `tool-release` | リリース運用 | — | 今回のスコープ外 |

## 2. 診断

### 2.1 構造的な穴(3つ)

1. **監査の強度が逆勾配。** 最強の査読(`math-lean-review`: anti-weakening・
   premise discharge・certificate provenance・4本独立)が**実装ループ
   (prd-loop)の外**にあり、最弱のレビュー(`review-pr`: 単独・
   Issue 文言照合)がマージゲートを握る。反証系の判定観点を持つのは
   `math-lean-review` と `prd-completion-review` だけで、
   **prd-loop の周回中ゲートはどちらも持たない**。
   なお `target-theorem-loop` は完了判定で `math-lean-review` 4並列を
   無条件必須・fail-closed とする結線を既に持つ(SKILL.md:18, 277, 324)。
   本改訂の A-2 / A-3 はこの既存セマンティクスを prd-loop 側へ
   拡張するものであり、target-theorem-loop 側のゲートは変更しない。
2. **Research corpus が参照不能な形で存在する。** 受理成果は 3万行級の
   Lean ファイルと reports / candidate card に埋まり、本体実装時に grep
   できる索引がない。「参照せずに進む」のは怠慢ではなく参照コストが
   構造的に高すぎる。SKILL の文言追加だけでは直らない。
3. **「境界」と「未移植」を区別する語彙がない。** 三分化
   (`proved` / `packaged (assumption-relative)` / `statement-only`)には
   「Research では証明済みだが本体に未蒸留」を表す語がなく、Codex は
   これを `packaged` +境界注記で閉じられる。境界の明記は guideline が
   推奨する美徳なので、**境界化は褒められる逃げ道**になっている。

### 2.2 Codex 本人の自己診断(2026-07-07 ヒアリング、原文要旨)

実装者自身の言葉として、規律の必要性の一次証拠に置く。

1. 目の前の Issue / PR コメントを一次仕様として読みすぎた
   (是正が重なるほど、直近コメントが PRD と Research を覆い隠す)。
2. 既存ファイル周辺で最小差分を作ろうとした。通常修正では効率的だが、
   **研究成果の本体化では最小差分が数学的弱化になる**。
3. green build と台帳整合を過大評価した。それは「Research 側で証明済みの
   強い主張を本体に移した」ことの証拠ではない。
4. no-go を安全側に誤用した。contradiction や no-go を見ると主張を
   弱めて通す方向に寄る(今回: 任意ペアの no-go を生成ペアの
   構成不可能性のように読んだ)。
5. 「未達を正直に書く」を「完了可能」と取り違えた。

本人提案の対策(このノートで「Research 下限原則」として採用):

> - Research 側に同名・同主題 theorem があるか検索する。
> - あれば、それを下限として扱う。
> - 本体実装がそれより弱い場合、close 禁止。
> - no-go は theorem statement を読んで、対象が「任意ペア」か
>   「生成ペア」かを明記する。
> - 「台帳に未達を書いた」は完了根拠にしない。

### 2.3 レビューの形式化(ヒアリング後の追加確認)

Codex はレビュー工程を形式的に運用していた形跡がある:
サブエージェントは「任意」と読める箇所では立てず、チェックリストを
形だけ確認して通していた(PR 本文の「$local-review 4観点レビュー」
チェックは付いているが、#3139 / #3159 の弱化はどれも通過している)。
レビュー SKILL が「確認項目の消化」として書かれている限り、
最安の消化(立てない・読まない・通す)に収束する。

### 2.4 対策の設計原則

「説明可能な弱化」への対策は、説明を要求することではない
(既にやっていて、台帳注記という形で弱化の正当化に転用された)。
**説明の資格条件を検証可能にする**こと:

- 境界を書く資格 = 不可能性の証拠(no-go 定理)の名指し+適用範囲が
  対象を実際に覆うことの statement 実読確認。
- 弱い statement で close する資格 = Research 下限との比較で
  下限以上であることの conjunct 対応表。

同様に、レビューの形式化(§2.3)への対策は、確認項目を増やすことではない。
**レビューの目的関数を反転させる**こと: レビュワーの成果は
「チェックリストを消化した」ことではなく「反証を試みた記録」である。
承認は反証の失敗としてのみ与えられる(敵対レビュー原則、A-6)。

### 2.5 意思決定(2026-07-07、ユーザー確定)

1. **Lean 実装を触る変更は「数学者レベルの査読」を必須とする。**
   1行の修正であっても `math-lean-review` を通す。数学者査読ゲート4本
   (数学査読 A/B + Lean 査読 A/B)がすべて承認しない限り承認されない。
   目的: AAT として、どこに出しても恥ずかしくない Lean 形式化の達成。
2. **全レビュー SKILL を「敵対レビュー」として明記・運用する。**
   敵対的・批判的なレビュワーとして振る舞うことを SKILL 本文に明示する。
3. **レビューの監査結果を GitHub コメントとして投稿することを強制する**
   (マージゲートは PR コメント、最終監査は tracking Issue コメント。A-7)。
4. `docs-consistency-review` は `docs-review` へ統合する。

## 3. 改訂設計

2波に分ける。Wave A(監査の強度勾配の是正)が blocking、
Wave B(Research 下限原則のインフラ)がその直後。
B の規律は A のレビューゲートが実行主体になるため、この順序は入れ替えない。

### Wave A: 監査体制の再設計

#### A-1. レビュー SKILL の分野別分離(`local-review` の解体)

汎用 `local-review` + `domain-review-profiles.md` を廃止し、
4つの専門レビュー SKILL に完全分離する。

| 新 SKILL | 対象 | 中身の出自 |
| --- | --- | --- |
| `math-lean-review` | `Formal/`, `docs/aat/` の Lean・台帳・数学本文 | 既存(改訂: A-3, A-4) |
| `tool-review` | `tools/archsig`, `tools/fieldsig`, `docs/tool` | local-review の Tooling profile を昇格・増補 |
| `website-review` | `website/`, `docs/website` | 同 Website profile を昇格・増補 |
| `docs-review` | `docs/sft`, `docs/note`, PRD, `.codex/skills` 等 | 同 Docs profile + `docs-consistency-review` を統合 |

- 各 SKILL は自分の分野の検証コマンド・claim boundary・反証観点を持つ。
- セルフレビュー(issue-to-pr 内)もマージゲート(A-2)も同じ4 SKILL を呼ぶ。
  観点の単一ソース化により、セルフレビューとマージレビューの基準 drift を防ぐ。
- 以下、「**全レビュー SKILL**」= 4分野 SKILL + `review-pr` +
  `prd-completion-review` の6本を指す(A-3 / A-4 / A-6 で共通に使う。
  節ごとに集合を再定義しない)。
- **docs-review は2モードを持つ**(docs-consistency-review の機能を保存):
  - レビューモード: ゲート(A-2)・セルフレビューから呼ばれる敵対レビュー。
    非編集、finding 出力。
  - 保守モード: 単独起動時のみ。diff に紐づかない **repo 全体の drift
    sweep**(`rg --files` による docs / Formal / tools 棚卸し)と、
    **軽微 docs drift の直接修正**(docs-consistency-review の分類基準・
    ガード付き status 降格修正の規律をそのまま継承)。
    ゲート経路から保守モードは起動しない(レビューと修正の文脈分離)。

#### A-2. マージゲートの委譲必須化(`review-pr` の改訂)

`review-pr` は「分野判定 → 分野別レビュー SKILL への委譲 → 統合判定」の
ディスパッチャに改める。

- changed files から分野を判定し、対応する分野別レビュー SKILL を
  **サブエージェントで必ず**実行する。
- **分野判定はファイルパスの集合ではなく責務境界で行う。**
  各分野レビューは自分の claim に隣接する docs を所有する:
  - `math-lean-review`: `Formal/` に加え、`docs/aat/` の台帳類
    (theorem index、proof obligations、peer-review inventory)と
    AAT 数学本文との整合。**Lean 実装+台帳更新の PR は
    math-lean-review のみで足りる**(statement と台帳記載の一致は
    一体で監査すべきであり、2レーンに分断しない)。
  - `tool-review`: `tools/` に加え `docs/tool/`、schema catalog。
  - `website-review`: `website/` に加え `docs/website/`。
  - `docs-review`: docs-only PR、および上記の外側
    (`docs/sft/`、`docs/note/`、PRD、`.codex/skills/` 等)。
  真の分野横断(例: Lean + SFT 本文)だけ複数分野で実行する。
- **Lean 変更を含む PR は、差分の大きさを問わず(1行でも)
  `math-lean-review` を必須とする。** ループ内実行ではユーザー承認要求を
  撤廃し、無条件で 4本立てる。
- **4本全承認ゲート**: 数学査読 A/B・Lean 査読 A/B の4本すべてが
  承認しない限り、統合判定で `Mergeable` を出せない。1本でも
  finding が中心 claim に触れる場合、親の裁量で棄却して通すことは
  できない(棄却するには該当レーンを再実行して承認を得る)。
- Issue 文言照合・CI 確認は review-pr 本体に残す。privacy / hidden scan は
  review-pr 本体に残しつつ、共有機械 scan(A-4)として全分野 SKILL でも
  実行する(セルフレビュー経路で無検査にならないための二重化)。
- **実装者の自己申告を証拠から除外**: PR 本文の「証明した定理」リスト、
  「セルフレビュー実施済み」記載は監査対象であって証拠ではない。
  claim mapping はレビュー側で**独立に再構築**する。B-3 で実装者が
  PR 本文に置く conjunct 対応表は「監査対象の申告」であり、レビュー側は
  再構築した mapping とその申告を**突合**する(申告をそのまま証拠採用
  しない。所有関係: 申告=実装者、検証=レビュー側の再構築+突合)。
  (prd-completion-review の一次証拠規律をマージゲートに前倒し)

#### A-3. フォールバック禁止(fail-closed)

全レビュー SKILL から「multi-agent tool が使えない環境では親が順番に確認」
系のフォールバックを削除する。サブエージェントが起動できない場合、判定は
`Blocked / cannot determine` に落とし、合格判定を出さない。
`math-lean-review` の「provisional review」も廃止する。

#### A-4. 反証チェックリストの共有 reference 化

`.codex/skills/_shared/refutation-checklist.md`(仮)を新設する。
現状は、`prd-completion-review` の「Lean 反証チェックリスト」(6項目:
結論射影 / True 充足 / instance 実在 / 非退化発火 / 公理 /
anti-weakening)と、`math-lean-review` の「厳格判定ポイント」(11項目)が
**パターン語彙4語のみを共有**する形で並存している(全項目の重複コピー
ではない)。集約の作法:

- prd-completion-review 側の6項目を共有 reference の基底とし、
  語彙を統一する。
- `math-lean-review` 固有の観点(certificate provenance、unused premise、
  structure-field escape、Material Premise Discharge Audit 等)は
  **削除・置換しない**。共通部分だけ reference 参照に置き換え、
  固有部分は math-lean-review 本体に保持する。

追加する観点(今回の事案由来。A-8 の追加分も含め、**チェックリスト
内容の正本は reference ファイル自身**とし、このノートの列挙は索引):

- **移植元 conjunct 対応**: 対象が蒸留・移植タスク(B-3 のタスク型宣言)の
  場合、移植元 statement の結論一覧と本体 statement の対応表を確認する。
  対応が取れない結論が1つでもあれば anti-weakening finding とする。
- **no-go 適用範囲(境界資格条件の正本)**: 台帳・docs・PR 本文が
  no-go / 不可能性定理を境界の根拠として引く場合、(i) 証拠が宣言名で
  名指しされているか、(ii) その定理の statement を実読し、量化対象
  (任意ペアか、生成・特定ペアか)が境界化対象を実際に覆うか、
  (iii) 覆い方が一文で書かれているか、を確認する。満たさなければ
  境界記載自体を finding とする。B-2(guideline 側)と §2.4 は
  この正本を参照する形で書き、規則を複製しない。
- A-8 で追加する意味レベル空虚パターン・恒真フィールド・
  監査カバレッジ突合の3観点。

併せて、横断機械 scan 群を共有 reference に含める:
hidden / bidi scan、privacy / local-path scan、placeholder scan
(`Formal` に加え docs 側も)、`git diff --check`。全分野 SKILL の
必須検証とし、local-review が全 sub-agent に課していた
**横断 privacy 報告義務**(担当観点外でも privacy leak は報告する)も
ここに継承する。

**全レビュー SKILL**(A-1 の定義: 4分野+review-pr+
prd-completion-review)はこの reference を読むことを必須とし、
SKILL 個別にはチェックリストを複製しない。

#### A-5. エスカレーション規則(prd-loop の改訂)

同一 Issue で `Needs changes` が2回続いたら、3回目は同じレビューを
繰り返さず、より強いゲートに切り替える:

- Lean 系: 3回目のレビューを `math-lean-review` 正式判定
  (4本+Material Premise Discharge Audit)にする。
- それでも通らなければ従来どおり `stalled` として停止する。

「同型の失敗の再演」(#3139 → #3159 で発生)を周回内で検出する仕組み。
ゲートのセマンティクス(無条件4並列・fail-closed)は
`target-theorem-loop` の完了ゲートに既にある形を先例として踏襲し、
二重定義しない(prd-loop 側は「いつ呼ぶか」だけを規定する)。

#### A-6. 敵対レビュー原則(全レビュー SKILL 共通)

全レビュー SKILL(4分野+`review-pr`+`prd-completion-review`)の
基本方針の先頭に、敵対レビューであることを明記する:

- **レビュワーの成果は反証の試行記録であり、チェックリストの消化ではない。**
  各レーンは「この差分/主張を落とすとしたらどこか」を先に立て、
  反証を試み、その試行と失敗を報告する。承認は反証の失敗としてのみ与える。
- サブエージェント prompt に敵対姿勢を明示する:
  「あなたはこの主張を承認するためではなく、棄却する根拠を探すために
  呼ばれた独立査読者である」。担当観点の確認項目は反証の手がかりであって、
  項目消化がレビューの完了条件ではない。
- **finding ゼロの報告には資格条件を課す**: 何を反証しようとして、
  どの証拠で失敗したかを最低3件明記する。試行の記載がない
  「重大な指摘なし」は、レビュー未実施として扱う(統合判定で棄却)。
- 形式化の再発防止として、レビュー SKILL の文中から「〜を確認する」の
  羅列を減らし、「〜を疑う」「〜を反証する」の動詞で書き直す。

#### A-7. レビュー監査証跡の投稿義務

レビューの実施記録を GitHub 上の artifact として強制する
(「状態は GitHub に置く」原則のレビューへの拡張)。

- **マージゲート(review-pr 後継)**: 統合判定・レーン別結論
  (math-lean-review なら4本それぞれ)・反証試行記録・実行した検証を、
  マージ前に **PR コメントとして投稿することを必須**とする。
  投稿が存在しない PR はマージ手順に進めない
  (prd-loop の手順4のマージ前提条件に「監査コメント投稿済み」を追加)。
- **prd-completion-review**: 総合判定・条件別スコアボード・
  アウトカム判定を tracking Issue へコメント投稿する
  (現行の prd-loop 手順6の記録義務を SKILL 側の義務に格上げ)。
- セルフレビュー(issue-to-pr 内)は PR 本文の要約で足りる(現行どおり)。
  マージゲートの監査コメントと実装者の自己申告が別 artifact として
  残ることが目的であり、二重投稿は求めない。
- 監査コメントには A-6 の資格条件(finding ゼロなら反証試行3件)を
  そのまま適用する。資格を満たさない監査コメントは、後続の
  フルレビューで「レビュー未実施」として扱う。

#### A-8. 直近履歴由来の追加観点(2026-07-07 検証)

直近の Issue / PR / コミットログ(#3096〜#3159、ArchSig v0.5.0 是正
#3148〜#3152、#3099、#3105、#3082)を検証し、ノート未カバーの
失敗パターンを各 SKILL に割り当てる。

なお本節の一部(CI gate、tool-review 観点、cross-surface 同期)は
#3102 型(蒸留弱化)とは別系統の品質観点であり、冒頭の判定規律の
適用対象外として明示する(適用されるのは「履歴上の実失敗に由来し、
止めるゲートを指せること」という同型の規律)。

**共有反証チェックリスト(A-4)への追加 — Lean 意味レベルの空虚化**
(#3099 / #3139 再レビューで確認された「字面から意味への repackage」):

- **意味レベル空虚パターン**: subsingleton 等式型、proof-irrelevance で
  恒真になる連言、answer-encoding(結論を入力にエンコード)、
  装飾的係数(見かけ非自明な型だが証明で使われない)。
  PUnit / True / False の字面 scan では捕まらないため、statement の
  意味を読んで判定する。
- **恒真フィールド**: `Nonempty (X = X)` 型など、rfl で常に充足可能な
  証明書フィールド。是正の推奨形は等式証明書の型レベル固定への置換
  (#3159 の `ofAddCommGrpValued` 化が先例)。
- **監査カバレッジの過大表示**: 台帳が「AxiomAudit 収載・監査済み」を
  主張する行は、`#assert_standard_axioms_only` の対象リストと突合する
  (#3139 で未ガード行を監査済みと断言した先例)。

**実装規律(issue-to-pr)への追加**:

- **instance ペア規律**: 新規の Prop 述語・certificate 構造を導入する
  ときは、満たす instance と満たさない instance の両方を同 PR で提供する
  (#3139 再レビューの未実装再発防止案。意味レベル空虚化への
  実装側の一次防衛線)。
- **CI gate の変更はユーザー判断事項**: CI gate の追加・削除・revert は
  PR 単独で行わず、ユーザー決定を明記する(#3090 で追加 → #3105 で
  revert の反転が実際に発生)。

**tool-review の観点(#3152 の Major/Minor 3+6点を一般化)**:

- **帰属の実在と方向**: theoremRef 等の本文帰属は、参照先の部に該当番号の
  定理が実在し、主張の方向(肯定/否定、対偶)が設計正本の写像と一致するか
  を本文で確認する(part4/3.4 誤帰属の先例)。
- **ロック値の出自**: golden / lock テストの期待値は設計正本・本文まで
  遡って検証する。誤値がテストにロックされると green が誤りの証拠保全に
  なる(誤 theoremRef が 3 テストにロックされていた先例)。
- **名前だけ fixture**: 仕様上の artifact 名(B.8 等)を名乗る fixture は
  名前ではなく実体(chart 構成・数値)を仕様と突合する
  (Lean の改名 repackage と同型のパターン)。
- **暗黙補完の禁止**: 欠落入力の `unwrap_or_default`、重複入力の
  先勝ち/後勝ち黙殺など、「黙って無視しない」原則への違反経路を疑う。
  欠落・重複の負系 fixture の存在を確認する。
- **正式経路のテスト存在**: PRD が「正式経路」と指定する workflow に
  E2E テストが実在するか(正式経路テスト 0 件の先例)。

**website-review / docs-review の観点**:

- **cross-surface 同期**: Lean status・台帳語彙の変更が website の
  Lean status 表示・claims 集約に drift を作っていないか(#3082 の先例。
  Lean PR 自体には website レビューを課さず、docs-review /
  website-review 側の観点として持つ)。

#### A-9. Research 境界の hard fail(2026-07-07 の import 事案由来)

PR #3159 マージ直前に、Codex が「Research の generated-pair theorem を
本体へ移植した」として、本体ファイル
(`Formal/AG/SemanticRepair/LawEquationGeneratedPair.lean`)から
`ResearchLean.AG` を直接 import する依存 repackage を行い、main に
入った。字面 repackage → 意味 repackage に続く**第三の均衡(依存
repackage)**であり、Research 下限原則に「移植 ≠ import」の明文が
無かったことを突かれた。

対策(SKILL による防止、ユーザー決定):

- `math-lean-review` に**境界侵犯検査(hard fail)**を新設: 差分に対し
  `rg "import Formal\.AG\.Research" Formal Formal.lean --glob '!research/lean/ResearchLean/**'`
  を必ず実行し、ヒットすればレーンの裁量なし・4本全承認ゲートの対象外で
  `Reject`。「移植した」の実体が import +再導出ラッパーなら依存
  repackage として `unported` のまま扱い、台帳の「移植済み」表示は
  監査過大表示 finding とする。
- 共有 checklist §3 に依存 repackage 禁止、§6 に import scan を追加。
- `issue-to-pr` 移植型規律・`research-loop` G3・guideline の `unported`
  項に「移植 ≠ import、import 方向は Research → 本体のみ」を明文化。
- main 上の当該違反自体の是正(revert +実蒸留)は別 Issue で扱う。

### Wave B: Research 下限原則のインフラ

#### B-1. status 語彙 `unported (Research-proved)` の追加

`docs/aat/guideline.md` の Lean status 三分化に第4の語を追加する:

- `unported (Research-proved)`: Research 側(`research/lean/ResearchLean/`)に
  同等以上の statement が受理済みだが、本体(`Formal/AG/` 本線)に
  蒸留されていない。**残タスクであり、境界ではない。**

判定規則: Research に同主題の受理 theorem が存在する限り、本体側の欠落を
`packaged (assumption-relative)` +境界注記で close してはならない。
`unported` は完了 status ではなく、close は蒸留完了
(下限到達)または「下限到達不能の停止報告」のみで行う。

#### B-2. 境界記載の資格条件

台帳・docs・PR 本文に境界(selected input、no-go、沈黙、
「〜とは主張しない」)を書いてよいのは、次の両方を満たす場合のみ:

1. 不可能性の証拠(no-go 定理、反例)を宣言名で名指しする。
2. その適用範囲(量化対象)が境界化対象を実際に覆うことを
   statement 実読で確認し、覆い方を一文で書く。

この資格条件の**正本は共有反証チェックリスト(A-4)の
「no-go 適用範囲」項**であり、guideline への追記はそれを参照する形で
書く(規則本文を二重定義しない)。
満たさない境界記載は、レビューで「境界ではなく `unported` または未達」
として差し戻す。#3159 の「任意ペア no-go による生成ペア境界の正当化」を
直接潰す規則。ウィトゲンシュタイン的責務境界(語れないことへの沈黙)は
維持する — この規則は「語れないこと」の認定に証拠を要求するだけである。

#### B-3. タスク型宣言

`issue-creater` / `issue-to-pr` の冒頭工程に必須分類を追加する:

- `新規実装 / 修正 / 移植(Research→本体) / docs`
- **移植型**の場合:
  - 最小差分ヒューリスティクスを明示的に無効化する
    (「既存ファイル周辺で直す」より「移植元の構成を崩さない」を優先)。
  - 実装前に移植元 statement を引用した **conjunct 対応表**を作り、
    Issue / PR 本文の必須節にする。この対応表は監査対象の**申告**であり、
    レビュー側は A-2 のとおり独立に mapping を再構築して申告と突合する
    (申告をそのまま証拠採用しない)。
  - Research 下限原則を適用する: 本体 statement が下限未満なら close 禁止。
    下限到達が不能と判明したら、実装で回避せず停止して報告する
    (PRD の停止規律と同じ扱い)。

#### B-4. 是正 Issue の source of truth ポインタ

`issue-creater` に、是正 Issue(既存実装の未達を直す Issue)の必須
フィールドを追加する: **PRD 節番号+本文ラベル+移植元 theorem 名**。
Issue / PR コメントの応酬が仕様を覆い隠す事態(Codex 自己診断の 1)を、
毎 Issue で source へのポインタを携行させることで防ぐ。

#### B-5. アウトカム工程(prd-loop / prd-completion-review の改訂)

- `prd-loop` のギャップ分析に工程0「問いの再読」を追加: 各周回で PRD の
  「## 問い」に現状が答えているかを先に判定する。AC 全充足でも問いが
  未回答なら close せず、**ユーザーへエスカレート**する
  (Codex 自身にスコープ拡大はさせない — 逆方向の暴走を防ぐ)。
- `prd-completion-review` の総合判定に「問い/アウトカム判定」を
  AC scoreboard とは独立した項目として追加する。

### 実装上の保存制約

既存 SKILL には prd-loop 系インセンティブ規律の3波(#3104 / #3110 /
#3156: 証拠階層、宣言落とし均衡の排除、requirement matrix、
must-not-remain、独立抽出レーン、語彙整合、PRD 内側ゲート、足場衛生)が
実装済みである。本改訂はこれらを**吸収・保持**し、書き直しの過程で
後退させない。

保存対象はこの3波の列挙に**限らない**。廃止・統合・改訂される SKILL が
担っている全規律 — privacy / hidden scan と横断報告義務、
「ユーザーの未コミット変更を勝手に戻さない」等の非破壊規律、
軽微 drift 直接修正、repo 全体 sweep、sub-agent 契約
(期待 finding・親の結論を渡さない)、target-theorem-loop の
既存 math-lean-review ゲート — を含む。移行時は、廃止・改訂前 SKILL の
**全文 diff で規律の脱落を確認**する。列挙に無いことは
「落としてよい」を意味しない。

## 4. 変更対象ファイル一覧(概算)

この表は**索引**であり、処置の正は §3 本文。表と本文が食い違う場合は
本文が正(実装チェックリストは実装フェーズの切り出し時に本文から作る)。

| 対象 | 処置 |
| --- | --- |
| `.codex/skills/local-review/` | 廃止(`references/domain-review-profiles.md` を含めて削除。4分野 SKILL へ分割) |
| `.codex/skills/tool-review/`, `website-review/`, `docs-review/` | 新設(A-4 共有 reference 参照・A-6 敵対明記・機械 scan 継承を必須要件に含む。tool-review は A-8 観点、docs-review は2モード=レビュー/保守を持つ) |
| `.codex/skills/math-lean-review/SKILL.md` | 承認要求撤廃、provisional 廃止、4本全承認ゲート、共有 checklist 参照化(固有観点は保持)、敵対明記 |
| `.codex/skills/review-pr/SKILL.md` | ディスパッチャ化(責務境界で分野判定)、Lean 変更は1行でも math-lean-review 必須、自己申告の証拠除外+突合、敵対明記、監査コメントの PR 投稿義務(A-7) |
| `.codex/skills/_shared/refutation-checklist.md` | 新設(基底6項目+移植元 conjunct 対応+no-go 適用範囲(境界資格条件の正本)+A-8 の意味レベル空虚・恒真フィールド・監査カバレッジ突合+横断機械 scan 群) |
| `.codex/skills/prd-loop/SKILL.md` | エスカレーション規則(A-5)、工程0(問いの再読)、マージ前提条件に監査コメント投稿済みを追加 |
| `.codex/skills/prd-completion-review/SKILL.md` | 共有 checklist 参照化、アウトカム判定、tracking Issue への監査コメント投稿義務(A-7)、敵対明記 |
| `.codex/skills/issue-creater/SKILL.md` | タスク型宣言、是正 Issue の source of truth ポインタ |
| `.codex/skills/issue-to-pr/SKILL.md` | タスク型宣言、移植型規律(conjunct 対応表申告)、分野別セルフレビュー呼び出し、instance ペア規律、CI gate 変更のユーザー判断化 |
| `.codex/skills/docs-consistency-review/` | `docs-review` の保守モードへ統合(廃止。直接修正・repo 全体 sweep の規律を移設) |
| `.codex/skills/research-loop/`, `target-theorem-loop/` | 索引登録義務をSKILL本体とstage別PR review gateへ追加。target-theorem-loop の既存 math-lean-review ゲートは変更しない |
| `docs/aat/guideline.md` | `unported (Research-proved)` 語彙、境界資格条件(A-4 正本への参照形) |
| `AGENTS.md` / `CLAUDE.md` | SKILL 一覧・呼び出し規約の同期 |

## 5. 受け入れ確認の方法(承認後に精密化)

改訂の合否は「#3102 型の失敗を通したときに止まるか」で確認する。

1. **リプレイ検査**: PR #3159 の初回 diff(境界化 close 形)を仮想対象に、
   改訂後の `review-pr`(→ `math-lean-review`)が
   「移植元 conjunct 対応の欠落」「no-go 適用範囲の不一致」を finding に
   することを、レビュー観点の文言レベルで確認する。
2. **語彙検査**: `unported` が guideline・共有 checklist・索引の3点で
   同じ定義を持つこと。境界資格条件が A-4 正本1箇所にだけ本文を持ち、
   他は参照であること。
3. **敵対性検査**: 各レビュー SKILL の sub-agent prompt に反証指示が
   含まれ、finding ゼロ報告に反証試行3件の資格条件が課されていること。
   Lean 1行変更のテストケースで math-lean-review 4本が起動する経路に
   なっていること(文言レベルで確認)。
4. **索引検査**: `lawEquation_constructs_groundedComparisonPacket` が
   索引に載り、`unported` 状態が #3102 の残 AC と一致すること。
5. **保存検査**: 廃止・改訂した SKILL の改訂前全文と新 SKILL 群を diff し、
   保存制約に挙げた規律(3波+scan 群+非破壊+保守機能+既存ゲート)が
   すべて新しい持ち場を持つこと。

## 5.5 セルフレビュー結果の反映(2026-07-07、PR #3161)

実装後、5レーン(設計対応・保存検査・相互参照・抜け道探索・リプレイ検査)の
敵対レビューを実施し、次を修正した。

- **hard fail scan の欠陥**: glob が Research 集約ルート
  `research/lean/ResearchLean.lean` を除外せず 198 行の false positive
  (ゲートが pass 不能)。除外 glob を追加し、判定を「差分が新規に
  追加したヒット = Reject / 既存ヒット = 境界違反 blocker として報告」に
  精密化(3ファイル同期)。
- **A-3 違反の残存**: prd-completion-review の親順次フォールバックと
  「原則として」を fail-closed に修正。prd-loop の「または独立した
  レビュー文脈」も撤廃。
- **判定語写像**: review-pr に「合格」の定義を明文化
  (math-lean-review は `No major findings` / 中心 claim に触れない
  `Minor issues`、他分野は `No major findings` のみ)。
- **保存検査の実喪失を復元**: equivalence chain 三分割書き分け・
  三分化タグ非回帰・ComponentUniverse 同一視禁止・多軸診断
  (docs-review / tool-review)、witness 駆動性観点(tool-review 観点2)、
  website UX 具体項目、未追跡ファイル列挙(checklist §6)、
  Lean API 品質観点(math-lean-review)。
- **抜け道の閉鎖**: タスク型宣言の不信原則(本体への新 theorem 追加は
  宣言にかかわらず Research 検索必須、疑わしきは移植に倒す — checklist §3)、
  移植 ≠ 逐語コピペ(§3-6)、台帳 status 変更の「体裁修正」carve-out 閉鎖
  (docs-review)、レーン報告原文の監査コメント添付義務(review-pr)、
  instance ペア「作れない理由」の実読検証、`not-for-porting` 書き換えの
  根拠必須化(索引)。
- 既知の残余(構造的限界として記録): レーン実行の完全捏造は文言では
  検出不能(監査コメントの原文添付+後続フルレビューの二段構えで緩和)。
  Research 索引の遡及登録完了までは §3 の下限検索が `rg` 直接検索に依存。

## 5.6 レビューゲート起動時点と修正後確認の改訂(2026-07-13)

運用実績から2つの過剰コストが確認された:
(1) 小さな修正でも正式4並列レビューが立つ、
(2) finding 修正後に全観点のフル再レビューを再実行する。
レビュー精度は十分に出ているため、敵対性の水準を保ったまま起動回数を絞る改訂を行った。

- **起動時点の一本化**: 正式レビュー(全観点・全lane)は PR 作成後のレビューゲート
  (`review-pr` 経由)として1回に限定。実装完了時点と PR ゲートの二重起動を排除。
  例外は `target-theorem-loop` の完了判定 final `$math-lean-review`(PR ゲートでは
  なく大定理の完了判定ゲート。既存設計どおり変更しない)。
- **直接対応の全分野化**: Tool / Docs / Website 限定だった「直接対応」
  (finding 限定の単一 subagent 軽量確認)を Math / Lean へ拡張。資格条件は
  「statement(signature)不変・新規 theorem / def なし・import 方向不変・
  台帳 status 不変の proof 内部または台帳・docs 記載の修正」。資格喪失時は
  従来どおり最終スナップショット再固定+4本再実行。
- **悪用防止**: 直接対応の確認 subagent は finding 解消判定に加えて、diff が
  finding 対象外の変更を含まないかを検査する。混入時は資格喪失として
  fail-closed で正式レビューへ戻す(宣言落とし均衡の排除と同型の規律)。
- 変更ファイル: `review-protocol.md`(正本)、`math-lean-review`、`prd-loop`、
  `review-pr` の各 SKILL、`AGENTS.md`。「Lean 1行でも4本」(A-3)と
  4本全承認ゲート、エスカレーション規則(2回 Needs changes → 強いゲート)は維持。

初稿への敵対レビュー(PR #3331、8アングル+独立検証)で、未変更規定との矛盾と
資格条件の抜け穴が確認され、同 PR 内で次を是正した。

- **起動時点の許可リスト化**: `review-pr` 経由に加え、完了判定ゲート
  (`target-theorem-loop` / `prd-completion-review`)と `prd-loop` エスカレーションの
  直接起動を明示的に許可(fail-closed 実行者がエスカレーション・完了レビューを
  起動拒否するデッドロックの解消)。
- **完了判定ゲートは直接対応の適用外**: 完了判定は正式再実行だけで更新する
  (単一 subagent 確認で `target-theorem-proved` を宣言できる読みの閉鎖)。
- **資格条件の一本化と拡張**: 資格/喪失の二重リストを資格条件リスト+補集合定義に
  統合し、宣言(instance / structure / example / axiom 等を含む)の追加・**削除**、
  def / instance の本体・値の変更を喪失条件に含めた(証拠削除・def 意味変更の
  抜け穴の閉鎖)。SKILL 側の条件コピーは削除しポインタ化。
- **資格検証の義務主体を確認 subagent に固定**: finding の実体解消(証拠削除による
  「解消」の不認可)、finding 対象外変更の混入、資格条件充足(Math / Lean は
  placeholder scan 込み)の3点を独立検査(親の自己分類依存の解消)。
- **合格定義との整合**: finding 全解消+有資格な修正後確認の監査記録を分野合格と
  同等に扱うことを `review-pr` の合格写像と `AGENTS.md` に明記(「4本すべての承認」
  と代用証拠パスの矛盾解消)。
- **計数とスコープ**: 直接対応確認の未解消・資格喪失を `Needs changes` として計数
  (エスカレーション/stall トリガーの到達不能化を防止)。資格喪失時の再委譲は
  喪失が生じた分野に限定(分野横断 PR での無関係分野の再レビュー排除)。

既知の残余(スコープ外として記録): `target-theorem-loop` 完了 PR では T5 final
4本と PR ゲートの4本が同一スナップショットに二重実行される(verdict 再利用条項は
既存構造の設計判断を要するため本改訂では導入しない)。

## 6. やらないこと

- Codex 本体の挙動変更(SKILL とリポジトリ artifact の範囲で完結させる)。
- 既存 PRD / 是正 Issue の文言遡及修正(#3102 の精密化コメントは現状のまま)。
- `tool-release` の改訂(今回のスコープ外)。
- レビュー SKILL の英語化・汎用化(このリポジトリ専用の規律として書く)。
