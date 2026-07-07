# PRD: Research 成果索引の全数棚卸し(backfill)

- 作成: 2026-07-07
- 対象: `docs/aat/research_evidence_index.md` の初期整備
- 実行: Codex prd-loop
- 前提: PR #3161(SKILL 監査体制再設計)がマージ済みであること。
  本 PRD の語彙(`unported (Research-proved)`、境界資格条件、タスク型)と
  レビュー体制(math-lean-review 4並列)は同 PR が導入したものを使う。

## 問い

**`Formal/AG/Research/` のどこまでが「語れる受理成果」で、どこからが足場か。**

この問いの判定規律: 全 239 ファイル・約 5,280 宣言のひとつひとつが、
「索引に登録された受理成果」「棚卸し台帳に勘定された支持補題・足場」の
**どちらかに必ず属し、件数の突合が機械的に取れる**こと。勘定されない
宣言が1つでも残る分類は、この問いに答えていない。

## 背景・現状診断

- `docs/aat/research_evidence_index.md` は器(記載契約)のみで**空**。
  空の期間、Research 下限原則(`docs/aat/guideline.md`)の検索は
  3万行級 Lean ファイルへの `rg` 直接検索に依存し、共有反証チェックリスト
  §3 の「本体への新 theorem 追加時の Research 必須検索」が人手頼みになる。
- 2026-07-07 の依存 repackage 事案(#3102、`LawEquationGeneratedPair.lean`)は、
  Research 側の到達点が検索不能であることが「参照せずに進む」「import で
  近道する」均衡の温床であることを示した。
- corpus の規模(2026-07-07 時点):

  | 塔 | ファイル | 行 | 宣言(概算) |
  | --- | --- | --- | --- |
  | `QualitySurface/` | 199 | 122,359 | 4,763 |
  | `SFT/` | 36 | 7,540 | 485 |
  | `SFTDynamics/` | 3 | 410 | 31 |
  | ルート(`Basic.lean` 等) | 1 | — | 少数 |
  | 合計 | 239 | 130,318 | ~5,280 |

  受理記録は `research/reports/`(G-aat-quality-surface-01/02/04/05/06、
  G-sft-conway-01)と `research/ideas/` の候補カードにある。
- research-loop / target-theorem-loop には受理時の索引登録義務が
  追加済み(PR #3161)だが、それは今後の受理にのみ効く。既存 corpus の
  遡及登録が本 PRD の対象である。

## 中心方針(採否規律)

1. **区分語彙は3値**: 各宣言を次のいずれかに区分する。
   - `spine`(受理成果): 受理された研究成果の中核宣言
     (theorem / 主要 def / structure)。**索引に1行ずつ登録する。**
   - `support`(支持補題): spine の証明を支えるが単独では受理成果で
     ない補題・構成。索引に登録せず、棚卸し台帳に件数と代表名で勘定する。
   - `scaffold`(足場): cycle 足場、premise 順列帯、再入口変種、
     checkpoint 帯、探索残骸。索引に登録せず、棚卸し台帳に件数と
     帯の説明で勘定する。
2. **全数勘定の機械突合**: ファイルごとに
   `spine 件数 + support 件数 + scaffold 件数 =`
   `rg -c "^(theorem|def|lemma|structure|class|inductive|abbrev|instance)\s" <file>`
   が成立すること。突合が取れないバッチは受理しない。
3. **区分の証拠階層**: 区分の一次証拠は、受理記録
   (`research/reports/` の cycle section・proof portfolio、候補カード)と
   Lean statement の実読。宣言名の字面・ファイル内の位置だけで
   区分しない。
4. **conjuncts 要旨の粒度**: 索引の `conjuncts 要旨` は、移植時の下限照合で
   **結論の数え漏れが出ない粒度**で書く(conjunction の各成分・packet の
   各 field が数えられること)。「〜のパッケージ」の一語要約は不可。
5. **移植状況の判定根拠**: 全行に判定根拠を残す。`ported` は本体側
   宣言名+conjunct 対応の確認記録が必須。`unported` が既定値。
   `not-for-porting` は理由+承認根拠が必須(索引の記載契約どおり)。
   本体側の対応検索(`rg` の検索語と結果)を PR 本文に記録する。
6. **受理記録の欠落は黙って埋めない**: spine と判定したが受理記録
   (report / 候補カード)に遡れない宣言は、`受理` 列を
   `unrecorded (backfill)` とし、**loop 台帳の欠陥 finding** として
   tracking Issue に登録する。受理記録を捏造・推定で書かない。
7. **Lean 実装・Research corpus・既存 docs を変更しない**: 本 PRD の
   成果物は索引・棚卸し台帳への追記(および tracking Issue への finding)
   のみ。区分の過程で発見した問題(足場衛生違反、statement の疑義)は
   修正せず finding として報告する。

## 改修

- **R1: 棚卸し台帳の新設** — `docs/aat/research_evidence_inventory.md`。
  1行 = 1ファイル: パス、宣言総数、spine 宣言名の列挙(索引行への対応)、
  support / scaffold の件数と帯の説明、突合結果(方針2のコマンド出力)。
  冒頭に記載契約(この節の方針1〜6の写し)を置く。
- **R2: 小塔の先行棚卸し(方式検証)** — `SFTDynamics/`(31宣言)→
  `SFT/`(485宣言)→ ルートの順に棚卸しし、索引・棚卸し台帳の書式と
  区分判定の運用を固める。方式上の問題(区分に迷う宣言のパターン等)は
  この段階で tracking Issue に記録する。
- **R3: QualitySurface 一般ファイル群** — `SemanticRepairCechGrounding.lean`
  を除く 198 ファイル(約 3,773 宣言)を、テーマ単位(ファイル名 prefix・
  GOAL 対応)でバッチ分割して棚卸しする。
- **R4: SemanticRepairCechGrounding.lean 専用バッチ** — 単体 990 宣言。
  行範囲セグメントに分割して棚卸しする。Cycle 332 の generated-pair route
  (`lawEquation_constructs_groundedComparisonPacket` ほか、#3102 の
  移植元)を含むため、この帯の spine 判定と conjuncts 要旨は特に
  丁寧に書く。
- **R5: 受理記録との突合** — 全 reports / 候補カードの受理成果が
  索引に載っていること(逆向きの検算)。載っていない受理成果、
  受理記録の無い spine(方針6)を一覧化して tracking Issue に登録する。
- **R6: 本文ラベル・本体対応の整合** — 索引の `本文ラベル` 列を
  数学本文(第X部ほか)と突合する。`ported` 判定は本体の実蒸留が
  存在する場合のみ(**import / コピペによる「移植」は ported と
  みなさない** — guideline の「移植 ≠ import」)。#3102 の generated-pair
  route は、main の是正状況にかかわらず本体の実蒸留が完了するまで
  `unported` とする。

## Implementation Plan(目安)

1周 = 1 Issue = 1 PR の prd-loop 標準。バッチ目安:
R1+R2 で 2〜3 PR、R3 はテーマ単位で 8〜12 PR、R4 は 3〜5 PR、
R5+R6 で 1〜2 PR。索引・棚卸し台帳は `docs/aat/` の台帳類であり、
**各 PR のレビューは math-lean-review(4並列・全承認)を通る**。

## Acceptance Criteria

- [ ] AC1: `docs/aat/research_evidence_inventory.md` が存在し、
  `Formal/AG/Research/` の全 .lean ファイル(239)を1行ずつ覆い、
  各行で区分件数の合計が宣言数と突合している(方針2。突合コマンドと
  結果を各バッチ PR 本文に記録)
- [ ] AC2: spine と区分された全宣言が `docs/aat/research_evidence_index.md`
  に1行ずつ登録され、全列(theorem / file / 本文ラベル / conjuncts 要旨 /
  受理 / 移植状況 / 本体対応)が埋まっている。conjuncts 要旨は方針4の
  粒度を満たす
- [ ] AC3: 全索引行に移植状況の判定根拠がある(方針5)。`ported` 行は
  本体宣言名と conjunct 対応の確認記録を持ち、`not-for-porting` 行は
  理由+承認根拠を持つ
- [ ] AC4: 受理記録に遡れない spine が `unrecorded (backfill)` として
  マークされ、tracking Issue に loop 台帳欠陥 finding として登録されている
  (方針6。0件ならその旨を R5 の PR で明記)
- [ ] AC5: `research/reports/` の全受理成果が索引から逆引きできる
  (R5 の検算。漏れは finding として登録)
- [ ] AC6: `git diff` 上、変更が `docs/aat/research_evidence_index.md`・
  `docs/aat/research_evidence_inventory.md`・tracking Issue 関連に
  限定されている(`Formal/`・`research/`・既存 docs の変更ゼロ)
- [ ] AC7: 各バッチ PR のレビュー監査コメントに、登録行のサンプル実読突合
  (最低5行、バッチが5行未満なら全行)の記録が含まれている
- [ ] AC8: `lake build` green(不変であること)、`git diff --check`、
  hidden / bidirectional Unicode scan、privacy scan が clean

## 停止規律

次の場合、該当バッチを進めずに停止して報告する(PRD は編集しない)。

- **足場衛生違反**: ファイル内で spine が行範囲でも命名でも切り出せず、
  区分判定が成立しない(research-loop の足場衛生規律の違反状態)。
  該当ファイルを `blocked` とし、衛生是正の要否をユーザー判断に回す。
- **受理記録と Lean の矛盾**: report が受理と記す宣言が Lean に存在しない、
  または statement が受理記録と食い違う。
- **区分不能**: 実読しても spine / support / scaffold のいずれとも
  判定できない宣言が残る(推定で埋めない)。

## Non-goals

- Lean 実装の変更(Research corpus のリファクタ・削除・改名を含む)
- 蒸留移植の実施(`unported` 行の解消は別タスク)
- `research/reports/`・候補カードの遡及改稿(欠落の指摘は finding まで)
- 数学本文・website への波及(本文ラベル列の突合は読み取りのみ)
- 索引の自動生成 tooling の作成(手動棚卸しが対象。tooling 化は
  棚卸し完了後に別途判断)

## 検証

```bash
# 宣言数の突合(バッチごと、対象ファイルに対して)
rg -c "^(theorem|def|lemma|structure|class|inductive|abbrev|instance)\s" <file>
# 変更範囲の確認
git diff --stat main...HEAD
# 共通
git diff --check
rg -nP "[\x{200B}-\x{200F}\x{202A}-\x{202E}\x{2066}-\x{2069}]" <changed-files>
lake build   # 不変確認
```

## 運用ノート(本 PRD の副次目的)

本 PRD は、SKILL 監査体制再設計(PR #3161)後に prd-loop で回る最初の
まとまった作業であり、**新体制の効果測定を兼ねる**(ユーザー意図)。
測定はユーザーが行う: 各バッチ PR の監査コメント(レーン別原文・
反証試行記録)、エスカレーションの発生、停止規律の発動を観察する。
この観察は本 PRD の Acceptance Criteria ではなく、ループ側が
意識・操作する対象でもない。
