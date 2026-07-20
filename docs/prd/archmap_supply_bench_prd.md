# ArchMap 供給ベンチ PRD — 再現性・精度の実測基盤(supply-bench + 参照裁定スライス)

対象は ArchMap 供給(archmap-creater SKILL による LLM 抽出)の測定基盤。
train-ticket フルビルド e2e(Issue #3545)と鍵収束実装(PR #3558)で供給の収束は
2.3倍改善したが、その実測は「単一 run 対・scratchpad 一時 artifacts・PR 本文が要約の正本」
という一回性の実験に留まっており、run-to-run 分散も抽出精度の参照も測られていない。
本 PRD は、以後の SKILL 改善をすべて実測で採否判定できる再現可能なベンチを
リポジトリに固定する。実装は Codex prd-loop、読者サブエージェントは Sonnet 固定
(軽量モデルで供給が成立することが製品条件)。

動機の外部文脈: 論文投稿時に最初に問われるのは「LLM 抽出は非決定的なのに、
その上の H¹ 計測をなぜ信用できるか」である。防御は
(1) ArchMap 以降の計測は決定論(golden corpus で固定済み)、
(2) 供給の再現性は分散付きで実測している(本ベンチ)、
(3) 主張は corpus・モデル・規約版に相対、の三段で、本 PRD は (2) を供給する。

関連(設計の正本):

- Issue #3545(フルビルド実測の一次記録)、PR #3558(鍵収束実装と再抽出実験の記録)
- `tools/archsig/skills/archmap-creater/SKILL.md` と references。特に
  `references/extraction-protocol.md` — **機械層の許可4操作
  (列挙 / hash / リテラル正規化鍵比較 / 参照解決)の正本はここ**(SKILL.md 冒頭にも同旨)。
  本 PRD はこの線を動かさない
- [責務憲章](../tool/archmap_lawpolicy_archsig_responsibility_charter.md) —
  ArchMap / LawPolicy / ArchSig の三層責務分離。本 PRD の成果物はすべて
  ArchMap 供給(観測)側にあり、ArchSig 診断側へ持ち込まない
- [reports 規律](../reports/README.md) — 正本報告の節構成、canonical JSON digest、凍結規律
- `docs/tool/golden_corpus.md` — ArchMap **以降**の決定論はここで固定済み。本 PRD は
  ArchMap **以前**(供給)の測定を担い、両者で計測パイプライン全体の信頼構図が閉じる

## 問い

**ArchMap 供給の再現性と精度は、第三者が再実行して反証できる測定として固定されているか。**

供給の安定性は「一度良い数字が出た」ことではなく「誰がいつ測り直しても同じ手順で
同じ種類の数字が出て、悪化すれば検出される」ことで初めて主張できる。判定は反例駆動で行う:

- **反例1(一回性)**: ベンチの corpus・手順・計量が fixture / 正本文書として
  リポジトリに固定されず、同じ測定を第三者が再実行できない経路が残れば fail
  (PR #3558 実験の規約 v1〜v2 系数値の現状がこれに当たる)。
- **反例2(分散不明)**: 単一 run 対の値だけで「収束率 X」と語り、独立 run 間の
  ばらつき(最小・最大・平均)が測られていなければ fail。
- **反例3(正解不在)**: 「精度」を語るのに参照裁定スライスが存在せず、
  参照に対する取りこぼし(回収率)と過剰生成が計算できなければ fail。
- **反例4(指標漂流)**: 指標の定義が PRD・PR 本文・scratchpad に散在し、
  現行 source of truth に正本がなければ fail。
- **反例5(主張の越境)**: ベンチ結果を、測定した corpus・読者モデル・規約版・
  調停者の記録を超えて一般化して語る文面が成果物に入れば fail。
- **反例6(既知への過適合)**: 規約のチューニングに使った chunks や、prompt-pack が
  リテラル例として埋め込んでいるサービスの上で**だけ**測り、prompt-literal-disjoint
  (規約例のリテラルに現れないコード)での値と区別しない報告が残れば fail。
- **反例7(手抜きの良化)**: 調停を部分的にしか行わない入力から裁定値系指標が
  無言で計算され、しかも手抜きが指標を良化させる方向に働く経路が残れば fail。

**(採用条件)** 上記反例を消す変更 — 指標正本の新設、corpus / 参照裁定スライスの
fixture 化、決定論的計量ツールと調停完全性検査、分散付き初回実測とその docs/reports 報告。
**(却下条件)** 機械層への意味比較・similarity merge・多数決の導入
(extraction-protocol.md の許可4操作の外)、**matchRate の合否化(文脈を問わず。
matchRate は記録であり合否ではない — SKILL 改善の採否判定に使ってよいのは
鍵収束率・参照回収率・過剰生成率などの裁定値系ベンチ指標だけ)**、
ベンチスコアを上げるためだけの alias 破壊的 object 正規化や corpus 特化規約の追加
(Goodhart。異なる観測は別鍵のまま、規約は corpus 非依存の収束点として書く)、
収束規約それ自体の第2波改善(ベンチ完成後の後続 PRD で実測駆動により行う)、
ベンチの LLM 実行を CI 常時実行にする変更(決定論部分のみ cargo test へ)。

## 実測ベースライン(PR #3558 再抽出実験、読者 Sonnet、単一 run 対)

| 条件 | 機械 matchRate | 鍵収束率 |
| --- | --- | --- |
| 規約なし | 0.149(atom-match-key@1) | 0.321 |
| 規約 v2(現行 prompt-pack) | 0.477(atom-match-key@2。@1 併記値も 0.477 — v2 規約は subject を正規形で直接書くため両鍵が一致) | 0.743 |
| kind\|subject\|axis レベル一致(規約 v2) | — | 0.816 |

出典注記: 本表の数値は PR #3558 本文由来。規約なし行はコミット済み fixture
(`tools/archsig/tests/fixtures/key_convergence/`)+フルビルド証拠束から第三者が
再計算可能であることを確認済み。規約 v2 行の一次 artifacts は scratchpad 一時領域に
しかなく、リポジトリ内からは再計算できない — 反例1 の実例であり、本ベンチが
この再計算経路を全条件に拡げる。なお当時の鍵収束率は merged 107 行を 53 対と数えた値で、
対の数え方は当時の裁定記録の読みに依存していた(R1 / R3 で機械化する)。

既知の不足要因(PR #3558 の系統分解): 語彙レンズの判断残余
(handlesCommand / servesQuery、calls / dependsOn)、粒度逸脱の合併残、単純誤り。
これらの改善は本 PRD のスコープ外だが、改善の採否を判定する物差しを本 PRD が作る。
上記数値は単一 run 対・チューニングセット上の値であり、分散も prompt-literal-disjoint 値も未知 —
これがベースラインの最大の弱点である。

## 要求

### R1: 供給ベンチ仕様の正本(docs/tool 新設)

`docs/tool/archmap_supply_bench.md` を新設し、次を恒久仕様として固定する。
以下の定義は正本が立つまでの**草案**であり、正本の merge をもって本 PRD の定義記述は
参照に切り替わる(PRD guideline: 恒久規律の正本は PRD の外。実装の最初の段で正本を
land すること):

- **指標定義**:
  - 機械 matchRate(@1 / @2 併記。記録であり合否ではない)
  - 鍵収束率 = matched / (matched + 調停で同一事実と裁定された merge グループ数)。
    adopted(片パスのみの真の相補観測)は分母に入れない。
    **merge グループは R3 の調停記録拡張で機械可読に記録されたものだけを数える**
    (行数からの推定・除算はしない)
  - 参照回収率 = 参照裁定スライスの atom のうち、新規供給が回収した割合
    (機械照合による下限値と、調停込みの裁定値を区別して併記)。
    **参照は既存 dual-pass candidate union の裁定に由来し、両 pass がともに
    見落とした事実を含まない。この指標は凍結 candidate union に対する回収率であり、
    source に存在する事実全体への再現率(source-level recall)を主張しない**
  - 過剰生成率 = 新規供給の atom のうち、参照に対応がなく調停で not-adopted と
    裁定された割合(参照にない**正しい**新発見は過剰に数えず、参照の改訂候補として記録)。
    参照回収率・過剰生成率は R3 の reference-alignment artifact からのみ計算する
  - run-to-run 分散 = 独立 run 対ごとの上記指標の最小・最大・平均。
    **「独立 N run 対」は 2N 本の独立 run から作る N 個の非交差ペア**(run の共有なし)
  - 供給コスト(分/kLOC。記録)
- **反証可能性の成立範囲**: 機械指標(matchRate・機械照合下限値)は入力 artifacts から
  バイト決定論で再計算可能。裁定値系指標(鍵収束率・参照回収率の裁定値・過剰生成率)は
  **記録された調停の関数**であり、調停記録込みで第三者が計算を再検証できるが、
  調停そのものの再現は主張しない。この区別を正本に明記する
- **実行プロトコルと比較系列 key**: 測定の同一比較系列は次の key の完全一致で定義し、
  いずれかが変われば新系列(直接比較不可)とする: corpus 版 / 参照版 /
  読者モデルの immutable snapshot(provider・version)/ inference 設定 /
  prompt・SKILL references 一式の bundle hash / 計量ハーネスの commit /
  調停 protocol 版 / 調停者(モデル id / 人間)。
  独立 run 対数は既定 3(= 6 独立 run)。**pairing は run 開始前に登録**し、
  既定は runOrdinal 昇順の非交差ペア((1,2)(3,4)(5,6))— 結果を見てからの
  組合せ選択を禁じる。「独立 run」は fresh session で他 run の packets・調停・
  出力を一切参照しないことと定義する(cache 共有の扱いも正本で規定する)。
  規約改善の採否比較では規約版以外の key を固定し、baseline / candidate を
  同時期に interleave 実行し、調停には条件名を blind 化して渡す。
  報告の置き場所と節構成は reports 規律準拠
- **出力 artifact schema**: R3 計量ツールの出力 JSON(指標表)の schema を
  この正本のスコープに含める(docs/tool のコマンド別 contract 文書の先例に倣う)
- **判定規則の所在**: ベンチは指標の記録を出すだけで、閾値・許容帯・採否の判定規則は
  持たない。判定規則は各改善 PRD の受け入れ条件側が、このベンチの指標を参照して定める
- **claim boundary**: 測定値は比較系列 key(corpus・参照・読者モデル・規約版・
  調停者ほか上記)に相対する記録であり、他言語・他規模・他モデルへの一般化を
  主張しない。分散は記述統計(最小・最大・平均)であり分布・有意性の主張はしない。
  参照回収率は「その参照が体現する規約系統の下での」相対値であり、規約系統が
  共有する盲点と、両 pass がともに見落とした事実は検出できない(この盲点への
  防御は prompt-literal-disjoint チャンクと反例駆動レビューが担い、source-level の
  正解主張はしない)

### R2: ベンチ corpus fixture

- train-ticket(commit `313886e99bef`)から**4 chunks 以上**を固定する:
  - PR #3558 実験で使った chunk-04(実体は ts-auth-service / ts-basic-service /
    ts-cancel-service / ts-common。application.yml 2本を含む — 構成は
    フルビルド証拠束の chunks.json を正とする)と chunk-13(notification / order /
    order-other 系)。これらは**規約チューニングに使った tuned チャンク**として明示する
  - **prompt-literal-disjoint チャンクを1つ以上**: prompt-pack のリテラル例に
    一切現れないサービスだけで構成する。交差検査は prompt-pack の**全リテラル種別**
    (サービス名・クラス名・route・object 鋳型の例示値)を対象に機械的に行い、
    交差ゼロの記録と選定規則を**スコア観測前に** fixture へ固定する。
    この区分が主張するのは prompt リテラルからの分離だけであり、
    **規約開発からの独立(真の held-out)は主張しない** — 現行 v2 規約自体が
    train-ticket フルビルド所見から作られているため。真の held-out は規約設計に
    使っていない別 repo / 別 revision の事前登録によってのみ主張でき、
    他 repo corpus 拡張(Non-Goals)の系列に属する
- scope-manifest を fixture 化し、対象ソースの sha256 を固定する。train-ticket 本体は
  vendoring しないが、**上流消滅に備え git bundle(当該 commit を含む)を証拠束に
  含める**。取得は「上流 checkout → hash 検証、不能時は bundle から復元」の二経路とする
- corpus の版管理規約(corpus を変えたら指標は比較不能、新系列として記録)を R1 正本に置く

### R3: 決定論的計量ツールと調停記録の拡張(archsig 機械層)

- **調停記録 schema の拡張(版上げ)**: 現行の調停記録(key / decision / basis)に
  **merge グループ構造**(同一事実と裁定された key 群を束ねるグループ id)を追加する。
  鍵収束率の分母はこのグループ数から一意に計算する。既存 artifacts(旧版)は
  グループ構造なしとして読み、鍵収束率を「計算不能」と報告する(遡及推定しない)。
  **グループ整合条件**を schema と検査で固定する: 各 merged 行はちょうど1つの
  group に所属し、各 group は Pass A / Pass B の member を最低1件ずつ含み、
  全 member は同一の統合先 atom(canonicalAtomId)を指す。adopted / not-adopted は
  group に所属しない。member の重複・存在しない key への参照・相互矛盾は
  fail-closed(グループ id の付け方で分母を縮める操作を機械的に塞ぐ)
- **reference-alignment artifact(版付き)**: 新規供給と参照裁定スライスの対応を
  機械可読に記録する versioned artifact を新設する。最低限、referenceAtomId /
  対応する candidate atom 群 / 裁定種別(参照一致・正しい新発見=参照改訂候補・
  not-adopted)/ basis / 裁定者を持つ。**完全性**(参照側全 atom と candidate 側
  全 atom が alignment に現れる — 未回収 reference atom も明示行として残る)と
  **一意性**(candidate の多重対応・member 重複の禁止)を fail-closed で検査する。
  参照回収率・過剰生成率はこの artifact からのみ計算する
- **計量コマンド**: 複数 run 対の candidate packets + 拡張調停記録から R1 の指標表を
  決定論的に計算し JSON 出力する(`archsig supply-bench` を仮称とする)
- **調停完全性検査**: extraction-diff の unmatched 全エントリ(onlyInPassA /
  onlyInPassB の全 atom)に裁定が存在することを検査し、**1件でも未裁定があれば
  裁定値系指標を「計算不能」として packet id・key 付きの明示エラー**にする
  (部分調停が指標を良化させる経路を機械的に塞ぐ。反例7 対応)。
  調停記録が全欠の場合も同様に明示エラー(暗黙の 0 や省略で流さない)
- **許可操作の線**: 実装に先立ち、extraction-protocol.md の機械層規定に
  「鍵比較結果の算術集計(計数・比率)は許可4操作の帰結として機械層に含まれる」旨を
  明記する(正本を先に更新してから実装する。意味比較・裁定の自動化・多数決は
  引き続き導入しない)
- **決定論**: 同一入力に対する出力はバイト決定論。「同一入力」の定義に入力の正準順
  (ファイル引数順に依存しない runId / packet id ソート)を含め、R1 正本に明記する

### R4: 参照裁定スライス(reference adjudicated slice fixture)

- **identity(肯定形)**: 参照裁定スライスは「フルビルドの全件調停(2,819 件・
  全件ソース再読)+独立の再読レビュー1回+人間の受理を経た裁定記録の凍結」である。
  精度指標はこの参照に相対する。参照は既存 dual-pass candidate union の裁定から
  作られ、両 pass がともに見落とした事実の語彙を持たない(source-first の独立
  annotation は行わない — Non-Goals)。新規供給との対応は R3 の reference-alignment
  artifact で記録する
- フルビルド調停済み ArchMap から R2 の対象 chunk(tuned・prompt-literal-disjoint の両方)に相当する
  atom 群を抽出し、**凍結時に現行規約版の鍵正規形(@2)へ再キー**した上で、
  参照が従う規約版を fixture メタデータに記録する(フルビルド原本は鍵収束規約以前の
  産物であるため、機械照合下限値が規約版ドリフト分だけ歪むのを防ぐ)
- **版管理**: 参照の改訂(新発見の採用・誤りの訂正)は裁定記録付きで行い、
  **参照の版が変わったら精度指標は新系列**とする(corpus と同じ比較不能規則。
  旧系列の値は凍結された報告に残り、遡及改稿しない)
- サニタイズの上 tests/fixtures へ。改訂手続の正本は R1 に置く

### R5: 実行・記録規律(reports 直結)

- ベンチ run は per-run で次を記録する: runId、scope-manifest digest、
  SKILL references の git blob hash、読者モデル id、**調停者(モデル id / 人間)**、
  実行日、chunk 範囲(tuned / prompt-literal-disjoint の別)、raw packets と拡張調停記録
  (canonical JSON digest 付き)
- 報告は `docs/reports/archmap_supply_bench/` に reports 規律の節構成で置き、
  証拠束から数値を機械的に突き合わせられる状態にする
- LLM 実行(抽出・調停)はベンチ run 時のみ。CI に入れるのは R3 の決定論計算と
  fixture 整合検査だけ

### R6: 初回実測(現行規約 v2 のベースライン凍結)

R1–R5 が揃った状態で、現行 SKILL(規約 v2)に対する初回ベンチを実施する:

- **独立 3 run 対以上(6 独立 run 以上)**、読者 Sonnet、R2 corpus 全 chunks
- 鍵収束率・参照回収率・過剰生成率・分散・コストを計測し、
  **tuned チャンクと prompt-literal-disjoint チャンクの値を分離して**
  `docs/reports/archmap_supply_bench/` に第1報として凍結する
- この数値は**記録であり本 PRD の合否ではない**(値が低くても本 PRD は fail しない。
  値を上げるのは後続の規約改善 PRD の仕事であり、その採否判定にこのベンチを使う)

## 受け入れ条件

1. **決定論**: R3 計量ツールが、fixture 化した packets + 拡張調停記録から同一の指標表を
   入力順によらず再実行で出力することを cargo test で固定。既存 fixture・golden corpus の
   回帰ゼロ
2. **初回実測の成立**: 独立 3 run 対以上の実測が完了し、全指標が分散付き・
   tuned / prompt-literal-disjoint 分離で `docs/reports/archmap_supply_bench/` に第1報として
   凍結されている。証拠束は R1 の比較系列 key 全要素(inputDigests / runId /
   読者モデル snapshot / inference 設定 / prompt・SKILL bundle hash / ハーネス commit /
   調停 protocol 版 / 調停者)と run 開始前の pairing 登録記録を完備し、
   README の再現手順から第三者が同じ測定を再実行できる。corpus の git bundle が
   証拠束に含まれる
3. **参照裁定スライスの成立**: R4 参照が独立再読レビューと人間受理を経て
   @2 再キー・規約版メタデータ付きで fixture 化され、初回実測で参照回収率・
   過剰生成率が reference-alignment artifact から実際に計算されている。
   prompt-literal-disjoint チャンクの全リテラル種別交差ゼロ記録と、スコア観測前に
   固定された選定規則が
   fixture に存在する
4. **負系テスト**: (a) 調停記録なしの入力で裁定値系指標が明示エラーになる。
   (b) **部分調停(未裁定 unmatched が1件でも残る入力)で裁定値系指標が
   packet id・key 付きの明示エラーになる**。(c) 旧版調停記録(merge グループなし)で
   鍵収束率が「計算不能」と報告される。(d) 必須フィールド欠落 packet の fail-closed
   (既存挙動)がベンチ経路でも保たれる。(e) **merge グループ整合条件違反**
   (group 非所属の merged 行、片 pass のみの group、canonicalAtomId 不一致、
   adopted の group 所属、member 重複・未知 key 参照)が fail-closed する。
   (f) **reference-alignment の完全性・一意性違反**(alignment に現れない
   reference atom / candidate atom、candidate の多重対応)が fail-closed する
5. **境界の不変**: 機械層の許可操作が extraction-protocol.md の規定
   (4操作+その帰結としての算術集計。R3 で正本に明記)を超えていないことを
   同文書と突き合わせて明記。「unmatched は調停の再読キューであり、matchRate は
   記録であり合否ではない」の原則が SKILL / references / 新正本の文面で保たれ、
   ベンチ指標が **golden corpus が固定する全診断 artifact**(measurement packet /
   gate / comparison / summary / insight / viewer / manifest)に一切現れない
6. **claim boundary**: R1 正本と第1報の両方に、測定は比較系列 key に相対する
   記録である旨、分散は記述統計である旨、参照回収率は凍結 candidate union に対する
   回収率であって source-level recall ではない旨、規約系統が共有する盲点を検出
   できない旨、prompt-literal-disjoint は規約開発からの独立を主張しない旨が明記され、
   一般化主張が成果物に含まれない

## Non-Goals

- 収束規約の第2波改善(語彙レンズ・粒度逸脱の低減)。ベンチ完成後に実測駆動の
  後続 PRD として切り出す。**その採否の閾値・許容帯の制定も後続 PRD の仕事**
  (本ベンチは記録を出す道具に徹する)
- PR #3558 で差し戻しとなった供給収束ゲート(0.8)の再裁定。それはユーザー判断であり、
  本ベンチはその判断材料(分散付き実測)を供給する。この依存関係は本 PRD の
  tracking Issue に dependency として登録して管理する
- 統計的検定・信頼区間の導入(n=3 の記述統計に検定の装いを与えない)
- 調停そのものの自動化・調停一致率の測定(調停者プロベナンスの記録までを本 PRD が担い、
  調停の再現性測定は将来の別論点)
- source-first の独立 annotation(candidate packets を見ない source 直読の参照作成)
  による source-level recall の測定。参照は candidate union 由来に限定し、
  その限定は claim boundary で明示する
- compare workflow・incremental-dual の拡張、sectionValue のセクション別比較化
- 他言語・他 repo corpus の追加(R1 正本に拡張点として版管理規約を書くに留める)。
  **真の held-out(規約設計に使っていない別 repo / 別 revision の事前登録)は
  この拡張系列で扱う**
- 読者モデルの固定・最適化(モデル id は記録するが、規約はモデル非依存の収束点として書く)
- ベンチ LLM 実行の CI 常時化・自動スケジュール化
