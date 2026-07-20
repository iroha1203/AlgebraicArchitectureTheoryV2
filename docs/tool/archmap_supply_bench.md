# ArchMap supply bench guide

`archsig supply-bench` は、ArchMap 供給(archmap-creater SKILL による LLM 抽出)の
再現性・精度指標を、candidate packets・拡張調停記録・reference-alignment から
決定論的に計算して JSON 出力する。本文書はベンチの指標定義・比較系列 key・
実行プロトコル・artifact schema・版管理規約の正本である。

ベンチは記録を出す道具であり、閾値・許容帯・採否の判定規則を持たない。
判定規則は各改善 PRD の受け入れ条件側が、このベンチの指標を参照して定める。

機械層の許可操作は
`tools/archsig/skills/archmap-creater/references/extraction-protocol.md` の
4操作(列挙 / hash / リテラル正規化鍵比較 / 参照解決)とその帰結としての
算術集計に限る。ベンチは意味比較・裁定の自動化・多数決を行わない。

## 指標定義

- **機械 matchRate**: `extraction-diff` が計算する atom-match-key@1 / @2 の
  機械一致率。@1 / @2 を併記する。記録であり合否ではない。
- **鍵収束率** = `matched / (matched + 調停で同一事実と裁定された merge グループ数)`。
  merge グループは拡張調停記録(下記)に機械可読に記録されたものだけを数える。
  行数からの推定・除算はしない。`adopted`(片パスのみの真の相補観測)は
  分母に入れない。
- **参照回収率** = 参照裁定スライスの atom のうち、新規供給が回収した割合。
  機械照合による下限値(@2 鍵の完全一致)と、調停込みの裁定値
  (reference-alignment の `reference-matched` 行)を区別して併記する。
  参照は既存 dual-pass candidate union の裁定に由来し、両 pass がともに
  見落とした事実を含まない。この指標は凍結 candidate union に対する回収率であり、
  source に存在する事実全体への再現率(source-level recall)を主張しない。
- **過剰生成率** = 新規供給の atom のうち、参照に対応がなく調停で
  `not-adopted` と裁定された割合。参照にない正しい新発見は過剰に数えず、
  `novel-correct`(参照改訂候補)として記録する。
  参照回収率・過剰生成率は reference-alignment artifact からのみ計算する。
- **run-to-run 分散** = 独立 run 対ごとの上記指標の最小・最大・平均。
  記述統計であり、分布・有意性の主張はしない。
- **供給コスト**(分/kLOC): 記録。

### 反証可能性の成立範囲

機械指標(matchRate・参照回収率の機械下限値)は入力 artifacts からバイト決定論で
再計算可能である。裁定値系指標(鍵収束率・参照回収率の裁定値・過剰生成率)は
記録された調停の関数であり、調停記録込みで第三者が計算を再検証できるが、
調停そのものの再現は主張しない。

## 比較系列 key

測定の同一比較系列は次の key の完全一致で定義する。いずれかが変われば新系列で
あり、系列間の値は直接比較不可として扱う。

1. corpus 版
2. 参照裁定スライス版
3. 読者モデルの immutable snapshot(provider・version)
4. inference 設定
5. prompt・SKILL references 一式の bundle hash
6. 計量ハーネス(archsig)の commit
7. 調停 protocol 版
8. 調停者(モデル id / 人間)

旧系列の値は凍結された報告に残り、遡及改稿しない。

## 実行プロトコル

- **独立 run**: fresh session で実行し、他 run の packets・調停・出力を
  一切参照しない。読者への prompt cache の共有は可(入力 prompt は全 run 同一の
  ため)だが、run の成果物・中間物の共有は不可。
- **pairing**: 独立 N run 対は 2N 本の独立 run から作る N 個の非交差ペア。
  pairing は run 開始前に登録し、既定は runOrdinal 昇順の非交差ペア
  ((1,2)(3,4)(5,6))。結果を見てからの組合せ選択を禁じる。既定 N=3。
- **per-run 記録**: runId、scope-manifest digest、SKILL references の
  git blob hash、読者モデル id、調停者、実行日、chunk 範囲
  (tuned / prompt-literal-disjoint の別)、raw packets と拡張調停記録
  (canonical JSON digest 付き)。
- **規約改善の採否比較**: 規約版以外の比較系列 key を固定し、baseline /
  candidate を同時期に interleave 実行する。調停には条件名を blind 化して渡す。
- **報告**: `docs/reports/archmap_supply_bench/` に reports 規律
  (`docs/reports/README.md`)の節構成で置く。LLM 実行(抽出・調停)は
  ベンチ run 時のみで、CI には決定論計算と fixture 整合検査だけを入れる。

## Artifacts

### 拡張調停記録(merge グループ)

`archmap-extraction-consistency` の `adjudications` は従来の
`key / decision / basis` に加え、group-structured 記録では全行が
`candidateAtomId`(裁定対象の candidate atom)を持ち、`merged` 裁定はさらに
`mergeGroup`(同一事実と裁定された atom 群を束ねるグループ id)と
`canonicalAtomId`(統合先 atom)を持つ。

整合条件(fail-closed):

- group-structured 記録の全行は `candidateAtomId` で onlyIn の atom を一意に指す。
  未知 atom への参照、同一 atom への複数行は受理しない。
- 各 `merged` 行はちょうど1つの group に所属する。
- 各 group は Pass A / Pass B の member を最低1件ずつ含む。
- 同一 group の全 member は同一の `canonicalAtomId` を指す。
- `adopted` / `not-adopted` は group に所属しない。
- member の重複、存在しない key への参照、相互矛盾は受理しない。

グループ構造を持たない旧版の調停記録に対しては、鍵収束率を「計算不能」として
明示報告する。遡及推定はしない。

### reference-alignment(`archmap-reference-alignment/v1`)

新規供給と参照裁定スライスの対応を機械可読に記録する。行の必須フィールド:

- `referenceAtomId`(未回収の場合も明示行として残す)または candidate 側のみの行
- 対応する candidate atom 群(run / packet / atom id)
- 裁定種別: `reference-matched` / `novel-correct`(参照改訂候補)/ `not-adopted`
- `basis`(裁定根拠の要約)
- `adjudicator`(モデル id / 人間)

整合条件(fail-closed): 参照側全 atom と candidate 側全 atom が alignment に
現れる(完全性)。candidate の多重対応・member 重複は受理しない(一意性)。

### 計量出力(`archmap-supply-bench-report/v1`)

`archsig supply-bench` の出力 JSON。比較系列 key の記録、run 対ごとの指標、
分散(最小・最大・平均)、tuned / prompt-literal-disjoint 別の内訳を持つ。
同一入力に対する出力はバイト決定論であり、入力は runId / packet id の正準順で
処理される(ファイル引数順に依存しない)。

調停完全性検査: unmatched 全エントリ(onlyInPassA / onlyInPassB の全 atom)に
裁定が存在しない入力、および調停記録が全欠の入力に対しては、裁定値系指標を
「計算不能」として packet id・key 付きの明示エラーにする。暗黙の 0 や省略で
流さない。

## corpus と参照の版管理

- **corpus**: corpus(chunk 構成・scope-manifest・対象 revision)を変えたら
  指標は比較不能であり、新系列として記録する。上流消滅に備え、対象 commit を
  含む git bundle を証拠束に含める。取得は「上流 checkout → hash 検証、
  不能時は bundle から復元」の二経路とする。
- **prompt-literal-disjoint チャンク**: prompt-pack の全リテラル種別
  (サービス名・クラス名・route・object 鋳型の例示値)との交差ゼロを機械検査し、
  交差ゼロの記録と選定規則をスコア観測前に fixture へ固定する。この区分が
  主張するのは prompt リテラルからの分離だけであり、規約開発からの独立
  (真の held-out)は主張しない。
- **参照裁定スライス**: 参照の改訂(新発見の採用・誤りの訂正)は
  reference-alignment の裁定記録付きで行い、参照の版が変わったら精度指標は
  新系列とする。参照は凍結時に現行規約版の鍵正規形(@2)へ再キーし、
  従う規約版を fixture メタデータに記録する。

## Claim boundary

測定値は比較系列 key に相対する記録であり、他言語・他規模・他モデルへの
一般化を主張しない。参照回収率は「その参照が体現する規約系統の下での」
相対値であり、規約系統が共有する盲点と、両 pass がともに見落とした事実は
検出できない。ベンチ指標は SKILL 改善の工学記録であり、ArchSig の診断語彙・
分析結論(golden corpus が固定する全診断 artifact)には現れない。
