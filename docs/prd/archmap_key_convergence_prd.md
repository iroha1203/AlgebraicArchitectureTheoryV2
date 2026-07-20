# ArchMap 鍵収束 PRD — 独立供給の再現性(archmap-creater 規約 + atom-match-key@2)

対象は archmap-creater SKILL(prompt-pack / references)と archsig authoring 機械層
(candidate-packet 検査・extraction-diff)。train-ticket フルビルド e2e(Issue #3545、
2026-07-18)の体験所見筆頭「subject 命名ドリフトが不一致の約9割」を起点に、
ArchMap 供給の再現性を工学ゲートとして固定する。実装は Codex prd-loop、
作業サブエージェントの既定は Sonnet(軽量モデルで供給が成立することが製品条件)。

関連(設計の正本):

- Issue #3545 コメント(フルビルド実測と所見7件の一次記録)
- `tools/archsig/skills/archmap-creater/SKILL.md` と references(prompt-pack /
  vocabulary-catalog / extraction-protocol / coverage-and-consistency)
- [責務憲章](../tool/archmap_lawpolicy_archsig_responsibility_charter.md) — 機械層の許可4操作
  (列挙 / hash / リテラル正規化鍵比較 / 参照解決)。本 PRD はこの線を動かさない
- 前例: #3505(prompt-pack への軸既定表 = 収束規約の第1波。本 PRD は同型の第2波)

## 問い

**同じコードへの独立供給は、同じ ArchMap 鍵に収束するか。**

ここが解決できれば ArchMap 供給は工学として成り立つ。`compare`(ドリフト検出)、
`incremental-dual` の baseline、「AI が地図を保守し人間が地図をレビューする」
レビュースタックは、いずれも再生成した地図の鍵が安定していることを前提にしており、
鍵が毎回変わる供給はこれら全てを偽差分で埋める。判定は反例駆動で行う:

- **反例1(命名非収束)**: 同一クラスの同一事実を観測した2独立パスの atom が、
  subject 表記(FQCN / 短縮形 / service-dir 形式)だけの理由で別鍵になる経路が残れば fail。
- **反例2(自由文 object)**: catalog に既定形のある定型観測(HTTP endpoint、
  response envelope、コード表、金額表現、authority 規則)の object が自由散文のままで、
  同一事実が言い回しだけで別鍵になる経路が残れば fail。
- **反例3(粒度未規定)**: per-verb か束ねか、interface か impl か、repository 集約か
  per-method かの選択が読者ごとに分かれ、同一事実が粒度だけで別鍵になる経路が残れば fail。
- **反例4(欠落の無言通過)**: 必須フィールド(kind / subject / axis / refs)を欠く
  candidate atom が無言で下流に流れる、または下流エラーがどのパケットかを言わない挙動が
  残れば fail。挙動は packet id・atom id を明示する fail-closed に限る
  (#3545 では axis 77 件・kind 204 件を integrator が暫定補完した。恒久機構にはしない)。

**(採用条件)** 一次指標は **鍵収束率 = mechanically matched / (matched + 調停で
merged と裁定された同一事実対)**。上記反例を消し、鍵収束率を受け入れ条件の数値まで
上げる変更、およびそれを負系テスト・fixture で固定する変更。
**(却下条件)** 意味読解の逐語一致の強制(観測の語りは自由でよい、鍵だけが収束する)、
unmatched をエラー扱いする変更(unmatched は調停の再読キューであり続ける。
matchRate は記録であり合否ではない — 鍵収束率は本 PRD の受け入れ指標としてのみ使う)、
機械層への意味比較・similarity merge・多数決の導入(責務憲章違反)、
alias preservation を壊す object 正規化(異なる観測は別鍵のまま)、
sectionValue の set 一括比較の変更(別論点として切り出す)。

## 実測ベースライン(#3545 フルビルド、全読者 Sonnet)

| 指標 | 値 |
| --- | --- |
| atom-match-key@1 matchRate | **0.094**(matched 294 / onlyInPassA 1,410 / onlyInPassB 1,409) |
| 調停 ground truth | merged 1,903 行(≈951 同一事実対)/ adopted 887(真の相補観測)/ not-adopted 29 |
| 鍵収束率(現状) | 294 / (294 + 951) ≈ **0.24** |
| subject 機械正規化のみ適用(シミュレーション) | matchRate **0.194**(2.1倍) |
| subject 正規化 + object 除外(上限参考値) | matchRate 0.489 |

含意: (1) 内容は再現している(not-adopted 29/2,819)のに表現が再現していない。
(2) subject 正規化だけで機械一致は2倍になるが収束には足りず、object 記法と粒度が次の壁。
(3) matchRate には天井がある — adopted 887 は片パスだけが気づいた真の相補観測で、
これは dual-pass 設計が拾うべきものであり、収束目標の分母に入れない。
鍵収束率を指標にするのはこのため。

## 要求

### R1: subject 正規形(prompt-pack 規約)

`<service-dir>.<ClassName>`(例 `ts-cancel-service.CancelServiceImpl`、共有モジュールは
`ts-common.OrderStatus`)。設定ファイルは `<service-dir>.application-yml`。
Java パッケージ経路は subject に入れない。prompt-pack に規約1行+正誤例を追記する。

### R2: 既定粒度表(prompt-pack 規約)

#3545 で系統的に分かれた選択それぞれに既定を与える(収束点であって強制ではない。
既定から外れる読みは従来どおり emit してよく、調停で裁かれる):

- HTTP endpoint capability: **per-endpoint(verb + path)**。複数 verb の束ねは既定外
- cross-service call effect: **per-provider**。「A or B」束ねは既定外
- capability の subject: **impl クラス**(挙動証拠)。interface 宣言は contract として別 atom
- repository: **`state:persistsIn` の集約1 atom** を既定。メソッドに挙動差の証拠が
  あるときのみ per-method を追加
- 二値 envelope 意味論(status 0/1 等): **1 atom に両分岐を1 object で**記述

### R3: 定型 object 記法(references 追記)

定型観測の object テンプレートを vocabulary-catalog(または新 reference)に定義する:
endpoint route(`GET /api/v1/...`)、response envelope(branch-descriptive の既定文形)、
status code 表(`int-codes-0-notpaid-1-paid-...` 形式)、金額表現
(`string-passthrough-unparsed` 等 #3545 で使った正準ラベル群を収載)、
authority(permitsAll / requiresRole の対象パス記法)。
非定型観測の object は従来どおり自由(語りの自由と鍵の収束を分離する)。

### R4: atom-match-key@2(archsig 機械層)

鍵計算を `kind | NFC(trim(subject_normalized)) | axis | predicate? | object?` に更新する。
`subject_normalized` は refs から決定論的に導出した service-dir による R1 正規形への
文字列写像(意味比較なし。責務憲章の「リテラル正規化鍵比較」の範囲内)。
extraction-diff は @1 / @2 両鍵の matched 数を併記し、移行検証を可能にする。

### R5: candidate-packet fail-closed 強化(archsig 機械層)

必須フィールド(kind / subject / axis / refs、semantic は object も)欠落を
packet 受領時(extraction-diff / archmap 監査の入口)に検出し、
**packet id と atom id を含むエラー**で fail-closed する。既定表による自動補完はしない。

### R6: 再現性 fixture と鍵収束率の実測

- #3545 フルビルドの 44 candidate packets + extraction-consistency(調停 2,819 件)を
  検証データとして fixture 化し、@2 適用時 matchRate ≥ 0.19 を回帰ロックする
  (機械正規化のみの下限。実データはサニタイズの上 tests/fixtures へ)
- R1-R3 規約適用後の **小規模再抽出実験**(train-ticket の同一 2 chunks × 独立2パス、
  読者 Sonnet)を行い、鍵収束率を実測・記録する

## 受け入れ条件

1. **鍵収束率 ≥ 0.8**(R6 再抽出実験、新規約 + @2、使用モデルと chunk 範囲を記録)。
   これが本 PRD のゲート。届かない場合は不足要因の系統分解を記録して差し戻す
2. fullbuild 実データ fixture で @2 matchRate ≥ 0.19、@1/@2 併記レポート出力、
   既存 fixture・golden corpus の回帰ゼロ
3. 負系テスト: axis / kind 欠落パケットが packet id・atom id 付きで fail-closed する
4. SKILL references 更新(R1-R3)。機械層の許可4操作が増えていないことを
   責務憲章と突き合わせて明記
5. 「unmatched は調停の再読キューであり、matchRate は記録であり合否ではない」の
   原則が SKILL / references の文面で不変であること

## Non-Goals

- 意味読解の逐語再現(notes・basis の語り口の同一性)
- sectionValue の set 一括比較のセクション別比較化(#3545 所見5。別 PRD で扱う)
- compare workflow 本体・incremental-dual の拡張(鍵収束はその前提整備)
- 読者モデルの固定(規約はモデル非依存の収束点として書く)
