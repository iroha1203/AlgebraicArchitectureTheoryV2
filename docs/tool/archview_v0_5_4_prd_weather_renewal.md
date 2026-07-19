# ArchView v0.5.4 PRD — 気象図リニューアル(typed view model + 新 viewer + 時間軸)

- 状態: 起草(2026-07-20)
- 対象 Issue: #3630(PRD 固定)。実装 tracking は PRD 受理後に別 Issue を切る
- 実装: Codex prd-loop。1 PR = 1 実装 Issue
- スコープ裁定: **フルスコープ一括**(2026-07-20 ユーザー決定)。
  Wave 1(ArchSig typed view model)+ Wave 2(新 viewer)+ Wave 3(時間軸)を本 PRD で扱う
- 関連文書(現行 source of truth):
  - [ArchView 気象図リニューアル 設計思想ノート](../note/archview_semantic_weather_map_design.md) — 本 PRD の正本。
    識別・視覚言語・fidelity・沈黙・時間軸の規律はすべて同ノートを正とする
  - [ArchView gluing geometry contract](archview_gluing_geometry_contract.md) — 現行 viewer 忠実性契約。
    本波で気象図 lens の恒久契約として全面改訂する(§R8)
  - [train-ticket ドッグフーディング正本レポート](../reports/train_ticket_dogfooding/) — 受け入れ材料の実測データ源

---

## 問い

**AAT の語彙を知らないエンジニアが、ArchSig の実測 evidence だけを典拠とする測量図から、
正しく境界づけられた説明(time-to-correct-bounded-explanation)へ到達できる状態を、
v0.5.4 として実装・出荷できるか。**

この問いを採否の判定規律として使う。判定は設計思想ノート冒頭の3条件を運用化した
Acceptance Criteria で行う:

- **忠実性の完備**(→ AC1 / AC2 / AC4): すべての視覚チャネルが view model のフィールドへの
  対応表に載り、fidelity 4区分(measured / derived / layout / decoration)で申告される。
  viewer 側の推測・合成はゼロ。
- **読み方の教養が流通していること**(→ AC3 / AC8): 気象図 lens のセンターピースが
  実測データから描け、第三者セッションが protocol の task に viewer だけで正しく答えられる。
- **wow が嘘をつかないこと**(→ AC4 / AC5 / AC6): 3D は俯瞰既定+平面化トグルの
  設計ベットとして実装するが、F₂ の無向規律・演出予算・profile 非合成・時間軸の
  位置安定性がテストで強制される。

機能の実装量は判定対象ではない。「描ける」は手段であり、判定対象は説明への到達である。

## 背景と現状診断

- 設計思想ノート(PR #3628、敵対レビュー2巡反映済み)が identity を固定した:
  ArchView は AAT が構成した意味の幾何の上に ArchSig の有界な evidence を投影する
  **人間向けの対話的な測量図**であり、structural verdict を生成しない
  diagnostic evidence の navigator である。気象図はその上の第一の engineer-facing lens。
- 現行 `tools/archview/archview.html`(v0.5.3、3,110行)は AG 語彙ネイティブな絵
  (étale sheet / patch / lens)が主役で、読み方の教養が流通していない。
  ユーザー裁定(2026-07-20): **ゼロから作り直す。現状のものは配布しても受け入れられない。**
- スパイク(2026-07-20、`.tmp/weather-spike/spike.html`、train-ticket saga evidence の
  再現 run `run:7a94d68ac5d7` から全転記)で確認済みの事実:
  1. センターピース(静穏×6 + 無向循環警報 + 基図の穴 + 託送の面あり対比)は
     実測データだけで1画面に成立する。
  2. 本複体(K3×2)でスペクトル埋め込みは実際に縮退し、現行契約の
     「宣言済み layout リングへ段階縮退」規則が実地で必要になった。
  3. 3D は雲(section 層)という 2D に無い情報面を持つが、オクルージョンコストが高く、
     俯瞰既定+層トグルが必須。ユーザーの選好は 3D(2026-07-20)。
     最終採否は AC8 の protocol 実測で判定する。
- 現行 handoff の欠落(ノート §8): 観測所を駆動する ObservationCoverage が無い
  (MeasurementProfile は run 全体で、context × axis の coverage を表さない)。
  診断階段(analyze×2 + compare + gate×2)は複数 out-dir に散らばり、束ねる artifact が無い。
- Three.js は CDN 参照(バージョン pin)を維持する。vendoring は不採用
  (2026-07-20 ユーザー裁定: 配布時点でネット接続前提、閉域網は想定しない)。

## 設計原則

1. **ノートが正本**: 視覚言語(語彙対応表)・fidelity 4区分・沈黙種別・無向規律・
   profile 非合成・時間軸契約は設計思想ノートを正とし、本 PRD は作業項目化だけを行う。
2. **lens 分離**: ArchSig が供給するのは表示非依存の typed measurement view model。
   気象語彙(前線・循環警報・穴・霧)は viewer の表示層に閉じ、Rust schema に入れない。
3. **M→V gating(不変)**: viewer は view model / dossier の実測フィールドからの投影だけを描く。
   coverage・verdict・向き・強さの viewer 側推測はゼロ。
4. **沈黙は描くが、種類を潰さない**: unmeasured / not_computed / silence_by_design 等は
   霧 family の中で badge / reason / whatNext により区別する。
5. **段階的縮退の決定論**: 埋め込みの縮退・大規模グラフ・供給欠落のすべてで、
   無言の空画面ではなく宣言された縮退先(layout リング / 集約 / 沈黙表示)へ落ちる。

## 改修

### Wave 1 — ArchSig typed measurement view model(Rust)

#### R1 — `archsig-measurement-view-model` artifact 新設

`archsig analyze` が表示非依存の view model を追加出力する。区画はノート §8 の7項:

- (i) **observationCoverage**: context × measurementAxis の行。
  `contextRef / profileRef / evaluatorRef / measurementAxis / status /
  conclusionCode? / supportRefs[] / boundaryKind? / whatNext? / sourceRefs[] /
  runId / inputDigests`。既存 packet / profile / evaluator 出力からの投影のみで構成し、
  新しい判定を作らない。
- (ii) **localObservations**: chart ごとの grounding 行(holds 生値、reason token)。
- (iii) **edgeMismatch**: overlap ごとの witness 行
  (mismatch 実測 / 一致実測 / witness 未供給 の3値。未供給を一致に潰さない)。
- (iv) **classSupport**: 非零類の代表元 support 辺、閉路構造、係数
  (F₂ は無向であることを schema 上で明示)、triple-overlap face の实在リスト。
  **face の不在は行の不在ではなく、閉路に対する face 欠落として明示的に導出可能な形**
  (complex の vertices / edges / triples を view model に含める)。
- (v) **harmonicFlow**: 調和代表元の符号付き辺値(R 係数 run 供給時のみ。無ければ区画ごと absent)。
- (vi) **scalarFields**: 実測 per-vertex / per-edge スカラーと測定出自(供給時のみ)。
- (vii) **boundaryStatements**: 沈黙種別つき(既存 boundary kinds を保持)。
- 全 leaf は packet / gate report フィールドへの対応表(§AC1)を持つ。
  schema catalog 登録・validation・conclusion-token lint 準拠を含む。

#### R2 — `archsig dossier` コマンド新設

- 既存 run 出力(analyze × N、compare、gate)を機械的に束ね、
  `archsig-diagnosis-dossier` artifact を出力する。計測はしない(束ね直しのみ)。
- 各 frame は `inputDigests` / runId の整合を検証して取り込む(不整合は fail-closed)。
- 各 frame に **state provenance** を必須で持つ:
  `observed-source / authored-model / measured-conclusion / hypothetical-state / actual-change`
  (ノート §6。train-ticket の repaired 変種は hypothetical-state)。
- frame の順序列(sequence)を持ち、Wave 3 の時間軸供給を兼ねる。
- 診断階段(head → BLOCKED → repaired → PASS)は dossier の代表ユースケースであって
  専用スキーマではない(任意の run 列を束ねられる一般形)。

#### R3 — 版数一斉更新(v0.5.4)

- 単一契約版数の規律に従い全 schema 文字列を `<name>/v0.5.4` へ一斉更新する。
  fixture・catalog・契約テスト・docs の同期を含む。
- 同期対象リストに CLAUDE.md / AGENTS.md の検証コマンド例を明示的に含める
  (v0.5.1 / v0.5.3 で2回連続した漏れの再発防止。rg で旧版数ゼロ+記載コマンド
  verbatim 実行を AC7 に固定)。

### Wave 2 — 新 viewer(ArchView weather)

#### R4 — 新 `archview.html`(ゼロベース)

- no-build 単一 HTML + Three.js CDN(pin)を維持。入力は view model + dossier
  (+互換のため既存 viewer-data / gate report も第二入力として受理してよいが、
  気象 lens の描画典拠は view model に限る)。
- **3D 俯瞰を既定**とし、**平面化トグル**(同一基図のカメラ・投影切替)を常設する。
  2D は別実装ではなく同じ scene graph の投影である。
- シーン構成(1シーン=1つの問い):
  1. **基図と観測網** — どの地区・道・面・穴があり、観測所はどこで何を観測しているか
     (observationCoverage 駆動。観測所の無い軸は観測所を描かない)。
  2. **天気** — 前線(edgeMismatch)・循環警報(classSupport、無向)・基図の穴
     (閉路に対する face 欠落)・風(harmonicFlow 供給時のみ)・等値線(scalarFields 供給時のみ)。
  3. **空(section 層)** — 雲層(section 値ごと)、一致辺の bridge、mismatch 辺の裂け目。
  4. **診断階段** — dossier の frame 列を state provenance badge つきで描く
    (grounding → descent → compare → gate。gate 未供給は沈黙)。
  5. **推移** — Wave 3(R7)。
- 旧 v0.5.3 viewer は `docs/archive/` へ退避し、release bundle を新 viewer で置換する。
  AG 数学語の詳細(Math lens 奥の間)の再建は本波では行わない(Non-Goals)。

#### R5 — fidelity manifest(機械検査可能)

- 視覚チャネル → fidelity 区分(measured / derived / layout / decoration)→
  駆動フィールドの対応を、viewer 内の宣言データ(JSON)として持ち、
  UI(How this is drawn)と e2e テストの両方が同じ宣言を参照する。
- **Decoration トグル OFF で主張が変わらない**ことをテストで固定する。
- **F₂ 系 glyph に回転・向きの視覚チャネルを与えない**ことを宣言+テストで固定する
  (回転アニメーション・矢印の禁止)。
- 未測定の滑らかな連続場は描かない。非データ背景を使う場合は別視覚文法+別 legend+
  既定 OFF(ノート §7.3)。

#### R6 — 沈黙種別と profile 非合成

- 霧 family 内で沈黙種別(measured_zero とは区別された unmeasured / unknown /
  not_computed、boundary kinds)を badge / reason / whatNext で表示する。
- **profile switcher / small multiples / レイヤーごとの profile badge** を実装し、
  cross-profile の比較契約が供給されない限り異なる profile の観測を1画面へ合成しない
  (money / status の2 run を素材にテストする)。

### Wave 3 — 時間軸

#### R7 — 推移シーン(dossier sequence の再生)

- dossier の frame 列を「天気の推移」として再生する:
  witness の新規記録 → 前線が立つ / selected cocycle の非自明化 → 循環警報が記録される /
  provenance 付き compare → obstruction が変更後に記録されなくなる(ノート §6 の測定粒度)。
- **位置の安定性**: 共通 context anchor、前 frame への Procrustes 整列、
  新規・削除 context の別表現、layout motion の fidelity 申告。
  frame ごとの独立スペクトル再計算による見かけ運動を禁止する(テストで固定)。
- 各 frame の state provenance badge を常時表示する(hypothetical と actual の混同禁止)。
- **予報はしない**: 未来 frame の合成・外挿 UI を持たない。
- 素材: one-cent drift デモ5幕(base → head → BLOCKED → repaired → PASS)を dossier 化した
  golden fixture、および train-ticket saga head → repaired(evidence 再現 run)。

### R8 — 恒久契約の改訂と e2e

- `archview_gluing_geometry_contract.md` を気象図 lens の忠実性契約として全面改訂する
  (語彙対応表・fidelity 4区分・沈黙種別・無向規律・profile 非合成・時間軸契約を
  ノートから恒久契約へ昇格。ノートは思想の記録として残る)。
- browser e2e(`saga_browser_e2e.cjs` 系列の後継 `weather_browser_e2e.cjs`)で
  最低限次の状態を検査する: センターピース描画 / decoration OFF 同一主張 /
  F₂ 回転禁止 / profile 非合成 / dossier 不整合の fail-closed / 縮退時の layout リング /
  sequence の Procrustes 安定。

## 却下条件(反例駆動)

次のいずれかが観測された実装は、機能が揃っていても却下する。

1. viewer が view model に無い値(coverage・向き・強さ・verdict・座標の意味)を推測・合成した。
2. F₂ 系 glyph が回転・矢印・「低気圧」等の向き/スカラー含意表現を持った。
3. 気象語彙(前線・循環警報・穴・霧)が Rust schema / view model のフィールド名に入った。
4. 異なる profile の観測が比較契約なしに1画面へ合成された。
5. Decoration トグル OFF で画面の主張(何が measured か)が変わった。
6. 未測定の滑らかな連続場が等値線・流線と同じ視覚文法で描かれた。
7. sequence 再生で埋め込みが frame ごとに独立再計算され、layout の変化が
   architecture の変化として見えた(Procrustes 整列・anchor の欠落)。
8. witness 未供給の辺が「一致」として描かれた(未測定 ≠ 一致)。
9. hypothetical-state の frame が actual-change と区別なく表示された。

## Implementation Plan(PR 分割)

| PR | Wave | 内容 |
| --- | --- | --- |
| PR-1 | 1 | R1 view model emitter + schema catalog + validation + golden fixture + R3 版数一斉更新 |
| PR-2 | 1 | R2 `archsig dossier`(digest 整合 fail-closed、state provenance、sequence) |
| PR-3 | 2 | R4 新 viewer コア(基図と観測網 + 天気シーン、3D 俯瞰既定 + 平面化トグル)+ e2e 基盤 |
| PR-4 | 2 | R4 残(空 + 診断階段)+ R5 fidelity manifest + R6 沈黙種別・profile 非合成 |
| PR-5 | 3 | R7 推移シーン(Procrustes + anchor + provenance badge)+ one-cent 5幕 dossier fixture |
| PR-6 | — | R8 恒久契約改訂 + 旧 viewer 退避 + release bundle 置換 + README / docs 同期 |

依存: PR-1 → PR-2 → PR-3 → PR-4 → PR-5 → PR-6(直列。PR-3 以降は PR-1/2 の artifact を典拠にする)。

## Acceptance Criteria

- **AC1(view model 対応表)**: view model の全 leaf が packet / gate report フィールドへの
  対応表(docs 内の表)を持ち、対応表に無い leaf が存在しない。validation pass。
- **AC2(dossier 整合)**: digest 不整合・provenance 欠落の dossier が fail-closed で
  拒否されるテスト。5区分 provenance の必須化。
- **AC3(センターピース)**: train-ticket saga evidence の再現 run
  (`docs/reports/train_ticket_dogfooding/README.md` のコマンド)から、新 viewer が
  センターピース(静穏×6・前線×3・無向循環警報・基図の穴・託送の面あり・
  witness 未供給辺の沈黙)を描く。e2e + スクリーンショット固定。
- **AC4(fidelity)**: fidelity manifest が UI とテストの共通典拠であること、
  decoration OFF 同一主張テスト、F₂ 回転禁止テストが pass。
- **AC5(沈黙と profile)**: 沈黙種別 badge の表示テスト、money / status 2 run の
  非合成テスト(比較契約なしの合成が UI 上不可能)が pass。
- **AC6(時間軸)**: one-cent 5幕 dossier の再生で、Procrustes 安定性テスト
  (共通 anchor の座標変動が閾値内)と provenance badge 常時表示テストが pass。
- **AC7(版数同期)**: rg で旧版数文字列ゼロ。CLAUDE.md / AGENTS.md 記載コマンドの
  verbatim 実行が成功。
- **AC8(protocol、ユーザー受け入れ)**: コード・AAT 非接触の第三者セッションが、
  viewer だけで protocol の task 7項目(どの profile / cover を見ているか、
  measured zero と unmeasured の区別、非零類 support の特定、局所正・大域不整合の説明、
  source への到達、actual と hypothetical の区別、何を結論してはいけないか)に答え、
  正確性・所要時間・コードに戻った理由を記録する。**3D 既定と平面化トグルの
  比較所見を含める**(3D 採否の最終判定材料)。

## Non-Goals

- **Facade SKILL(単一入口)**: 独立 PRD(v0.5.4 のもう1本)。本 PRD の viewer は
  供給済み artifact の投影に徹する。
- **website 同期**: 新 viewer の website 反映(live demo / getting-started)は
  本 PRD 完了後の別 Issue(v0.5.3 の同期波 #3596 と同型)。
- **Math lens 奥の間**: AG 数学語の詳細ビュー再建はしない(math terms の
  二層文言切替は R4 の範囲で最小限維持してよい)。
- **R 係数 harmonic run の実測供給**: harmonicFlow 区画は受け皿のみ。
  runtime 実測の供給 workflow は別課題。
- **予報・外挿・increment 抽出**: 時間軸は実測 frame の再生まで。
- **Three.js vendoring**: 不採用裁定を維持。
- **Lean / FieldSig への波及**: なし。

## 検証コマンド

```bash
cargo test --manifest-path tools/archsig/Cargo.toml
node tools/archview/weather_browser_e2e.cjs <out-dir> <state>   # PR-3 以降
git diff --check
rg -nP "[\x{200B}-\x{200F}\x{202A}-\x{202E}\x{2066}-\x{2069}]" <changed-files>
```
