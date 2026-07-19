# ArchView 忠実性契約(気象図 lens、v0.5.4)

ArchView の恒久的な忠実性契約。設計思想の正本は
[気象図リニューアル設計思想ノート](../note/archview_semantic_weather_map_design.md)、
実装 PRD は [ArchView v0.5.4 PRD](archview_v0_5_4_prd_weather_renewal.md)。
本書は viewer が**恒久的に守る規則**だけを持つ。
旧 v0.5.3 契約(AG 語彙ネイティブ描画)は
`docs/archive/2026-07-20-archview-v053/` に退避した。

## Identity

ArchView は、AAT が構成した選ばれた意味の幾何の上に、ArchSig が測定した有界な
architecture evidence を投影する、人間向けの対話的な**測量図**である。
新しい structural verdict を生成しない(diagnostic generator ではない)が、
ArchSig が生成した diagnostic evidence の navigator ではある: 観測範囲の把握、
局所観測と大域結論の接続、沈黙理由の確認、support と source への到達、
run 間の比較を支援する。

気象図はこの証拠面に対する第一の engineer-facing lens である。
気象語彙は viewer の表示層に閉じ、ArchSig の schema / artifact には入らない。

## 入力契約

| 入力 | 必須 | 契約 |
| --- | --- | --- |
| `archsig-measurement-view-model.json` | ✅ | `archsig-measurement-view-model/v0.5.4`(受理完全一致)。[leaf 対応表](archsig_view_model_contract.md)が typed 典拠 |
| `archsig-diagnosis-dossier.json` | 任意 | `archsig-diagnosis-dossier/v0.5.4`。診断階段・推移シーンの典拠。未供給は沈黙(エラーにしない) |

- 供給は sibling fetch / file picker / drag & drop。
- 契約外 schema・必須区画欠落・空複体は**無言の空画面にせず明示拒否**する。
- viewer は観測範囲・coverage・向き・強さ・座標の意味を**推測しない**。
  描けるのは view model / dossier の行に載っていることだけである。

## 視覚語彙(気象 ↔ 測定)

| 気象 | 駆動する測定 | 沈黙条件 |
| --- | --- | --- |
| 地区・道・面 | `complex`(packet coverNerveProjection の逐語投影) | —(常設の基図) |
| 観測所と axis チップ | `observationCoverage` 行 | 行の無い context×axis は観測所を描かない |
| 前線 | `edgeMismatch.status == mismatch_observed` | witness 未供給は点線の沈黙(**未測定 ≠ 一致**) |
| 一致の道 | `edgeMismatch.status == agreement_observed` | — |
| 循環警報 | `classSupport.classNonzero == true` の代表元 support | 類ゼロ・未計測は警報なし。**無向** — 回転・矢印・強さは描かない |
| 基図の穴 | 非零類の代表元が単純閉路、かつそれを埋める face が `complex.triples` に無い | 単純閉路でなければ support 辺表示へ決定論縮退。穴は structural absence であり霧ではない |
| 雲(section 層) | `sectionValues` 行(宣言の逐語) | 宣言なしは空のみ |
| 雲の bridge | `agreement_observed` の辺のみ | mismatch 辺の裂け目は「bridge を描かないこと」で表す |
| 風・等値線 | `harmonicFlow` / per-edge スカラー(現行 packet は未記録) | 描かない(「無風」と「観測なし」を混同しない) |
| 霧・沈黙 badge | `boundaryStatements[].kind`、coverage の not_observed 等 | 種別を1色に潰さない(badge / reason / whatNext で区別) |

「晴れ」は描かない — 語れるのは「この観測網では静穏」までであり、安全の主張ではない。

## fidelity 申告

- 4区分 `measured` / `derived` / `layout` / `decoration` を**視覚チャネル単位**で申告する。
  申告は viewer 内の単一の宣言データ(FIDELITY)が持ち、UI(How this is drawn)と
  e2e テストが同じ宣言を参照する。
- 加えて**禁止チャネル台帳**(`forbidden`)を宣言に含める: F₂ 類の回転・向き・強さ、
  未測定の連続場(等値線・流線)、未来 frame(予報・外挿)。禁止チャネルは実装しない。
- 代表例: 複体・witness・類 support = measured / スペクトル埋め込み座標 = derived
  (決定論 Jacobi。縮退時は宣言済み決定論リングへ段階縮退 = layout)/
  成分間配置・雲の高さ・色割当 = layout / 発光・明滅 = decoration
  (測定された非零類のみに予約。演出トグル OFF で停止し、**OFF で画面の主張は変わらない**)。
- source landing: 詳細パネルの `sourceRefs` は view model の行の逐語表示であり、
  viewer は位置を発明しない。

## profile 非合成

描画されるのは常に**1つの run の view model だけ**である。複数 run の読み込みは
switcher による全置換のみで、比較契約なしに2つの profile の観測を1画面へ合成する
UI は存在しない。active profile はヘッダに常時表示する。

## 診断階段(dossier の投影)

- frame 行は dossier の逐語投影: frameId / conclusion / runId /
  **state provenance badge(常時表示)** / gate decision(未供給は沈黙 chip)/
  compare 結論行。
- dossier は digest 整合検証済み bundle(`archsig dossier` が fail-closed で構築)であり、
  viewer 側は schema と形状のみ検査し、値を再導出しない。
- hypothetical-state は「この修理案なら貼り合う」の事前検証であり、
  repository への適用を主張しない(注記を常設)。

## 時間軸(推移)

- 再生できるのは dossier に記録された実測 frame だけである。予報・外挿・未来 frame の
  合成 UI を持たない。
- frame ごとの埋め込みは前 frame へ **Procrustes 整列**(回転・鏡映・平行移動、
  共通 context を anchor)してから描く。埋め込みの不定性による見かけの運動を
  architecture 変化として見せない。frame 間の位置の動きは layout として申告する。
- 新規 context は new リング、削除 context は前 frame 整列位置の ghost という
  **別表現**を持つ(位置の動きと出入りを混同させない)。
- 各 frame の state provenance を常時表示する。

## 執行

`node tools/archview/weather_browser_e2e.cjs <out-dir> <mode>` の10モード
(weather / flat / reject-schema / missing / sky / staircase / staircase-silent /
decoration-off / profile-switch / transition)が本契約の機械検査である。
cargo 側は `--test archview_e2e`(analyze 生成物)と view model / dossier の
cli 契約テストが対応する。
