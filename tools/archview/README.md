# ArchView

**AAT ツールレイヤーの可視化担当 — 意味の測量図。** ArchSig が測量し、ArchView が地図にする。

- **ArchSig** … ArchMap + LawPolicy + evidence contract から、選ばれた語彙内の肯定的
  diagnostic conclusion を**計測**する(Rust)。
- **ArchView** … その計測を表示非依存の typed view model 経由で受け取り、
  **気象図 lens** として投影する no-build 単一 HTML viewer(Three.js)。

## Identity と境界(最重要)

ArchView は新しい structural verdict を生成しない。しかし ArchSig が生成した
diagnostic evidence の navigator ではある — 観測範囲の把握、局所観測と大域結論の接続、
沈黙理由の確認、support と source への到達、run 間の比較を支援する。
恒久契約の正本は [ArchView 忠実性契約](../../docs/tool/archview_gluing_geometry_contract.md)、
設計思想は [気象図リニューアル設計ノート](../../docs/note/archview_semantic_weather_map_design.md)。

読み方の要点:

- **観測所 = contract 相対性**。天気図が観測網に相対的なように、この地図は supplied
  contract が観測した行だけを描く。「晴れ」は描かない — 語れるのは「この観測網では静穏」まで。
- **前線 = witness が実測した規約 mismatch**。witness 未供給の道は点線の沈黙
  (未測定 ≠ 一致)。
- **循環警報 = 非零 H¹ 類(無向)**。F₂ から向き・強さは出ないので回転は描かない。
- **基図の穴 = 閉路を埋める面が複体に無いこと**(structural absence)。霧(未観測)とは別語彙。
- **雲 = section 宣言**。bridge は一致が実測された辺にだけ架かる。裂け目は bridge の不在。

## 入力(ArchSig → ArchView handoff)

同一ディレクトリから fetch する(file picker / drag & drop でも可):

| ファイル | 必須 | 内容 |
| --- | --- | --- |
| `archsig-measurement-view-model.json` | ✅ | `archsig analyze` が出力する表示非依存 view model([契約](../../docs/tool/archsig_view_model_contract.md)) |
| `archsig-diagnosis-dossier.json` | 任意 | `archsig dossier` が束ねた digest 整合検証済み bundle(診断階段・推移シーンの典拠) |

契約外 schema は無言の空画面にせず明示拒否する。

## シーン(1シーン=1つの問い)

| シーン | 問い |
| --- | --- |
| 基図と観測網 | どんな地区・道・面があり、観測所はどこで何を観測しているか |
| 天気 | 前線はどこに立ち、循環警報と基図の穴はどこにあるか |
| 空(section 層) | 各地区は何を宣言し、どこで雲が繋がり、どこで裂けているか |
| 診断階段 | dossier の frame 列は何を測り、gate は何を決めたか(provenance 常時表示) |
| 推移 | 実測 frame の再生で天気はどう変わったか(Procrustes 整列、予報なし) |

既定は **3D 俯瞰**。「平面」トグルは同一 scene graph のカメラ・投影切替であり、
主張は変わらない。「演出」トグル OFF で発光・明滅が止まる(主張は変わらない)。
fidelity 申告(measured / derived / layout / decoration+禁止チャネル台帳)は
サイドパネルの HOW THIS IS DRAWN に常設。

## Repository checkout demo

```bash
# ① one-cent drift head を計測(view model が同時に出力される)
cargo run --manifest-path tools/archsig/Cargo.toml -- analyze \
  --archmap tools/archsig/examples/practical-rust-service/archmap/archmap_head.json \
  --law-policy tools/archsig/examples/practical-rust-service/law_policy/law_policy.json \
  --measurement-profile tools/archsig/examples/practical-rust-service/law_policy/measurement_profile.json \
  --measurement-profile tools/archsig/examples/practical-rust-service/law_policy/measurement_profile_drift.json \
  --law-surface tools/archsig/examples/practical-rust-service/law_policy/law_surface.json \
  --repair-plan tools/archsig/examples/practical-rust-service/saga/repair_plan_head.json \
  --out-dir .tmp/archview-demo

# ② viewer を成果物の隣に置いて配信
cp tools/archview/archview.html .tmp/archview-demo/
python3 -m http.server 8000 --directory .tmp/archview-demo
# → http://localhost:8000/archview.html

# ③ (任意)診断階段・推移も見る場合は repaired run と compare / gate を作り dossier を束ねる
#    コマンドは tools/archsig/docs/commands.md の Dossier 節を参照。
#    出力を archsig-diagnosis-dossier.json として同ディレクトリへ置く。

# ④ Chrome headless smoke test(前提: Chrome/Chromium と website/node_modules の ws)
node tools/archview/weather_browser_e2e.cjs .tmp/archview-demo weather
```

e2e は10モード: `weather / flat / reject-schema / missing / sky / staircase /
staircase-silent / decoration-off / profile-switch / transition`。

## Release bundle

ArchSig release archive では `archview/` に `archview.html` と本 README が同梱される。

## 依存

- Three.js r0.164.1(unpkg importmap、no-build)。CDN 参照は設計判断であり
  vendoring は不採用(閉域ネットワークは想定しない)。
- ArchSig の出力契約に依存するが、ArchSig を改変しない。

## 旧実装

v0.5.3 の AG 語彙ネイティブ viewer(étale sheet / patch-lens 描画)と旧 e2e は
`docs/archive/2026-07-20-archview-v053/` に退避した。現行 source of truth ではない。
