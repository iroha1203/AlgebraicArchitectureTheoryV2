# ArchView

**AAT ツールレイヤーの可視化担当。** ArchSig が計測し、ArchView が見せる。
ArchSig（計測）/ FieldSig（進化）と並ぶ、**可視化（geometry projection）**のコンポーネント。

- **ArchSig** … ArchMap + LawPolicy + evidence contract から、選ばれた語彙内の肯定的 diagnostic conclusion を **計測**する（Rust）。
- **ArchView** … その計測 artifact を AAT 代数幾何の **幾何として投影**する no-build 単一 HTML viewer（Three.js）。

## 役割と境界（最重要）

ArchView は **projection に徹し、新しい structural verdict を一切作らない**。
ArchSig が input contract 時に一度だけ前払いした境界を、そのまま投影するだけである。

忠実性契約（ArchSig measurement-first の従属レイヤーとして）:

- **形は測定量が駆動する。** 位置は測定された nerve トポロジー + atom membership の作図（adjacency / membership は実在、絶対座標は verdict を持たない）。hash は declump jitter のみ。
  cell 半径 ∝ |atoms| / strut 太さ ∝ |support| / bead サイズ ∝ valence / seam = 実測 `cocycleRibbon.supportEdges`。
- **色レーンを分離する。** measured_zero = teal / measured_nonzero = amber / analytic_reading = lavender / 沈黙 = grey。
- **bloom は測定された H¹ evidence に予約する。** lawful / analytic は calm reflector のまま光らせない。
- **沈黙は霧・すりガラス・非描画で表す。** 赤エラー化しない。未測定・ゼロを「flat = lawful」と読まない（near-flat ≠ lawful）。
- **H² coherence は可視化しない**（triple-overlap face は存在のみ）。holonomy 系は restriction-path 探索であって monodromy verdict ではない。

> ArchView は語れることだけを幾何にし、語り得ない領域には沈黙する。input contract を補完・推測・拡張しない。

## 入力契約（ArchSig → ArchView の handoff）

ArchView は自分と同じディレクトリから以下を fetch する（`archsig analyze` の出力）:

| ファイル | 必須 | 内容 |
| --- | --- | --- |
| `archsig-atom-viewer-data.json` | ✅ | `archsig-atom-viewer-data/v0.5.0` 投影本体（nerve / cocycleRibbon / atomGlyphs / overlays / finitePosetSite / reportPane …） |
| `archsig-analysis-summary.json` | 任意 | verdict / assumption ledger / structural verdict summary（report pane にマージ） |
| `archsig-run-manifest.json` | 任意 | artifact パス一覧（report pane にマージ） |

primary が無ければ空シェル表示。**file `<input>` と drag-drop でも読める**ので、任意の `archsig-atom-viewer-data.json` を投げ込めばよい。

## シーン（1 シーン = 1 つの問い）

| シーン | 問い |
| --- | --- |
| Nerve & Cover | どんな有限 site と cover を ArchSig は計測したか |
| **Gluing & H¹ obstruction** | 局所の一致は大域の section に貼り合うか、どこで閉じないか（headline。閉じない縫い目 = amber seam） |
| Curvature / Hodge debt | 曲率はどこに集中するか（analytic reading、verdict ではない） |
| Period / Stokes | クラスは cycle にどう巻きつくか（analytic reading） |
| Forbidden support / flatness | どの atom 共起が禁止され、section はどう repair しうるか |
| Projection boundary | 選ばれた profile は何を観測し、何が沈黙か |

## Release bundle

ArchSig release archive では ArchView は `archview/` に同梱される。

```text
archview/
  archview.html
  README.md
```

ES module + Three.js CDN を使うので、`archview.html` はローカルサーバ経由で開く。
`archview.html` を `archsig analyze --out-dir` の出力ディレクトリへコピーするか、
出力ディレクトリをローカルサーバで配信して file picker / drag-drop で
`archsig-atom-viewer-data.json` を読ませる。`archview-sequence.json` が同じ
ディレクトリにある場合は sequence mode に入り、各 frame の実測 ArchSig packet を
順に表示する。

## Repository checkout demo

```bash
# ① ArchSig で計測 artifact を生成
cargo run --manifest-path tools/archsig/Cargo.toml -- analyze \
  --archmap tools/archsig/examples/practical-rust-service/archmap/archmap.json \
  --law-policy tools/archsig/examples/practical-rust-service/law_policy/law_policy.json \
  --measurement-profile tools/archsig/examples/practical-rust-service/law_policy/measurement_profile.json \
  --out-dir .tmp/archview-demo

# ② ArchView をその成果物の隣に置いて配信（sibling fetch が成立する）
cp tools/archview/archview.html .tmp/archview-demo/
python3 -m http.server 8000 --directory .tmp/archview-demo
# → http://localhost:8000/archview.html
```

リポジトリ全体を配信して `archview.html` を開き、`archsig-atom-viewer-data.json` をドラッグしてもよい。

## 依存

- Three.js r0.164.1（unpkg importmap、no-build）。offline 環境では CDN 取得に失敗する。
- ArchSig 本体・出力契約には依存するが、ArchSig を改変しない。
