# ArchView

**AAT ツールレイヤーの可視化担当。** ArchSig が計測し、ArchView が見せる。
ArchSig（計測）/ FieldSig（進化）と並ぶ、**可視化（geometry projection）**のコンポーネント。

- **ArchSig** … ArchMap + LawPolicy + evidence contract から、選ばれた語彙内の肯定的 diagnostic conclusion を **計測**する（Rust）。
- **ArchView** … その計測 artifact を AAT 代数幾何の **幾何として投影**する no-build 単一 HTML viewer（Three.js）。

## 役割と境界（最重要）

ArchView は **projection に徹し、新しい structural verdict を一切作らない**。
ArchSig が input contract 時に一度だけ前払いした境界を、そのまま投影するだけである。

忠実性契約（ArchSig measurement-first の従属レイヤーとして）:

- **形は測定量が駆動する。底空間は代数幾何の絵そのもの。** context は開被覆の **patch**(半透明の平たい円盤)として描かれ、
  X,Z = 実測 nerve の Laplacian スペクトル埋め込み(同一成分内の近さ ≈ 拡散距離。等長変換・固有値縮退を除いて一意)。
  patch は**ほぼ同一平面**に置かれる(Y は常に 0)。restriction poset の深さは patch の高さではなく、
  2つの patch を結ぶ **overlap lens**(vesica 形の重なり領域。サイズ ∝ √(実測共有 atom 数)、mismatch marker があれば amber)
  の沈み込みとして残る — 深い重なりほど lens が低く沈む。3重 overlap は既存どおり frosted な face(存在のみ、H² 沈黙)。
  atom は必ず自分の実測所属領域(単一 context の patch / ペア重なりの lens / 3重 overlap の face)の内側に立ち、
  領域内の並びは family セクター + id 順リングという決定論規則(hash・乱数は一切使わない)。
  patch 半径 ∝ |atoms| / lens サイズ ∝ √(共有 atom 数) / lens 縁太さ ∝ #mismatch markers / bead サイズ ∝ valence /
  seam = 実測 `cocycleRibbon.supportEdges`。
- **上空は étale space、二重被覆は文字通り2枚のシート。** Sections シーンは宣言された section 値ごとに
  patch 上空へ半透明のシート片を浮かべ、値が一致する restriction edge 上ではシート片を連続な bridge で貼り、
  不一致の edge では裂け目(zigzag の fault line)で明示的に切る。H¹ cocycle support 上の裂け目だけ amber + bloom
  (bloom は測定 H¹ evidence 専用の予算のまま)。大域切断があれば teal の一枚シートが全 patch を覆う。
  Twist view は同じ base の上に2枚のシート(±h)を重ね、cocycle support edge 上で帯(band)が他方のシートへ渡る
  ことで、Möbius 的な捻れを見せる(連結性判定ロジック自体は従来どおり、packet との不一致時は沈黙)。
- **色レーンを分離する。** measured_zero = teal / measured_nonzero = amber / analytic_reading = lavender / 沈黙 = grey。
  高彩度はこの4レーンに予約し、atom family 色・section レーン色は意図的に低彩度(グレイッシュ)にする —
  family の識別は主に **形**(FAMILY_SHAPE)が担う。hover/選択時だけ一時的に高彩度へポップしてよい。
- **bloom は測定された H¹ evidence に予約する。** lawful / analytic は calm reflector のまま光らせない。
- **沈黙は霧・すりガラス・非描画で表す。** 赤エラー化しない。未測定・ゼロを「flat = lawful」と読まない（near-flat ≠ lawful）。
- **H² coherence は可視化しない**（triple-overlap face は存在のみ）。holonomy 系は restriction-path 探索であって monodromy verdict ではない。

> ArchView は語れることだけを幾何にし、語り得ない領域には沈黙する。input contract を補完・推測・拡張しない。

## 分析ツールとしての3つの面

- **幾何/装飾の申告(fidelity declaration)** … 要素(context / atom / strut / seam …)や insight カードをクリックすると
  右側に詳細パネルが開き、視覚チャネルごとに `measured`(測定量駆動)/ `layout`(実測adjacencyの埋め込み。座標はverdictなし)/
  `decoration`(bloom・pulse・アーチ等の演出)を申告する。詳細パネルは on-demand で、未選択時は完全に非表示(空パネルは出さない)。
  × で閉じると選択状態もクリアされる。ツールバーの **Decoration** トグルをOFFにすると、演出を全て落とし測定駆動の幾何だけを描画する
  (seamは直線実線tube、bloom/pulse/probeなし)。どちらのモードでも主張は変わらない。
- **二層用語(Engineer terms / Math terms)** … シーン名・バッジ・legend・詳細文言はエンジニア語(デフォルト)と
  AG数学語の2層を持ち、ツールバーのチップで切替できる。文言だけが変わり、主張・境界・conclusion codeは変わらない。
- **legend の二段構成** … 画面左下には teal / amber / lavender / grey の4色だけを示すコンパクトな color key を常設する。
  凡例の全文(色・形の意味の詳細)はツールバーの **How to read** ボタンで開く slide-in パネルにあり、× で閉じる。
  常設パネル(toolbar / question band / insights / color key / status)は互いに重ならないレイアウト規律を持つ。
- **コード到達(source landing)** … atom / amber seam / strut をクリックすると、supplied ArchMap の `sources`
  宣言から解決された `path:line`(+symbol)が表示され、⧉ でコピーできる。amber要素では
  「対立しているsection宣言(objectRef)+それぞれのコード位置」が並ぶので、
  画面から実コードの改善ポイントへ直接降りられる。解決はArchSig側(`sourceRefSamples`)で行われ、
  ArchViewは位置を発明しない。

## 入力契約（ArchSig → ArchView の handoff）

ArchView は自分と同じディレクトリから以下を fetch する（`archsig analyze` の出力）:

| ファイル | 必須 | 内容 |
| --- | --- | --- |
| `archsig-atom-viewer-data.json` | ✅ | `archsig-atom-viewer-data/v0.5.4` 投影本体（nerve / cocycleRibbon / sagaDescent / atomGlyphs / overlays / finitePosetSite / reportPane …） |
| `archsig-analysis-summary.json` | 任意 | verdict / assumption ledger / structural verdict summary（report pane にマージ） |
| `archsig-run-manifest.json` | 任意 | artifact パス一覧（report pane にマージ） |
| `archsig-gate-report.json` | 任意 | `archsig-gate-report/v0.5.4` の decision / per-row action（SAGA 最終段に投影） |

primary が無ければ空シェル表示。**file `<input>` と drag-drop でも読める**ので、任意の `archsig-atom-viewer-data.json` を投げ込めばよい。
gate reportは同じディレクトリに置くか、toolbarの **Open gate report…** から第二入力として指定する。packet digestが不一致の報告は反映せず、理由をstatusに表示する。

## シーン（1 シーン = 1 つの問い）

| シーン | 問い |
| --- | --- |
| Nerve & Cover | どんな有限 site と cover を ArchSig は計測したか（patch の底空間 + overlap lens） |
| **Gluing & H¹ obstruction** | 局所の一致は大域の section に貼り合うか、どこで閉じないか（headline。閉じない縫い目 = amber seam）。**Twist view** トグルで F₂ cochain をその二重被覆として描く: coboundary なら base の上に 2 枚の平行シートが浮かび、H¹≠0 なら cocycle support edge 上で帯が他方のシートへ渡って 1 枚に連結する（「閉じない」の幾何的実体） |
| **Étale space / sections** | 宣言された section 値はどこまで延び、大域切断はあるか（値ごとのシート片が patch の上空に浮かび、一致する overlap では連続な bridge、不一致では裂け目で切れる。大域切断があれば teal の一枚シートが全体を覆う） |
| Curvature / Hodge debt | 曲率はどこに集中するか（analytic reading、verdict ではない） |
| Period / Stokes | クラスは cycle にどう巻きつくか（analytic reading） |
| Forbidden support / flatness | どの atom 共起が禁止され、section はどう repair しうるか |
| Projection boundary | 選ばれた profile は何を観測し、何が沈黙か |

各シーン名は Engineer terms lane では平易名（Global consistency / Section lanes 等）で表示される。
設計の正本は `docs/note/archview_measured_geometry_design.md`（計測駆動幾何）と
`docs/tool/archview_gluing_geometry_contract.md`（忠実性契約）。

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
# ① ArchSig で計測 artifact を生成(archmap_head.json = 1セントのドリフトの障害あり状態)
cargo run --manifest-path tools/archsig/Cargo.toml -- analyze \
  --archmap tools/archsig/examples/practical-rust-service/archmap/archmap_head.json \
  --law-policy tools/archsig/examples/practical-rust-service/law_policy/law_policy.json \
  --measurement-profile tools/archsig/examples/practical-rust-service/law_policy/measurement_profile.json \
  --measurement-profile tools/archsig/examples/practical-rust-service/law_policy/measurement_profile_drift.json \
  --law-surface tools/archsig/examples/practical-rust-service/law_policy/law_surface.json \
  --repair-plan tools/archsig/examples/practical-rust-service/saga/repair_plan_head.json \
  --out-dir .tmp/archview-demo

# ② ArchView をその成果物の隣に置いて配信（sibling fetch が成立する）
cp tools/archview/archview.html .tmp/archview-demo/
python3 -m http.server 8000 --directory .tmp/archview-demo
# → http://localhost:8000/archview.html

# ③ Chrome headless smoke test: SAGA stage ⇔ Three.js scene, HUD, and gate absence
#    前提: Chrome/Chromium（見つからなければ CHROME_BIN で指定）と
#    website/node_modules の ws（初回は cd website && npm install）
node tools/archview/saga_browser_e2e.cjs .tmp/archview-demo absent

# ④ gate reportを生成し、SAGA最終段への供給・表示を確認
cargo run --manifest-path tools/archsig/Cargo.toml -- gate \
  --packet .tmp/archview-demo/archsig-measurement-packet.json \
  --policy tools/archsig/examples/practical-rust-service/law_policy/gate_policy.json \
  --out .tmp/archview-demo/archsig-gate-report.json
node tools/archview/saga_browser_e2e.cjs .tmp/archview-demo supplied
# gate reportのschemaまたはpacket digestを壊したディレクトリでは mismatch を指定する
node tools/archview/saga_browser_e2e.cjs .tmp/archview-demo mismatch
# JSON parse error と per-row boundaryOverrideApplied 欠落も明示拒否する
node tools/archview/saga_browser_e2e.cjs .tmp/archview-demo malformed
node tools/archview/saga_browser_e2e.cjs .tmp/archview-demo missing-boundary
# sagaDescent の段形状が契約と食い違う viewer-data は、無言の空シーンにせず明示拒否する
node tools/archview/saga_browser_e2e.cjs .tmp/archview-demo invalid-saga
```

リポジトリ全体を配信して `archview.html` を開き、`archsig-atom-viewer-data.json` をドラッグしてもよい。

## 依存

- Three.js r0.164.1（unpkg importmap、no-build）。offline 環境では CDN 取得に失敗する。
- ArchSig 本体・出力契約には依存するが、ArchSig を改変しない。
