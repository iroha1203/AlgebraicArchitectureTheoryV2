# ArchSig 3D Viewer リッチ化 設計考察ノート

日付: 2026-06-15
対象ファイル:
- `tools/archview/archview.html`(現 viewer、Three.js r0.164.1 単一HTML)
- `tools/archsig/src/ag_measurement.rs`(viewer-data v2 ビルダー `build_measurement_viewer_data_v1` / `gluing_geometry_projection_v1`)
- 既存実装: Issue #2082とPR #2088/#2094/#2103/#2110/#2116で導入されたgluing geometry viewer

---

## 問い

このリッチ化が本当に答えるべき問いは一文で言える:

> **「クオリティがもう一つ」の正体は、ライティングが平板なことではなく、空間形状が AG 量を駆動していない(hashText とゴールデン角の擬似ランダム配置が view mode を支配し、curvature/holonomy/cocycle 値が形として読めない)ことである。リッチ化は『綺麗にする』のか『形が数学になる』のか、どちらを主目的に据えるのか。**

この問いを採否の判定規律にすると、各提案は「見栄えを上げるが意味は駆動しない案(器)」と「AG 量が形を駆動する案(本体)」に二分され、前者だけで PRD を切ると audit 最重要ギャップが残ったまま画面だけ豪華になる、という失敗が事前に見える。

### 問いの立て方の候補(オーナーが選ぶ)

**候補 A: 見栄え優先(rendering-fidelity を主目的)**
「製品3Dツールに見えない」を直す。ACESFilmic トーンマップ・環境IBL・接地影・Selective Bloom・fog・DOF を入れる。
- 意味: audit が列挙したレンダリングパイプラインの欠落(toneMapping/env map/shadow/postprocess すべてゼロ件)を埋める。
- 採否への効き方: 効果は確実だが「綺麗になる」に限定される。AG 量はレイアウトを依然 hashText が支配するため、view mode を変えても「同じスパイラルの再配色」感は本質的に残る。**A 単独を選ぶと、問いの核(形が意味を駆動しない)は次フェーズへ繰り越す前提を明文化する必要がある。**

**候補 B: AG忠実=「形が数学である」を優先(ag-faithful-geometry を主目的)** ← 本ノートの推奨軸
「curvature が地形を、degree が鉛直階層を、b_1 が光る閉路を駆動する」を実装する。レイアウトの主係数を hashText から `axisMetricBindings` の実 metric・実測 AG 値へ置換する。
- 意味: audit 最重要指摘(`nodePosition` L2089-2132 / `sceneAxisPosition` L1444-1465 が hash 主導、AG 値は `value*0.08` で薄く足されるだけ)を正面から解く。
- 採否への効き方: 効果が最も深いが、一部は Rust 側(`ag_measurement.rs`)への新規データ配線を伴い effort が上がる。**B を選ぶと「綺麗さ」は B の前提インフラとして A から最小限だけ取り込む構成になる。**

**候補 C: 時間と操作で動かすことを優先(temporal-interaction を主目的)**
holonomy traversal・assembly snap・degree スクラブ・カメラトゥイーン・cinematic tour で「同じ対象を別 reading で見ている」を時間軸で示す。
- 意味: view mode 遷移が瞬間切替(全 clear→再構築)でアニメは repair marker の lerp 1種のみ、という audit 指摘を時間次元で解く。
- 採否への効き方: 体験は一段上がるが、被写体の形が hash 配置のままだと「美しい無意味シャッフル」に堕する危険がある。C は B(形の駆動)と組んで初めて「動いたとき形が読める」に到達する。

推奨は **B を中心に、A から器の最小セットを取り込み、C を後続フェーズに置く**。理由は問いに直結する: 綺麗さも時間も、形が意味を駆動して初めて「数学が見える」に効くため。

---

## 現状診断

Phase1 の rendering 監査と data-contract 調査を踏まえると、「クオリティがもう一つ」の原因は二層に分かれる。

### レンダリング層の欠落(器の問題)

`createRenderer()`(L1001-1018)は素の `new THREE.WebGLRenderer({antialias:true})` を返すだけで、grep 確認で `toneMapping` / `outputColorSpace` 明示設定 / `shadowMap` / 環境マップ / `EffectComposer` / `fog` がすべてゼロ件。

- r0.164 デフォルトの `NoToneMapping` のままなのでハイライトが飽和し、フィルミックな階調が出ない。
- 環境マップ不在で `MeshStandardMaterial`(15箇所)の `metalness`/`roughness` が反射に寄与せず、PBR が事実上 Lambert に退化している。
- `castShadow`/`receiveShadow` がゼロ件で全オブジェクトが宙に浮く。
- ライティングは Ambient(0.76)+ Directional(1.2)の2灯のみ。rim も fill もない。
- 「映画的」演出は CSS の `filter: saturate(1.08) contrast(1.05)`(L124)と走査線 `repeating-linear-gradient`(L66-82)という2Dオーバーレイで偽装している。これが安っぽさの一因。
- `emissive` は4箇所(nerve marker L1521, cocycle gap L1640, repair arrow L1743, repair marker L1751)あるが、bloom 不在で「光って見えない」。

### 忠実性層の欠落(本体の問題=最重要)

レイアウトを決める関数群が hashText とゴールデン角(`2.399963229728653`)の擬似ランダムに支配されている:

- `nodePosition`(L2089-2132)/ `outsideAnalysisPosition`(L2250-2253)はゴールデン角スパイラル + hashText が支配。実 AG 値(`item.value`)は `addScaledVector` の weight に `value*0.08` で薄く足されるだけ。
- `curvatureFieldPosition`(L2174-2186)/ `holonomyPathPosition`(L2188-2200)/ `spectrumPosition`(L2219-2243)は hash 配置の上に y 高さや radial 倍率を後付け。x/z 平面は依然 hash 主導。
- `sceneAxisPosition`(L1444-1465)は `axisMetricBindings` の実 metric を持つが、`xScale`/`yScale` を `hashText(axes.x) % 17` で決め、index 由来項(`sqrt(index)*1.8`)に希釈される。
- 結果: view mode を変えても「同じスパイラルの再配色」に見え、AG 構造の幾何的差異が伝わらない。

加えて、データ供給側に gap がある。viewer の `buildAatContext`(L1852-1977)が読みに行く `signatureAxes` / `curvatureSupports` / `pathPairs` / `loops` / `holonomyReadings` / `viewerDistanceInputs` / `spectrumReport` は、現 runtime artifact(`archsig-atom-viewer-data-v2`)に**出力されておらず実行時に空配列へ解決される**(これらは旧 v0 経路 `cli/atom_viewer.rs` にしか配線が残っている)。実データで駆動できるのは `aatGeometryOverlays.gluingGeometry` 配下(nerve / cocycleRibbon / locusField / forbiddenCages / repairMorphs / atomGlyphs)に集中している。

### 既存実装 #2082 との関係(重複回避・補完)

Issue #2082はPR #2088/#2094/#2103/#2110/#2116で実装まで完了済みである。この実装はnerve / cocycle ribbon / locus field / obstruction cage / repair morph の**静的な幾何描画**と、`axisMapping` の HUD 表示、visual encoding の意味固定、scene 単位の non-claim を提供している。

したがって本ノートが狙うべきは #2082 の上層であり、**重複しない領域は明確**:
- 表現品質レイヤー(#2082 は立てていない: tone mapping/IBL/shadow/bloom/fog/postprocess)
- AG 量による空間形状の駆動(#2082 は幾何を「描く」が、配置の主係数を hash から実 metric へ移す改修はしていない)
- 時間・操作層(#2082 は静的、アニメは repair lerp 1種のみ)
- #2082 が Non-Goals で明示的に沈黙とした H^2 を「failure でなく沈黙ガラス」として控えめに空間化すること

`gluing_geometry_projection_v1` には `projectionBoundary` に「It adds no structural verdict」がハードコードされ、`cli.rs:1297-1301` が「does not create a new structural verdict」「visual richness below verdict level」を assert している(#2103 で packet 境界を固定)。本ノートのどの案も**この test-locked 境界を越えない**(verdict を新規に作らない)。

---

## 改善提案

採用された提案を tier 別に整理する。各案の effort と「3D である必然」は Phase1 検証に基づく。**本ノートの中心は Tier 2(AG忠実)** に置く。Tier 1 は Tier 2 の前提インフラ(器)であって、それ単体では忠実性を上げない点を期待値として固定する。

### Tier 1 即効(レンダリング品質)

これらは新規データ不要で `archview.html` だけで成立し、no-build の importmap 経由 `three/addons/` で実装する。**ただし「綺麗になる」に限定され「意味が見える」ようにはならない。**

**T1-1 PBR基盤の刷新(ACESFilmic + RoomEnvironment IBL + 3点照明 + 接地影 + fog)**
- 見える像: atom 球と幾何が環境反射とソフトな接地影を得て床に立つ。ハイライトが白飛びせずフィルミックな階調になる。距離フォグで camera far=4000 の奥行きが残る。
- AG概念: geometry first / representation as window(part_7)。曲率場・nerve・locus を同一 geometry の異なる reading として立体表示する「器」の刷新。
- Three.js実装方針: `createRenderer()`(L1001-1018)の WebGL/WebGPU 両経路に `toneMapping=ACESFilmicToneMapping`, `toneMappingExposure≈1.05` を設定。WebGPU 経路に `setPixelRatio(min(dpr,2))` を追加し `resize()`(L1024)で再適用。`PMREMGenerator.fromScene(new RoomEnvironment())` を `scene.environment` に(データURI HDRI 不要)。L951-954 の2灯を key(DirectionalLight castShadow / PCFSoftShadowMap)+ fill(HemisphereLight)+ rim の3灯に。`ShadowMaterial` の不可視床(y≈-24)で contact shadow。`scene.fog=new THREE.Fog(0x0d1015, 600, 2600)`。
- 駆動データ: 新規不要(既存 atomNodes と全 gluingGeometry の見えを底上げするだけ)。
- 3D必然: 環境反射・接地影・距離フォグは視点と3D位置に依存し、2Dスクリーンショットでは再現不可。
- effort: M

**T1-2 Selective Bloom で計測済み H^1 証拠だけを発光させる**
- 見える像: 暗いシーンで `closureGapEncoding.visible=true` の cocycle seam・nerve の sharedAtom マーカー・obstruction cage・repair marker だけが本物の光のにじみを伴う。lawful/measured-zero は落ち着いた反射体のまま。unmeasured は光らず沈黙する。
- AG概念: H^1 一次 verdict 軸(`MEASURED/NO_MEASURED_H1_OBSTRUCTION_UNDER_PROFILE`, `ag_measurement.rs:1385-1395`)を視覚的中心に。
- Three.js実装方針: `three/addons/postprocessing/` から `EffectComposer`/`UnrealBloomPass`/`OutputPass`。`animate()`(L1038)の `renderer.render` を composer に置換。bloom layer 方式(発光対象に `obj.layers.enable(1)`、darken→bloomComposer→合成)。`strength≈0.7` と控えめに。
- 駆動データ: 既存 `closureGapEncoding.visible`(Rust 側 `class_nonzero && !nonzero_edges.is_empty()`, ag_measurement.rs:2635)/ `triangles[].sharedAtomRefs` / `forbiddenCages` / `repairMorphs`。**接地強化**: 発光を headline H^1(seam/loop)を最強トーン、`forbiddenCages`(H^0寄り)/`repairMorphs`(candidate)は弱トーンに分ける。可能なら強度を `aggregateReadings.HolMass`/`curvatureValue` で連続変調し「二値発光」から「量の発光」へ。
- 3D必然: bloom は HDR 輝度から計算され視点距離で にじみ径が変わる。CSS の2Dオーバーレイと違い遮蔽・奥行きが正しく反映される。
- effort: M

**T1-3 霧と被写界深度による「沈黙の後退」(measured を手前、unmeasured を霧の奥へ)**
- 見える像: 焦点面に measured 幾何が鮮鋭・接地影付きで立つ。`coherenceClaim=not_visualized` の三角面・`unmeasured` 域は奥の depth 帯へ配置され指数霧に溶けて DOF でかすむ。**沈黙は「失敗の赤」ではなく「遠くて見えない霧の奥」として後退**。
- AG概念: ウィトゲンシュタイン的境界(語り得る/語り得ない)を被写界深度として実装。
- Three.js実装方針: `scene.fog=FogExp2(0x0d1015, …)` を既存 background と一致させる。`EffectComposer`+`BokehPass`、focus を `controls.target` 追従。depth は per-object status 由来(`locusField.fieldRows[].status` / `nerve.triangles[].coherenceClaim` / `cocycleRibbon.closureGapEncoding.visible`)で、カメラ視線方向への射影でバイアス(world-z 加算でなく)。
- 駆動データ: 上記 status は v2 packet に実在。**現状コードの境界違反(blockedRegions を `0xff6b6b` 赤 wireframe で沈黙を赤エラー化している, L1687)を撤廃する**。
- 3D必然: 焦点面=measured と霧の奥=silence の差は z 軸の連続量で初めて成立する。彩度差だけでは measured_zero の薄色と混同する。
- effort: L

**T1-4 H^2 三角面の「意図的かすれ」(存在は描くが coherence verdict は載せない)**
- 見える像: nerve 三角面が measured な頂点・辺に対して半透明・低彩度・微細ノイズの「すりガラス」に。輪郭は破線、hover で「H^2 coherence: silence by design(未測定)」の控えめなツールチップのみ。verdict バッジは一切付かない。
- AG概念: Čech nerve の 2-cell を幾何として投影しつつ `h2CoherenceVisualized=false` を厳守。
- Three.js実装方針: 現 nerve 三角形 material(opacity 0.34)を専用 silence material(低彩度グレー、opacity≈0.12、ハッチ CanvasTexture の alphaMap、depthWrite=false)に置換。**現状の emissive マーカー+shared-atom ラベル(L1516-1532)と solid/bright outline(L1564-1568)を減光・除去**(発光は measured 専用に予約)。
- 駆動データ: `nerve.triangles[].coherenceClaim` / `h2CoherenceVisualized`。新規不要。
- 3D必然: triple overlap は3パッチが重なる体積で、辺(線)との階層差は面 vs 線で表現される。
- effort: M(本質は「直すべき既存バグ」に近い)

**T1-5 視線追従ラベルの非散乱配置(共有アトラス + 距離フェード + 衝突回避)**
- 見える像: ラベルが重ならず、近いものだけ鮮明・遠いものは霧と同調してフェード。top insight(`priorityScore=100`)のラベルだけ常時表示。measured は高コントラスト、unmeasured は霧色で控えめ。
- AG概念: ラベルは reading への索引であって verdict ではない。
- Three.js実装方針: `createTextSprite`(L1576、毎回 512x128 CanvasTexture を新規生成)を共有アトラス方式へ。距離フェードは `vector.project(camera)` の簡易グリッド占有判定で衝突を間引き、`priorityScore` 順で優先。
- 駆動データ: `atomNodes[].labels` / `priorityScore`(v2 実在)。`nonzeroHolonomyLoops[].loopId` は v2 未投影なので、H^1 top insight には `cocycleRibbon.holonomyLikeGapMarker`(実出力あり)経由に限定。`spectrum hotspot` ラベルは別 phase(spectrumReport の v2 追加が前提)。
- 3D必然: ラベル衝突は3D→2D投影でのみ発生。billboard・距離フェード・引出線は視点が動く3Dでしか必要かつ有効。
- effort: L

**T1-6 空間文脈レイヤー(3D基準グリッド・座標プレート・ヴィネット・カメラトゥイーン)**
- 見える像: 床に淡い発光グリッドと軸ラベル付きプレート。view mode 切替が瞬間消去でなくカメラトゥイーン+crossfade。四隅は控えめなヴィネットで中心の肯定的結論に視線が集まる。HUD に「座標は視覚投影であり意味距離・因果・等価ではない」を明記。
- AG概念: `axisMetricBindings`(x/y/z)で軸の意味を空間化(representation as window)。
- Three.js実装方針: 自作グリッド(`LineSegments`+fog で遠方フェード)を床に。view mode 遷移は `renderScene`(L1103)で全消去前にカメラ位置を保持し、自作 lerp で `camera.position` と `controls.target` を新シーンの bounding sphere へトゥイーン。ヴィネットは OutputPass 後の薄い ShaderPass。
- 駆動データ: `axisMapping` / `axisMetricBindings` / `nonConclusions` / `distance_boundary`(v2 実在)。新規不要。
- 3D必然: 基準グリッドは視点角で透視収束し fog で遠方が消える。カメラトゥイーンは3D空間内のパス補間。
- effort: M
- 留意: グリッドが整合する `sceneAxisPosition` の軸スケールが hash 主導である事実を踏まえ、グリッド線間隔・目盛を将来 Tier2 の実 metric へ差し替える前提で設計し、grid が擬似座標を権威付けしないこと。

### Tier 2 AG忠実(形が数学)— 本ノートの中心

ここで「AG 量が空間形状を駆動する」=audit 最重要ギャップを解く。各案は実データ接地と新規データ要否を明記する。

**T2-1 コホモロジー次数の鉛直三層: H^0 地表 / H^1 中層リボン / H^2 沈黙の天井** ← 最有力(高接地・新規データ不要)
- 見える像: シーンが3つの水平帯に物理分割される。最下層(y≈-20)=H^0: context 球と atomGlyph、source_backed が静かに発光。中層(y≈0〜30)=H^1: `cocycleRibbon` の supportEdge が頂点パッチ間を結ぶ捻れたリボンとして浮き、`value=1` の mismatch 辺だけ太く明るく、閉路があれば closureGap が「閉じない帯」になる(視覚の主役)。最上層(y≈55)=H^2: nerve の triple-overlap 三角面が極薄の半透明ガラス面として頭上に浮かぶが色も verdict も載らない「意図的な灰色の沈黙面」。
- AG概念: コホモロジー次数 H^0/H^1/H^2 の階層(part_4 §4 意味4.2)、系12.3 `H^1(U,k)=b_1(N(U))`。headline は `MEASURED_H1_OBSTRUCTION_UNDER_PROFILE`。
- Three.js実装方針: `renderNerveGeometry`/`renderCocycleRibbon` を新規 `cohomologyDegreeLayer(degree)` で y バンドへ強制配置し、`sceneAxisPosition` の hash 由来 y を degree 固定 y で上書き。中層 tube radius=`lerp(0.4, 2.2, edge.value)`。天井は `MeshPhysicalMaterial({transmission:0.9, opacity:0.12, color:0x6b7280, depthWrite:false})` の「沈黙のガラス」。selective bloom は H^1 リボン emissive のみ。
- 駆動データ: **すべて v2 artifact に実在・新規データ不要**。`nerve.vertices/edges/triangles`(`triangle.sharedAtomRefs`, `coherenceClaim='not_visualized'`, `h2CoherenceVisualized=false`)、`cocycleRibbon.supportEdges[].value`、`atomGlyphs[].semanticAnchor`。
- 3D必然: degree の階層性は本質的に「縦の積み重ね」。2Dで3層を潰すと所属が混線する。天井ガラスは「頭上にあるが触れない層」という2Dでは出せない空間隠喩。
- effort: L
- 接地強化(追加データ不要): (1) 凡例に `edge.value` が `len(supportAtomRefs)%2` の離散 mismatch パリティ marker であり連続コホモロジー量ではない旨を明記し、太さ・bloom を「H^1 強度の連続スケール」と誤読させない。(2) H^2 ガラスは hover/選択でも verdict テキストを出さず `sharedAtomRefs` 数の事実提示に留める。

**T2-2 実測曲率場の heightmap 曲面(signedCurvature が膜を変形し lawful locus が谷になる)** ← 本命(audit 中核ギャップを直接解消)
- 見える像: 現 `locusField` の「個別シリンダー柱」を一枚の弾性膜に置換。`signedCurvature>0` の cell は山、`<0` は谷、`measuredZeroRegion` は膜が y=0 に接地する平らな盆地(=lawful locus、零点集合)。色は `harmonicMass` のヒートマップ、`distanceToFlatness` が谷への落差。`blockedRegion` は補間せず破れた縁(blocked_unmeasured)として残す。現在の architecture section を1つの光る点で示し、盆地(lawful)上か斜面(curvature>0)上かが一目で分かる。
- AG概念: 曲率場 = obstruction valuation `κ_U(X)`(part_7 §7.2)、lawful locus = 零点集合 `Flat_U(X)=V(I_Ob)`(part_3 §6-7)、Hodge debt / distance-to-flatness(part_8 §8.3, §8.5-8.7)。near-flat ≠ lawful を段差で区別(原則10.3)。
- Three.js実装方針: `renderLocusField`(L1648)を全面改修。fieldRows を x ソートし `BufferGeometry` 格子の頂点 y を `signedCurvature` で IDW 補間、`computeVertexNormals()` で連続法線。`vertexColors` で `harmonicMass` を `Lut('cooltowarm')` 着色。SSAO で谷の窪みを深める。`measuredZeroRegion` は y クランプ+弱 emissive、`blockedRegion` は三角形を間引いて穴+破線縁。
- 駆動データ: **v2 viewer artifact に runtime 実在を実測確認済み**(laplacian fixture を analyze で materialize: `signedCurvature` `[1.0,-1.0]`, `harmonicMass`/`distanceToFlatness` が出力)。新規データ不要。
- 3D必然: 曲率はスカラー場の「曲がり」で、膜を実際に変形させるのが定義の可視化。零点集合=平らな盆地、障害=山、未測定=穴の3状態は2D等高線では near-flat/flat/blocked を取り違えさせる。
- effort: L
- 接地強化(acceptance 必須): (A) 測定セル(`signedCurvature` を持つ fieldRow)を離散頂点として明示し、IDW 補間面は「measured 点を結ぶ window であり点間は測定でない」と non-claim 明記(補間が形を捏造して見えるのを防ぐ)。(B) `measuredZeroRegions` は verdict 由来で x 座標を持たないため「zeroRegion の x 範囲で y=0 接地」という x 対応を仮定せず、盆地は `signedCurvature≈0` のセル位置から導く(または Rust 側で zeroRegion に field x ヒントを出す小改修を**別 Issue**で切る)。(C) より豊かな膜には cell を増やした密な archmap fixture が要る(現 laplacian fixture は 2-3 点で地形が痩せる)。

**T2-3 Čech 神経の本物の単体複体(triple 被覆を塗りつぶし b_1 ループを光る閉路に)** ← 忠実性最高(系12.3 に逐語接地)
- 見える像: context = 球頂点(半径∝`atomRefs` 数)、pairwise overlap = 辺チューブ(太さ∝`supportAtomRefs` 数)、triple overlap = `sharedAtomRefs` を持つ塗り三角面。核心は b_1: nerve グラフの独立サイクルをグラフ理論で抽出し、その閉路を1本の光るループで縁取る(これが `H^1(U,k)≅b_1` の幾何的本体)。`value=1` の mismatch 辺が閉路を closureGap として「閉じなくさせている」箇所を強調。塗り三角面は coherence の色を付けない(沈黙)。
- AG概念: Čech 神経 N(U) と高次単体(part_4 §3 §12)、**系12.3 `H^1(U,k)≅b_1(N(U))`**(part_4 L1415-1432)。H^1 一次 verdict 軸。
- Three.js実装方針: 新規 `renderNerveSimplicialComplex`。b_1 抽出は spanning tree + non-tree edge ごとの基本サイクル復元(union-find + BFS、80辺上限なので軽量)。各サイクルを `CatmullRomCurve3`(閉ループ)→`TubeGeometry` の発光リング。selective bloom を発光リングのみに。
- 駆動データ: v2 artifact に実在(base archmap_v2 fixture で triangle 確認済)。`nerve.vertices[].atomRefs` / `edges[].supportAtomRefs/.value` / `triangles[].sharedAtomRefs`。b_1 は viewer 側の純粋な位相計算で導出(新規 Rust データ不要、入力 contract を拡張しない)。
- 3D必然: 単体複体は次元を持つ幾何対象。三角面で穴が「塞がれる/残る」様子と b_1 ループの絡みは2Dグラフでは辺の交差で潰れる。`H^1≅b_1` を抽象スコアでなく「実際に光る閉路の本数」として見せられる。
- effort: M
- 接地強化: [A] viewer 側 b_1 は「定数係数 k・標準 restriction 下の N(U) の reading」であり、MeasurementProfile に相対化された headline H^1 verdict とは**別 reading** である旨を loop 近傍に minimal boundary として明記(part_8 §3.3, 原則2.5/4.4)。[B] filled/unfilled の判定は triangle boundary で商を取った 2-複体の b_1 として実装。**推奨第三案**: 既存 `reduced_simplicial_homology_f2`(ag_measurement.rs L5633)を nerve に適用して Rust 側で b_1 を出し、viewer は ref を描くだけにすれば JS 再実装のバグ余地が消える(acceptance に併記)。

**T2-4 Čech 神経を呼吸する被覆束に(signedCurvature 駆動の fiber bundle + H^1 holonomy seam)**
- 見える像: nerve の各 vertex(context パッチ)が base 円盤になり、その上に section を表す縦のファイバー柱が立つ。柱の高さ・色は `locusField.fieldRows` の `signedCurvature` で駆動。overlap 辺は2 base をつなぐチューブで section を平行移動し、`closureGapEncoding.visible` のとき太く発光する dashed seam。triple-overlap 三角面は灰色・無発光・透明=意図的沈黙。
- AG概念: 被覆 `{W_i→W}` と sheaf section を base 上の色付き fiber bundle として(part_2 §6-8, part_4 §3 §12, 系12.3)。
- Three.js実装方針: `renderNerveGeometry`(L1467)を base+fiber bundle に拡張。fiber 柱は InstancedMesh + `setColorAt`。closureGap seam と `signedCurvature>閾値` の柱のみ selective bloom。
- 駆動データ: **要新規 fixture(現行 fixture は排他で両立しない)**。laplacian fixture(`signedCurvature` あり/nerve・seam なし)と cech_h1 fixture(nerve・seam あり/curvature なし)が排他。`nerve`/`cocycleRibbon`/`locusField.fieldRows[].signedCurvature` は各々 v2 実在だが**同一 packet に共起しない**。
- 3D必然: fiber bundle は base × fiber の積空間そのもので、平行移動の holonomy ズレは閉路を一周する3Dパスでしか見えない。
- effort: L
- 接地強化(acceptance 必須): (1) cover を持つ archmap に `graph-laplacian-hodge-proxy@1` reading を同時付与し `nerve.vertices` と `locusField.fieldRows[].signedCurvature` を共存させる新 fixture を追加。(2) 共起時に `fieldRows.cellRef→nerve vertex(contextRef/atomRefs)` へ fiber を結合する写像を viewer 側で定義。(3) curvature 未測定時の valence degrade は色温度オフ=明示沈黙にし「curvature の代わり」と誤読させない。

**T2-5 二つの lawful loci の交差と非横断 residue(Tor_1 質量がもう一方の軸へ移送される)**
- 見える像: 二つの法世界(`lawPair: law:checkout / law:inventory`)の lawful locus を交わる2枚の半透明曲面で描く。共有 common ambient を交差線として可視化。横断的なら交差線は鋭く residue ゼロ。非横断(`measured_nonzero=Tor_1≠0`)のとき交差部に「綺麗に消えずに残る余剰の塊」=transferred obstruction が膨らみ、repair で一方の軸を動かすと質量がもう一方の軸へ流れる。高次 Tor は描かず凡例に一行だけ「高次は沈黙」。
- AG概念: derived/repair とコボルディズム的移送(part_5)、`LawConflict_1=Tor_1`。
- Three.js実装方針: 新規 scene `law-conflict-tor`(`viewerVisualScenes` に kind=law_conflict が既存・geometry 未配線)と `renderLawConflictIntersection`。lawful locus を緩い `PlaneGeometry` 2枚、common ambient を2平面の解析的交線(`LineGeometry`)で。質量移送は既存 `updateRepairMorphAnimation` の lerp 機構を流用。
- 駆動データ: **一部新規データ要**。`ag.law-conflict-tor@1` 評価器が `verdict=measured_nonzero` と `computedInvariants.commonAmbient`(`ambientRef/atomRef/lawPair/sourceRefs`)を実出力(tor fixture で確認)。だが `commonAmbient/lawPair` は packet にあるが `aatGeometryOverlays` に未投影。`build_measurement_viewer_data_v1` 周辺 + `attach_gluing_scene_geometry` の law-conflict-tor arm に projection を追加する必要がある。
- 3D必然: 横断/非横断は交差理論そのもので、2枚の余次元曲面が「綺麗に交わるか余剰を残すか」は3次元配置でしか正しく見えない。
- effort: XL
- 接地強化: residue 球の膨らみ/移送フロー量は LawConflict class 本数・共有 support 数など packet 実測の**離散量**に束ね、連続質量スカラーを捏造しない(膨らみは verdict ではなく projection と凡例明記)。各曲面は連続サンプルが packet に無いため `PlaneGeometry` 近似である旨を non-claim に明示。

**T2-6 周期 Stokes 会計メーター(閉路の積分蓄積と residual=0 の肯定的整合)**
- 見える像: `cycleBasis` の各サイクルを閉ループ(リング)として描く。リングに沿って周回する光の弧が流れ、`periodPairingMatrix` の値が「一周で蓄積する積分量」としてメーターに現れる。Stokes 会計は各辺に正負フロー矢印を流し、`dΩintegral` と `boundaryPeriod` が一致して residual=0 のとき辺が緑に整合し、中央に「Stokes 恒等式 checked, max residual 0.0」という肯定的結論を控えめに据える。
- AG概念: 周期/積分サイクルと Stokes 会計(part_7 §5.2, part_4 §13, §9.4)。肯定的 bounded conclusion = `stokesAudit.maxAbsoluteResidual=0`。
- Three.js実装方針: 新規 scene `period-stokes` と `renderPeriodMeter`。周回弧は `animate()` の時間 t で開始角を回す。selective bloom を周回弧に。`modelRelative=true`/`nonConclusion`(構造的 verdict でない)を凡例に明記。
- 駆動データ: **要新規データ配線**。`analytic:period-stokes` の `cycleBasis/forms/periodPairingMatrix/stokesAudit.pairs[].(dOmegaIntegral, boundaryPeriod, residual)/maxAbsoluteResidual/status='checked'` を `evaluate_period_stokes_v1` が実出力(`ag_measurement.rs:1123-1156`, residual>1e-9 でハードエラーなので `checked` は真に residual=0)。だが v2 `aatGeometryOverlays` に未投影。`build_measurement_viewer_data_v1` へ `aatGeometryOverlays.periodStokes` 投影を追加する必要がある。
- 3D必然: 周期 pairing は「閉路を一周して蓄積する量」で、円環の幾何が本質。2Dでは積分経路の向きと符号が読みづらい。
- effort: XL
- 接地強化: 専用 profile(`ag.period-stokes` 行)でしか `checked` にならないため、一般 packet での空表示時の沈黙挙動(赤エラー化しない)を AC に含める。`modelRelative` な擬円周モデル相対量を絶対 period と誤読させない注記を必須化。

### Tier 3 時間と操作

被写体が Tier 2 で意味駆動になって初めて「動いたとき形が読める」に到達する。Tier 3 単独では美しいシャッフルに堕する危険があるため、Tier 2 とセット運用を前提とする。

**T3-1 view mode 間のレイアウト morph(スパイラル再配色でなく幾何の連続変形で見せる)** ← audit 最重要指摘への正面回答
- 見える像: view mode 切替で同じ atom 群が消えて再生成されず、現レイアウトから次レイアウトへ各点が滑らかに流れて再配置される(curvature 高さ場→spectrum 峰→nerve パッチへ連続 morph)。点の軌跡で「同じ対象を別の reading で見ている」が体感できる。
- AG概念: geometry first / representation as window(part_7)。
- Three.js実装方針: `renderScene` 全 clear→再構築(L2899)を改め、atom InstancedMesh(L1146)のインスタンス位置を破棄せず次 view の `nodePosition` へ `easeInOutCubic` 補間。geometry overlay は morph 中 crossfade。カメラも scene 別推奨へ lerp + lookAt slerp(900ms Clock 駆動)。
- 駆動データ: `atomNodes` / `axisMetricBindings` / 各 view の nodePosition 系。新規不要。
- 3D必然: 同一対象の複数 reading 間の対応は「どの点がどこへ動くか」の軌跡で示され、2Dでは view 切替がカット編集になり対応が切れる。
- effort: M
- **必須前提**: `axisMetricBindings` の実 metric を主係数化し hash jitter を従に下げるレイアウト係数再調整(demote-hash)を独立 acceptance criterion として切り出す。これが伴って初めて morph が「同じ atom を別 reading で見る」を意味として駆動する。morph 軌跡を verdict として読ませない non-claim を併記。

**T3-2 Holonomy traversal(フレームをループに沿って運び「閉じなさ」をアニメで見せる)**
- 見える像: cocycle ribbon の CatmullRom チューブに沿って小さなフレーム三面体が周回し、一巡して戻ったとき初期姿勢に対して回転がズレて重ならない。`closureGapEncoding.visible` のループだけ末端でギャップマーカーが明滅。閉じる(measured_zero)ループはフレームがピタリ重なって静止。常時「restriction/cover path の探索ビュー」ラベル。
- AG概念: boundary holonomy / monodromy(part_4 §9, part_6 §10-11)。
- Three.js実装方針: 既存 `renderCocycleRibbon` の `CatmullRomCurve3` curve を保持し、`animate()` 内で `getPointAt(t)`/`getTangentAt(t)` でフレームを周回。t が 1 を跨ぐ瞬間に始点ゴーストを残置。
- 駆動データ: `cocycleRibbon.supportEdges[].value` / `closureGapEncoding.visible`(実在)。**ズレ角の精密駆動には holonomy residual スカラーが v2 未出力**なので、`gluing_geometry_projection_v1` の `closureGapEncoding` に `holonomyTwist` スカラー(`BoundaryHolonomyAxisResidualV0` を v0→v2 配線、または `aggregateReadings.HolMass` を edge へ写す)を新規追加が望ましい。なければ parity 由来の離散 twist に留め「unmeasured magnitude」注記。
- 3D必然: holonomy は閉路を一周した姿勢のズレ=SO(3) の要素。2Dでは閉路と回転ズレを同時に表せない。
- effort: M(配線込みなら L 寄り)

**T3-3 cohomology degree スクラブ(H^0/H^1/H^2 層を時間スライダーで剥がす)**
- 見える像: 縦の degree スライダー(0→1→2)。0 で地表 H^0、1 へスクラブすると cocycle ribbon と holonomy seam が浮上して主役化、中心は SAFE 系結論バッジ。2 で nerve 三角面が薄く立ち上がるが色なし灰色のまま「coherence は測っていない」沈黙ラベルだけ。
- AG概念: コホモロジー次数の階層、`h2CoherenceVisualized=false`。
- Three.js実装方針: 3 Group(layerH0/H1/H2)に振り分け、slider 値 s∈[0,2] に `smoothstep` 補間、focus 層以外は opacity*0.25(focus+context)。
- 駆動データ: H0 は `atomGlyphs`/`atomNodes`/`locusField.fieldRows`(注: `obstructionCircuits` は v2 未出力なので使わない)、H1 は `cocycleRibbon`/`nerve.edges`、H2 は `nerve.triangles`/conclusion code。新規不要(H0 のデータ源訂正が条件)。
- 3D必然: degree は積層構造。スクラブで層が高さ方向に剥離する様は3Dの積層でしか表せない。
- effort: M

**T3-4 findings シネマティックツアー(tourState を活かした自動カメラ巡回)**
- 見える像: Start tour でカメラが各ステップの highlightRefs へシネマティックに飛び、対象を中央に据え focus+context で他を減光。各ステップで該当幾何がパルス発光、字幕がローワーサード。最終ステップは肯定的結論バッジへ寄って締める。手動ドラッグで pause、Resume で再開。
- AG概念: H^1 一次 verdict を中心とした guided reading。
- Three.js実装方針: 既存 `activeTourState`(L975)/`startTour`(L3062)/`renderTourStep`(L3073)を拡張。highlightRefs から `userData.item` を逆引きし world 座標へ camera/target を lerp トゥイーン。
- 駆動データ: `tours[].steps[].sceneId/caption/highlightRefs`(実在)、conclusion code。新規不要。highlightRefs から座標が引けない場合は scene 全景にフォールバック(沈黙を捏造で埋めない)。
- 3D必然: 寄る・旋回する・減光で隔離するは立体空間でのみ意味を持つ。
- effort: M
- 接地強化: caption は packet 由来 `step.caption` を逸脱せず viewer 側で煽り文言を創作しない。focus+context の減光下限を設け H^2 三角面・blocked 領域を「隠す」のでなく「控えめに残す」。

**T3-5 貼り合わせ assembly(パッチが飛来して snap、H^1 seam では snap し損ねる)**
- 見える像: scene 再生時、nerve の頂点パッチが外側から定位置へ飛来し overlap 辺で吸着して一枚に綴じる。`value=0` の辺は密着、`value=1` の辺は微小隙間を残して振動する seam。完成後 b_1 個の閉路が一拍発光。
- AG概念: descent / gluing(part_2 §9-11)。
- Three.js実装方針: `renderNerveGeometry`(L1467)の頂点に開始位置(法線方向外側 +120)と目標位置を userData 格納し `easeOutBack` で飛来→snap。
- 駆動データ: `nerve.vertices/edges.value` / `cocycleRibbon.supportEdges`。新規不要。
- 3D必然: 貼り合わせは局所パッチを大域へ綴じる空間操作。
- effort: L
- **必須の境界修正2点**: (1) b_1 閉路発光は viewer 側 graph cycle basis であって packet の H^1 量ではない。「graph cycle, H^1 verdict ではない」non-claim を発光近傍に併記。(2) `edge.value` は `(support_atom_refs.len() % 2)` の parity marker なので seam を「貼り合わない経路」と断じず「value(parity)で色分けした overlap seam」と legend に明示。

### Tier 4 新規・大胆

新規 reading を初めて空間化する、または既存案を質的に引き上げる大胆案。effort が高く Rust 配線を伴うものが多い。

**T4-1 スペクトル峰の固有地形と再発 hotspot(transfer operator の Perron-Frobenius モードを峰に)** ← 要再設計
- 見える像: transfer operator の固有モードが地形の峰として並び、spectral radius が最大の主モードが最も高く光る。`topHotspots` が峰の頂で脈動発光し「再発する障害の中心」を示す。`transferEdges` の weight が峰の間をつなぐ尾根線。
- AG概念: スペクトル/固有値地形と curvature transfer spectrum(part_7 §3.5-3.6, part_8 §8 §8.9)、定理候補8.10。
- 駆動データ: **要新規データ配線**。`ArchitectureSpectrumReport.topHotspots`/`topEigenmodes`/`CurvatureTransferReading` は measurement packet に実在するが v2 `aatGeometryOverlays` に未出力。
- effort: XL
- **採用前提の再設計(現案のままでは不可)**: (1) 視覚的中心を hotspot ではなく measured-zero の「平らで安定した lawful plain」に置き、峰は局所的逸脱として副次的に描く(障害峰の主役化は規律違反、`NO_MEASURED_H1_OBSTRUCTION` を中心化)。(2) **`curvatureStatus` フィールドは実 packet の `topHotspots[]` に存在しない**(捏造)ので使わず、report レベルの `status:needsReview`/`measurementStatus:proxy` を visual に明示し analytic-reading-not-verdict boundary を付す。(3) measured-zero(cv=0)と unmeasured を別色・別レイヤで区別し measured-zero を「描かず沈黙」にしない(実 fixture の hotspot は `[1,0,0,0]` で 3/4 が cv=0=SAFE)。(4) `spectralRadius "1.000"` は文字列なので数値パース経路を Rust 側で明示し proxy を失わない。(5) 水平配置を `axisRef` ベースの決定論配置にして golden-angle 擬似ランダム依存を断つ。

**T4-2 Repair を obstruction cage から lawful locus への support repair morph に(supportVariables 座標空間で連続変形)**
- 見える像: `forbiddenCages[].supportVariables`(例 `x_checkout/x_inventory/x_payment`)を実座標軸として張った部分空間に、各 cage が壊れた線の simplex として浮く。repairMorph 再生で fromAtomRefs の cage が toCandidate へ向かって連続変形し、支持変数から外れた軸の cage が緑の lawful 領域に着地。常時 nonClaim「not automatic repair / lower-bound inspection aid」。
- AG概念: support repair(part_5 L712)、square-free 障害イデアルの minimal forbidden support を coordinate subspace arrangement の cage として(Stanley-Reisner regime, 定理5.6C / part_3 L697-724)。
- Three.js実装方針: `renderRepairMorphs`(L1723)と `renderForbiddenCages`(L1696)を統合。cage は `supportVariables.length` 次元を3軸へ写像(2変数→辺、3変数→三角形 simplex)。morph は現 lerp を頂点モーフへ拡張。
- 駆動データ: 現状データで駆動可。`forbiddenCages[].{supportVariables,atomRefs,lineRole}` / `repairMorphs[].{fromAtomRefs,fromCageRefs,toCandidateRef,samplePhase,supportVariables,nonClaim}`(square_free fixture で和集合ちょうど3変数を確認)。新規 Rust 変更不要。
- 3D必然: repair は obstruction 配置空間内の連続経路。`supportVariables` を実座標軸にすると「どの変数を落とせば lawful か」が空間位置として読める。
- effort: L
- **必須補強**: (1)「cobordism」「mass-preserving / 質量を保ったまま」を**全面削除**(理論に存在せず、part_5 L43 の repair=obstruction の移動・解消・転送(非保存)と矛盾する捏造)。正しい語りは「support repair: 支持変数を落とす連続変形」。(2) 肯定的 bounded conclusion を視覚的中心に保つ規律を明記し、緑の lawful 着地面=Flat_U を結論の視覚中心に。(3) supportVariables 和集合が4変数以上での3軸写像方針を定義(hash 退行を禁じる)。

**T4-3 repair morph の質量移送(一方の谷を埋めると他方の軸に obstruction が転送される。自動修復ではない)**
- 見える像: repair morph 再生で forbidden cage から lawful locus 候補へ向かう矢印に沿って質量塊が流れ谷を埋めるが、`targetAxis` を埋めるのと連動して `transferredObstructionRefs` が指す別軸の locus 高さが同時に盛り上がる(質量が消えず移送)。`protectedAxisMovement` の軸は保護される。常時「not automatic repair / lower-bound」ラベル。
- AG概念: derived/repair と `LawConflict_1=Tor_1`(part_5)、transferredObstruction/transportDistance。高次 Tor は沈黙。
- 駆動データ: `repairMorphs[]` 本体は v2 実在。**連動先の `transferredObstructionRefs`/`transportDistance`/`targetAxisDecrease`/`protectedAxisMovement` は v2 packet 未配線**(`CurvatureMassReading` 由来)。`build_measurement_viewer_data_v1` の repairMorphs へ新規追加が必要。なければ単軸 morph(現状)に留め他軸連動は出さない(捏造しない)。
- effort: M(配線込みなら L 寄り)
- 注意: 連動データが無い場合は #2082 UC5 と重複するため、他軸連動の Rust 配線を伴わないなら本案は採らない。

---

## 境界規律チェック

各 tier が CLAUDE.md の境界規律(捏造しない/沈黙を沈黙として描く/肯定的結論を中心に/Lean 対応を要求しない)をどう守るかを示す。

| 規律 | Tier 1 | Tier 2 | Tier 3 | Tier 4 |
| --- | --- | --- | --- | --- |
| 捏造しない | 全案 新規データ不要、描画品質のみ | T2-1/2/3 は v2 実在データのみ。T2-4/5/6 は新規データ要を**正直に開示**し配線前提を明記 | 全案 既存データ。T3-1 demote-hash は係数再調整であり捏造でない | T4 は Rust 配線前提を明記。T4-1 の `curvatureStatus` 捏造、T4-2 の mass-preserving 捏造を**削除**条件 |
| 沈黙を沈黙として描く | T1-3/T1-4 が中核(現状の赤エラー化 blockedRegions `0xff6b6b` を撤廃し、霧の奥/すりガラスへ) | T2-1 の H^2 ガラス天井、T2-2 の破れた穴 | T3-3 の H^2 灰色面、T3-5 の seam は parity 注記 | T4-1 の measured-zero と unmeasured の分離 |
| 肯定的結論を中心に | T1-2 は計測済み H^1 のみ発光、T1-6 はヴィネットで中心へ視線 | T2-1 は H^1 中層を主役、T2-6 は residual=0 整合を中央 | T3-4 ツアー終点を結論バッジに | T4-1 は lawful plain を中心へ再設計、T4-2 は Flat_U 着地面を中心へ |
| Lean 対応を要求しない | 全 tier 共通。可視化はすべて MeasurementProfile/ArchMap/LawPolicy に相対化された reading として提示し、絶対的 architecture debt を主張しない |

設計指針として2点を強調する:

**「沈黙の可視化」の設計指針**: 沈黙(H^2 coherence / unmeasured / not_computed)は赤エラー・残タスク・欠落警告として主役化しない。具体言語は3つ:
1. **霧の奥への後退**(T1-3): depth で measured を手前に、silence を遠景に。
2. **すりガラス/灰色ガラス**(T1-4, T2-1, T3-3): 存在は描くが verdict も色も付けない。emissive を measured 専用に予約。
3. **破れた縁/穴**(T2-2): 補間で滑らかに埋めず blocked_unmeasured として残す。
これは現状コードが沈黙を `0xff6b6b` 赤で表示している境界違反(L1640/1687)の是正でもある。

**「SAFE_WITHIN_POLICY を中心に」の設計指針**: headline conclusion code(`NO_MEASURED_H1_OBSTRUCTION_UNDER_PROFILE` / `MEASURED_H1_OBSTRUCTION_UNDER_PROFILE`)を scene の重心・焦点面・ツアー終点に据える。bloom/発光は measured 証拠に限定し、長い non-conclusion 一覧を主役化しない。`NO_MEASURED_H1` のケースで「閉じている overlap = lawful」を淡い肯定色で主役化する設計(T2-1 接地強化 A)が、SAFE を画面の地にする鍵。

---

## 接地と新規データ

Tier 2/4 のうち、現状パケットで描けるものと Rust(`ag_measurement.rs`)側に新規フィールドが要るものを分ける。

### 現状 v2 パケットで描ける(新規データ不要)

- **T2-1 鉛直三層**: `nerve.vertices/edges/triangles`, `cocycleRibbon.supportEdges[].value`, `closureGapEncoding`, `atomGlyphs[].semanticAnchor`(全 fixture で確認)。
- **T2-2 曲率膜**: `locusField.fieldRows[].{signedCurvature,harmonicMass,distanceToFlatness,height,status}`, `measuredZeroRegions`, `blockedRegions`(laplacian fixture を analyze で runtime 実在を実測確認)。
- **T2-3 単体複体 b_1**: `nerve.{vertices,edges,triangles}`。b_1 は viewer 側の純粋な位相計算で導出。
- **T4-2 support repair morph**: `forbiddenCages[].supportVariables`, `repairMorphs[].{fromAtomRefs,toCandidateRef,supportVariables,nonClaim}`(square_free fixture)。

### Rust 側に新規フィールドが要る(最小の追加データ案)

- **T2-4 fiber bundle**: cover と `signedCurvature` を**同一 packet に共起させる新 fixture**(`graph-laplacian-hodge-proxy@1` reading を cover 付き archmap に付与)。`nerve.vertices` と `locusField.fieldRows[].cellRef` を結ぶ写像が前提。
- **T2-5 Tor 交差**: `aatGeometryOverlays.lawConflict` 投影を追加(`commonAmbient.{ambientRef,atomRef,lawPair,sourceRefs}` を `build_measurement_viewer_data_v1` 周辺 + `attach_gluing_scene_geometry` の law-conflict-tor arm に配線)。
- **T2-6 周期 Stokes**: `aatGeometryOverlays.periodStokes` 投影を追加(`cycleBasis/periodPairingMatrix/stokesAudit.pairs/maxAbsoluteResidual/status` を v2 へ運ぶ)。専用 profile 不在時の空表示=沈黙挙動も実装。
- **T3-2 holonomy twist**: `gluing_geometry_projection_v1` の `closureGapEncoding` に `holonomyTwist` スカラー(`BoundaryHolonomyAxisResidualV0` を v0→v2 配線、または `aggregateReadings.HolMass` を edge へ写す)。
- **T3-5 / T2-3 真の H^1**: 任意で `reduced_simplicial_homology_f2`(L5633)を nerve に適用し Rust 側で b_1 を出す配線(JS 再実装のバグ余地を消す)。`edge.value` の parity marker を真の coboundary 判定(`edge_cochain_is_coboundary` 活用)に置換する `coboundaryStatus` を別 Issue で。
- **T4-1 spectrum**: `aatGeometryOverlays` へ `topHotspots/topEigenmodes/transferEdges` を投影。`spectralRadius` の文字列→数値パースを Rust 側で明示。
- **T4-3 質量移送**: repairMorphs へ `transferredObstructionRefs/transportDistance/targetAxisDecrease/protectedAxisMovement` を追加。

これらの追加はいずれも「測られた量を viewer へ運ぶ projection」であって、新規 verdict を作らない。`gluing_geometry_projection_v1` の `projectionBoundary`(no structural verdict)と `cli.rs:1297-1301` の test-locked 境界を維持する。T2-5/T4-1/T4-3 は scene への per-object verdict / scalar 配線を伴うため、この test 文言の意図を維持しつつ拡張する設計合意を PRD に明記する。

---

## 棚卸し(見送り)

検証で棄却された案を、失敗ではなく沈黙として正直に残す。

- **周期メーターと Stokes 会計を「閉路を一周して period を符号付きに蓄積する周回会計」として1オブジェクトに合成する案**: 棄却。理由3点が measurement packet と構造的に整合しない。(1) `cech_edge.value` は cocycle 値でなく parity marker(L5816)。(2) Stokes 監査の residual は常に 0 の恒等チェック(L4636-4643)で「残る周期≠0」の動態を生まない。(3) period 評価器の唯一の fixture は `b_1=0` の単一 context・cover でループ自体が存在しない。粒子が流れる nerve ループ(cech 由来)・矢印の符号(laplacian 由来)・周回メーター(period 由来)は3つの独立評価器の別 cover reading であり、これを1オブジェクトに合成するのは入力 contract の拡張に当たる。

  なお **T2-6(周期 Stokes 会計メーター)はこの棄却案とは別物**で、period 評価器の実フィールド(`stokesAudit.maxAbsoluteResidual=0` の肯定的整合)に単独で接地し、「residual=0 の整合」を中央に据える形なら採用可とした。混同しないこと。

- **T3 曲率場の呼吸とフローライン**のうち**フローライン部分**: 棄却(脈動は残す)。「curvature 降下方向=lawful locus 方向へ流れ落ちる」の降下方向(勾配ベクトル)は packet に存在せず(`locus_field_projection` は座標も勾配も持たない)、「最寄り zeroRegion」も `sceneAxisPosition` の hash 合成座標で決まるため、流れの方向と落下先は viewer 側で捏造した routing になる。脈動(振幅=height、色温度=colorRole)と blockedRegions の静止灰色=沈黙のみに縮約すれば採用可。

- **構造的 verdict で全幾何の形状を支配的に駆動する案(T2-x として一度検討)**: 条件付き格下げ。locusField の `analytic_reading` 行(`signedCurvature` 等)を verdict の隆起と同じ鉛直言語に混ぜると「analytic reading を structural verdict と取り違えさせない」(part_8 §3.3)に正面から反する。かつ `cli.rs:1297-1301` の test-locked「no structural verdict」境界と衝突する。premium レンダリング層(T1-1 相当)だけ即採用し、verdict 形状言語は「支配的ドライバ」でなく補助エンコード(measured_zero の接地影強調/unmeasured のガラス)に格下げ。本気で verdict 駆動するなら per-object verdictRef を出す別 PRD が前提。

---

## PRD 候補

このノートから切り出せる PRD を複数の framing(スコープの切り方)で提示する。各 framing の「問い」案・含む tier・受け入れ条件の方向性を述べる。

### Framing 1: 「器を premium に」(rendering-fidelity 単独)
- 問い案: 「ArchSig viewer が製品3Dツールに見えないのはなぜか。新規データを一切触らず、レンダリングパイプラインの欠落(toneMapping/IBL/shadow/bloom/fog)だけで、どこまで premium に底上げできるか。」
- 含む tier: Tier 1 全部(T1-1〜T1-6)。
- 受け入れ条件の方向性: `toneMapping=ACESFilmic` 設定、`scene.environment` 設定、接地影が出る、Selective Bloom が計測済み H^1 のみに当たる、blockedRegions の赤エラー化が撤廃される、no-build 単一 HTML が維持される。golden UX 視覚回帰 fixture との整合。Rust 変更ゼロ。
- 性質: 最小リスク・最速。ただし**問いの核(形が意味を駆動しない)は解かない**ことを PRD 冒頭に明記し、Framing 2 を後続フェーズに置く約束をする。

### Framing 2: 「形が数学である」(ag-faithful、新規データ不要の範囲)← 推奨
- 問い案: 「view mode を変えても『同じスパイラルの再配色』に見えるのは、curvature/holonomy/cocycle の実測量が空間形状を駆動せず hashText が支配しているからである。現状 v2 パケットの実データだけで、AG 量が形を駆動する viewer をどこまで作れるか。」
- 含む tier: Tier 2 のうち**新規データ不要な T2-1(鉛直三層)/T2-2(曲率膜)/T2-3(単体複体 b_1)/T4-2(support repair morph)** + その前提として Tier 1 の最小セット(T1-1 PBR基盤、T1-2 selective bloom、T1-4 H^2 すりガラス)。
- 受け入れ条件の方向性: degree が鉛直階層を駆動(hash 由来 y を degree 固定 y で上書き)、`signedCurvature` が膜を変形し measuredZeroRegion が盆地、b_1 が光る閉路として抽出される、`supportVariables` が実座標軸になる。各案に接地境界の non-claim(`edge.value` は parity marker / IDW は補間 window / b_1 は定数係数 reading)。Rust 変更ゼロまたは最小(T2-3 の任意 b_1 Rust 配線のみ)。
- 性質: audit 最重要ギャップを最大効率で解く。**本ノートの本命**。

### Framing 3: 「動かして読む」(temporal-interaction)
- 問い案: 「同じ atom が別 reading で別の形になることを、瞬間切替でなく時間軸で見せられるか。view mode morph・holonomy traversal・degree スクラブ・cinematic tour で。」
- 含む tier: Tier 3 全部(T3-1〜T3-5)。
- 受け入れ条件の方向性: view mode morph が atom 位置を破棄せず補間(demote-hash を独立 AC に)、holonomy traversal が closureGap ループで非一致を見せる、degree スクラブが H^2 を灰色沈黙に保つ、ツアーが結論バッジへ着地。morph 軌跡を verdict として読ませない non-claim。
- 性質: 体験は上がるが、**Framing 2 の demote-hash と組まないと美しいシャッフルに堕する**。Framing 2 の後続として切るのが自然。

### Framing 4: 「測定を viewer へ運ぶ」(Rust 配線を伴う AG 拡張)
- 問い案: 「measurement packet には実在するが v2 viewer artifact に未投影の reading(period-stokes / law-conflict-tor / spectrum / holonomy twist / mass transfer)を、新規 verdict を作らずに viewer へ運び、肯定的 bounded conclusion を中心に空間化できるか。」
- 含む tier: Tier 2 の T2-4/T2-5/T2-6、Tier 4 の T4-1(要再設計)/T4-3、Tier 3 の T3-2(holonomy twist 配線)。
- 受け入れ条件の方向性: `build_measurement_viewer_data_v1` への projection 追加 + schema/fixture/golden_ux/test 更新、`projectionBoundary` の「no structural verdict」維持、空 packet での沈黙挙動、各 reading の boundary 注記(modelRelative / proxy / parity / 非保存)。
- 性質: effort 最大(Rust + viewer 両面、XL 級複数)。複数 PRD に分割推奨(period-stokes / law-conflict / spectrum を別 PRD)。

---

**どの framing で PRD 化するか選んでほしい。** 推奨は Framing 2(形が数学である、新規データ不要)を本命に据え、Framing 1 の器を最小限だけ取り込む構成。Framing 3 と Framing 4 は Framing 2 が landed した後の後続フェーズに置くのが、問い(綺麗さや時間でなく「形が意味を駆動する」を主目的にする)と最も整合する。Framing 1 単独を先に出す選択肢もあるが、その場合は「核は次フェーズ」と冒頭で明記する規律が要る。
