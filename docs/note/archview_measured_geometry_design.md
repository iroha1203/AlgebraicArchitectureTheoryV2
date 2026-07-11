# ArchView 計測駆動幾何 設計ノート(方向A+B)

このノートは、ArchView の可視化を「誠実な注釈付きグラフ描画」から
「計測そのものが形になる幾何」へ進めるための設計文書である。
PR #3239(fidelity 申告・二層用語・source landing)の次の段階として、
方向A(計測駆動の座標系)と方向B(層の幾何)を定義し、実装 wave に分解する。

これは確定仕様ではなく、PRD 起草の正本となる設計ノートである。

---

## 問い

**「ArchView の画面上の形・座標・距離は、どこまで計測そのものになれるか」**

この問いを採否の判定規律として使う。新しいビュー・レイアウト・視覚チャネルは、
次の3条件を満たさない限り採用しない。

1. **駆動データが packet の実測フィールドであること。**
   viewer が新しい観測・推測・補完を行わない。
2. **数学的対応が定理として言明できること。**
   「この形はこの実測量のこの性質を表す」が、AAT AG 本文または標準的な数学の
   命題として書き下せる(例: F₂ cocycle と二重被覆の対応)。
3. **fidelity 申告で区分が書けること。**
   measured / derived / layout / decoration のどれかに一意に落ち、
   詳細パネルでチャネル別に申告できる。

現行実装で「measured」を名乗れるのは大きさ・太さ・amber・辺の存在だけであり、
座標・距離は「layout(verdict なし)」と申告している。この問いは、
その申告を「derived(実測量から一意に導出)」へ格上げできる範囲を定める。

---

## 1. 現状認識

- 位置は force-directed layout + 決定論 jitter。adjacency / membership は実在するが、
  絶対座標・距離は何も語らない(fidelity 申告どおり)。
- H¹ 障害は amber の seam(アーチ・stitch・probe)として演出されるが、
  これらは decoration であり、「閉じない」ことの幾何的実体は画面上にない。
- 数学はラベル・文言(二層用語)に住んでおり、形には住んでいない。
- ArchSig 側の packet には、形を駆動できる実測フィールドが既に揃っている
  (§2)。**本ノートの全提案は ArchSig 側の変更なしに viewer だけで実装できる。**

## 2. 原資: packet 内の実測フィールド

| 実測フィールド | packet 上の場所 | 幾何としての意味 |
| --- | --- | --- |
| 有限 poset site(restrictsTo) | `finitePosetSite.contexts[].restrictsTo` | 深さ(層化): どれだけ深い重なりか |
| nerve グラフ | `aatGeometryOverlays.nerve.edges` | 結合構造 → Laplacian スペクトル |
| nerve 2-faces | `aatGeometryOverlays.nerve.triangles` | 単体複体としての実現 |
| F₂ cochain 値 | `coverNerveProjection.edges[].value`(0/1) | 二重被覆の貼り方(捻れ) |
| cocycle support | `cocycleRibbon.supportEdges` | 障害を担う辺 |
| section 宣言値 | cech atom の `objectRef`(`section=...`) | étale 空間のファイバー点 |
| 共有 atom 数 | `nerve.edges[].supportAtomRefs` | 辺の重み候補 |

## 3. 方向A: 計測駆動の座標系

### A-1 スペクトル埋め込み(X, Z 座標)

**定義。** 選択カバーの nerve グラフ(頂点 = contexts、辺 = restriction edges)の
グラフ Laplacian `L = D − A` の固有分解をとり、非零固有値に属する固有ベクトル
v₂, v₃(Fiedler ベクトル以降)を X, Z 座標に使う。

**意味論。** スペクトル座標での近さは拡散距離(commute time)に対応する:
**画面上で近い = 実測された結合が強い**。force-directed の「なんとなく近い」と違い、
距離の読み方を legend に定理として書ける。

**決定論性の規律。**
- 固有ベクトルの符号: 座標和が正になる向きに正規化。
- 固有値縮退(対称なグラフ): 縮退空間内で頂点 id 辞書順の標準基底射影から
  Gram–Schmidt で決定論的に基底を選ぶ。
- fidelity 申告: `position (X,Z): derived — spectral embedding of the measured
  nerve, unique up to isometry and eigenvalue degeneracy`。

**非連結グラフ。** 連結成分ごとに埋め込み、成分間の相対配置は layout のまま
(成分間距離は無意味であることを legend に明記)。

### A-2 poset 層化(Y 座標)

**定義。** Y 座標 = restrictsTo poset における深さ(その context から最深要素への
最長鎖の長さ)。1セントのドリフトなら shared が最深(Y 最下)、settlement が中間、
application / runtime が上層になる。

**意味論。** 「下にあるほど多くの context に共有される重なりである」。
これは poset の実測構造そのものであり、fidelity 申告は `depth (Y): measured —
longest chain in the restriction poset`。

### A-3 距離 legend

legend に「画面距離の読み方」を常設する:
- 同一成分内の水平距離 ≈ 拡散距離(実測 nerve から導出)。
- 高さ = poset 深度(実測)。
- 成分間の距離・絶対スケール・向き: 意味なし(layout)。

### A の採否判定(問いへの回答)

条件1: nerve は実測 ✓。条件2: スペクトル埋め込みと拡散距離の対応は標準的な
スペクトルグラフ理論の定理 ✓。条件3: derived / measured / layout に分解して
申告できる ✓。

## 4. 方向B: 層の幾何を描く

### B-1 二重被覆ビュー(cocycle twist)

**数学的対応(条件2の言明)。** F₂ 係数 1-cochain `c: E → {0,1}` に対し、
二重被覆 `X_c` を「各頂点 v の上に 2 点 {v⁰, v¹} を置き、辺 (u,v) を
c=0 なら平行(u⁰–v⁰, u¹–v¹)、c=1 なら交差(u⁰–v¹, u¹–v⁰)に貼る」で定める。
このとき:

> **X_c が連結 ⟺ [c] ≠ 0 in H¹(nerve graph; F₂)。**
> c が coboundary なら X_c は 2 枚のシートに分解し、
> 非自明なら「一周すると必ずシートが入れ替わるループ」が存在する。

これは `MEASURED_H1_OBSTRUCTION_UNDER_PROFILE` の**幾何的実体**である。
「閉じない縫い目」という演出を、実際に捻れた被覆という測定由来の形で置き換える。

**描画。** gluing シーンに「twist view」トグルを追加。各 context セルの上下に
2 枚のゴーストシート(±h オフセット)を置き、`edges[].value` に従って
平行 / 交差の接続チューブを描く。障害があるとき(head)、被覆は連結な
一枚のねじれた帯(メビウス的)になり、ないとき(base / repaired)は
2 枚の平行なシートに分かれる。1セントのドリフトの 3 状態がそのまま
「分離 → 捻れて連結 → 分離」という幾何の変化になる。

**二層用語。**
- math lane: 「the F₂ cocycle defines a double cover of the nerve;
  it is connected iff the class is nonzero」
- engineer lane: 「各モジュールの帳尻の合わせ方は 2 通り(そのまま / 反転)。
  このループを一周すると必ず反転して戻ってくるので、全体で 1 つの
  整合的な選び方が存在しない」

**contract 上の位置づけ(重要)。** シート接続の計算は viewer 側の決定論的な
純関数計算だが、これは packet の cochain 値の数学的帰結の**表示**であり、
新しい structural verdict ではない(layout 計算と同格)。防御的規律として:
被覆の連結性と packet の verdict(measured_zero / nonzero)は数学的に一致する
はずだが、万一不一致を検出した場合は **packet を正**とし、twist view を
沈黙(非描画+boundary 表示)に落とす。viewer が verdict を上書きしない。

**非主張境界。** F₂・可換係数に限る。非可換 torsor / stacky descent / gerbe は
従来どおり対象外(既存境界文言を継承)。edge value は parity であり大きさではない。

### B-2 étale 空間ビュー(section fibers)

**数学的対応。** 各 context の宣言 section 値(cech sectionValue atom の
objectRef)をその context の上のファイバー点として持ち上げ、restriction 辺の
両端で値が等しいときのみ水平辺で結ぶ。これは宣言された値たちの成す
présheaf の étale 空間(の有限スケッチ)であり:

> **大域切断が存在する ⟺ 全 context を通る水平連結成分が存在する。**

1セントのドリフトの head では、3 つの丸め流儀が 3 本の途切れたレーンとして
走り、どのレーンも全体を貫けないことが見える。「どの流儀がどの範囲まで
通用して、どこで途切れるか」の絵である。

**描画。** 新シーン「Sections」。値ごとに水平レーン(高さ割当は値文字列の
辞書順で決定論的 = layout 申告)、レーンの色は値のハッシュではなく
テキストラベル(実測 objectRef)を常時表示。source landing(PR #3239)と
組み合わせ、レーンの断絶をクリックすると対立宣言とコード位置に降りられる。

**沈黙の規律。** section 値を宣言していない context のファイバーは空として
描く(点を発明しない)。値なし context を跨ぐレーンの連結は主張しない。

### B の採否判定

条件1: `edges[].value` と `objectRef` は実測 ✓。条件2: 二重被覆対応・
étale 切断対応は上記のとおり定理として言明できる ✓(B-1 は graph H¹ に
対する古典的事実、AAT 側は part4/12.3 の cover-relative 読みに従属)。
条件3: 「シートの捻れ = measured(cochain値)、シート間隔・レーン高さ = layout、
接続チューブの見た目 = decoration」と申告できる ✓。

## 5. 実装 wave

| Wave | 内容 | 主な変更 | 検証 |
| --- | --- | --- | --- |
| 1 | A-1/A-2/A-3: spectral + poset layout、距離 legend、fidelity 申告の格上げ | archview.html(layoutContexts 差し替え) | 同一 packet → 同一座標の決定論 golden。既存 fixture 5 ケース + 1セントドリフト 3 状態 |
| 2 | B-1: 二重被覆 twist view(gluing シーンのトグル) | archview.html(新 build 関数) | base=2枚分離 / head=連結 / repaired=分離 の E2E。packet verdict との一致検査 |
| 3 | B-2: étale 空間シーン「Sections」 | archview.html(新シーン+SCENE_MAP) | head で 3 レーン断絶、repaired で単一レーン貫通の E2E |

各 wave で `docs/tool/archview_gluing_geometry_contract.md` に対応条項を追記し、
`tools/archsig/tests/archview_e2e.rs` / golden UX manifest の監査対象を拡張する。
ArchSig 本体(Rust の測定・packet 生成)の変更は全 wave で不要。

## 6. 却下した代替案

- **force-directed の継続**(現行): 座標が何も語らない。A で置換。
- **t-SNE / UMAP 系の埋め込み**: 非決定論的で、距離の意味論を定理として
  言明できない。条件2で不採用。
- **Wasserstein-MDS**(transfer 費用の距離化): 実測費用は `ag.support-transfer`
  選択時にしか存在せず、cech 主体の現行デモに合わない。将来、transfer を使う
  example が整った時点でオプション埋め込みとして再検討する。
- **高次の被覆 / gerbe の可視化**: 係数を F₂ 有限から出るため条件1・2を
  満たさない。境界文言のまま沈黙。

## 7. 忠実性契約への影響(追記予定条項)

- 座標の区分に `derived`(実測量からの一意導出。up to isometry 等の
  一意性の但し書き付き)を追加する。
- viewer 側純関数計算(スペクトル分解・被覆の連結性・レーン連結)の
  位置づけ: 表示のための導出であり、verdict は常に packet が正。
- twist view / Sections ビューの非主張(automatic repair・大域 correctness・
  非可換系への言及をしない)。

## 8. 未決事項(PRD 化時に確定)

1. スペクトル埋め込みの辺重み: 一様(1)か共有 atom 数か。初期案は一様
   (重み選択も profile-relative な解釈を増やすため、まず最小で入れる)。
2. twist view のシート間隔・交差チューブの視覚語彙(decoration の範囲)。
3. 大規模 site(contexts > 数百)でのスペクトル計算コストとフォールバック
   (現行 force-directed の ITERS 打ち切りと同様の段階縮退)。
4. sequence mode(base→head→repaired 再生)で twist view を既定にするか。
