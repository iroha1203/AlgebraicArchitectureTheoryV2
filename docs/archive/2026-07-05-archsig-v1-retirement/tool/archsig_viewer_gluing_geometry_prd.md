# ArchSig Viewer Gluing Geometry PRD — 貼り合わせの歪みを幾何で見せる

Related PRDs:
- `docs/tool/archsig_v0_4_0_insight_viewer_prd.md`(R9–R17 の scene 機能を前提とする）
- `docs/tool/archsig_v0_4_0_algebraic_geometry_measurement_prd.md`（R3 Čech obstruction / R14 golden fixture を測定源とする）

Target surface:
- `tools/archsig/viewer/archsig-atom-viewer.html`
- `viewerVisualScenes`(`archsig-insight-report/v1` 内の projection）

---

## 問い

この PRD のすべての要求は、次の問いに仕える。

```text
問い:
  局所的にはすべて合法なのに、全体は歪んでいる——
  その「貼り合わせの歪み」を、誰の主観にも頼らず
  3D の幾何として見せ、エンジニアが
  where(どの cover / cocycle / atom)に着地できるか?

  core PRD: 歪みを「測る」
  本 PRD:   その歪みを「見て、誰の cocycle / hole / locus か言い当てる」
```

この問いは採否の判定規律である。ある要求・実装が「貼り合わせの歪みを幾何として立たせ、where に着地させる」ことに寄与しないなら、本 PRD のスコープに入れない。逆に、測定済みの packet 情報を幾何として読みやすくすることだけが、本 PRD の仕事である。

---

## 位置づけ

本 PRD は insight viewer PRD の **追補**であり、置き換えではない。

insight viewer PRD は、Viewer の scene 機能を定義した。

```text
insight viewer PRD の責務:
  - viewerVisualScenes / axisMapping / layers の schema を立てる
  - 各 scene が userQuestion と refs と click target を持つ
  - Insight Card / brief / boundary digest を typed surface にする
```

その機能要件は `archsig-insight-report/v1` と viewer 実装(PR #2022 / #2040）で達成された。本 PRD はその**上のレイヤー**を立てる。

```text
本 PRD の責務:
  scene の「器」は満たされた。だが幾何が立っていない。
  measurement packet が既に語っている貼り合わせ情報を、
  scatter plot から「代数幾何が幾何として立つ scene」へ引き上げる。
```

本 PRD は新しい structural verdict も新しい測定も導入しない。**表現品質**(visual richness と projection の意味）だけを対象にする。

---

## 背景と課題

現状の Viewer を実測すると、scene の器は通っているが、幾何描画はほぼ placeholder である。

```text
tools/archsig/viewer/archsig-atom-viewer.html の実測（語の出現数）:
  viewerVisualScenes : 5   （器は入った）
  axisMapping        : 4   （器は入った）
  cover patch        : 3
  overlap seam       : 1
  cocycle ribbon     : 1   （名目のみ）
  scene morph        : 0   （未実装）
```

描画の実体は次に留まる。

- atom は `SphereGeometry`(均質な球）として点配置される。
- 依存・距離は `LineSegments`(均質な線分）として描かれる。
- cover / context / overlap / cocycle / curvature / repair は、専用の幾何オブジェクトを持たない。

座標系も同様である。`axisMapping` フィールドは存在するが、軸の意味が幾何配置を駆動していない（insight viewer PRD P2「3D 空間は装飾ではなく意味を持つ座標系にする」が表面的にしか満たされていない）。

`aat_geometry_overlays`(viewer data schema の代数幾何オーバーレイ用フィールド）は空き器のまま残っている。

---

## アウトカム

本 PRD が達成されると、エンジニアは次を**目で**読める。

### UC1. 貼り合わせの歪みを、ループの閉じなさとして見る

H¹ mismatch の scene で、各辺（pairwise restriction）が整合しているのに、cocycle support のループを一周すると閉じない――その「閉じなさ」を ribbon の捻れ／発光として見る。「局所は全部 OK なのに大域で歪む」が一目で伝わる。

### UC2. cover の貼り合わせ構造を、単体複体として見る

context = 頂点、pairwise overlap = 辺、triple overlap = 塗られた三角形として nerve が立つ。「どのモジュール群がどう重なって全体を覆っているか」が形になる。

### UC3. locus を地形として、obstruction を特異点として見る

lawful locus は滑らかな面、obstruction support は尖り／穴、curvature mass は高さ場・色温度として読める。負債の集中が地形の歪みとして見える。

### UC4. atom を、内部構造を持つ幾何として見る

均質な球ではなく、fiber / carrier / valence / semantic anchor が点の幾何に反映される。「scheme の点が内部構造を持つ」感覚で、どの atom がどんな型の事実かを形から読む。

### UC5. repair を、連続変形として見る

repair candidate を、obstruction を持つ配置から lawful locus へ向かう連続変形（morph）として動かす。修復が「何をどう変形させるか」を運動として理解する。

---

## 設計原則

### P1. Visual は projection であって verdict ではない（insight viewer P8 を継承・厳守）

richness は measurement packet の情報を理解するための projection である。Viewer の描画から新しい structural verdict / curvature / cohomology class を導出してはならない。豪華さが「証明されたように見える」ことを禁じる。

### P2. Packet が語る範囲だけ描き、語らない範囲には沈黙する

Viewer は `archsig-measurement-packet/v1` と `archsig-insight-report/v1` が持つ情報だけを幾何にする。packet に無いもの（例: H² coherence、未測定 support、assumed/unknown 域）を幾何で「埋めて」はならない。沈黙すべき域は、滑らかな面ではなく明示的な blocked/unmeasured の見えとして残す。

### P3. 座標系は意味を担う

全 primary scene で `axisMapping` が実際の幾何配置を駆動し、axis HUD と legend に意味を表示する。軸は装飾ではなく projection の宣言である。

### P4. Richness は情報を増やさず、readability を上げる

本 PRD は新しい測定軸・新しい claim を足さない。既存 packet 情報を、より読みやすい幾何へ翻訳することだけを行う。情報量ではなく可読性を上げる。

### P5. 3D を操作できなくても同じ意味が読める（insight viewer R22 を継承）

幾何 richness は detail panel / insight queue のテキスト表現を置き換えない。3D を回せない読者にも同じ where が届く。

---

## 要求

### R1. Nerve geometry — cover の貼り合わせを単体複体として描く

`viewerVisualScenes` の Site/Cover scene と Cover&Gluing scene で、context を頂点、pairwise overlap を辺、triple overlap を塗られた三角形として nerve を構成する。三角形の存在は packet の cover データから導く（描画側で overlap を推測しない）。

### R2. Cocycle ribbon — H¹ mismatch をループの閉じなさとして描く

H¹ scene で、cocycle representative support を ribbon として描き、ループを一周したときの「閉じなさ」(holonomy-like の捻れ／継ぎ目）を visual encoding として固定する。これは insight viewer PRD の monodromy non-claim（monodromy verdict を復活させない、holonomy-like 表示は restriction/cover path の exploratory view に留める）を厳守する。

### R3. Locus field — curvature support / mass を地形として描く

curvature support と mass を、高さ場・色温度の field として描く。measured-zero（selected-support zero）と blocked/unmeasured を視覚的に区別し、blocked を「滑らかな lawful 面」として描かない。

### R4. Obstruction cage — minimal forbidden support を立体として描く

Obstruction scene で minimal forbidden support を cage / simplex として描き、どの atom 集合が forbidden を構成するかを形から読めるようにする。

### R5. Repair morph — repair candidate を連続変形として描く

Repair scene で、repair candidate を obstruction 配置から lawful locus への morph アニメーションとして実装する（現状 morph 0 を埋める）。insight viewer R19 の lower-bound 言語と「自動修復ではない」non-claim を常に併記する。

### R6. Atom internal glyph — atom を内部構造を持つ幾何にする

atom node の描画を、均質な球から、fiber / carrier / valence / semantic anchor を反映した glyph に拡張する。semantic anchor の欠落は blocker として（zero ではなく）見えるようにする。

### R7. 意味ある座標系 — axisMapping を幾何実装する

全 primary scene で `axisMapping` が幾何配置を駆動し、X/Y/Z の意味を axis HUD と legend に表示する。scene ごとに軸の意味が変わってよいが、必ず宣言される。

### R8. Visual encoding の意味固定（insight viewer R15 / R16 を継承）

色・形・線・透明度・厚みの意味を本 PRD の幾何全体で固定し、color だけに依存しない（形・パターンでも区別できる）。legend に全 encoding を列挙する。

### R9. Projection boundary の明示

richness が claim に昇格しないことを scene 上で明示する。large graph degradation（insight viewer R23）と object kind 別の omitted counts を、新しい幾何オブジェクトにも適用する。

---

## スコープ

- `archsig-insight-report/v1` の `viewerVisualScenes` / `layers` / `axisMapping` を消費し、`tools/archsig/viewer/archsig-atom-viewer.html` の幾何描画品質を上げる。
- 描画に必要な構造化データ（nerve の頂点・辺・三角形、cocycle support、curvature field、forbidden support、repair morph target）を、既存 packet から `aat_geometry_overlays` / insight-report projection へ橋渡しする。データが packet に無い幾何は描かない。
- golden UX fixture（insight viewer R25）に、本 PRD の幾何が正しく立つ視覚回帰ケースを追加する。

---

## Non-Goals

- `archsig-measurement-packet/v1` の意味論、5値 verdict discipline、assumption ledger を変更しない。
- 新しい structural verdict / 新しい測定 evaluator を導入しない。
- **H² coherence(triple overlap）の可視化を本 PRD では行わない。** ArchSig 側に H² 測定が無いため、packet が H² を語らない。これはウィトゲンシュタイン境界に従い沈黙とし、別途 ArchSig H² coherence measurement PRD が測定を立てた後に接続する。本 PRD の nerve は triple overlap を「面の存在」までは描くが、その coherence failure（hole）には踏み込まない。
- monodromy verdict を復活させない（holonomy-like 表示は exploratory view に留める）。
- insight viewer PRD R9–R17 の scene 機能要件を再定義しない。本 PRD はその上の表現品質のみを対象にする。
- ビルド工程の追加をしない（no-build static surface を維持し、Three.js は現行の読み込み方式を踏襲する）。

---

## Acceptance Criteria / 完了条件

- AC1. R1: Site/Cover・Cover&Gluing scene で nerve が頂点・辺・塗り三角形の単体複体として描かれ、三角形が packet の cover データに由来する。
- AC2. R2: H¹ scene で cocycle support が ribbon として描かれ、ループの閉じなさが固定された visual encoding で表現される。monodromy verdict を復活させない non-claim が表示される。
- AC3. R3: curvature support / mass が field として描かれ、measured-zero と blocked/unmeasured が視覚的に区別される。
- AC4. R4: Obstruction scene で minimal forbidden support が cage / simplex として描かれる。
- AC5. R5: Repair scene で repair morph が連続変形として動き、lower-bound 言語と「自動修復ではない」non-claim を併記する。
- AC6. R6: atom node が fiber / carrier / valence / semantic anchor を反映した glyph として描かれ、semantic anchor 欠落が blocker として見える。
- AC7. R7: 全 primary scene で axisMapping が幾何配置を駆動し、X/Y/Z の意味が HUD / legend に表示される。
- AC8. R8: 色・形・線・透明度・厚みの意味が固定され、color 非依存で区別でき、legend に列挙される。
- AC9. R9: richness が claim に昇格しない明示と、新規幾何への degradation / omitted counts 適用がある。
- AC10. golden UX fixture に本 PRD の幾何の視覚回帰ケースが追加され、`cargo test --manifest-path tools/archsig/Cargo.toml` が通る。
- AC11. `git diff --check`、hidden/bidi Unicode scan、禁止語 scan を通す。
- AC12. 本 PRD は H² coherence の可視化を要求しない（Non-Goals の沈黙境界を侵さないことをレビューで確認する）。

---

## 検証コマンド

```bash
cargo test --manifest-path tools/archsig/Cargo.toml
python3 -m http.server 0 --directory tools/archsig/viewer   # viewer の目視確認
git diff --check
rg -nP "[\x{200B}-\x{200F}\x{202A}-\x{202E}\x{2066}-\x{2069}]" <changed-files>
```
