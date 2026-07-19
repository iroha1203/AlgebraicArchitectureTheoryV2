# ArchView 気象図リニューアル 設計思想ノート — 意味の測量図としてのコード可視化

このノートは、ArchView をゼロベースで再設計するための設計思想を固定する。
出発点は train-ticket ドッグフーディング
([fullbuild](../reports/train_ticket_dogfooding/fullbuild.md) /
[saga_diagnosis](../reports/train_ticket_dogfooding/saga_diagnosis.md))完遂後のユーザー判断
「ArchView は AAT と ArchSig のための可視化装置としてゼロから設計するべきだ。
現状のものを配布しても受け入れられない」である。
確定した PRD でも実装計画でもなく、リニューアル PRD の正本として機能させる。

関連文書:

- [ArchView 計測駆動幾何 設計ノート](archview_measured_geometry_design.md) — 現行 AG 視覚言語の正本
- [ArchView gluing geometry contract](../tool/archview_gluing_geometry_contract.md) — 現行 viewer の忠実性契約
- [ArchView コード理解支援 構想ノート](archview_ai_code_understanding_hypothesis.md) — AI 時代仮説(理解・探索軸)。
  本ノートは伝達・可視化装置軸の再設計であり実施順序は同ノートに従属しないが、
  同ノートの理解実験 protocol(問い固定→viewer回答→コード答え合わせ→記録)は
  本ノートの判定規律として継承する(§9)

作成: 2026-07-20(2026-07-20 レビュー反映: PR #3628 の敵対レビュー10項目を本文へ統合)

---

## 問い

**「コードベースの可視化はなぜ失敗し続けてきたのか」に、AAT / ArchSig は構造的な答えを持つか。**

この問いを採否の判定規律として使う。「答えを持つ」と判定するのは、
再設計された ArchView が次の3条件を同時に満たすときに限る。

1. **忠実性の完備**: すべての視覚要素が「どの測定がそれを駆動するか/いつ沈黙するか」の
   対応表(§4)に空欄なしで載る。測定に還元できない視覚チャネルは fidelity 4区分
   (§7.1: measured / derived / layout / decoration)のいずれかで申告されるか、描かれない。
2. **読み方の教養が流通していること**: AAT の語彙を知らないエンジニアが、
   読み方を新たに学習せずに画面を**正しく**読める。「もっともらしい誤読」を成功扱いしないため、
   判定は理解支援構想ノートの protocol を継承する: 問いを先に固定し、viewer だけで回答し、
   コードで答え合わせし、正確性・所要時間・コードに戻った理由を記録する。
   North Star は wow ではなく **time-to-correct-bounded-explanation**
   (正しく境界づけられた説明への到達時間)である(task 一覧は §9)。
3. **wow が嘘をつかないこと**: すべての視覚チャネルが fidelity 4区分(§7.1)のいずれかで
   申告され、驚きの演出が主張を追い越さない(演出予算は測定された非零類に予約)。
   3D は前提ではなく、base / fiber の区別の理解に有効な場合に限り採用する(§3)。

条件1が崩れれば忠実性契約違反(設計に戻る)、条件2が崩れれば視覚言語の選定ミス
(気象図言語の見直し)、条件3が崩れれば 3D の放棄(2D 基図へ縮退)がそれぞれの帰結である。

## 1. 問題史: なぜコード可視化は墓場なのか

コード可視化は CS に長く存在する問題であり、成功事例は乏しい。
UML リバース、CodeCity 系のソフトウェア都市、依存グラフブラウザ、コールグラフ探索は
繰り返し作られ、繰り返し使われなくなった。死因は個別の実装品質ではなく、3つの構造的欠陥に還元できる。

**診断1: 構造を描いてきて、測定を描いてこなかった。**
これらのツールが描くのはコードの構文的構造(ファイル・クラス・呼び出し)である。
しかし構造は IDE で読める。絵は「すでに読めるものの別レンダリング」でしかなく、
絵にしか無い情報がゼロだった。「眺めるが、使わない」の根本原因はここにある。

**診断2: 空間に意味がなかった。**
地図・分子構造・流れ場の可視化が成功するのは、絵の背後に本物の幾何を持つ数学的対象があり、
位置と距離が何かを意味するからである。force-directed layout の座標は美的乱数であり、
絵の中の「近さ」は何の主張でもない。読者はそれを直感的に見抜き、絵を信用しなくなる。
空間が嘘をつく絵は、読む対象ではなく壁紙になる。

**診断3: 全体性を主張して、鮮度と信頼で死んだ。**
「これがあなたのアーキテクチャです」という絵は、見る側が知っている反例1つで信頼を失い、
コミット10個で腐る。手書き図は保守されず、自動生成図は些末で、どちらも
「この絵は何を根拠に、いつ語っているのか」に答えられなかった。

### 1.1 例外が規則を証明する: flame graph

コード周辺で広く定着した可視化はほぼ一つ、flame graph である(coverage overlay、
リポジトリ熱地図が続く)。成功の理由は明確で、**測定量(サンプリング時間)を、
不変量が保存される幾何(幅=時間の加法性、包含=呼び出し階層)で描いた**からである。
絵のすべてのピクセルが測定の投影であり、レイアウトの自由度がない。

この失敗史と例外から、次の経験則が立つ:

> 構造の可視化は失敗し続け、**測定の可視化**は成功してきた。

## 2. 解答: AAT は測量術であり、ArchView は測量図である

地図学が成立したのは、測地学(測量)と投影法(歪みの宣言)があったからであり、
絵心があったからではない。コード可視化が失敗してきたのは、**測量なしに地図を描いてきたから**である。

AAT + ArchSig は、この欠けていた測量術に相当する。

- **AAT はコードベースに本物の幾何を与える**: site、被覆、overlap、切断、コホモロジー。
  これは比喩ではなく、supplied contract から計算される実在の有限単体複体である。
  絵の背後に初めて「地球に相当する数学的対象」が立つ(診断2への回答)。
- **ArchSig はその幾何の上の測定器である**: mismatch 辺、cocycle support、類の零/非零、
  grounding、descent。すべての視覚要素を flame graph 原理(1ピクセル=1測定)で描ける
  (診断1への回答)。
- **contract 相対性と沈黙の規律が信頼問題を解く**: 絵は「あなたのシステムの全体」を主張しない。
  「この contract・この runId の下で測定されたこと」だけを digest と再現コマンド付きで語り、
  未測定は沈黙として描く(診断3への回答)。

したがって ArchView の identity は「コード可視化ツール」ではなく:

> **ArchView は、AAT が構成した選ばれた意味の幾何の上に、ArchSig が測定した有界な
> architecture evidence を投影する、人間向けの対話的な測量図(survey-based map)である。**

役割境界は次のとおり定める。ArchView は新しい structural verdict を**生成しない**
(diagnostic generator ではない)。しかし、ArchSig が生成した diagnostic evidence の
**navigator ではある**: 観測範囲の把握、局所観測と大域結論の接続、沈黙理由の確認、
support と source への到達、run 間の比較を支援する。gate 判定・修理案の生成・比較は
ArchSig(CLI artifact)の語りであり、ArchView の仕事はそれを人が理解できるよう
投影し、方位づけ可能にすることである。

## 3. 3D の正当性: 層は底空間の上の空間である

CodeCity 型の 3D が信用されなかったのは、Z 軸が嘘をつくからである
(ビルの高さ=LOC、距離=無意味、オクルージョンだけが増える)。
3D が正当なのは、対象が本当に3次元のときだけである。気象図が 3D で成立するのは
大気が本当に 3D だからである。

ここで対象の数学的な形が効く。**層(sheaf)とは底空間の上に立つ空間**であり、
étale space は「基図の上空」に相当する構造 — 底への射影と fiber membership — を持つ。

ただしこの主張は正確に型づける必要がある。étale space が与えるのは
**base / fiber の分離という semantic な区別まで**であり、fiber 内の標準的な高さ・距離・
順序は与えない。したがって:

> **base / fiber の分離は semantic である。垂直位置・垂直距離・スケールは、
> 追加測定がない限り layout である。** また有限 site の nerve を 2D に置くこと自体も
> 投影(スペクトル埋め込み = derived)であり、対象が「2D の地面」を持つわけではない。

それでも「地図とその上空」という編成が他の候補より有利なのは、
**気象図が「底空間+その上の場」を描く、読み方の流通した唯一の大衆的視覚言語**だからである。
3D は前提にしない。2D / 2.5D / 3D は同じ view model(§8)の上の投影・カメラの選択であり、
採否は base / fiber の区別の理解に効くかどうかの task-based 比較(スパイクを含む)で決める。

## 4. 視覚言語: 気象図と語彙対応表

AAT の難解さのカプセル化は、機能ではなくこの対応表で実現される。
エンジニアは左列(気象語)だけで会話でき、各行に「駆動する測定/沈黙条件」が固定される。

| 気象 | AAT | 駆動する測定 | 沈黙条件 |
| --- | --- | --- | --- |
| 地形・地区 | site / cover の nerve | ArchMap contexts / overlaps(スペクトル埋め込み、決定論) | —(常設の基図) |
| 地区間の道 | overlap | 共有 atom 数 | 共有なしは道なし |
| **観測所** | measurement profile / contract | どこで何を観測しているか | 観測所の無い地域は測定なし |
| **前線** | overlap 上の規約 mismatch(F₂ support) | witness marker(F₂、辺単位) | witness 未供給なら描かない |
| **循環警報(渦)** | 非零 H¹ 類(F₂) | `MEASURED_NONGLUING_RESIDUAL_CLASS` の類 support と閉路構造 | 類ゼロ・未計測は警報なし。**無向マーク** — 回転方向・強さは F₂ から得られない |
| **基図の穴** | triple-overlap face(2-simplex)の不在 | ArchMap から測定された複体の形(閉路を埋める面が無い) | structural absence であって `unmeasured` ではない — 霧で描かない(§5) |
| **風(流線)** | 調和 1-form(Hodge 代表元) | harmonic 系(R 係数 run)の符号付き辺値 | R run なしなら「無風」でなく「風の観測なし」 |
| 等値線・濃淡 | スカラー場 | 実測 per-vertex / per-edge スカラー(debt 等)とその測定出自 | 実測なしなら描かない(内挿で発明しない) |
| 雲層 | section / étale の各シート | sectionValue(値ごとに1層) | 宣言なしは空のみ |
| 雲層のせん断・裂け目 | restriction の不一致 | mismatch 辺上のシート不連続 | — |
| **霧** | 未観測領域 | boundary statement | (霧こそが沈黙の描画。ただし種類を潰さない — §7.1) |

この表が自動的に解いてくれる問題が2つある。

**観測所メタファーが contract 相対性を無料で伝える。**
天気図が観測網に相対的であることは誰でも知っている。「観測所の無い山間部の天気は描かれない」は、
「profile が観測しない領域は沈黙」の完全な翻訳であり、謙虚さの弁明ではなく
当たり前のこととして伝わる。同じ理由で**「晴れ」は描かない**: 描けるのは
「この観測網では静穏」であって「安全」ではない(near-flat ≠ lawful の気象語版)。

**F₂ と R の二段が気象表現に正確に写る。**
F₂ 段(train-ticket 実測)で言えるのは、非零性・代表元 support・閉路構造(parity)までである
→ 無向の循環警報は描くが、回転方向・角速度・流速・中心・気圧の極小は描かない。
「低気圧」の語は scalar field の極小を含意するため、H¹ 類の名称としては使わない。
F₂ glyph を回転アニメーションさせることは未測定の向きの主張であり禁止する。
R 係数の harmonic run が供給されたときだけ、符号付きの風(流線)が吹く。
視覚表現の段差が測定の段差に一対一対応する。

**複数 profile を一つの「天気」に混ぜない。**
同一地域には F₂ / R、money / status 等の異なる profile の観測が並存し得る。
cross-profile の比較契約なしに1画面へ合成すると、異なる contract に相対的な観測を
「一つの現在の天気」として見せてしまう。profile switcher / small multiples /
レイヤーごとの profile badge を設け、比較契約が供給されない限り合成しない。

## 5. センターピース: 全観測所が静穏を報告し、上空に消えない循環が立つ

train-ticket SAGA 実測([saga_diagnosis](../reports/train_ticket_dogfooding/saga_diagnosis.md))の
grounding の構造 — 各チャートは自分の法を完全に守っている(`measured_zero`)のに、
ループ一周で非零類が立つ — は、気象言語でこう描ける:

> cancel・inside-payment・order の3観測所はいずれも静穏を報告している。
> しかしその3地区を結ぶ閉路の上には、消えない循環警報が立ち続けている。
> そしてこの循環を埋めるはずの「三地区を同時に照合する面」は、
> 基図そのものに存在しない — **地図には穴が開いている**。

「局所正・大域壊」という署名フレーズが1枚の絵になる。
循環=閉路上のコホモロジー類なので、この絵は誇張ではなくほぼ定義の描画である
(ただし F₂ 実測で語れるのは循環の存在と support までであり、向き・強さは描かない — §4)。

ここで型を一つ間違えてはならない。train-ticket で欠けているのは
「存在する土地が未観測なこと」ではなく、**三者同時照合を担う triple-overlap face
(2-simplex)自体が複体に存在しないこと**である。これは `unmeasured` ではなく
structural absence であり(ArchMap から測定された複体の形そのもの)、
霧(沈黙)ではなく**基図の穴**という別の視覚語彙で描く。
非零 H¹ 類とは「循環があるのに、それを埋める面が無い」ことなので、
穴の描画は比喩ではなくほぼ定義である。
初期コンテンツは合成デモではなく実在 OSS の実測であり、これが先行ツールとの証拠面の差になる。

## 6. 時間軸: 天気は動くから天気である

静止画で終わらせない道具立ては計測側に既にある(compare、sequence)。
コミット履歴の再生は気象の推移として描ける:

- mismatch witness の新規記録 → 前線が立つ
- 閉路上の selected cocycle が非自明になる → 循環警報が記録される
  (閉路の形成だけでは類は立たない — 非自明な class support の記録が要る)
- provenance 付き2状態の compare → obstruction が変更後に記録されなくなる
  (`MEASURED_OBSTRUCTION_NO_LONGER_RECORDED_AFTER_CHANGE`。repair が実装・適用されたことや
  repair が原因で消えたことは主張しない — 語れるのは「変更後の状態では記録されない」まで)

これは ICSA 計画の経済性の柱(ArchMap 永続+差分更新、コミット履歴再生)の可視化面に重なり、
将来 FieldSig(進化)が語る場の言語と地続きである。
ただし**予報はしない**。未来予測は語れない領域であり、語れるのは「実測の記録とその再生」までである。

時間軸の描画には2つの追加契約が要る。

- **位置の安定性**: 各 frame でスペクトル埋め込みを独立計算すると、符号反転・回転・鏡映・
  graph 変化による全体移動が起き、layout の変化が architecture の変化に見えてしまう。
  共通 context anchor、前 frame への Procrustes 整列、新規・削除 context の別表現、
  layout motion の fidelity 申告(§7.1)を必須とする。
- **state provenance**: 画面上の各状態がどの現実に対応するかを常に区別して表示する —
  observed source state / authored measurement model / measured conclusion /
  hypothetical repaired state / actual repository change。
  train-ticket の repaired 変種は実コードへ適用済みの修理ではなく hypothetical ArchMap であり、
  この区別を潰した瞬間に絵が嘘をつく。

## 7. 規律: 継承するもの、捨てるもの、先に自白する罠

### 7.1 現行 ArchView から継承する規律

- **M→V gating**: 測定に無いものを描かない(捏造ゼロ)。
- **沈黙の描画**: 未観測は霧。赤エラー化しない。ただし**沈黙の種類を潰さない**:
  measured_zero / unmeasured / unknown / not_computed、および boundary の種別
  (silence_by_design / out_of_selected_vocabulary / unmeasured_support /
  violated_assumption / blocked_method / not_applicable)は認識論的に異なる。
  霧を共通 family として使う場合も、模様・境界・badge・reason・whatNext で種類を区別する。
- **1画面=1つの問い**: シーンは問いの単位である。
- **fidelity declaration の4区分**: `measured`(測定量が駆動)/ `derived`(実測量からの一意導出 —
  スペクトル埋め込み・調和代表元・Laplacian 拡張はここ)/ `layout`(意味を持たない作図選択)/
  `decoration`(演出)。現行 gluing geometry contract の4区分を後退させない。
  申告は glyph 単位ではなく**視覚チャネル単位**で行う(例: 循環警報の存在 = measured、
  support 辺 = measured、2D 位置 = derived、glyph 中心 = layout、発光 = decoration、
  回転方向 = 対応する測定が無い限り禁止)。
- **演出予算の予約**: 発光・雷などの高輝度演出は測定された非零類のみに使う。

### 7.2 捨てるもの

- **AG 語彙ネイティブな絵**(étale sheet、patch/lens の直接描画)を主役から外す。
  数学的に忠実でも、読み方の教養が世に流通していない視覚言語は伝達装置にならない。
  現行実装を Math lens(奥の間)として残すか退避するかは PRD 側の判断とする。
- **Three.js vendoring は不採用**(ユーザー判断、2026-07-20)。配布物を開く時点で
  インターネット接続は前提であり、閉域ネットワークは想定しない。CDN 参照を維持する。

### 7.3 先に自白する罠

- **等圧線の内挿問題**: 観測所間を滑らかに補間した瞬間、測定に無い値を発明する。
  場は nerve の辺上(測定の台)だけに描くか、調和拡張(Laplacian 上で数学的に正準、
  `derived` として申告)に限る。**未測定の滑らかな連続場は Weather lens では原則描かない** —
  等値線・流線と同じ視覚文法で描けば、詳細パネルで `decoration` と申告しても画面自体が嘘をつく。
  非データの背景表現をどうしても使う場合は、測定・derived の場と混同し得ない別の視覚文法+
  別 legend とし、既定 OFF にする。
- **3D のオクルージョン**: 既定は斜め俯瞰の低い視点+層のトグル(空を消して基図だけにできる)。
  「驚かせる 3D」と「読める 2D」は、同じ基図の上のカメラ角度差として実現する。
- **メタファーの過伸長**: 対応表(§4)に無い気象語は使わない。
  表に測定列が書けない気象表現を追加したくなったら、それは装飾ではなく捏造の始まりである。

## 8. ArchSig 側の handoff 拡張(素描): 表示非依存の typed view model

気象語彙を ArchSig の schema へ直接結合しない。ArchSig が供給するのは
**表示非依存の typed measurement view model** であり、気象図はその上に載る第一の
engineer-facing lens である。将来の Math / Table / Source lens は同じ view model を共有する。
lens の語彙(前線・循環警報・霧)は viewer 側の表示層に閉じ、schema には持ち込まない。

view model が持つべき区画(確定は PRD 側。ここでは素描に留める):

1. **observation coverage** — 「観測所」(§4)を駆動する契約。現行 MeasurementProfile は
   run 全体の profile であり、context × measurement-axis の観測 coverage を直接は表さない。
   viewer が観測範囲を推測してはならないため、次の形の明示供給が要る:

   ```text
   ObservationCoverage {
     contextRef, profileRef, evaluatorRef, measurementAxis,
     status, conclusionCode?, supportRefs[], boundaryKind?,
     whatNext?, sourceRefs[], runId, inputDigests
   }
   ```

2. **local observation / edge mismatch** — 観測所の報告と前線(witness marker、辺単位)。
3. **class support** — 非零類の代表元 support と閉路構造(F₂ 段は無向)。
4. **harmonic flow** — 調和代表元の符号付き辺値(R 係数 run 時のみ)。
5. **scalar field** — 実測スカラーの per-vertex / per-edge 値と測定出自。
6. **boundary statement** — 沈黙の種別つき(§7.1)。
7. **temporal transition** — 診断階段(analyze×2 + compare + gate×2)とコミット系列が
   現状複数 out-dir に散らばっている。digest 整合検証済みの単一 bundle に束ねる
   機械的コマンドの追加は ArchSig の責務境界内(計測ではなく既存 artifact の束ね直し)。
   state provenance(§6)の区別を bundle に含める。

## 9. 次工程

1. **スパイク**: `docs/reports/train_ticket_dogfooding/evidence/` の実測 viewer-data を使い、
   実データでセンターピース(§5)を描く捨て前提の試作。2D / 2.5D / 3D を同じ view model 上で
   比較し、§3 の採否判断(task-based 比較)の材料にする。
2. **判定 protocol の固定**: 理解支援構想ノートの実験 protocol を判定規律として継承し、
   最低限次を task として測る — どの profile / cover を見ているか、measured zero と
   unmeasured の区別、非零類 support の特定、局所正・大域不整合の説明、source への到達、
   actual change と hypothetical repair の区別、何を結論してはいけないか。
3. **ArchView リニューアル PRD**: 本ノートを正本に起草。判定規律は冒頭の3条件を引き継ぐ。
   ArchSig handoff 拡張(§8 の typed view model)は PRD 内で確定する。
4. v0.5.4 のもう1本(単一 Facade SKILL — 入り口を1つにし、SAGA は LLM が内部でよしなに使う)は
   本ノートとは独立の PRD として扱う。
