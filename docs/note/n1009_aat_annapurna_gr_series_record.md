# Gr 系列踏破の記録 — 5週間の実装と成果、愛称アンナプルナ

本ノートは記録ノートである。2026-08-02 の G-101 から 2026-09-06 の G-118 まで、
5週間で Gr 系列の全 GOAL の結論が出た。本ノートはこの期間の実装記録を残し、
AAT にもたらされた数学的成果と CS への意義を書き、系列の総称の愛称を定める。
各定理の statement と証明状態は各 GOAL カードと report にある。
Gr の5段階(Gr0 から Gr4)の定義は
[n1001 §3.5](n1001_atom_is_all_you_need_discussion.md) にある。

## 要旨

1. Gr の5段階は、「AAT は Grothendieck 的である」という比喩を、段階を踏んで
   定理にしていくための計画である。Gr2(構成された実例)と Gr3(擬関手的整合)は
   定義どおり達成した。Gr4(base change 完備)は定義どおりには成り立たなかった。代わりに、
   三層の定理群と、その上の冪等正規化因子・descent transport の層が確定した。
2. 5週間の結果は `target-theorem-proved` が 16、`target-refuted` が 2(G-105、
   G-117)である。反証は消耗ではなく、後続カードの固定素材として再利用された。
3. G-116 と G-118 で、比較射の破れの正体が確定した。生成比較は可逆な canonical
   mate と冪等な正規化因子に分解する。正規化因子は観測に見えず、自然変換では
   消せない。比較を保つ端点変更は torsor で分類され、その分類は入力の表示に
   依らず、係数の観測からは判定できない。
4. CS への意義は、観測とメトリクスだけでは設計整合性を判定できないことの定理化、
   変更自由度の完全なパラメータ化、解析の表示独立性、無害に見える正規化の
   消去不能性である。
5. Gr 系列の総称の愛称をアンナプルナと定める。正式名は各定理の数学名であり、
   愛称は数学名と GOAL 番号を置き換えない。

## 1. Gr の5段階と本記録の範囲

n1001 §3.5 は、初版が比喩として置いた「Grothendieck 的」という呼び名を、
5つの段階を踏んで定理にしていくと宣言した。

```text
Gr0 比喩(n1001 初版の状態)
Gr1 statement 化
Gr2 構成された実例
Gr3 擬関手的整合
Gr4 base change 完備
```

本記録の範囲は G-101 から G-118 までの 18 枚(旧 G-105 を含む)である。
Gr2 は 2026-08-02 に G-101 で、Gr3 は 2026-08-18 に G-109 で達成した。
Gr4 は G-110 で土台を作り、責務を一つずつに絞った 6 枚(G-111 から G-116)に
分けて進めた。6 枚は全て証明で確定したが、Gr4 は n1001 の定義どおりには
成り立たなかった(§3)。後続の G-117 と G-118 は、成り立たなかった理由の層
そのものを研究対象にした。

## 2. 実装記録

### 2.1 結果一覧

| GOAL | 主結果 | 判定 | 確定日 |
| --- | --- | --- | --- |
| [G-101](../../research/goals/G-101-aat-atom-foundation.md) | Atom Transport Opcartesian Lift Theorem(Gr2 到達) | proved | 2026-08-02 |
| [G-102](../../research/goals/G-102-aat-two-phase-obstruction.md) | Two-Phase Obstruction Support Theorem | proved | 2026-08-02〜08 |
| [G-103](../../research/goals/G-103-aat-canonical-resolution.md) | Finite Canonical Resolution Representability Theorem | proved | 2026-08-02〜08 |
| [G-104](../../research/goals/G-104-aat-resolution-invariance.md) | Atlas 定理 | proved | 2026-08-08 |
| [G-105](../../research/goals/G-105-aat-structural-cover-invariance.md) | structural cover invariance | refuted | 2026-08-11 |
| [G-107](../../research/goals/G-107-aat-uniform-invariance-characterization.md) | 一様不変性 defect の特徴づけ | proved | 2026-08-11 |
| [G-106](../../research/goals/G-106-aat-transport-coherence.md) | Transport Coherence Theorem | proved | 2026-08-15 |
| [G-108](../../research/goals/G-108-aat-geometry-reading-transport.md) | Geometry Reading Transport Theorem | proved | 2026-08-16 |
| [G-109](../../research/goals/G-109-aat-cross-stage-coherence.md) | Cross-Stage Transport Theorem(Gr3 到達) | proved | 2026-08-18 |
| [G-110](../../research/goals/G-110-aat-doctrine-fiber-product.md) | Doctrine Fiber Product and Base Change Theorem (A)–(E) | proved | 2026-08-25(Cycle 111) |
| [G-111](../../research/goals/G-111-aat-indexed-base-change-schema.md) | Indexed Base-Change Calculus and Coherent Diagnostic Assembly Classification Theorem | proved | 2026-08-26 |
| [G-112](../../research/goals/G-112-aat-exact-bottom-coverage.md) | Exact-Bottom Coverage Classification and Global Lift Coherence Theorem | proved | 2026-08-27 |
| [G-113](../../research/goals/G-113-aat-diagnostic-conservativity.md) | Indexed Diagnostic Transport Equivalence and Orbit Exactness Theorem | proved | 2026-08-28(revision 2) |
| [G-114](../../research/goals/G-114-aat-refinement-base-change.md) | refinement base change(revision 3、(a)–(f)) | proved | 2026-08-29 |
| [G-115](../../research/goals/G-115-aat-upper-stage-lift.md) | 上段 lift と typed comparator descent(revision 9、(a)–(d)) | proved | 2026-09-01(Cycle 84) |
| [G-116](../../research/goals/G-116-aat-idempotent-exchange-structure.md) | Split Configuration Descent and Idempotent Beck–Chevalley Exactness | proved | 2026-09-04 |
| [G-117](../../research/goals/G-117-aat-lax-diagnostic-projector.md) | Natural Idempotent Modification and Lax Diagnostic Projector Theorem | refuted((c)) | 2026-09-05(Cycle 4) |
| [G-118](../../research/goals/G-118-aat-diagnostic-descent-transport.md) | Source-Presentation-Natural Qualified Comparison Transport and Diagnostic Information Loss Theorem | proved | 2026-09-06(revision 2、Cycle 30) |

判定の列の proved は `target-theorem-proved`、refuted は `target-refuted` を指す。
G-117 のループは (c) の反証定理
`no_taggedAdmissibleCanonicalNormalizationNatTrans` で終了した。終了記録は
tracking Issue #4359 にある。(i) の同型判定義務は G-118 の B2 が引き受けた。
G-105 の反証記録と salvage reading はカードを参照。

### 2.2 実装の仕組み

各 GOAL は次の一定の手順で走った。カードに target theorem の statement、量化域、
完了条件、失敗時の扱いを固定する。`$target-theorem-loop` が F0(型の確定)から
cycle 単位で証明を積み、cycle ごとに固定 head、証拠、監査を記録する。完了時は、
schema を満たす completion packet、同一 head への独立査読 4 本(数学 2、Lean 2)、
formal completion ledger、merge、GOAL と report の同期、の順で確定する。

この手順は複数回、止まるべき所で止まった。G-111 と G-114 は F0 で型の欠陥を
検出して停止し、人間の判断でカードを改訂してから再開した。G-112 は証拠の
provenance 検査で一度停止した。G-114 と G-118 では、`proved` の宣言後に監査が
記録の不備(依存関係の記載と完了手順の順序)を検出し、状態を差し戻してから
完了をやり直した。いずれも定理本体の欠陥ではなく、証拠の記録の欠陥である。
定理と同じ強度で証拠を検査する設計が、宣言の信頼性を支えた。

規模の参考値として、2026-09-06 時点で research 木の
`research/lean/ResearchLean/AG/` 配下は 791 module、約 30 万行である。
`DoctrineFiberProduct/` 配下だけで 364 module になる。個別では G-111 の宣言
map が 345 件、G-115 が 80 module・公開宣言 1516 件、G-118 が 451 宣言である。

### 2.3 反証の再利用

この 5 週間の特徴は、反証が次のカードの入力になる仕組みである。

- G-105 の反証は、残差が住める方向と住めない方向の区別を後続の witness 設計に
  引き継いだ。
- G-113 revision 1 の反証(保守性が全 hom で成立し、消える作用の要求と両立
  しない)は、同日の revision 2 の設計に直結した。
- G-114 revision 2 の棄却(垂直 mate の非恒等 Atom 作用は構成できない)は、
  非恒等性を cartesian lift edge へ移す revision 3 を生んだ。
- G-115 revision 8 の比較対(係数の水準では自明な comparator の差が descent を
  反転させる)は、G-118 の固定 datum になった。
- G-117 の反証は、G-118 が正規化因子を「消す」のではなく「分類する」対象に
  据える根拠になった。

## 3. Gr4 の結論

n1001 の Gr4 は「doctrine 圏の fiber product 込みで相対的視点の全操作が閉じる」
と定義した。6 枚を証明した結果、この定義どおりの達成は成り立たないと確定した。
2026-09-04 の人間の判断で、Gr4 の達成記録カードは作らないことが確定した。

成り立たなかった内容は二つに集約される。第一に、垂直方向の剛性である。fiber
内の垂直射では base 射影が恒等になり、upper と base の Atom 対応が一致するため、
非恒等な意味作用は垂直方向に住めない(G-114 revision 2 の棄却)。第二に、
package 圏は冪等完備でない。生成比較 `β` は可逆な canonical mate `α` と冪等な
正規化因子 `E` に分解し、`E` は raw の圏では同型にならない(G-116)。しかも
この因子は自然変換では消せない(G-117 の反証)。

代わりに確定した形が、[n1007 §8](n1007_aat_sakura_gr4_completion_design.md) の
三層提示である。

- **Coherent Reading Tower**(G-106 / G-108 / G-109): reading の輸送が段を
  横断して合成する。
- **Relative Base-Change Calculus**(G-110 / G-111 / G-114 / G-115): base
  change がどの方向で定理として立つかの計算体系。
- **Coverage and Diagnostic Transport Exactness**(G-112 / G-113 / G-116):
  被覆と診断輸送がどこまで閉じるかの分類。

そして三層の上に、閉じない部分そのものを研究対象にする層が乗った。G-116 が
正規化因子の正体を、G-117 がその消去不能性を、G-118 がその周りの descent
transport の分類を確定した。完備性の障害は無定形の失敗ではなく、それ自体が
冪等構造と torsor 構造を持つ数学的対象である。これが Gr4 の答えである。

## 4. AAT にもたらされた成果

### 4.1 相対化の計算体系

reading を一つの底の上で解析する段階から、底を取り替えて解析する段階へ進んだ。
indexed な base 作用(G-111)、有限被覆と大域 lift の同値条件(G-112)、診断の
輸送同値と orbit exactness(G-113)、refinement に沿った base change(G-114)、
上段の問題への lift(G-115)が、いずれも量化域を固定した定理として立っている。
どの操作が閉じ、どこで閉じないかが、予想ではなく分類になった。

### 4.2 正規化因子の正体

G-116 は、exchange の破れに見えた現象の背後に冪等な正規化因子 `E` を同定し、
exactness を raw / image / observable の三層に分けた。raw で壊れても、Karoubi
の像の上と観測可能な関数の上では回復する。G-117 は、この因子を admissible
fiber を貫く一つの自然な modification に束ねる試みが成り立たないことを、
具体的な非可換 witness で確定した。正規化は局所的には常に働くが、大域的な
一つの自然変換ではない。package 圏の冪等完備化(Karoubi 包絡)が configuration
の層を付け加えるという読みが、次の段の入口になる。

### 4.3 比較の移送理論

G-118 は、AAT が生成する比較射 `c` について四つを一度に確定した。第一に、
比較を保つ端点変更の対は群 `Γ_c` をなし、片側を固定した相手の全体は
stabilizer の自由かつ推移的な作用の軌道(torsor)である。第二に、実際に生成
された比較では、source 由来の変更は常に運べ、相手の全体は部分群 `J` の剰余類
で尽き、`J` は入力写像の具体的なデータ条件で特徴づけられる。第三に、この分類
は入力の表示の取り替えに自然である。表示を変えてから生成しても、生成してから
移送しても、同じ分類に着地する。第四に、係数の観測はこの分類を判定できない。
観測上区別のつかない二つの変更対で、比較との両立が分かれる実例があり、観測の
どんな関数もこの判定を再現できない。

### 4.4 次の予想

踏破の収穫として、三つの予想が立った。詳細な育てる候補は
[n1008 §6](n1008_aat_idempotent_exchange_structure_program.md) にある。

- **予想A(Morita 形)**: package 圏の Karoubi 包絡は configuration 層を付け
  加え、n1001 の因子化テーゼは Morita 同値の形で定理化できる。定理になるための条件は
  包絡の上での実現関手の構成である。
- **予想B(H¹ の細分)**: obstruction 類は base change で不変だが、descent の
  両立性はそうでない。G-118 の torsor 分類は、コホモロジー類より細かい不変量
  が実在することの構成的証拠である。定理になるための条件は、この不変量の well-defined
  な class 化である。
- **予想C(compactness)**: coverage の有限性条件は compactness の実例である。
  定理になるための条件は、G-112 の分類を位相の言葉へ移すことである。

置き場所はいずれも後続 GOAL であり、G-118 カードの frontier(variable-comparator
の圏、regular comparison、restriction category、coherence height、実現関手)が
接続点になる。

## 5. CS への意義

### 5.1 観測だけでは設計整合性を判定できない

G-118 の非因子化を CS の言葉に訳すとこうなる。テスト、メトリクス、係数観測の
上で完全に等価な二つの変更が、大域的な貼り合わせの可否では異なりうる。そして
この差は、観測値をどう加工しても検出できない。「アーキテクチャの整合性は
数値だけでは管理できず、構造データそのものを見る必要がある」という現場の
直感が、経験則ではなく不可能性定理になった。
[one-cent ドリフト実例](../../tools/archsig/examples/practical-rust-service/README.md)が
不整合の測定可能性を示したのに対し、本結果はその測定の限界の位置を確定した。

### 5.2 変更自由度の完全なパラメータ化

インターフェースを挟んだ両側の変更が比較を保つ組になる条件と、その組の自由度
が、群と torsor で正確に記述された。一つの適応方法を見つければ、残りの選択肢
は stabilizer の作用で尽きる。適応レイヤの設計自由度という工学的な問いに、
剰余類という代数的な答えがある。

### 5.3 解析の表示独立性

入力の表示を取り替えても解析の分類が変わらないこと(G-118 C1s)は、計測
パイプラインの well-definedness の型である。抽出の順序や表現の選び方の産物
ではなく、意味構造の不変量を測っているという主張を、証明付きで立てる形が
できた。この仕組みを実際にツールへ持ち込むかどうかは、別途、実地の検証で
判断する。

### 5.4 無害に見える正規化は消去不能な実構造である

正規化因子は、二回かけても一回と同じで、どの観測にも見えず、しかし可逆でなく、
自然変換では消せない。フォーマッタや正規化パスのような「何にも影響しない
はず」の操作が系の構造を規定して取り除けない、という現象が定理として存在する。
帰結は、正規形を一級市民として扱う(Karoubi 包絡)という設計指針である。

### 5.5 意味の変更はラベルの層を通れない

垂直方向の剛性は、型やタグや configuration の付け替えだけでは観測可能な意味
が動かず、変更は実際の経路にしか住めないことを言う。メタデータの変更が意味を
保存することの構造的な理由である。

### 5.6 分割統治の健全性条件

G-112 と G-113 は、有限個の部分の解析で全体の lift が得られる条件を必要十分の
形で与えた。モジュラー解析がいつ嘘をつかないかの条件であり、予想Cが立てば
これは compactness の実例になる。

### 5.7 方法論の実証

ソースコードの観測から出発する形式化が、5週間で 16 本の機械検証済み
大定理に到達した。証明本体だけでなく証拠の依存関係まで機械的に監査する
fail-closed の運用が、この速度と信頼性を両立させた。理論の中身と独立に、
この開発様式自体が一つの成果である。

## 6. 愛称アンナプルナ

Gr 系列(G-101 から G-118)の総称の愛称をアンナプルナと定める。
正式名は各定理の数学名であり、愛称は数学名と GOAL 番号を置き換えない。系列
全体を一語で指す場面でだけ使う。定理の固有名としては Atlas 定理(G-104)の
前例があり、本愛称は定理ではなく系列に与える名である。

由来は実在の山群アンナプルナとの五つの対応である。

1. 人類が最初に登頂した 8000m 峰である(1950 年)。Gr 系列は AAT が最初に
   登り切った大きな山体である。
2. 遠征隊の当初の目標は隣のダウラギリで、偵察の結果、転進して登った。Gr4 も
   当初の定義の山は存在せず、実在する頂(三層の定理群と正規化因子の層)へ
   転進して登った。
3. 登頂より下山で大きな代償を払った山である。本系列も、証明完了後の監査と
   独立査読という下山を最後まで踏んで確定した。
4. 名はサンスクリットで「食物に満ちた者」を意味し、豊穣の女神の名である。
   山が地図どおりでなかったことが収穫をもたらした。一番の収穫は反証から
   生まれた。
5. 単一峰ではなく、一つの山体に複数の頂を持つ連峰である。責務を一つずつに
   絞った 6 枚への分割は、一本の経路では登れない山体だという地形の認識
   だった。山群には
   意図して登らない聖山が一座あり、Gr4 の達成記録カードを作らないという
   判断に対応する。
