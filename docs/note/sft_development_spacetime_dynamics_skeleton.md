# SFT 全面改訂 理論骨格: 開発時空の力学系としての Software Field Theory

- 作成: 2026-07-04(第1版)/ 同日 第2版(敵対レビュー 5 本・MAJOR 29 件 MINOR 11 件を反映)/
  同日 第3版(有識者レビュー 15 項目を全採用。§13 参照)
- 位置づけ: `docs/sft/software_field_theory.md` 全面改訂(SFT v2)の理論骨格。
  骨格分岐はユーザー決定済み(2026-07-04、§12)。本文は PRD を挟まず Claude が部単位で直接執筆する。
- 先行素材:
  - [Grothendieck–Derived AAT/SFT ポジションペーパー](Grothendieck_Derived_AAT-SFT.md)(第9章が SFT 側の種)
  - AAT AG 版本文 第IV部(Čech・boundary holonomy)・第V部(導来 law 幾何・repair 比較)・
    第VI部(cotangent complex・monodromy・stack)・第VII部(representation・period・距離)・
    第VIII部(measurement・Hodge 分解・repair 下界)・第IX部(evolution geometry)・第X部(SAGA)
  - [path monodromy](path_monodromy_obstruction_theorem.md) /
    [boundary holonomy](boundary_holonomy_conjecture.md) /
    [homotopy holonomy Stokes](homotopy_holonomy_stokes.md)(第II部の素材。
    ただし boundary holonomy は AAT 第IV部 §9、monodromy debt は AAT 第VI部 定義10.3 として
    既に AAT 本体化済みであり、SFT 側はその差分だけを扱う)

---

## 問い

```text
ソフトウェア進化 — コードベースと開発組織の時間発展 — は、
AAT が与える幾何の上の力学系として、比喩なしに定式化できるか。

すなわち:
  場・力・衝突・安定性が実在の数学的対象
  (層データ、選択された貼り合わせ、コホモロジー類、Lyapunov 汎函数)であり、
  かつ、マージ、並列開発、Conway の法則、技術的負債、老化、統治という
  10 年級の工学的現象が、その定理・系・模型定理として現れるか。
```

この骨格の採否規律:

1. 中心対象はすべて数学的キャリア(圏 / site / 層データ / 射 / 類 / 汎函数)を持ち、
   **名乗った構造は定理か実例で本質的に使われる**(D1′)。
2. 旗艦定理は「仮定 → 結論」の形と AAT 側アンカーを持ち、アンカーの
   証明状態(proved / certified bounded / candidate)を区別して表示する。
3. 工学的現象は公理ではなく、実例・系・模型定理として現れる。
4. AAT 本文は無変更。依存は AAT → SFT の片方向のまま。AAT 所有概念の「昇格・後継・本体化」を
   SFT 側から宣言しない(D3)。
5. 測定・tooling・実組織との対応は解釈境界(付録と FieldSig 側)に置き、数学本文へ混ぜない。
   コードベースそのものを数学本文の index に使わない(D4)。
6. 普遍性(colimit / pullback / pushout)に依存する定義を置かない。overlap・merge base・輸送・接続は
   選択データである(D8)。
7. Model theorem は、結論が成立しない相の非空性を併せて示す(D6)。
8. 経験的仮説は事前固定 profile と棄却条件を持つ(D7)。

---

## 1. 診断: なぜ全面改訂か

旧 SFT(現行本文)の構造的限界は一つに要約できる。

```text
旧 SFT は「場の理論」を名乗りながら、
本文自身が field / force / attractor / dissipation を
「物理量ではない」と宣言して簿記概念へ分解した。
```

force は ArtifactMediatedChange の非公式名、attractor は StableRegion へ、
dissipation は ProposalAccounting へ分解された。これは誠実さの表れだったが、
理由は明確で、**古典 AAT の上では場や力に実体を与える幾何が存在しなかった**からである。

AAT が代数幾何(site、層、obstruction ideal、cohomology、導来幾何、stack、
evolution geometry)へ進化したことで、この封印は不要になった。

```text
場   = AAT site 上の層データ(実在の層)
力   = 台と輸送データをもつ場の部分変換(実在の射・変形)
衝突 = 貼り合わせの障害(実在のコホモロジー類・Tor)
安定 = 散逸方針と Lyapunov 読み(実在の汎函数; AAT 第IX部)
```

もう一つの限界は、理論本文への tooling の食い込みである。claim level L0–L5、
FieldSig artifact 名、workbench phase plan が本文に混在し、AAT AG 版が確立した
「純数学本文と測定・tooling の分離」規律とは非対称だった。SFT v2 はこの分離を SFT にも適用する。

なお公平のために記録する: 旧 SFT は退屈だが Lean で機械検証された定理群
(support safety、cone projection 等)を持っていた。v2 は当面それを持たない。
この後退を自覚し、§11 で Lean 最初の的(L1–L3)を本文執筆と並行に格上げする。

---

## 2. 設計原理

SFT v2 が守る規律。AAT AG 版の規律の継承 + SFT 固有の追加。

```text
D1′ 実在性(使用強制つき):
  核概念はすべて数学的キャリアを持つ。さらに、核概念が名乗る構造
  (cover / restriction / pairing / 汎函数)は、少なくとも一つの旗艦定理または
  正準有限実例の仮定・結論・計算で本質的に使われなければならない。
  使われない構造は名乗らない(site ではなく圏、層ではなく割り当てと書く)。
  名前だけの概念は、旧 SFT の簿記退化が層の名前を着て再演したものにすぎない。

D2 相対性と沈黙(AAT 継承):
  すべての主張は selected trace profile / vocabulary / law universe /
  coverage / coefficient / measurement profile に相対化される。
  選ばれていない事象・遷移・軸について理論は沈黙する。
  さらに AAT 第IX部 定義3.4 の規律を明文継承する:
  構成データ(site、係数、cocycle、輸送)が固定されていない式は
  定義ではなく reading schema として扱う。

D3 片方向依存(AAT 継承+語法規律):
  AAT は SFT に依存しない。SFT は AAT の対象を使うが再定義しない。
  SFT が新しい純数学(進化 site、力の複体、組織対応)を作るのは自由だが、
  それは SFT 側の数学であり、AAT 本文を書き換えない。
  語法規律: AAT の定義・定理・定理候補に対して「昇格先・後継・本体化」を宣言しない。
  SFT 側の対応物は「SFT 側対応定理候補」と呼び、AAT 側の対象とは比較命題で接続する。
  AAT アンカーは proved / certified bounded / candidate の状態を区別して引用する。

D4 純数学本文と解釈境界の分離:
  本文は「モデル化された開発系」についての純数学。
  実在の PR・組織・CI・リポジトリとの対応は付録の解釈境界に一度だけ置く。
  本文はこの表を参照せず、コードベース・commit・PR という語を定義の index に使わない。
  tooling(FieldSig)は本文の外。

D5 主張の梯子(claim ladder):
  Formal theorem / Certified bounded inference / Analytic reading(AAT 継承)に加え、
  SFT は次の 1 段を新設する。
    Model theorem — 明示された確率・エージェント模型の内部での定理。
  Empirical hypothesis(現実の開発系についての仮説)は AAT 既存の台帳階級
  (docs/aat/proof_obligations.md が管理する empirical hypothesis)の継承であり、
  SFT の新設ではない。SFT の Formal theorem / 定理候補は
  docs/aat/lean_theorem_index.md・proof_obligations.md に対応行を置く
  (または SFT 専用 index を新設して両者から相互参照する)。
  旧 L0–L5 の claim level はこの梯子に置き換える。

D6 模型非自明性:
  Model theorem は、同じ模型族の中で結論が成立しない相が非空であることを併せて示す。
  望ましい標準形は相境界定理である(パラメータの臨界値が存在し、両側の相が非空)。
  「模型に結論を書き込めば定理になる」型の空虚化をこれで遮断する。

D7 反証規律:
  Empirical hypothesis 台帳の各行は、(a) 事前固定された measurement profile、
  (b) 棄却条件(この観測が出たら当該 profile で棄却)、(c) profile 安定性
  (宣言された profile 族に亘る成立か単一 profile か)を必須列として持つ。
  検証時の profile 事後再選択は反証の回避として扱い、別仮説として行を分ける。

D8 選択データ優先:
  普遍性(colimit / pullback / pushout)への依存を定義に置かない。
  merge の overlap(base)、branch 間の輸送、力の接続、complement は
  すべて evolution profile の選択データである。
  これは AAT 第II部 定義7.1(admissible cover から生成される位相)と
  第X部 定理6.4(incidence はデータである)の方式の継承である。
  「マージ解決は貼り合わせの選択である」(T1)と普遍性は両立しない。
```

D5–D6 の位置づけ: 開発の統計力学(第VIII部)や Conway の法則は、
「現実についての無条件定理」ではなく「模型内定理 + 経験的仮説」として初めて誠実に語れる。
これは統計力学や熱力学が物理学で占める位置と同じである。

---

## 3. 中心対象: 開発系

SFT v2 の中心対象は**開発系(Development System)**である。

```text
𝔇 = (𝒯, 𝔛, 𝔖, Π, M)

𝒯 : 開発トレース site(時間)
𝔛 : 進化族(空間 = 場の配置の族)+ 辺上の輸送データ
𝔖 : 源構造(開発組織 = 参加者と力の生成)
Π : 方針(運動の法則 = コスト幾何と選好)
M : 計測輪郭の族(観測 = 軌道に沿った計器の族)
```

五成分はそれぞれ「時間・空間・源・法則・観測」であり、力学系の標準装備に対応する。
ただし力学系としての実質は §3.6 の生成子と挙動空間が与える(五成分は部品にすぎない)。
以下、各成分の数学的な形を statement level で固定する。

### 3.1 𝒯 — 開発トレース site(時間)

時間は線形ではない。開発は分岐し、合流する。バージョン履歴の DAG を site として扱う。

```text
開発トレース site 𝒯_E(evolution profile E で選択):
  台となる圏: selected version state を頂点、selected forward transition を辺とする
              有限 DAG 上の自由圏
              (revert は新しい前進辺として扱う。逆射は導入しない。
               categorical inverse が必要な regime は別の selected 構造として隔離する)
  cover:      selected merge family {A_i -> M} を admissible cover と宣言し、
              そこから生成される最小の位相(sieve ベース)を採用する
              (AAT 第II部 定義7.1 の方式。引き戻し安定性・合成は生成側で閉じる)
  overlap:    merge base(branch 対の共通底)は pullback で計算せず、
              evolution profile の選択データとして与える
              (AAT 第X部 定理6.4「incidence はデータである」の方式)
```

- **マージ点はその親 branch たちに被覆される**。この一文が第III部(マージ=降下)の土台になる。
- criss-cross 履歴(極大共通祖先が複数)は「base 選択はデータである」ことの正準例として本文に置く。
- マージ点 M を branch 群の colimit とは**読まない**。M は selected cocone であり、
  同じ親対から相異なる解決 M, M′ が作れることが理論の前提である(解決 = 貼り合わせの選択)。
- 線形履歴は cover が自明な特殊例である。
- **履歴書き換え**(squash / rebase / force-push)は trace site の商・押し出し
  functor 𝒯 → 𝒯′ として一項立てる。どの衝突類・ホロノミー witness が書き換えで
  生存・消滅するかは定理候補(witness 生存定理)であり、rewrite policy は
  evolution profile E の選択項目である。squash はダイヤモンド内部を消すので、
  witness の計算は書き換え前の trace 上で行うという測定契約が従う(解釈境界)。

### 3.2 𝔛 — 進化族と場の配置(空間)

```text
進化族:
  fiber 𝔛_t = X_{A_t}^{V, U_t, J, k}
    A_t は時点 t の selected Atom family(抽象データ。コードベースではない)

輸送データ(quiver connection 方式):
  𝒯 の各 selected 辺 e : t -> t′ に、部分 context 対応
    u_e : 𝔛_t <- K_e -> 𝔛_{t′}   (span; 生成・削除された context は対応の外)
  と cover 適合条件を、evolution profile の明示データとして与える。
  輸送は辺生成子の上にだけ与え、path へは自由合成で延長する。
  平行 path 上の輸送の一致は要求しない — その欠損こそが場の強さ(第II部の曲率)である。

場の配置(field configuration):
  Φ_t = fiber 上の選ばれた層データ一式
        (構造層 O^U、law algebra、obstruction ideal I_Ob、semantic 層、state 層)

歴史(history):
  トレース路に沿った場の配置の整合族(prestack / presheaf level)。
  merge cover に対する層条件(descent)は公理として課さない。
  課すと F(M) が親と base から一意に決まり、衝突解決の自由が消える。
  descent の成立は公理ではなく診断述語(衝突類の零性)である。
```

設計点:

1. **fiber は抽象の Atom family で index する**。「コードベース C_t が A_t を定める」という
   対応は解釈境界(付録)にのみ置く。数学本文に C_t は現れない(D4)。
   記法注記: AAT 正典は `X_C^{V,U,J,k}`(AG README。付録 A.2 はパラメータ組 (V,U,J,k) を扱う)。
   SFT 本文の `X_{A_t}^{V,U_t,J,k}` は AAT 記法の再定義ではなく、解釈境界を通じて得られた
   selected Atom family を index に使う **SFT 側の selected-family notation** である(D3 と整合)。
2. **base 上で動くのは Atom family だけではない**。law universe も動く: `U_t`。
   要求変更は lawful locus の目標を動かす(ポジションペーパー §9.5 の読みの継承)。
   ただし Flat_{U_t} と Flat_{U_{t′}} は異なる fiber 上の異なる law universe の locus であり、
   これを「同じ目標の運動」と読むには **law universe 輸送**(辺ごとの law 対応)が
   evolution profile の追加データとして要る(§10 台帳)。AAT 第V部 §8(repair comparison
   profile)・§10(transferred obstruction、定理10.5/10.6)は同一 site 上の先行機械であり、
   原則2.2「Law Universes Are Distinct Readings」の規律ごと継承する。
   **U_t 定数の regime(目標固定)を第一段の定理化対象とし、目標運動は第二段に分離する。**
3. **場の記憶**は独立概念ではない。トレース site とその上の配置の堆積が記憶そのものである。
   旧 CodebaseAsFieldMemory は第I部の一節に吸収される。

### 3.3 𝔖 — 源構造(開発組織)

**「参加者は場の参加者である」の文字通り化**。組織は力学系の変数である(パラメータではない)。

```text
組織圏 𝒪_t:
  対象: participant / team / mob(複数 participant の合成源)/
        delegator(model・prompt・policy などの生成様式の共有元)
  射:   selected reporting / collaboration / delegation
  注意: role(役割)は対象にしない。役割は力の型の分布として第II部の分類子から導く。
  注意: 「site」を名乗るのは communication cover(下記)を実際に使う定理が立つ場合に限る(D1′)。

二つの独立な被覆データ:
  communication cover: 会話・レビュー・会議由来の selected 被覆(組織側の位相)
  ownership 対応:      own_t ⊂ 𝒪_t × 𝔛_t(所有由来の被覆 index)
  この二つは独立に定義する。一方から他方を index として導くと
  Conway 対応(第V部)が定義の展開に退化する。

可視性割り当て:
  participant p に、p が読める場の部分データ V_p ⊆ Φ_t を割り当てる。
  (「層」を名乗るのは restriction 構造を使う定理が立ってから。D1′)
  可視性の力学: V_p の成長 = オンボーディング、唯一の cover 保持者の離脱 = バス事象、
  AI participant の V_p はセッション毎に蒸発し、組織記憶が trace 側へ移る。

生成(source):
  gen_p : (visible field, 目標場) -> 提案された力の族
  理論は trace に現れる生成だけを扱い、意図・心理については沈黙する。
  提案された力と適用された力を区別する(レビューは両者の間に立つ。第IV部)。

相関の担い手:
  二つの力が相関する ⇔ その源が共通の delegator を経由して分解する。
  同一 model / prompt から複製されたエージェント群の力は独立でない。
  この相関は第VIII部のアンサンブルの必須パラメータになる。
```

役割の違いは**生成する力の型の違い**として数学化される(型分類 τ は第II部で定義)。

```text
点を動かす力(feature / repair)     — 実務上は主にエンジニアが生成する
法則側・コスト側を動かす力          — 実務上は主にアーキテクトが生成する
semantic / contract 層への力        — 実務上は主にデザイナーが生成する
目標場の設定(lawful locus の移動)  — 実務上は主に PdM が生成する
選択の力(貼り合わせ・却下の選択)  — 実務上は主にレビュアーが生成する

役割は力に付き、人には分布として付く。
participant の「役割プロファイル」= 窓内で生成した力の τ 分布。
役割の流動性 = プロファイルの移動(エンジニアが設計もし、PdM がコードも書く)。
AI agent は専用公理を持たない participant である。違いは生成率・可視性・delegator 相関の形だけ。
```

**目標場と力の区別**: PRD・design doc・issue は場に直接作用しない。
participant を介して力を誘導する(目標場 → induced force ensemble)。
これは「PdM の文書がなぜコードを変えるのか」の因果を、源を介した二段構造として保存する。
なお「ポテンシャル」という語は使わない — 物理のポテンシャルは力の勾配源だが、
ここにはまだ勾配法則がない。gen の応答公理(ギャップ単調性)を置いた模型でのみ
potential 呼称を許す(§7 辞書)。

組織も時間発展する: `𝒪_t` は 𝒯 上の族であり、reorg は組織側への力である。
アーキテクチャと組織は**結合力学系**をなす(第V部 Conway 対応)。

### 3.4 Π — 方針(運動の法則)

物理と違い、開発系の運動法則は自然が与えない。組織が選ぶ。したがって法則は方針相対的である。

```text
コスト幾何(自己相互作用):
  現在の場の配置がコストを定める: cost_t(f)
  anchor: AAT 第VII部 定義10.1 Operation Distance・定義10.2 Distance to Flatness・
          §12 Repair Cost・§8 Metric Enrichment、AAT 第VIII部 定義10.6 Wasserstein Transfer Cost
  自己相互作用仮定(明示する): cost_t は Φ_t の局所障害質量に単調依存する。
  この仮定を置かない限り「場が力を形作る」は詩である(T5 の前提として明記)。

方針 Π の階層(混同しない):
  近視眼的散逸方針: 一段ごとに評価汎函数を下げる(局所最小に捕まり得る)
  有限先読み方針:   深さ B の探索で選ぶ
  Bellman 最適方針: cost-to-go 値函数 V を最小化する(migration の「一旦悪化して直す」を許す)
  統一装置: V を Lyapunov 汎函数に採る control Lyapunov function(CLF)。
  幾何汎函数 Φ_M と値函数 V の上下界比較は第VI部の必置補題である。
```

「場が力を形作る」は旧 attractor engineering の再建である:
アーキテクチャ設計とは、**望ましい進化が(値函数の意味で)低コスト経路になるように
コスト幾何を設計すること**。これで「良い設計は正しい変更を最小抵抗経路にする」が
数学の命題になる。

### 3.5 M — 計測輪郭の族(観測)

```text
計測輪郭の族:
  M = (M_t)_{t ∈ 𝒯} — 計器族は時間発展する(計器の追加・削除も系の出来事である)

計器(instrument):
  軌道に沿った period pairing の族(AAT 第VII部 §5 period / 第VIII部 profile)
  可観測性は pairing の言葉で立てる:
    計器族が障害類 α を検出する ⇔ ある計器 m について ⟨m, α⟩ ≠ 0
  (双線形構造を実際に使う。boolean チェックの改名にしない。D1′)

計器の源独立性:
  計器の評価が力の源と同じ delegator を経由しない、という独立性条件を
  明示仮定として扱う(同系 AI がレビューする場合、生成の盲点と計器の盲点が相関し得る)。

runtime 側:
  deploy / rollback は selected transition、incident は非計画の計器読み値として
  同じ枠に入る(解釈境界)。計器族の拡大(観測軸の追加)は controller の作用の
  一型である(第IX部。旧 InstrumentingIntervention の転生)。

沈黙規律: 未測定軸について理論は語らない(AAT VIII 継承)。
```

### 3.6 生成子と挙動空間(力学系としての実質)

トレース site は**実現した履歴の記録**であり、それ自体は運動法則ではない。
力学系を名乗るには、可能な軌道の空間とそれを生成する法則が要る。

観測系と生成模型を分ける(「橋渡し」が定義から真になるのを避けるため):

```text
ObservedDevelopmentSystem(記録):
  実現済み trace 𝒯 と配置族 Φ_t を持つ。

GenerativeDevelopmentModel(法則):
  source rule・policy・admissible force schema・measurement rule から
  生成子(閉ループ更新対応)を持つ:
  T_Π : (Φ, 𝒪, U) ⇒ P(次の (Φ′, 𝒪′, U′) と、それを実現する力・輸送)
  = 源が可視場を見て力を生成し、方針が選好し、選択された力が配置を更新する
    一段の合成。非決定・方針添字つき(coalgebra x -> P(F × X) の形)。

挙動空間:
  𝔗(𝔇, Π) = 初期条件から T_Π が生成する許容トレース(と配置族)全体

TraceRealization 定理(第I部必置; 検査可能な形):
  観測 trace が T_Π の解軌道である
  ⇔ 各辺に source generation witness・policy selection witness・
     transport witness・field update witness が存在する。

命名規律:
  T_Π を trace から後付けで構成する場合、上の主張は定理ではなく
  reconstruction lemma と呼ぶ。
```

アトラクター・可制御性・安定化(第VI・IX部)はすべて挙動空間上の量化であり、
この節なしには定義できない。

---

## 4. 中心描像: 追跡力学と自己相互作用

部構成に入る前に、理論全体を貫く力学的な像を一つに固定する。

```text
追跡力学(pursuit dynamics):

  目標:   lawful locus Flat_{U_t}(要求とともに動く)
  点:     X_{A_t}(力が動かす)
  ギャップ: e_t = 障害質量 / distance-to-flatness(AAT VII/VIII の測度)

  誤差力学(可能性と不可能性は、別々の仮定を持つ二つの模型定理に分ける):

  Tracking Model A(有界性):
    e_t >= 0、repair は δ_t <= min(e_t, r_t)、drift は 0 <= v_t <= v_max
    e_{t+1} <= max(0, e_t − r_min) + v_max
    r_min > v_max ⇒ e_t は究極有界

  Impossibility Model B(線形成長):
    すべての方針について δ_t <= r_max、外生 drift は v_t >= v_min
    v_min > r_max + ε ⇒ e_t >= e_0 + εt

  注意: 上側不等式だけからは線形成長は出ない。不可能性側は
  下側仮定(最悪入力・不可避注入)を明示して初めて定理になる。

  開発とは、動き続ける lawful locus への追跡過程である。
```

この描像は装飾ではなく、次の定理群の仮定として働く(旗艦 T0、§6):

- **追跡可能性**(Model A): 修復帯域の下界が目標速度の上界を上回る regime では
  ギャップは有界に留まる(究極有界性)。
- **追跡不可能性**(Model B): 目標速度の下界が修復帯域の上界を超える regime では
  ギャップは線形成長する。修復に必要な最小コストの下界は AAT 第VIII部 系8.7
  (Essential Repair Lower Bound)が r_max 側の評価を与える
  — **修復下界は開発速度の限界**として読める。この理論で最も本物になり得る不可能性定理である。
- **負債の定義**(利子つき): 負債ストック = ギャップ e_t。
  利子(carrying cost)= 自己相互作用(§3.4)による修復コストの増分
  I_t = cost_t(repair | Φ_t) − baseline_cost_t(baseline は模型データ)。
  技術的負債汎函数 = ギャップの重みつき時間積分 + 利子の累積。
  ギャップ積分だけでは「将来の変更コストを増やす」という負債の本性(interest)が消える。
  利子項が T5(吸収域)・T6(骨化)への接続を与える。
- **Lehman 第一法則**(絶えざる変化)= 「v は零にならない」という Empirical hypothesis(台帳行)。
- **目標編集の力**: U_t を点の方へ動かしてギャップを消す(spec capitulation)は
  理論内の実在の力の型である(τ の一類)。名前を与えないと負債の幾何がゲーム可能になる。
- ギャップの比較には**ギャップ輸送補題**が要る(目標が動いたとき既存ギャップ値が
  どう輸送されるか。anchor: AAT 第VIII部 定義6.1 Witness Perturbation Distance・
  定理候補6.5 Monotone Witness Stability)。U_t 定数 regime では不要(第一段)。

これに自己相互作用(§3.4)と組織の共進化(§3.3)を合わせると、SFT v2 の全体像は:

```text
コードベースは場であり、
PR は力であり、
開発組織は力の源である。

場は力のコストを形作り、力は場を変え、
源は場を見て力を生み、目標は要求とともに動く。

開発とは、アーキテクチャ幾何の上を流れる場の時間発展である。
```

この三行は看板(スローガン)である。本文の核では「場の配置 = selected Atom family 上の層データ」
であり、「コードベース ↔ A_t」「PR ↔ 力」の読みは解釈境界を一度通す(D4)。
理論の看板三行は次で置き換える(旧「SFT はソフトウェア進化を計算可能にする」の後継)。

```text
AAT はソフトウェアに空間を与える。
SFT はソフトウェアに時間を与える。
開発は、その時空の中の力学である。
```

計算可能性は看板から降ろすが、捨てない: AAT と同じく、有限・selected regime での
構成がそのまま計算可能性を与える。各部に有限 worked example を必置とする。

---

## 5. 部構成案

AAT AG 版と同じ「部 + 付録」構成。各部に、目的・中心対象・中心定理候補・AAT アンカー
(証明状態つき)・新規数学の要否を示す。

| 部 | 題 | 中心対象 | AAT アンカー(状態) |
| --- | --- | --- | --- |
| 序 | 新しい対象 | v2 contract、開発系 𝔇、生成子と挙動空間、規律、非主張 | README・付録(規律) |
| I | 開発時空 | トレース site 𝒯、進化族と輸送データ、場の配置、歴史、履歴書き換え商 | 第II部 定義7.1(方式)、第X部 定理6.4(方式)、第IX部 trace category(proved 定義) |
| II | 力の幾何 | 台つき部分変換、commute(primitive)、接続、力の曲率、ダイヤモンドホロノミー、可積分性 | 第IX部 §7(**candidate**)、第VI部 定義9.4・monodromy(proved 定義)、第IV部 §9 boundary holonomy(certified) |
| III | マージと降下 | 三段 filtration(cocone 判定 / Čech H¹ / 導来 Tor)、並列平坦性、積方向ダイヤモンド | 第IV部 Čech(certified)、第V部 導来衝突(certified)、第X部 SAGA(certified) |
| IV | 参加者と組織 | 組織圏 𝒪、delegation と相関、所有対応、可視性、生成、目標場、レビュー=計器評価+降下選択 | 第II部 site 一般論(形式のみ借用) |
| V | Conway 対応 | communication cover と ownership 由来被覆(独立データ)の比較、Conway 障害、reorg/refactor 双対 | 第IV部 cohomology(形式)。**statement 未確定 = 研究課題** |
| VI | 力学: 運動の法則 | 追跡定理 T0、質量収支則、方針階層と CLF、アトラクター(吸収類)、ゲージ合同定理 | 第IX部 §5–6(certified)、第VIII部 定理8.5–8.6・系8.7(certified)、第VII部 §8–12(定義) |
| VII | 変形と可能性 | 変形空間(Ext 次数)、拡張障害、剛性・骨化、進化容量、モジュライ族 | 第VI部 §3 cotangent/tangent complex・§6 Square-Zero Lifting / Kuranishi(certified)、第VI部 §15 Dec stack(定義) |
| VIII | 開発の統計力学 | 力のアンサンブル(相関つき)、Boltzmann 型エントロピー、第二法則(計数補題)、regime 境界、throughput | 第VIII部 measurement packet・mass(定義・certified) |
| IX | 観測と制御 | 計器 pairing、可観測性(annihilator 型)、可制御性、フィードバック統治、究極有界性 | 第VII部 §5 period(certified)、第VIII部 profile(定義) |
| X | 寿命と長期挙動 | 軌道 regime、終焉(有効変形の枯渇)、migration=base change、継承 | 第X部 SAGA descent(certified)、第V部 repair(certified) |
| 付録 | 境界と実例 | アナロジー辞書(3列)、claim ladder、解釈境界、正準有限実例、先行研究接続、仮説台帳 | 付録(status ledger 形式) |

序には非主張を明記する: プロダクト価値の判定(U_t の価値は外生入力)、個人の意図・心理・信念、
悪意ある源の意味論(trust boundary の型だけ与える)、runtime コストの経済学(計器軸としてのみ扱う)、
一般 AI 安全性。

序の冒頭には **v2 contract** を置く:

```text
SFT v2 の本文は、現実の開発活動を直接定義しない。
本文の対象は、selected profile によって構成された開発系 𝔇 と、
その上の生成子 T_Π の解軌道である。

実在の repository / PR / CI / organization との対応は、
付録の解釈境界を通じてのみ読む。

したがって SFT v2 の定理は、現実の開発系についての無条件主張ではなく、
selected development system の内部定理、Certified bounded inference、
Model theorem、または Empirical hypothesis である。
```

各部の要点:

### 第I部 開発時空

§3.1・§3.2・§3.6 の内容の本体化。加えて:

- cover 公理は「宣言された admissible family から生成される位相」で閉じる(D8)。
  本文では、生成された最小位相が cover の引き戻し安定性・合成閉包を満たすことの
  構成を一度明示する。正準有限実例に criss-cross(base 選択の非一意性)を必ず含める。
- 環境・tenant・feature flag は 𝒯 の積方向として読める(第III部の積方向ダイヤモンドの土台)。
- 履歴書き換え商 𝒯 → 𝒯′ と witness 生存定理候補。
- 新規数学(リスク中): 辺生成子上の輸送データ(u_e の型、cover 適合、マージ点の二重輸送)、
  可積分性障害の受け皿となる **t-依存 selected incidence site** の有限構成
  (AAT 第IX部の固定積 site `Tr_E × X` は X 固定が前提であり、fiber が動く版は新設。
  AAT IX 定義3.4 の reading schema 条項を継承し、データ未固定の式を定義に昇格させない)。

### 第II部 力の幾何

```text
力(二層で定式化: 位置に載る前の schema と、trace 上の実現):
  ForceSchema:
    s = (W_s, C_s, φ_s, dom_s, τ(s))
    W_s = 台(触る範囲の selected context family)
    C_s = selected complement family({W_s, C_s} が selected cover をなす。
          complement は補集合演算ではなく選択データである)
    φ_s = 局所作用、dom_s = domain 条件、τ(s) = 力の型(後述)
    trace 辺にはまだ載っていない。

  AppliedForce:
    f = (e, s, u_f, witness)
    e : t -> t′ は 𝒯 の辺、s は ForceSchema、
    u_f = selected 輸送(complement 同一視を含む)、
    witness = before / after 配置と適用の証拠
  「台の外では恒等」の正確な形: u_f に沿った C_s 上の層データ比較が恒等。

locality 公理(schema level):
  φ_s は Φ|_{W_s} のみに依存し、domain 条件を満たす任意の配置に適用できる
  (patch 型の部分局所作用素)。これが力の再適用・輸送を可能にする。

commute(primitive; Darcs 型。ForceSchema または transported AppliedForce の上で定義):
  部分演算 (f, g) ↦ (g^f, f_g)、定義式 g^f ∘ f = f_g ∘ g(定義されるとき)。
  trace 上の AppliedForce は schema 合成の実現として扱う。
  transport 不能な対(commute が未定義)こそ第一の障害である。

遠隔可換(定理候補):
  仮定: 台は selected dependency closure に関する証明された過大近似である。
  supp(f) ∩ supp(g) = ∅(selected cover の意味で)
    => commute が定義され、transport は自明(g^f = g, f_g = f)

接続(必置定義):
  接続 = selected transport 規則の族(ダイヤモンドごとの選択データ。正準ではない)。
  Darcs の commute、OT の transform、rebase 規則はその実例(解釈境界)。
  曲率・ホロノミーはすべて接続に相対化される。

力の曲率:
  δ(f, g) = 両 transport が存在するときの二辺形比較の残差 witness。
  abelian 係数 regime での受け皿(いずれか選択を宣言):
    AAT 第VI部 定義9.4 presentation two-complex の 2-cell 値、または
    t-依存 selected incidence site 上の total complex の (1,1) 成分。
  受け皿未固定の式は reading schema(D2)。

ダイヤモンドホロノミー:
  branch -> 2 経路 -> merge における二つの平行輸送の M 上での比較残差
  (「一周」ではない。DAG に逆射はない)。= merge residue。
  局所曲率零から大域残差零は従わない(path monodromy ノートの主定理と整合)。

可積分性(SFT 側対応定理候補):
  ob(f) ≠ 0 in H¹(t-依存 incidence site, selected 係数)
    => f は大域 lawful 進化へ積分できない。
  AAT 第IX部 定理候補7.2 は固定積 site 上の AAT 側対象としてそのまま残る。
  SFT 側対応物との関係は「固定 fiber regime では両者が一致する」という比較命題で接続する。
  7.2 が candidate である以上、この帰結に依存する主張はすべて conditional と明記する。

力の型分類:
  τ(f) ∈ { 点 / 法則 / コスト / semantic / 目標編集 / 選択 }
  refactor = semantic 射影が零の力(選ばれた semantic profile に相対的なゲージ)
  repair   = 障害類を消す方向の力(AAT V repair・X SAGA)
```

### 第III部 マージと降下

**T1 は分類定理ではなく、マージ構成の進行に相対的な三段の診断 filtration 定理である。
段階0 が成立しない場合、段階1 以降は未定義または conditional になる(本文に明記する)。**

```text
branch = span A <- B -> C(B = selected base。criss-cross では選択データ)

段階0(台・状態圏):
  selected cocone の validity 判定。
  「押し出しが存在しない」と「標準的融合が存在しない(非正準性)」を区別する。
  集合的な状態圏では押し出しはほぼ常に存在する — textual conflict の実体は
  「valid state の部分圏に落ちない / 標準的融合の選択が要る」である。
  「押し出し」の語は状態・presentation 圏でのみ使い、𝒯 側では cover の語だけを使う。

段階1(法則・Čech):
  base B の支持被覆の nerve に輸送した law データの Čech H¹
  (site・cover・係数を宣言する。AAT 第X部 §4/§7 の additive regime を借用)。
  branch 間の輸送(接続)が先に要ることに注意 — 段階1 は第II部に依存する。

段階2(導来):
  構成済み X_M の内部で、二つの branch 内容を transported loci として同定し
  (同定データは明示的仮定)、その導来交叉の Tor を読む(AAT 第V部 定義4.1・定理6.1)。
  「テキストは貼れたが意味が壊れる」の数学的実体。
```

- **バージョン管理は降下理論である**: マージ解決 = 貼り合わせデータの選択。
  第X部 SAGA(semantic repair descent と Čech H¹ の比較)が直接の機械を提供する。
- 並列開発平坦性(定理候補)は二つの別仮定に分けて述べる:
  - 自明側: 台が互いに素な力の族は commute し合流可能 [Formal theorem 候補]。
  - CRDT 側: 台が重なっても、状態を metadata で拡大した理論への持ち上げの中で
    曲率 witness δ(f,g) が構成的に消える [Model theorem]。
    **CRDT は「可換化(商)」ではなく「可換(半束)理論への持ち上げ」である。**
    収束には結合・可換・冪等(ACI)+ inflationary update(状態ベース)、または
    concurrent 対の可換性 + causal delivery + 冪等配送(操作ベース)を仮定として明示する。
    局所可換(曲率零)から大域順序非依存は従わない(ホロノミーは別条件)。
- 台の推定は**証明された過大近似**でなければならない(selected dependency closure に関して)。
  過小近似した台で「素だから安全」と結論する使い方は unsound(解釈境界の計器契約)。
- **積方向のダイヤモンド**: feature flag / tenant / 環境軸の分岐と収束(flag 除去 = 積方向のマージ)
  にも T1–T3 の機械を再利用する(トランクベース開発はダイヤモンドが branch 軸でなく
  flag 軸に立つ)。monorepo の cross-project atomic commit は多重台の力の例。
- 系: AI エージェント群の安全並列度は台の重なりと flatness で上下界を持つ [Model theorem]。
  実運用への対応は Empirical hypothesis 台帳(H4 と接続)。
- 先行研究は「包摂」ではなく**接続**として付録に置く(§13 の言い直し)。

### 第IV部 参加者と組織

§3.3 の本体化。追加の要点:

- **レビューの二重の型**: レビュー = 計器評価(pairing の読み)+ 降下データの選択、の合成。
  ラバースタンプ = 分離能力が退化した計器での選択(承認は続くが計測が止まる)。
  この定義が第VIII部の相図(実効分離容量)と第IX部の可観測性を接続する。
- 提案された力と適用された力の区別(レビューコメントによる力の改変)を保存する
  (旧 ProposalAccounting が守っていた区別の継承)。
- AI agent は participant の一型であり、専用の公理を持たない。違いは生成率・可視性・
  **delegator 相関**の形だけ。同一 model / prompt 由来の力の相関は独立性仮定を壊す
  (第VIII部の必須パラメータ)。
- 沈黙規律: 意図・心理・文化は扱わない。trace に現れる生成だけを扱う。

### 第V部 Conway 対応

```text
Conway 対応(研究課題; statement 未確定):
  communication cover(組織側の位相)と ownership 由来の architecture 被覆は
  独立に定義された二つの被覆データである(§3.3)。
  Conway 障害 = この二位相の不整合の測度(descent failure として測る)。

reorg / refactor 双対:
  Conway 障害を消す 2 方向(組織側を動かす / 幾何側を動かす)。
```

- 定式化は cohomology から始めない。二つの被覆の refinement / common refinement /
  nerve map の不整合という有限組合せ論から始め、障害の類はその後に置く。
- **採否条件**: 正準有限実例で、適合例(障害零)と障害類非零例の**両方**を構成できること。
  これができるまで T4 は旗艦表で「研究課題」と表示する(定理を名乗らない)。
- 経験的な mirroring 研究(Conway / MacCormack 系)は Empirical hypothesis として
  台帳へ(D7 の棄却条件つき)。
- 新規数学の最大株。research loop の主要 GOAL 候補。

### 第VI部 力学: 運動の法則

§3.4・§3.6・§4 の本体化。**内容は汎函数の選択と力の類型への適合性に宿る。
停止性自体(有限 + 整礎 ⇒ 停止)は自明であり、旗艦にしない。**

```text
T0 追跡定理 [Model theorem](旗艦; §4 の Model A / B):
  Model A: r_min > v_max ⇒ ギャップ汎函数は究極有界(Foster–Lyapunov 型)
  Model B: v_min > r_max + ε ⇒ ギャップは線形成長(下側仮定を明示した不可能性)
  r ≈ v の帯が第VIII部の regime 境界を与える(D6 の標準形)

質量収支則(定理候補; 停止定理の置き換え):
  ΔΦ_M = (目標移動・feature による注入) − (repair による散逸) + (merge residue) 
  かつ refactor(ゲージ)項 = 0
  即ち「harmonic mass は {repair, refactor} という力の類の共通 Lyapunov 汎函数だが、
  {feature} を含めると違う」という、汎函数と力の類型の適合定理。
  anchor: AAT 第VIII部 定理8.5(Hodge 分解)・定理8.6(Harmonic Debt Minimality)。
  有限散逸停止(AAT IX 定理5.3)はこの静的目標特殊例の系に格下げする。

ギャップ輸送補題(必置):
  目標(law universe)が動いたときのギャップ値の輸送。
  anchor: AAT 第VIII部 定義6.1 Witness Perturbation Distance・定理候補6.5。

追跡不可能性定理(候補):
  AAT 第VIII部 系8.7(Essential Repair Lower Bound)が一段予算を超える
  到達可能状態が存在すれば、いかなる方針でも追跡は失敗する。
  修復下界を「開発速度の限界」として使う不可能性定理。

方針階層と CLF(§3.4):
  近視眼的散逸 / 有限先読み / Bellman 最適。値函数 V と幾何汎函数 Φ_M の上下界補題。

アトラクター(挙動空間上で定義):
  需要過程(目標移動を rate λ の明示的確率過程として入れ、系を Markov 連鎖化)の下で、
  アトラクター = 誘導連鎖の吸収類、吸引域 = 吸収確率(閾値つき)の状態集合。
  may / must の量化子は常に分離する(有限離散に位相的「近傍」はない)。

悪い吸引域の模型定理 [Model theorem](空虚化しない三要件つき):
  (1) cost の内生化: cost_t は Φ_t から第VII部 metric enrichment 経由で導出(自由パラメータ禁止)
  (2) 需要過程の明示
  (3) 比較形: 同一予算で、貪欲方針は mud 類に確率1で吸収されるが、
      修復比率 ρ > ρ_c の方針は正再帰で質量の平均有界を保つ(Foster–Lyapunov 条件)。
      臨界値 ρ_c の存在が D6 を満たし、第VIII部の相構造を同じ定理から導く。

ゲージ合同定理(「Noether 型」の置き換え; 不変量命題):
  semantic 零の力が生成する関係 ≈ を取る(力は一般に可逆でないため群作用ではない)。
  ≈ が遷移関係・cost・観測クラス・衝突 witness と両立する congruence / bisimulation
  であるという仮定の下で、値函数・到達集合・衝突類は quotient system に降下する。
  「リファクタは(≈ が congruence である限りで)可能性を変えない」の正確な形。
  変分構造を定義するまで Noether を名乗らない。
```

merge residue の収支(第III部)と branch 並列度(第VIII部)をこの部の定理群に接続し、
「力学 + 降下」という本理論固有の軸を守る。

### 第VII部 変形と可能性

**ForecastCone の後継**。未来を予言する代わりに、現在の幾何の変形理論を読む。

```text
変形空間(AAT の Ext 次数規約に揃える):
  automorphism = Ext^{-1}、一次変形 = Ext^{0}、拡張障害 = Ext^{1} = Obs
  anchor: AAT 第VI部 §3(定義3.1 Cotangent Complex・定義3.2 Tangent Complex)・
          §6(Square-Zero Lifting Obstruction・Kuranishi)
  注意: AAT 第VI部の変形理論は「固定 geometry 内の stratum / test object の変形」である。
  アーキテクチャ配置そのもの・law 構造そのものの変形理論は新規数学であり、
  §10 台帳にその範囲で申告する。

剛性と骨化:
  変形空間の縮小 = 進化容量の減少
  骨化(定理候補): 剛性化方針の下で有効変形空間は単調減少する
  レガシー = 高障害 × 高剛性(直せない × 動けない)の regime

モジュライ:
  分解 stack Dec_{U_t}(X_t)(AAT 第VI部 §15)は固定 fiber の対象であり、
  開発は「𝒯 上の stack の族の中の path」として読む。
  アーキテクチャ自体のモジュライは新規数学(台帳)。

変形空間上のコスト構造(必要):
  operation cost からの誘導、または AAT 第VII部 §8 metric enrichment の fiberwise 借用(台帳)。
```

- 「この設計からどんな進化が可能か」= 変形空間、「なぜこのシステムは動けないのか」= 剛性。
  予測(prediction)ではなく可能性(possibility)の理論であることを明示する。

### 第VIII部 開発の統計力学

すべて **Model theorem / Empirical hypothesis** ラベルの規律下で書く(D5–D7)。

```text
力のアンサンブル:
  源の族が生成する力の分布。delegator ごとの生成核 + 相関パラメータ ρ を必須で持つ
  (同一 model 由来の力は独立でない。§3.3)。

アーキテクチャエントロピー(主候補を宣言):
  S(m) = log #{ Φ : Packet_M(Φ) = m }
  — AAT 第VIII部 measurement packet の繊維サイズの対数(計器が残す無知の量)。
  粗視化(packet の選択)は模型データの一部として宣言する。
  比較可能性条件(必置): fiber が時間で変わると S は素朴には比較不能である。
  固定サイズ族・固定参照測度・輸送写像のいずれかを模型データに入れ、
  エントロピーの時間比較を許す条件を先に置く。
  可観測性(第IX部)= エントロピー零、という部間接続を持つ。

第二法則(模型定理の形; 実体は計数補題):
  「サイズ n の配置族で質量 <= m の配置の割合は指数的に消える」(位相体積論法)
  + 確率的混合 + 低エントロピー初期条件の下で、無統治極限では
  障害質量・エントロピーは非減少 [Model theorem; D6 により統治相の非空性も併示]。
  Lehman の進化法則群はこの部の Empirical hypothesis 台帳行(D7 の棄却条件つき)。

regime 境界(「相転移」を名乗らない):
  誘導連鎖の再帰 / 推移境界(queueing の λ < μ 型)として定義する(有限系でも鋭い)。
  真の相転移を語る場合のみ、系サイズ n → ∞ の族上の sharp threshold として別立てする。
  有限系に非解析性はない(§7 辞書)。臨界指数の語は使わない。
  パラメータには統治強度・review の実効分離容量(承認スループットではない。第IV部)・
  目標速度を含める。模型定理候補: 臨界負荷を超えると、承認が継続していても
  実効計器族が lawful / drift を分離しなくなる(可観測性崩壊駆動の regime 遷移)。

throughput(導出する; 仮定しない):
  N エージェント、台の重なり分布から衝突確率 p(N) を第III部の条件で導出し、
  review 帯域 μ の再試行つき待ち行列として T(N) の上界(Universal Scalability Law 形)を導く。
  安定条件が「安全並列度」の上界を与える。
  相関 ρ の増加は p(N) を押し上げる(独立仮定は危険側に外れる)。
  模型定理候補: 同能力なら混成 delegator 群のコヒーレントドリフトは
  単一 delegator 群より小さい(diversity premium)。
```

### 第IX部 観測と制御

- 可観測性 = 計器 pairing による分離(annihilator 型: 検出 ⇔ ⟨m, α⟩ ≠ 0)。
  **pairing の双線形構造を実際に使う最初の定理をこの部に置く**(D1′ の模範)。
- 可制御性 = 統治された源で到達できる領域(挙動空間上)。
- フィードバック統治: controller = 観測に基づく方針の変換。
  計器族の拡大(観測軸の追加)も controller の作用の一型(旧 InstrumentingIntervention の転生)。
  参照枠は離散事象系の監督制御(Ramadge–Wonham: 可制御事象・可観測事象・supervisor 合成)。
- **安定化定理 T8(仮定を明示した形に書き直し)**:

```text
仮定:
  (1) Φ-detectability: 計器読みから汎函数 Φ_M の値が推定可能
  (2) 沈黙軸の有界結合: 未測定軸から測定軸への影響に ISS 型のゲイン上界
      (無仮定では沈黙軸に蓄積した負債が測定軸へ結合して反例を作る)
  (3) 一様修復可制御性: 到達可能域の各状態で予算内の Φ 減少力が存在(能力下界)
  (4) 目標速度上界(§4 の v)
  (5) 計器の源独立性(§3.5)
結論:
  軌道は lawful locus の近傍に究極有界(ultimate boundedness / practical stability)。
  漸近安定は主張しない。
```

- runtime / incident の再建: incident = 非計画の計器読み値、deploy / rollback = selected
  transition。incident 対応 = 計器族拡大 + repair force + 台帳更新、として同じ枠で扱う。
- 沈黙規律: 未測定軸は語らない(AAT VIII 継承)。

### 第X部 寿命と長期挙動

```text
軌道の regime: 誕生 -> 成長 -> 安定 -> 骨化 -> 終焉

終焉判定(定義; 恒偽にならない形):
  有効変形の枯渇 =
  { ξ ∈ 変形空間 : ξ が selected gap 汎函数を strict に減らす、
    または selected 目標方向成分が非零 } ∩ 予算球 = ∅
  (零変形は常に存在するので、変形空間と予算球の単純な交叉では系は死ねない)

終焉定理(候補):
  有効変形の枯渇状態は、外生予算の増加なしには吸収状態である(挙動空間上)。

migration = 開発時空の間の base change / 場の輸送(SAGA descent が素材)
継承     = 系の置換 = 開発系の射
供給:     依存 bump = 他の開発系が生成した力の輸入(𝔇′ -> 𝔇 の base change 読み。
          悪意の意味論は非主張、trust boundary の型のみ)
```

- 終焉判定には runtime 側計器の読み(第IX部)を軸として含める(旧 EndOfLifeDecision の
  runtime risk 軸の継承)。

### 付録

- **アナロジー辞書(3列: 安全 / 条件付き / 輸入禁止)**(§7 参照)。
- claim ladder(D5)と Empirical hypothesis 台帳の書式(D7 の必須列つき)。
- **解釈境界**: 実在物 ↔ 理論対象の対応を一度だけ置く(下表)。本文はこの表を参照しない。
- **正準有限実例**: 小さな開発系(2 チーム、4 module、1 branch/merge)で、
  クーポン要求を目標場とし、誘導された 2 つの力の衝突類をダイヤモンド上で手計算する。
  必置ケース: criss-cross(base 選択)、三段 filtration の各段の実例、
  Conway の適合例と障害非零例(第V部の採否条件)。
  (旧 running example の転生: 旧版は path 名を列挙した。新版は H¹ 類を計算する。)
- **先行研究の接続**(「包摂」を名乗らない): 各理論について
  「同型な部分 / SFT が加える層 / SFT が再導出しないもの」の三行書式で書く。
  対象: Darcs patch theory(commute)、Mimram–Di Giusto "A Categorical Theory of
  Patches"・Pijul(merge = 押し出しの先行)、homotopical patch theory、
  OT(TP1/TP2)、CRDT(SEC; ACI 半束)、Horwitz–Prins–Reps program integration
  (「テキストは貼れたが意味が壊れる」の PDG 干渉検出としての先行)、
  Mazurkiewicz trace / conflict-serializability / Lipton mover(遠隔可換の先行)、
  directed algebraic topology(順序依存の幾何化の先行)、
  Conway・mirroring 研究(MacCormack, Colfer & Baldwin)、Lehman(FEAST を含む)、
  change entropy(Hassan)、socio-technical 系。
  SFT の新規性の主張は三点に集中する: **衝突の三層分離(法則 H¹ と導来 Tor の区別と
  SAGA 接続)、law 構造の変形理論(骨化)、二位相の不整合としての Conway 障害**。

```text
解釈境界(付録に置く対応表の骨子):
  リポジトリ状態           <-> selected Atom family A_t と fiber(観測は ArchMap 側の契約)
  commit / PR              <-> 力(台・輸送つき部分変換)。提案された力と適用された力を区別
  branch / merge           <-> span / selected cocone / cover(base 選択はデータ)
  merge queue / 投機ビルド <-> 曲率計器(両順序輸送の比較)
  squash / rebase          <-> トレース商 functor(witness は書き換え前に計算する)
  org chart / CODEOWNERS   <-> 組織圏 + 所有対応(communication cover は別途観測)
  model / prompt / policy  <-> delegator(相関の担い手)
  PRD / design doc         <-> 目標場(lawful locus の移動)
  CI / テスト              <-> 計器(period pairing)
  deploy / rollback        <-> selected transition
  incident                 <-> 非計画の計器読み値
  レビュー                 <-> 計器評価 + 降下データの選択
  AI agent                 <-> participant(delegator 相関を持つ源)
```

- **反証仮説の初期セット**(P1 で台帳へ先置き; D7 の列つき):

```text
H1 三層衝突の分離:
  テキスト衝突なしで auto-merge した変更対のうち、selected dependency closure の
  重なりを持つものは、持たない対照群より短期 revert / hotfix 率が有意に高く、
  テキスト重なり単独ではこれを予測しない。
H2 曲率計器:
  両順序の投機適用による δ(f,g) の witness は、diff サイズ基準を超えて
  post-merge 欠陥を予測する(merge queue の投機ビルドが計器の半分を既に実装している)。
H3 レビュー負荷の regime 遷移:
  負荷閾値超過期間は、承認レート維持のままラバースタンプ徴候を示し、
  遅延して障害質量 proxy が上昇する。
H4 diversity premium:
  同能力の混成 delegator 群は、単一 delegator 群より hotspot 重なり衝突率が低い。
```

---

## 6. 旗艦定理群と 10 年の工学課題

理論の背骨となる 9 本。各行に主張種別と AAT アンカー状態を明示する(採否規律 2)。
定理・定義・スローガンを混在させない: T6 の終焉判定は定義であり、定理は吸収性の形で別に立つ。

| # | 旗艦(候補) | 形 | 部 | 種別 / anchor 状態 |
| --- | --- | --- | --- | --- |
| T0 | 追跡定理 | Model A: r_min > v_max ⇒ ギャップ究極有界。Model B: v_min > r_max + ε ⇒ 線形成長(別仮定の二模型)。r ≈ v の帯が regime 境界 | VI, VIII | Model theorem / AAT VIII 系8.7(certified)を下界側で使用 |
| T1 | マージ診断 filtration 定理 | merge は三段 filtration(cocone 判定 / 法則 Čech H¹ / 導来 Tor)で診断され、段階0 不成立時は以降 conditional。解決は貼り合わせの選択である(最後の一文は原則) | III | Certified bounded 目標 / AAT IV・V・X(certified) |
| T2 | 並列開発平坦性定理 | 台が素 ⇒ commute・合流 [Formal 候補]。係数拡大で δ≡0 の持ち上げ(CRDT 型模型)でも合流 [Model theorem] | II–III | 混合 / AAT V(certified) |
| T3 | 力の曲率・ホロノミー定理 | 接続に相対化された順序依存性 = 曲率; ダイヤモンドの平行輸送比較 = merge residue; 局所零曲率から大域零残差は従わない | II | 定理候補 / AAT VI 定義9.4(定義)・IX 7.2(**candidate**; conditional 明記) |
| T4 | Conway 対応 | communication cover と ownership 被覆(独立データ)の適合と障害類 | V | **研究課題**(statement 未確定; 採否条件 = 適合例と障害例の両構成) |
| T5 | 内生コスト吸収域定理 | 内生 cost + 需要過程の下で、貪欲方針は mud 類に吸収され、修復比率 ρ > ρ_c で質量有界(比較形) | VI | Model theorem(D6 充足: ρ_c が相境界)。「測地線」は metric enrichment から実構成するまで名乗らない |
| T6 | 変形剛性定理 | 進化容量 = 有効変形空間; 剛性化方針下で単調減少(骨化)。終焉判定は定義、終焉の吸収性が定理 | VII, X | 定理候補 / AAT VI §3・§6(certified)。配置自体の変形は新規数学 |
| T7 | 開発の第二法則 | 明示模型内で無統治極限は質量・エントロピー非減少(実体は計数補題)+ 統治相の非空性 | VIII | Model theorem(D6 標準形) |
| T8 | フィードバック安定化定理 | detectability + 沈黙軸有界結合 + 修復可制御性 + 目標速度上界 + 計器独立性 ⇒ 究極有界 | IX | Certified bounded 目標(仮定 5 点を明示) |

10 年の工学課題への対応(理論の賭けどころ):

| 工学課題(今後 10 年) | 対応する理論 |
| --- | --- |
| AI エージェント大量並列開発(マージ地獄、swarm 統治) | T2, T3, T1 + 第IV部(delegator 相関)+ 第VIII部 throughput・H4 |
| 組織設計とスケーリング(Conway 逆転、チーム分割) | T4 + 第IV–V部 |
| 技術的負債・レガシー・モダナイゼーション | T0, T5, T6 + 第VII, X部(骨化・migration) |
| 統治の自動化(review 自動化、policy as code) | T8 + 第IX部(監督制御)+ H3 |
| 開発生産性の科学(速度限界、律速の同定) | T0, T7 + 第VIII部(regime 境界・throughput) |
| 規制対応・監査(AI 規制、SOC2) | 目標場としての外部法的源 + 要求計器と evidence contract + 期限付き到達可能性(第IX部) |
| サプライチェーン(依存 bump、外部生成力) | 第X部の輸入(base change)+ trust boundary の型(悪意の意味論は非主張) |

賭けの構造を明示しておく: T1–T2 は AAT の certified 機械(IV/V/X)で射程内にあり、最初に固める。
T3 の可積分性帰結は AAT IX 7.2(candidate)に依存する部分が conditional。
T4・T6(配置変形)は新規数学が必要な高リスク・高価値株で、research loop に回す。
T0・T5・T7 は Model theorem として D6 を満たす形で書けるかが勝負。T8 は仮定 5 点の明示で到達可能。

---

## 7. 物理アナロジー辞書と限界

「本物になる」とは、ソフトウェアが物理になることではない。**語が指す先が実在の数学的対象になる**ことである。

| 語 | 指す数学的対象 | 区分 | 注意 |
| --- | --- | --- | --- |
| 場 | AAT site 上の層データ(場の配置 Φ_t) | 安全 | 場の方程式は輸入しない |
| 力 | 台・輸送つきの場の部分変換 | 安全 | ニュートン力学の力ではない |
| 接続 | selected transport 規則の族(commute / rebase) | 安全 | 正準接続は存在しない(選択データ) |
| 力の曲率 | commute 二辺形の比較残差 witness / 類 | 安全 | AAT 第VIII部 定義8.9 Curvature Transfer Spectrum(スペクトル曲率 reading)とは**別対象**。本文では常に「力の曲率」と修飾する |
| ホロノミー | ダイヤモンドの平行輸送比較残差(逆射不要) | 安全 | lattice gauge 的読み。physical gauge 場は輸入しない |
| ゲージ変換 | semantic 射影が零の力(refactor) | 条件付き | 一般に可逆でない(群でなく groupoid が上限)。gauge 性は selected semantic profile の関数(profile が変われば breaking change になり得る) |
| 目標場 | lawful locus を動かす目標(要求) | 条件付き | 「ポテンシャル」を名乗るのは gen の応答公理(ギャップ単調性)を置いた模型のみ。物理の potential(力の勾配源)と向きが逆になり得る |
| 散逸 / Lyapunov | 評価汎函数と方針の適合(AAT IX §5–6) | 条件付き | 有限系では停止性は自明。内容は汎函数と力の類型の適合(質量収支則)に置く |
| エントロピー | measurement packet 繊維計数の対数(粗視化は模型データ) | 条件付き | 有限決定系では減少し得る。第二法則は計数補題 + 混合仮定の Model theorem |
| regime 境界 | 誘導連鎖の再帰 / 推移境界 | 条件付き | 「相転移」は n → ∞ の族上の sharp threshold の場合のみ。有限系に非解析性はない |
| 輸入禁止 | — | — | Bianchi 恒等式、Jacobi 場・測地線偏差、gradient flow(離散貪欲降下に存在・一意性理論はない)、臨界指数・普遍性、エネルギー保存則。「測地線」も metric enrichment から length minimizer を実構成するまでは保留語 |

規律: 物理の定理をアナロジーで輸入しない。輸入するのは**構造**(層・降下・変分・アンサンブル)
だけであり、各語の定義は本文内で自足する。この辞書は付録に置き、本文は辞書に依存しない。

---

## 8. 旧概念の処遇表

| 旧 SFT 概念 | 処遇 | 行き先 |
| --- | --- | --- |
| SoftwareField | 転生 | 場の配置 Φ_t(実在の層データ)— 第I部 |
| DevelopmentField | 転生 | 開発系 𝔇 — §3 |
| CodebaseAsFieldMemory | 吸収 | 𝒯 上の配置の堆積 — 第I部 |
| ArtifactMediatedChange / Force | 転生 | 力(台・輸送つき部分変換)— 第II部 |
| OperationSupport | 転生 | 源の生成系 + Π の許容構造 — 第IV, VI部 |
| OperationPolicy | 転生 | 方針 Π(方針階層・CLF)— 第VI部 |
| **ForecastCone** | **廃棄(legacy 墓標化)** | 後継 = 挙動空間上の到達集合 + 計器 pairing による観測可能射影 + 方針 Π による governed reachable class(第VI・IX部)。可能性の理論としては変形空間(第VII部)。専用ブランドは持たない。Lean・台帳側は SFT v1 legacy theorem surface として status を明記する(§9) |
| **ConsequenceEnvelope** | **廃棄** | 理論からは消える。FieldSig 側の report 書式として将来再利用可 |
| GovernanceIntervention | 転生 | controller(監督制御)— 第IX部 |
| InstrumentingIntervention | 転生 | 計器族の拡大 = controller の作用の一型 — 第IX部 |
| FieldUpdate / closed loop | 転生 | 生成子 T_Π(§3.6)+ 観測とフィードバック — 第IX部 |
| ProposalAccounting / Dissipation | 分割 | 散逸は第VI部(質量収支則)、集計は第VIII部(アンサンブル)。「提案された力と適用された力の区別」は第II・IV部に保存 |
| ReviewMediation | 転生 | 計器評価 + 降下データの選択 — 第IV部 |
| IncidentFeedback | 転生 | 非計画の計器読み値 + 計器族拡大 + repair — 第IX部 |
| runtime guard | 転生 | runtime 側計器と controller — 第IX部 |
| StableRegion / ReachablePreimage | 転生 | 吸収類・吸引域(挙動空間上; may / must 分離)— 第VI部 |
| Attractor Engineering | 転生 | 場の設計(コスト幾何の設計)— 第VI部 |
| MigrationEnvelope | 転生 | migration = base change / 場の輸送 — 第X部 |
| Claim Level L0–L5 | 置換 | claim ladder(D5)+ 台帳(D7) |
| AI Proposal Governance | 分割 | agent = delegator 相関つき源(第IV部)+ 監督制御(第IX部) |
| LifecycleTrajectory / EndOfLife | 転生 | 軌道 regime と終焉(有効変形の枯渇)— 第X部 |
| SFT Workbench / benchmark 節 | 撤去 | 理論本文から FieldSig docs 側へ(D4) |

---

## 9. 旧資産の処遇

| 資産 | 現状 | 提案 |
| --- | --- | --- |
| `docs/sft/software_field_theory.md` | 旧本文 1551 行。**保護ファイル**(CLAUDE.md・sft guideline) | P1 で同 path を一括置換(第I–III部完全 + T0 最小版 + 残部は薄い予告)。旧本文は docs/archive へ退避。授権 = 2026-07-04 のユーザー指示と §12 決定 |
| `docs/sft/aat_interface.md` | 古典語彙の対応表。**保護ファイル** | 全面書き換え(授権同上)。新しい借用表(第IV/V/VI/VII/VIII/IX/X部 anchor + 証明状態列)へ。現行の「非混同」「ArchSig bridge」「ArchSig/FieldSig claim 分離」の三節は新語彙で存置する |
| `docs/sft/sft_theorem_roadmap_and_research_vision.md` | ForecastCone Descent を主定理とする定理ロードマップ | `docs/archive` へ退避(新旗艦 T0–T8 が後継)。`docs/aat/lean_theorem_index_classical_aat.md` からの参照を P5 で更新し dangling を防ぐ。あわせて P5 で lean_theorem_index / proof_obligations の SFT 関連行に legacy(SFT v1 theorem surface)status を明記し、v2 ladder へ移行する obligation と legacy として閉じる obligation を分別する |
| `docs/sft/README.md`, `guideline.md` | 旧概念一覧 | 本文確定後に書き換え。P1 の時点で guideline に「SFT v2 改訂進行中(本ノート参照)」の暫定注記を入れ、旧語彙規律との規範的矛盾を防ぐ |
| `Formal/Arch/Evolution/` 配下 39 ファイル | 旧 SFT の Lean 塔(`SFT*.lean` 27 本 + AttractorEngineering・SignatureDynamics・Chapter7–11 等 12 本)。Formal.lean が import 済みで root build に組み込まれている | **凍結**。operational 定義: (a) 凍結対象 = `Formal/Arch/Evolution/` 配下の全 39 ファイル(旧 SFT 理論 surface として)、(b) Formal.lean の import は維持(`lake build` の対象のまま)、(c) 変更は build 修復のみ許可、(d) 新規 import・新規定理参照を禁止、(e) 新塔が対応部を覆った時点で個別に削除判断(削除時に Formal.lean から import 行を落とす) |
| `tools/fieldsig` | 旧 artifact(forecast-cone-skeleton 等)前提 | **凍結**。第I–III部確定後に再設計。v2 の一次 workflow 候補を先に命名しておく: **merge-residue probe**(H2 の曲率計器; merge queue の投機ビルドを利用)と**並列度アドバイザ**(T2 の台過大近似 + 衝突確率)。買い手は agent オーケストレーションのスケジューラ |
| `website/sft/` 約 20 ページ | 旧構成(field-and-force / forecast-cone / workbench) | 現状維持 → 本文確定後に追随 |
| `docs/outreach/`・website の過去 outreach 記事 | 旧語彙(ForecastCone 等)を含む公開文書 | **残す**(歴史的文書としてそのまま保存。新本文からは参照しない) |
| `docs/note/Grothendieck_Derived_AAT-SFT.md` | ポジションペーパー | 参照維持。AAT 半分は実現済み、SFT 半分(§9)は本骨格が後継であることを本文冒頭の系譜に記す |

ArchSig は影響を受けない(AAT 静的計測のまま。軌道に沿った時系列供給源として第IX部の計器の実例になる)。

---

## 10. 新規数学の台帳(research loop の的)

SFT v2 が AAT の外側で新たに要る数学。リスク順。「AAT にアンカーがあるように見えて実は新規」
の項目を正直に申告する。

| 項目 | 部 | リスク | 進め方 |
| --- | --- | --- | --- |
| 生成子 T_Π と挙動空間、TraceRealization 定理(witness 化) | I | 低〜中 | 本文内で構成(有限 coalgebra)+ Lean L1 |
| トレース site(生成位相・selected base・履歴書き換え商と witness 生存) | I | 中 | 本文内で構成。criss-cross 実例必置 |
| 辺生成子上の輸送データ(u_e、cover 適合、マージ点二重輸送) | I–II | 中 | 本文内で構成(quiver connection 方式)。「有限なら素直」とは申告しない |
| commute primitive・力の曲率の受け皿(two-complex 2-cell / incidence total complex) | II | 中 | 本文 + Lean L2–L3。受け皿未固定の式は reading schema に留める |
| t-依存 selected incidence site(可積分性 ob(f) の受け皿) | II | 中〜高 | research loop 候補。AAT IX 7.2 との比較命題まで |
| **law universe 輸送**(辺ごとの law 対応、Flat_{U_t} の輸送、transferred obstruction の時間版) | I, VI | 中〜高 | research loop GOAL 化。U_t 定数 regime を第一段に |
| **communication cover / ownership 被覆の二位相と Conway 障害** | V | **高** | research loop GOAL 化(採否条件 = 適合例と障害例の両構成) |
| **アーキテクチャ配置・law 構造の変形理論**(AAT VI §3/§6 は固定幾何内の変形であり流用不可) | VII | **高** | research loop GOAL 化 |
| 変形空間上のコスト構造(operation cost からの誘導) | VII, X | 中 | 本文で候補構成 → research loop |
| エントロピー計数補題(低質量配置の指数的希少性) | VIII | 中〜高 | research loop で模型探索 → Model theorem 化 |
| 内生 cost + 需要過程の吸収類解析(Foster–Lyapunov、ρ_c) | VI, VIII | 中 | Model theorem 規律(D6)で本文候補 → 検証 |
| 有限監督制御の安定化(仮定 5 点版 T8) | IX | 中 | AAT IX 散逸機械 + Ramadge–Wonham 型の有限構成 |

Lean 最初の的(いずれも新塔。旧 `Formal/Arch/Evolution/` は触らない。
配置は `Formal/AG/Research` sandbox → 本体化の既存運用に従う):

```text
L1: 有限トレース site + 進化族 + 場の配置 + 生成子・挙動空間の record 群(第I部)
L2: commute 部分演算と遠隔可換定理(selected dependency closure の過大近似に関して
    台が素 ⇒ commute 定義済み・transport 自明)(第II部)
L3: ダイヤモンド上の平行輸送比較残差(abelian 係数の有限模型での merge residue)(第III部)
```

- **L1–L3 は P1 の本文執筆と並行に進める**(証明資産の後退(§1)を早期に埋める)。
- 各部の受け入れ条件: 最小定理一本の Lean 化、または正準有限実例の手計算のいずれかを必置とする。

---

## 11. 執筆・検証計画

SAGA 改訂(設計 → 本文 → 台帳同期)と同じ流れを部単位で回す。
本文は PRD を挟まず **Claude が直接執筆**し、部単位で敵対レビューを回してからユーザー受け入れへ渡す
(2026-07-04 ユーザー決定。骨格と本文の齟齬を避けるため)。

| フェーズ | 内容 | 形 |
| --- | --- | --- |
| P0 | 本骨格の合意と敵対レビューによる磨き上げ | このノート(第2版; §13) |
| P1 | 序(v2 contract)+ 第I・II・III部(完全)+ 第VI部 T0 追跡模型の最小版(Model A/B)+ 付録核(解釈境界・旧概念処遇・正準有限実例)+ 残部(IV/V/VII/VIII/IX/X)は「この理論が向かう先」として薄い予告 + H1–H4 の台帳先置き。旧本文は docs/archive へ退避 | Claude 直接執筆 + 敵対レビュー。**Lean L1–L3 を並行着手** |
| P2 | 第IV部(組織)完全化 + 第VI部完全化(質量収支則・吸収域・ゲージ合同) | Claude 直接執筆 + 敵対レビュー |
| P3 | 第IX部(観測と制御)+ 第X部(寿命)完全化 | Claude 直接執筆 + 敵対レビュー |
| P4 | 第V部 Conway・第VII部 変形・第VIII部 統計力学の完全化(research loop の成果を取り込み次第) | Claude 直接執筆 + 敵対レビュー |
| P5 | `aat_interface.md`・README・guideline 書き換え、roadmap archive + `lean_theorem_index_classical_aat.md` 参照更新、台帳整備 | Claude 直接執筆 |
| 並行 | Conway 二位相・law 輸送・配置変形理論・確率模型の候補探索 | research loop GOAL(G-sft-*) |
| 後続 | FieldSig 再設計(merge-residue probe / 並列度アドバイザ)、website 追随 | 別途(PRD 化して Codex も可) |

**P1 受け入れ契約**(この 4 点を満たすまで P2 に進まない):

```text
1. 開発系の有限 record が書ける。
2. trace site + selected merge cover + selected base の有限例がある。
3. force schema / applied force / commute / merge residue の有限例がある。
4. 三段 filtration のうち、少なくとも Čech H¹ と Tor の違いが
   同じ running example 上で見える。
```

P1 では **U_t 定数 regime を第一対象**とする。law universe が動く regime は
law-universe transport が定義されるまで reading schema として扱う。

- 各部の冒頭では本ノートの問いを部ごとに特殊化して掲げ、採否の判定規律として機能させる。
- 検証: docs-only でも hidden Unicode scan と `git diff --check` に加え、
  **Lean status・tool schema・website copy への影響確認**(CLAUDE.md 準拠)。
  Lean 着手後は `lake build`。
- PRD-10(SAGA 蒸留)の進行と独立(AAT 本文は無変更のため衝突しない)。

---

## 12. 決定記録(2026-07-04 ユーザー決定)

1. **部構成**: §5 の 10 部 + 付録構成で確定。
2. **参加者モデルの深さ**: A+B で確定 — trace に現れる生成 + 可視性(バス係数・サイロを語る)。
   意図・心理・信念・学習(epistemic agent)は射程外として本文に明記する。
3. **第VIII部(統計力学)**: 本文に含める。Model theorem / Empirical hypothesis 規律で書く。
4. **旧 Lean 塔**: 凍結・legacy 宣言(operational 定義は §9)。新塔が対応部を覆った時点で個別に削除判断。
5. **英語サブタイトル**: "The Dynamics of Software Evolution on Architecture Geometry" で確定。
6. **ForecastCone 語彙**: 完全廃棄で確定(後継は変形空間 + 到達集合。旧名は理論に残さない)。
   ただし**過去の outreach 記事は歴史的文書としてそのまま残す**(§9 の処遇表に反映済み)。

執筆体制: PRD を挟まず Claude が本文を直接執筆する(§11 に反映済み)。

---

## 13. 敵対レビュー記録(2026-07-04)

本骨格第1版に対し、独立した 5 方向の敵対レビューを実施し、MAJOR 29 件・MINOR 11 件を
第2版に反映した。

| レビュー | 主要な指摘(反映先) |
| --- | --- |
| 数学的実在性(代数幾何・圏論) | トレース site の cover 公理は生成位相 + selected base でのみ成立(§3.1)。fibered 輸送は quiver connection 方式で辺上にのみ(§3.2)。力の型は complement 同一視つきに再定式化(第II部)。commute を primitive に(第II部)。マージ押し出しの圏未指定 → 三段 filtration へ(第III部)。cotangent complex は第VI部 §3・障害は Ext¹(第VII部)。law 輸送の台帳欠落(§10)。終焉判定の恒偽修正(第X部) |
| AAT 整合・境界規律 | C_t を本文から排除し A_t index へ(§3.2)。「昇格・後継・本体化」語法の禁止(D3)。アンカー誤引用の修正(第VII部ほか)。Lean 凍結の operational 定義(§9)。Empirical hypothesis は既存階級の継承(D5)。保護ファイル授権の記録(§9)。interface 書き換えでの三節存置(§9) |
| 理論的価値・先行研究 | CRDT は可換化でなく持ち上げ(第III部)。接続の必置定義(第II部)。「包摂」→「接続」と三行書式(付録)。T4 の定義循環回避(二位相の独立データ化; 第V部)。D6 模型非自明性・D7 反証規律の新設。目標場への改名と potential 条件(§3.3・§7)。anchor 状態列(§6) |
| 力学系の実質 | 生成子と挙動空間の新設(§3.6)。停止定理の自明性 → 質量収支則へ(第VI部)。追跡可能性・不可能性(T0; §4)。mud 模型の三要件(第VI部)。エントロピー主候補と計数補題・regime 境界(第VIII部)。T8 の仮定 5 点と究極有界性(第IX部)。方針階層と CLF(§3.4)。辞書の 3 列化(§7) |
| 実務・10 年課題 | 履歴書き換え商とイベントログ契約(§3.1・付録)。delegator 相関と diversity premium(§3.3・第VIII部)。runtime / incident の再建(§3.5・第IX部)。台の過大近似健全性と積方向ダイヤモンド(第III部)。レビューの二重の型とラバースタンプ(第IV部)。規制・サプライチェーン行(§6)。役割 = 力の型分布(§3.3)。H1–H4 の反証仮説(付録)。診断ツール先行の導入経路(§9) |

レビューが一致して認めた強み: 衝突の三層分離(法則 H¹ / 導来 Tor)と SAGA 接続、
law 構造の変形理論(骨化)、二位相の不整合としての Conway 障害、
「力学 + 降下」という本理論固有の軸。新規性の主張はこの三点 + 一軸に集中させる。

**第3版(同日)**: 有識者レビュー(外部)を受領し、15 項目を全採用した。主な反映:
ObservedDevelopmentSystem / GenerativeDevelopmentModel の分離と TraceRealization 定理の
witness 化・reconstruction lemma 命名規律(§3.6)、AAT 記法注記 `X_C^{V,U,J,k}` との
関係明示(§3.2)、力の二層化 ForceSchema / AppliedForce と schema level の commute(第II部)、
T0 の Tracking Model A / Impossibility Model B 分離(§4・第VI部)、負債の利子項
(carrying cost; §4)、T5 改名「内生コスト吸収域定理」と「測地線」の保留語化(§6・§7)、
ゲージ合同定理(congruence / bisimulation quotient)への書き直し(第VI部)、
エントロピー比較可能性条件(第VIII部)、T1「診断 filtration 定理」名と段階0 conditional
(第III部)、Conway の refinement / nerve map 起点(第V部)、ForecastCone の legacy 墓標化と
台帳分別(§8–9)、P1 受け入れ契約 4 点と U_t 定数宣言・実行順序の再編(§11)、
v2 contract 前文(§5 序)、生成位相の閉包明示(第I部)、L2 仮定への過大近似条件(§10)。
外部レビューの総括「勝負所は T1/T2/T3 と T0 に絞る。三層衝突 filtration・力の曲率 /
merge residue・追跡可能性限界の三つが最初に成立すれば、SFT v2 は語彙刷新ではなく
独立した理論的前進として立つ」を P1 の焦点として採用する。
