# Atlas 定理の補強計画 — 観測解像度の理論として CS へ開く

本ノートは考察ノートである。新しい公理・定義・定理は導入せず、証明済み定理の
statement(G-104 / G-107 の fixed statement)を変更しない。目的は、Atlas 定理
(G-104 の Diagnostic Resolution Invariance Theorem と、その位置を定める G-107 の
Uniform Invariance Defect Semantics and Nonfactorization Theorem。以下まとめて
**Atlas**)の現在価値を **AAT 内部**と **CS 一般**に分けて測り、CS に届く補強の
項目・優先順位・判定規準を固定することである。

補強は既存 statement の改訂ではなく後継 GOAL として起票する。本ノートに書く
数学的主張のうち G-104 / G-107 の report に無いものは、すべて**未証明の
candidate**(手証明・有限例の機械検算のみ、Lean 未検証)であり、採否は
ユーザー裁定に従う。lifecycle の経緯(PR・Issue・裁定日)は各 report と
tracking Issue を正本とし、本ノートには持ち込まない。

## 要旨

1. Atlas の対象は一つしかない。比較写像 `f_A : H¹(粗い観測) → H¹(細かい観測)`
   と、その欠損 `J_A = (dim ker, dim coker) = (phantom, hidden)` である。隠蔽・
   偽の類・観測すべき解像度・観測の分割で落ちる診断・構造条件(設計規約)・局所
   観測の限界は、すべてこの一つの写像についての定理として統一される(§1.1)。
   `J_A` は数であり、その背後には次元を取る前の**欠損対象**(比較写像錐 `D_A`、
   台署名半束 `Σ_M^op` 上の欠損加群)がある(§1.2)。AAT 内部では測定器の解像度
   理論として必須である。
2. CS 一般への貢献は、単独ではまだ薄い。大域不変量が局所観測で決まらないのは
   理論 CS には予想どおりであり、十分条件は設計規約の精密化に見え、還元は関手性の
   帰結に見える。弱さの正体は定理の弱さではなく**位置の未確定**である: 枠が
   工程語(レビュー)で語られ観測の理論として置かれていない、最近接先行との差分が
   未記述、実システムでの欠損プロファイルが未測定、計算量・合成・半径一般化が
   frontier のまま、係数体(ℚ と F₂)が測定器と揃っていない(§1.4)。
3. 枠は「コード観測の解像度理論」へ置き直す(§2)。観測は変わり、診断が不変か
   を問う。解像度はスカラーでなく poset であり、観測者には半径と幅の二軸がある。
   比喩の出所は計測器の解像度と標本化であり、レビューの経験則ではない。
4. 補強の中心は「数から対象へ」。`J_A` を次元化する前の欠損対象に戻し、表現・
   局所分解・合成・局所大域・限界・安全な解像度の幾何を、その対象の定理族として
   束ねる(§1.2、§4)。中心命題は「**意味側には全 law 診断を完全に表現する正準で
   有限な最小座標系(意味閉包 `cl_M`、`Σ_M`)が存在し、安全な観測解像度側には
   一般に正準な最粗点も有限局所的な完全判定も存在しない。その間で失われる診断は
   欠損対象として完全に表現・分解・輸送・計算できる**」。定理水準の candidate:
   観測クラスの退化定理と完全局所分解の系(R8)、解像度合成の六項完全列と相殺
   写像 `χ_A`(R14)、No Complete-Shell / No Natural Selector / 指数 frontier
   (R10)、概念方向の Mayer–Vietoris(R15)、`(r, k)` 二変数の有限観測不可能性
   (R3)、正の側の support-width 算法と Excision(R17 / R18)。一様判定の coNP
   完全性(R4a)と欠損 locus の実現(R19)、Interchange(R16)は後続。失敗しうる
   主張と、失敗しえない構成は §6 で分ける。
5. 必須は R2(差分表の充填)と R1(実システムの多解像度観測。P1–P10 を事前登録
   し、完全列のどの項が支配的かを測る)。前提確認 R0(今回の論文の係数は ℚ、
   decider の一回実行、観測クラスの確認)を最初に置く。優先順位は
   R0 > R2 > R1a > R14 > R8 > R10 > R3-w > R15 > R18 > R11 > R3-r > R9 > R1c > R17 >
   R4a > R19 > R16 > R4b > R5 ≫ R7(§5)。論文は大定理版の最小構成で一本(§5)、
   着手は Gr4 完了後(Gr4 は G-110 一枚では閉じず、G-110 と後続 n 枚のカードで成る)、期間の目安は 1 か月。本ノートの補強項目はこの版で
   凍結する。R12(エージェント読解)と R13(方法論論文)は別
   トラック。係数 base change(整数係数の錐・Fitting・jump locus)は次カードへ送る。
6. 判定は二段(§6)。「CS に届いた」の最低条件は三つ(差分表が肯定形で埋まる、
   実測で欠損プロファイルが領域ごと・源ごとに異なる値を取る、R8 / R10 / R15 /
   R3 のいずれかが定理として立つ)。「ジャーナルの大定理」の完成条件は二階建て
   (Foundation = 構成の完備、Main = 鋭い構造定理・正準 / 非正準・無限族・正の
   算法の四本、そのうえで Lean と実測)。最低条件が揃わなければ Atlas は「AAT の
   測定器の校正理論」として正確に主張し、それ以上を名乗らない。

## 参照

**正本**(事実関係の判定基準):

- [G-104 カード](../../research/goals/G-104-aat-resolution-invariance.md) /
  [G-104 report](../../research/reports/G-104-aat-resolution-invariance.md)
  (claim (i)–(v)、条件 C0–C6、K0 / K1)
- [G-107 カード](../../research/goals/G-107-aat-uniform-invariance-characterization.md) /
  [G-107 report](../../research/reports/G-107-aat-uniform-invariance-characterization.md)
  (還元・decider・位置・非必要性・非分解性、frontier)
- Lean: `research/lean/ResearchLean/AG/UniformInvariance/UniformPresentationDecider.lean`
  (decider は `List.sublists` で全部分集合を列挙)、同 `ExecutableRationalRank.lean`
  (rank は列選択の全探索)、`Formal/Util/AssertStandardAxioms.lean`
  (`Lean.ofReduceBool` = `native_decide` を拒否)
- ArchSig: `tools/archsig/src/saga.rs`(SAGA の係数は `F2` 固定)
- [研究の全体目標](../research_goal.md)(禁忌 4・5・6・7 が本計画の停止規則)

**上流考察ノート**(正本ではない):

- [解像度診断の設計ノート](n1003_aat_resolution_diagnostic_design.md)
  (observation factorization、成果物の四分法、`J_L` と `J_A`)
- [Semantic Geometry of Architecture 測量台帳](n1005_aat_semantic_geometry_route_after_g107.md)
  (§4 登路、§7 論文への含意)
- [Atom Is All You Need 考察ノート](n1001_atom_is_all_you_need_discussion.md)
  (§7.7 差分と評価規準、§12 論文ロードマップと実証節計画)

---

## 1. 現在地 — Atlas は何か

### 1.1 一つの対象と統一表

Atlas の証明済み内容は、すべて比較写像 `f : H¹(粗) → H¹(細)` と欠損
`J_A(f) = (dim ker, dim coker)`(領域 `A` ごと)についての主張である。現場で
別々に語られてきた現象は、この一つの写像の核と余核に畳まれる。

| 観測の現象 | Atlas での正体 | 宣言(正本は各 report) |
| --- | --- | --- |
| 粗い観測で真の類が隠れる(隠蔽) | `coker`(hidden) | G-104 (iv)(b) `fixed_claim_iv_b` |
| 粗い観測で偽の類が生じる(エイリアシング) | `ker`(phantom) | G-104 (iv)(a) `fixed_claim_iv_a` |
| この解像度で観測してよいか | `J_A = (0, 0)` の領域 | G-107 (i) `uniformInvariance_iff_allNonemptyASubnerveDefect_eq_zero` |
| 判定は計算で決まる | sound / complete decider | G-107 (ii) `uniformPresentationCheck_eq_true_iff` |
| 観測すべき解像度は規約の中身でなく台で決まる | law 全量化 → 領域 `A` への還元 | G-107 (i) `uniformInvariance_iff_allNonemptyASubnerveH1Bijective` |
| 関心事ごとに分けて観測すると落ちる診断 | `A` は概念の集合で効く(単独概念に還元しない) | 還元の量化域そのもの(§7 の最小例 変種 B が例示) |
| 解像度を保証する構造条件 | 条件 C は十分、各条項は非必要 | G-104 (ii) `generatedComparisonH1Map_bijective`、G-107 (iii)(iv) `conditionC_of_conditionCAllA`、`ConditionC0NonnecessityWitness`〜`C6` |
| 過剰な精細化は診断を増やさない | No-New-Diagnostics Corollary | G-104 (iii) `overresolution_no_new_diagnostic_classes` |
| 局所観測だけでは解像度の妥当性を決定できない | 零 locus が半径1観測を通して分解しない | G-107 (v) `uniformPresentation_not_factors_through_obsG` |

統一されているのは表の右列が一本であることであり、左列のどれか一つを取り出すと
「普段やっていること」に見えるのは当然である。新しいのは一つの機構から全部が
出ることである。

係数について一点。Atlas は ℚ 係数で固定されている(G-104 claim boundary)。
ArchSig の SAGA 実装は F₂ 係数である(`saga.rs`)。両端の `H¹` を「SAGA と同じ
対象」と言えるのは係数を揃えたときであり、F₂ は ℚ より多くの類を見うる(有限
nerve に ℤ/2 torsion が実在しうる)。どちらで測定の鎖を回すかは理論側の裁定
事項である(R0)。

### 1.2 構造像(candidate): 欠損対象と Leray 分解

`J_A` は数である。補強の中心は、次元を取る前の対象に戻し、その対象について定理を
述べることにある。以下はすべて candidate。

**(a) 欠損対象。** 各領域 `A` で、cochain 水準の比較写像
`u_A : C•(N_A) → C•(N'_{π⁻¹A})` の写像錐 `D_A := Cone(u_A)` を欠損対象と呼ぶ。
錐の長完全列 `… → H¹(N_A) → H¹(N'_A) → H¹(D_A) → H²(N_A) → H²(N'_A) → …` により、
`H⁰(D_A)` は `ker H¹(f_A)` と `coker H⁰(f_A)` の拡大、`H¹(D_A)` は `coker H¹(f_A)`
と `ker H²(f_A)` の拡大である。`J_A` は `H¹` 水準の切片
`(dim ker H¹(f_A), dim coker H¹(f_A))` であり、錐コホモロジーの次元そのものでは
ない。錐を本体に置く理由は、Leray 分解 (e)、合成 (f)、概念方向の Mayer–Vietoris
(g)、将来の係数 base change をこの一つの対象が保持するからである。

**(b) 表現。** law family `L` の K0 係数複体は値クラス `A_λ` ごとの定数係数複体の
直和であり(G-104 の block 直和分解を cochain 水準で読む)、`D_L ≅ ⊕_λ D_{A_λ}`、
`J_L = Σ_λ J_{A_λ}`。指示 law により各 `A` は law 側から実現できる(G-107 (i) の
資産)。従って**全ての law 由来診断は有限個の `A`-欠損対象から完全に再構成される**。
内容の大半は G-104 / G-107 の既証明の再配置であり、新規の証明義務は錐水準の直和
だけである。主定理として売らず、枠の命題として置く(禁忌 5)。§7 の最小例が確認
する「law の直接計算 = 値クラスの和」はこの命題の最小発火例である。

**(c) 意味閉包と台署名半束 `Σ_M`。** 比較データの全 cell `Ω_M` と、各 target `t`
が選ぶ cell 集合 `S_t ⊆ Ω_M`(台に `t` を含む cell)から `α_M(A) := ⋃_{t∈A} S_t`、
`γ_M(X) := {t | S_t ⊆ X}` と置くと `α_M(A) ⊆ X ⟺ A ⊆ γ_M(X)`、すなわち Galois
接続 `α_M ⊣ γ_M` が立ち、`cl_M := γ_M ∘ α_M` は正準な有限閉包作用素になる。
A-subnerve は `α_M(A)` そのものなので、台署名半束 `Σ_M ≅ Fix(cl_M) ≅ im α_M`、
`D_A ≃ D_{cl_M(A)}`(定義的)、`σ_M(A ∪ B) = σ_M(A) ∨ σ_M(B)`。全 law 診断は `Σ_M` を
通して factor し、一様判定は `Σ_M` の代表だけで足りる。`Σ_M` は comparison geometry
を保存する意味商の中で最粗、すなわち診断に必要な意味の区別だけを残した正準な
最小座標系である。最悪の場合 `|Σ_M| = 2^|Target| − 1`(任意の部分集合族が欠損集合
として実現される。R4a / R19)。R10 と合わせると「**診断の座標化は正準だが、安全な
解像度の選択は正準でない**」という対照になり、これが Atlas の中心命題の骨である。

**(d) 欠損加群。** `A ⊆ B` なら `N_A ⊆ N_B` なので cochain の制限が
`H¹(N_B) → H¹(N_A)` を与え、`A ↦ H¹(N_A)` は `Σ_M^op` 上の関手、粗側・細側の二つの
関手の間で比較写像は自然変換になる。点ごとの核・余核で
`Phantom_u, Hidden_u : Σ_M^op → Vect_ℚ` を得る。`J_A` はその次元表、幅
`min{|A| : Hidden_u(A) ≠ 0}` は加群が最初に非零になる rank である。persistence の
語彙(generalized rank invariant、Möbius 反転)はこの構成の後で問い、barcode は
要求しない(一般の poset では区間分解が無い)。添字 poset が時間やスケールでなく
台署名から内生的に作られる点が Atlas の特徴である。

**(e) Leray 分解。** 比較写像は「粗側の係数から順像係数への unit 射」と「Leray の
edge map」の合成に分かれる:

```text
f_A = (edge map) ∘ H¹(unit),   unit : ℚ_{N_A} → φ_* ℚ_{N'_A}
0 → H¹(N_A; φ_*ℚ) → H¹(N'_A; ℚ) → ⊕_c H¹(Φ_c^A) → H²(N_A; φ_*ℚ) → …
```

ここで `Φ_c` は粗 chart `c` の**位相的 fiber**(`c` 上の細 chart と、退化宣言
された辺・面だけから成る部分複体)である。edge map は単射(5 項完全列)なので
`phantom_A = dim ker H¹(unit)`、余核側には短完全列

```text
0 → coker H¹(unit) → hidden_A → ker d₂ → 0
```

が立つ。現行の観測クラス(面は全辺 mapped か全辺退化のどちらか)では `d₂ = 0` が
見込まれ、そのとき `hidden_A = dim coker H¹(unit) + Σ_c dim H¹(Φ_c^A)` は**等式**に
なる。欠損の源は四枚の層(unit の核 `K`、余核 `Q`、`R¹φ_*`、`d₂`)で尽き、条件 C
の各条項はその茎の消滅に対応する(`K`: C0 / C2 / C4、`Q` at chart: C1 ∧ C6、
`Q` at edge: C5、`R¹`: C3 の位相的部分)。n1003 §4 の「機構カタログ」はこの四枚で
構造化でき、G-104 / G-107 の反例史は「各条項は必要でなかった」という負の目録から
「分解のどの項を過剰に殺していたか」という正の構造理解に変わる。

この分解から系として次が出る。

- **必要条件 C3′**: 一様不変 ⟹ 全非空 `A`・全粗 chart `c` で `H¹(Φ_c^A; ℚ) = 0`。
  `R¹` は chart に集中し、`d₂ = 0` の下では大域コホモロジーで相殺されない唯一の
  源だからである(零拡張の cochain 論法)。G-107 の C3 非必要性 witness は、G-104
  の C3 が self-loop の lift を fiber 辺に数える定義上の過剰部分を突いており、
  位相的 fiber の非輪状性は破っていない。これは G-107 の地図(C0–C6 はどれも
  必要でない)と矛盾せず、**必要条件側の一枚を初めて足す**。
- **順像の系**: 粗い観測者が自前の係数を作らず細かい観測の順像 `φ_*F` を係数に
  採れば unit は恒等で phantom は恒等的に零、hidden は fiber 内部の閉路だけに
  なる。偽の類は「粗い観測者が集計でなく再観測をする」ことの代償である。
- **誤差予算不等式**: 等式から導く数値的な系(項の正確な形は要固定)。
- **transgression 定理**: 混在 face(2 者が同一 chart、1 者が外の三者合意)を許す
  観測クラスでは `d₂ ≠ 0` がありえて、fiber 内の局所欠損が大域 `H²` へ transgress
  し hidden から消える。**観測モデルが、局所 fiber 欠損を診断欠損として残すか
  二次整合性へ吸収するかを決める**。C3′ はこの定理の pure class での特殊化で
  あり、観測モデルの選び方で必要条件が生まれたり消えたりすること自体が定理
  水準の観測である(R8 の後半、R9 が実現。SAGA / G-106 側の `H²` 整合性と将来
  接続する)。

**(f) 合成。** 三段の読み `q₀ ≤ q₁ ≤ q₂` の A-block 比較 `U → V → W`(`f`, `g`)に
対し、線形写像の六項完全列

```text
0 → ker f → ker(gf) → ker g → coker f → coker(gf) → coker g → 0
```

の連結射を相殺写像 `δ_A : phantom_A(q₁→q₂) → hidden_A(q₀→q₁)` と読み、
`χ_A := dim im δ_A` とおけば

```text
phantom_A(gf) = phantom_A(f) + phantom_A(g) − χ_A
hidden_A(gf)  = hidden_A(f)  + hidden_A(g)  − χ_A
```

`χ_A` は完全列に最初からある部分空間の次元であり、新しい指標ではない(禁忌 6)。
意味は「途中の解像度で生じた偽の類が、前段で隠蔽された類と接続して最終比較では
相殺される」。R10 の非単調 witness `(0,0) → (1,0) → (0,0)` はこの相殺機構の
発火例である。零欠損射は恒等を含み合成で閉じ、2-out-of-3 も出る。従って
**安全性は観測変更の射としては合成可能だが、安全な観測点の選択空間は束を
なさない**(R10)。連結射の追跡は blame の正本になる(最終 hidden が前段の
`coker f` の残りか、後段で新たに生じたか、相殺されなかったか。phantom も同様)。

**(g) 概念方向の Mayer–Vietoris。** A-subnerve は「台が `A` と交わる cell」なので
`N_{A∪B} = N_A ∪ N_B` は成り立つが、`N_A ∩ N_B` は `N_{A∩B}` より一般に大きい
(台が `A` にも `B` にも触れる cell — 二概念をまたぐ共有スキーマ、両側に関与する
辺)。短完全列 `0 → C•(N_{A∪B}) → C•(N_A) ⊕ C•(N_B) → C•(N_A ∩ N_B) → 0` を
粗側・細側で作り、縦に比較写像を置いた錐の長完全列を取ると、`J_A = J_B = 0` なのに
`J_{A∪B} ≠ 0` となる源を**交差複体上の連結射**として同定できる。概念またぎ欠損は
意味領域の交差に住む貼り合わせデータから生じる — AAT の主題「局所では正しく大域で
壊れる」の概念方向版である。R3-w の交互多角形はその sharp witness で、幅 `k` の
観測者が見落とすのは cell 数や閉路長ではなく「何次の意味的重なりを同時に観測
できないか」で説明される。解像度方向 (e) と概念方向 (g) の二方向が、§2 の二軸の
数学的足場になる(多領域の MV スペクトル系列・二方向の二重複体は frontier)。

### 1.3 AAT 内部の価値

- ArchSig の抽出粒度の選択に定理の warrant を与える(第VIII部測定理論の錨)。
- reading 圏上の関手化(G-107 frontier)は program context / 意味のモジュライの
  種であり、登路(n1005 §4)の土台に接続する。
- 論文A 実証節の第三段(解像度スイープ)の theorem 側の錨である(n1001 §12)。

### 1.4 CS 一般から見た現在の弱さ

定理が常識と一致する部分は説明すれば「普段やっていること」になる。発見として
立つのは常識と食い違う部分だけである。証明済みの食い違いを強い順に並べる。

1. 局所をいくら丁寧に観測しても解像度の妥当性は決まらない(G-107 (v))。
2. 関心事で分けて観測すると、関心事をまたぐ閉路は誰にも見えない(`A` が集合)。
3. 観測すべき深さは規約の中身でなく台で決まる(還元)。
4. 粗い観測は隠すだけでなく偽の類を生じさせる(phantom)。
5. 構造条件(設計規約)をすべて破っても安全な配線がある(非必要性)。

candidate(witness の Lean 化後に昇格する):

6. 最粗の安全な読みは一意でない。安全な併合を二つ合わせると閉路が隠れる(R10)。
7. 途中まで細かくすると偽の類が生じ、降り切ると消える。欠損は精細化に沿って単調で
   ない(R10)。
8. 幅 `k` の観測(概念 `k` 個までの領域を見る)は `k+1` 概念をまたぐ閉路を
   見落とす(R3-w)。
9. 偽の類は、粗い観測者が集計でなく再観測をするところから生まれる(R8 順像の系)。
10. 観点を固定すれば判定は多項式、全観点では coNP 完全(R4a)。
11. 途中の解像度で生じた偽の類は、前段で隠蔽された類と相殺されうる(合成の
    相殺写像 `χ_A`。R14)。
12. 外部の cost / utility を足さない限り、対称な候補の中から正準な安全解像度を
    一つ選ぶことはできない(No Natural Selector。R10)。

そのうえで、CS 一般にまだ届かない理由は五つある。

- **枠**: レビューという工程語で語られ、観測の理論として置かれていない。
- **差分**: 抽象解釈の exactness / completeness、CEGAR、Leray 型写像定理、
  persistence、「局所 ⟹ 大域 iff 非輪状」族、lumpability、SE の lifting 系列、
  有限モデル理論の局所性との差分が未記述である(§3)。
- **実測**: 実システムで欠損プロファイルが領域ごとに異なる値を取ることが示されていない。
  小さな例では閉路は目で見えるため、計算で出ることに価値が立たない。
- **frontier**: 計算量・合成・半径一般化が G-107 の frontier のままである。
  decider は存在定理であり、一度も実行されていない。
- **係数体**: 測定器(F₂)と定理(ℚ)が揃っていない。

## 2. 枠の置き直し — コード観測の解像度理論

- **観測**とは、解像度を選んでコードを読み、nerve と台を得る行為である。人間の
  レビュー、エージェントのコード読み、ArchMap の抽出は同じ行為の三つの担い手で
  ある。問いは「観測の解像度を変えたとき、どの診断が安定で、欠損はいくらか」
  であり、これは計測理論の問いである。
- 形式側は既に観測の言葉で書かれている(G-103 の reading、G-107 の `Obs_G` と
  observation factorization、n1003 の題)。「レビュー」は現場向けの皮であり、
  剥がすと理論の語彙と一致する。
- **二軸**: 軸1 = 読みの解像度(reading `q`、画素サイズに相当。スカラーでなく
  **poset** であり、同じ粒度で区切りを変える zoning と、粒度を変える scale の
  両方を含む)。軸2 = 観測者の視野(certificate / grammar の半径 `r` と、同時に
  見る概念の幅 `k`)。G-107 (v) は軸2・半径1の限界、R3 は二軸の限界を描く。
- 二軸の数学的足場: 解像度方向は Leray 分解(§1.2 (e))、概念方向は Mayer–Vietoris
  (§1.2 (g))。二つの homological な方向として分かれる。
- 比喩の出所は計測器の解像度・標本化・エイリアシングである。許可する語 =
  分解能、エイリアシング(機構として)、masking、系統誤差(`J_A` は決定論的で
  不確かさではない)、誤差予算、トレーサビリティ(核まで)、校正曲線(相対)。
  定義を伴わない限り題にも節名にも使わない語 = Nyquist の閾値定理、不確かさ
  (抽出分散を測らない限り)、renormalization / universality、contextuality、
  rate–distortion、resolution limit(network science の語。別機構)。
- 命名の注意: 変わるのは観測、不変(または欠損)なのは診断である。定理の主語は
  「診断の安定性」のままとし、「観測が不変」と読める名は使わない(G-104 の
  命名記録どおり)。
- 位置づけの規律: 否定形のメタ記述(「新しい数学ではない」「AI 生成ではない」
  等)は書かない。最近接の先行を引き、足した分だけを肯定形で具体に書く
  (n1001 §7.7 の規律と同じ)。統一は宣言せず、§1.1 の表で見せる。
- 応用節は三つ: 人間のレビュー(どこまで降りるか)、エージェントのコード読み
  (どの粒度で読めば診断を誤らないか)、ArchSig の抽出粒度選択(正当化)。

## 3. 最近接先行との差分(肯定形で埋めるべき表)

各行の書誌は執筆時に外部 API で突合する(本ノートは著者・年の水準に留め、確信
の無いものには「要確認」を付す)。

### 3.1 抽象化の精度理論

| 先行 | 彼らの問い・結果 | Atlas が足すもの |
| --- | --- | --- |
| strong preservation / exactness(Ranzato–Tapparo 2004 / 2007)、may / must 抽象(Dams–Gerth–Grumberg 1997) | 抽象が性質を強保存する条件。spurious(may)と見落とし(must) | Atlas は completeness より **exactness の instance**。`J` は may / must の両側欠損を一つの線形写像の核・余核で数える包装 |
| completeness(Giacobazzi–Ranzato–Scozzari 2000)、complete shell / core | complete 領域の族は閉じ、最粗の完全精細化が一意に存在 | **対照**: Atlas の零 locus は共通粗化で閉じず、最粗の安全な読みは一意でない(R10、candidate)。サイクル一つで壊れる |
| local completeness(Bruni–Giacobazzi–Gori–Ranzato 2021)、partial completeness(Campion–Dalla Preda–Giacobazzi 2022) | 入力ごとの completeness、距離で測る片側の不完全さ | 一様 / pointwise = global / local。有限 Target ゆえ有限基底が存在(還元)。両側の次元 |
| CEGAR | spurious counterexample を見つけて精細化 | spurious(`ker`)と見落とし(`coker`)を精細化の前に数える decider。精細化は欠損を単調に減らさない(R10) |

### 3.2 写像定理・persistence

| 先行 | 彼らの問い・結果 | Atlas が足すもの |
| --- | --- | --- |
| Leray / Grothendieck 合成関手スペクトル系列 | 写像に沿う順像と higher direct image | G-104 (ii) はその有限・局所係数・次数1版の系。Atlas の固有分 = law 係数の block 分解で座標ごとに適用、退化宣言つき部分写像の Lean 固定、位置(非必要性7枚+非分解性)、decider、**必要条件 C3′**(R8、現行クラス限定) |
| Vietoris–Begle、Quillen Theorem A、McCord 1966、poset fiber theorems(Björner–Wachs–Welker 2005) | 局所非輪状 ⟹ 同型 | 条件 C は VB 型の incidence 十分条件であり、self-loop について真に強い(C の下では座標 subnerve 内の粗 self-loop は `H¹`-neutral にしかなれない)。弱化した局所十分条件 C^loc(R8) |
| persistence(Zomorodian–Carlsson 2005)、rank invariant、interleaving 安定性(Chazal–de Silva–Glisse–Oudot 2016、Bauer–Lesnick 2015)、zigzag(Carlsson–de Silva 2010)、Möbius 反転(Patel 2018、Kim–Mémoli 2021、要確認) | 解像度 poset 上の module と barcode | 鎖 `q_i ≤ q_j` 上で `r_ij = rank(H¹(q_i) → H¹(q_j))` とすると `phantom_ij = dim H¹(q_i) − r_ij`、`hidden_ij = dim H¹(q_j) − r_ij`。`J` は rank invariant そのものではなく、端点の次元と rank から導かれる両側欠損。barcode は要求しない(一般の poset では区間分解が無い)。概念方向は被覆 `{N_t}` の Mayer–Vietoris(関心事で分けると見えない閉路 = 連結準同型の像)。安定性は入れ子の観測者族に限る。一手の編集で `J_A` は各成分 ≤ 1 しか動かない(R7 の下界補題) |
| cellular sheaf(Curry 2014、Hansen–Ghrist 2019) | 一般の制限写像、Laplacian | 順像係数の再定式化は採用(R8)。一般の制限写像は A-還元を壊すので、「法則 = subnerve 上の定数層の直和」という特別なクラスが還元を可能にしていると明言する。Laplacian は計算・表示手段に限り、量としては presentation 依存で不採用(禁忌 6) |

### 3.3 「局所 ⟹ 大域」の定理族

| 先行 | 彼らの問い・結果 | Atlas が足すもの |
| --- | --- | --- |
| Vorob'ev 1962、Beeri–Fagin–Maier–Yannakakis 1983、Fagin 1983、Abramsky–Brandenburger 2011(Čech `H¹` 版は Abramsky–Mansfield–Barbosa 2011) | 「対ごとの整合 ⟹ 大域整合」が全インスタンスで成り立つ iff スキーマ hypergraph が非輪状。データ非依存・反復還元で決定可能 | 問いは `H⁰`(大域切断の存在)と `H¹` の解像度比較で別。定理の**型**が同じ: 大域性質 / 局所十分条件 = 非輪状 / データ非依存 / 決定可能。C3(位相的 fiber 非輪状)が非輪状性の対応物で、C は十分のみ、半径1には iff なし。positioning の主軸候補 |
| lumpability(Kemeny–Snell 1960、weak は Rubino–Sericola 要確認)、bisimulation 最粗商(Paige–Tarjan、Larsen–Skou 1991) | strong / weak lumpability。最粗の正確な商が一意に存在 | strong / weak = 一様 / pointwise。**対照**: 最粗の一様読みは一意でない(R10) |
| rough set(Pawlak 1982)、reduct(Skowron–Rauszer 1992) | 定義可能集合、下近似、reduct は多数 | 定義可能性 = adequacy(G-103 `factors_iff_kernel`)、下近似 = descend 可能部分族の診断。Atlas は定義可能な係数の上で導出不変量が不変でないことを扱う |
| Herlihy–Wing 1990 の locality、connected information(Schneidman et al. 2003)、十分統計量 / IB(Tishby et al. 1999) | 成分ごとの検査で全体が決まるか。最小十分は一意 | 一様性は概念ごとでは決まらない(幅の非分解性、R3-w)。最粗の一様読みは一意でない |

### 3.4 SE の観測と粒度

| 先行 | 彼らの問い・結果 | Atlas が足すもの |
| --- | --- | --- |
| lifting 演算子(Feijs–Krikhaar–van Ommering 1998、Relation Partition Algebra 1999、Holt 1998) | part-of 階層で uses 関係を上位へ lift する | これが粗視化 `π` の直接の先祖。彼らは lift したグラフを計算する。Atlas は lift の `H¹` への誘導写像の核・余核を領域別に出す |
| Melton–Tempero 2007、Laval et al. 2011 / 2012、Oyetoyan et al. 2015、Al-Mutawa et al. 2014 | class 水準の閉路の量、package 閉路の細粒度分析。**containment の位置は有害 / 無害の判別基準にならない** | Atlas の予言: 判別するのは containment の位置でなく概念 `A` 上の fiber 連結性(C1)。無害な package 閉路 ≈ phantom、という検証可能な仮説 |
| 階層化 reflexion model(Koschke–Simon 2003、水準間の食い違い事例は要確認)、Lutellier et al. 2015 / 2017、Pruijt et al. 2017、Arcan(要確認) | 階層 mapping。観測(辺の種類・ツール)の差で結果が変わる | 観測の差が診断に効くのは `J` を変える場所だけ。辺種類の粗視化が chart 集約の形に乗るかは別途検討 |
| 注意 | SE の閉路文献は**有向**閉路 | Atlas の `H¹` は無向の貼り合わせ閉路。R2 の表と論文に区別を明記する |

### 3.5 局所性・計算・検証

| 先行 | 彼らの問い・結果 | Atlas が足すもの |
| --- | --- | --- |
| Hanf 1965、Gaifman 1982、Fagin–Stockmeyer–Vardi 1995、Cai–Fürer–Immerman 1992、1-WL(Morris et al. 2019、Xu et al. 2019)、LOCAL(Linial 1992) | 有界半径の局所論理・局所アルゴリズムの表現力 | (v) はその instance。R3-r で任意半径の族へ上げる。**理論 CS の下界とは名乗らず**、AAT の限界定理として置き、系「一様不変性は有界次数上 FO 非定義・1-WL 非不変」とだけ書く |
| Monotone 3-SAT(Gold 1978)、ℚ-rank ∈ NC²(Mulmuley 1987) | — | 一様判定 coNP 完全 / pointwise ∈ P の candidate(R4a) |
| certifying algorithms(McConnell–Mehlhorn–Näher–Schweitzer 2011、Alkassar et al. 2014)、LRAT / GRAT(Cruz-Filipe et al. 2017、Lammich 2017、Heule et al. 2017、Tan–Heule–Myreen 2021)、CompCert、seL4 | 証書検査の検証 | 証書が証すのが rank でなく law 全量化の意味論的性質であること(還元・決定可能性定理を通して)、二段の信頼水準、観測側の非検証性の明示(R11) |
| 大規模形式化報告(Equational Theories Project、PFR、LTE。いずれも要確認) | 既知定理の形式化 | 反証ループ下の statement 発見と、核が弾けない欠陥の分類学(R13) |

### 3.6 「同じでない」と先に書く行、導入の接点

- Fortunato–Barthélemy 2007 の resolution limit(目的関数の artifact。hidden と
  語は同じで別機構)、spectral coarsening(Loukas 2019。計量が無いので近似版は
  輸入しない)、繰り込み(flow・固定点が無い)、rate–distortion(重みを発明
  しない)。
- MAUP(Openshaw 1984)・ecological fallacy・Simpson は related work でなく
  **導入の接点** に置く。Atlas は決定論的・組合せ的で標本誤差を持たないと冒頭で
  言う。「数の一致は診断の一致でない」(dim の差 = phantom − hidden の打ち消し)は
  恒等式であり、R1 の測定規律として扱う(定理の名を与えない)。

## 4. 補強項目

各項目に、内容・産物・登路上の位置(幹 / 支線 / 土台補強)・判定規準を付す。
見積もりは規模感のみ(小 / 中 / 大)。

### R0 前提確認(極小、最初に)

- (a) **係数体の裁定**: ℚ で統一して ArchSig / harness に ℚ rank を持たせるか、
  F₂ 版 Atlas を別途立てるか。「同じ `H¹`」の文言はこの裁定まで留保。
- (b) **decider の一回実行**: `#eval` で `uniformPresentationCheck` を T3 等に
  走らせ、現 decider(`2^|Target|` × rank 全探索)の実行可能性と kernel `decide`
  の挙動を実測する。`native_decide` は公理監査で禁止されている。
- (c) **観測クラスの確認**: 現行クラスは混在 face(2 者が同一 chart、1 者が外)を
  排除していること、G-104 の fiber graph(self-loop lift を含む)と位相的 fiber の
  定義差を固定する(R8 / R9 の前提)。
- (d) 最小例の pullback は辺の向きが揃う前提で符号を付けていない。一般の分割を
  扱うときは符号付き版にする(R10 の witness 計算に要る)。

### R1 実システムの多解像度観測(必須。三分割)

- **R1a 構造欠損プロファイル**: 決定論的な静的抽出器(LLM 抽出でない。欠損プロファイルは
  配線と台だけから決まり、law の値を要らないため)で service / class / method
  の三段を読み、概念語彙(10 前後を PRD で固定)の領域ごとに `J_A` を計算する。
  v1 は graph 水準(面なし。C3 / C4 は空虚と明記)。対象は train-ticket を含む
  5 系以上(できれば 2 言語)。既存の train-ticket 資産から読める事前観測:
  service ↔ class の欠損プロファイルは**ほぼ全域で零**(41 / 42 サービスでサービス内 class
  依存が木)になる公算が高く、phantom は class ↔ method に現れる見込み。これは
  LLM 抽出の下界に基づく事前登録予測であり、外れても資産。
  事前登録する問い: P1 存在(phantom > 0 と hidden > 0 の領域が各 1 以上)/
  P2 非一様(`J = 0` と `J ≠ 0` の領域の共存)/ **P3 概念またぎ**(`|A| ≥ 2` で
  `J_A ≠ 0` かつ各単独概念で `J = 0` の領域)/ P4 還元検算 / P5 機構帰属
  (`J ≠ 0` で破れる条項の分布、`J = 0` で C が破れる割合 = C の偽警報率)/
  P6 段階的精細化の安定化(どの段で `J` が止まるか)。
  さらに **P7 相殺**(三段で `χ_A > 0` の実例があるか)/ **P8 欠損源の内訳**
  (hidden のうち unit 由来・fiber 由来・transgression 由来の割合、phantom の
  うち unit 由来)/ **P9 署名圧縮**(`|Σ_M| / (2^|Target| − 1)`)/ **P10 局所
  大域の帰属**(P3 の概念またぎ欠損が MV の連結射に帰属するか)。実証の問いは
  「Atlas の完全列のどの項が、実システムのどの解像度・どの領域で支配的か」で
  あり、数を測る実証ではなく theory-guided な実証にする。
  測定規律: `(phantom, hidden)` を領域ごとに別々に報告し差を指標にしない、
  両側 dim が一致しながら `J ≠ 0` の打ち消し例の有無、欠損ごとの幅
  `min{|A| : J_A ≠ 0}`、鎖 (s,m)・(m,f)・(s,f) の三対で非単調が出るか、同じ
  粒度で区切りを変えた二つの分割(repo 単位と deploy 単位)による zoning 例、
  欠損源の内訳(`K` / `Q` / fiber 由来)。pointwise(law 固定)モードを主、
  一様モードは小部分系で。
  産物: 実証節 PRD(問い節で事前固定)、`docs/reports` の凍結規律に従う測定
  artifact、ArchSig の多解像度入力(`π` は観測なので ArchMap の context に
  `refines` を持たせ、欠損プロファイルは ArchSig の計算)。
- **R1b law 係数の還元検算**: 既存 sectionValue 証拠で直接計算が値クラス和に
  一致することを確認する(定理上必ず一致。不一致は抽出 / 実装バグの検出器)。
- **R1c 面の導入**: 「三者が同じ共有型・定数・スキーマを参照する三つ組」を面と
  する。混在 face を扱うには R9 が先。
- 位置: 土台補強。論文A 実証節計画(n1001 §12)の第三段と同一対象であり、二重に
  作らない。査読者が納得する条件: 5 系以上・決定論抽出+digest 固定・統計
  (service 水準の閉路の x % が phantom、class 水準の閉路の y % が hidden、概念またぎ
  z 件)・外部結果への接続(修正履歴、ツール間不一致が `J ≠ 0` 領域に集中するか、
  R12 の下流タスク)。
- 判定: 欠損プロファイルが**領域ごとに、かつ源ごとに**異なる値を取ること。全域 `J ≠ 0` なら
  一様モードの情報量が無いことを記録し pointwise へ重心を移す。全域 `J = 0`
  (service ↔ class でほぼ全域が零)なら失敗ではなく「この系ではその粒度の読みが安全」
  という結果として記録し、method 水準と他系へ進む。どちらも葬らない(禁忌 3)。
- 規模: R1a 中(抽出器は一度、以後は系ごとの限界費用小)、R1b 小、R1c 中。

### R2 最近接先行との差分表の充填(必須、R1 の PRD より先)

- 内容: §3 の各行を書誌突合つきで埋める。有向 / 無向の区別、辺種類の粗視化が
  定理の形に乗るかの検討を含む。加えて、似ていると説明するだけでなく、その分野の
  標準対象から Atlas へ送る **translation proposition** を短く持つ: 抽象解釈(ある
  クラスの抽象写像を Atlas の比較として埋め込み、強保存 / exactness を零欠損に
  対応させ、complete shell が存在する regime と No Complete-Shell regime を分ける)
  と DB / CSP(schema / 台 hypergraph を Atlas の意味台系へ送り、join-tree /
  非輪状の場合に R15 が局所大域の欠損計算を与える)の二本を今回の論文の目標にする。
  分散計算(`Obs_{r,k}` を LOCAL / 局所証明モデルへ)、TDA、SE、エージェントへの
  translation は後続。
- 判定: 粒度依存の直接の定量実証は無い(最近接は lifting 系列)と見られるため、
  CS への接点 の主軸は「集約アーティファクトを概念領域ごとに `(ker, coker)` で厳密に
  勘定し、機構を名指しし、判定を計算に置く」に限る。positioning の主軸候補は
  exactness(3.1)と「局所 ⟹ 大域 iff 非輪状」族(3.3)。
- 規模: 小。

### R3 観測者の視野の限界 — `(r, k)` 二変数の有限観測不可能性

- 目標 statement(candidate): 半径 `r` 以内の typed 局所構造と、同時に見る概念数
  `≤ k` だけを読む観測写像 `Obs_{r,k}` に対し、任意の有限 `(r, k)` で `Obs_{r,k}`
  が一致し一様性が異なる有限 presentation 対 `M⁺_{r,k}, M⁻_{r,k}` が存在する。
  一文なら「半径を広げても、同時に見る概念数を増やしても、観測予算を有限値に
  固定する限り一様不変性は判定できない」。R3-r と R3-w はその二軸の族であり、
  積 / 代入で二軸同時の分離族が作れるかが問い。非局所性は二種類(構造的 =
  任意有限半径で見えない、意味的 = 任意固定幅で見えない)。

- **R3-r 半径**(中): 任意の固定半径 `r` に対する有限 presentation 対の族。
  構成案: `T_n` = chart 1 つに self-loop `n` 本と面 `(i, i+1, i+2) mod n`。一様 ⟺
  `6 ∤ n`(粗側 `H¹` は循環行列 `1 − x + x²` の核で決まる)。`T_{2n}` と
  `T_n ⊔ T_n`(`n ≡ 3 mod 6`、`n > 2r + 1`)は cell 数が同じで全ての `r`-typed ball
  が一致し、前者は非一様・後者は一様(`J` の直和加法性)。grammar は半径 `r` の
  typed ball だけを読む最小のものに定義し直す(`G_local-v1` の成分を一般化しない)。
  anti-answer-encoding の規律(n1003 §8)を保つ。名乗りは「有界局所の証明書は
  存在しない」(AAT の限界定理)。
- **R3-w 幅**(小): 幅 `≤ k` の全ての `A` で `J_A = 0` が一致しながら一様性が
  異なる対。witness 候補: `k+1` 概念をまたぐ fiber 内の交互多角形(chart の台
  `{c_{i−1}, c_i}`、辺の台 `{c_i}`)。幅 `≤ k` は全零、幅 `k+1` で hidden = 1。
  `k = 1, 2, 3` は例示スクリプトと同じ線形代数で検算済み。Mayer–Vietoris で「`A ∪ B` の `J` は
  `J_A`、`J_B` と両方に触る cell 上の接続写像で決まる」を説明に使う。R4a の
  構造問題(どの `A` の族で足りるか)への否定回答(有界幅の族では足りない)。
  R15(概念方向の Mayer–Vietoris)の sharp witness として取り込む。
- 産物: 後継 GOAL(R3-w を先に)。二軸の限界 `(r, k)` と欠損の(長さ、幅)の
  図を論文の一枚にする。上界方向の鋭い閾値は主張しない(Leray 分解の「局所 +
  fiber 層のコホモロジー」が exact な上界の型。R8)。
- 位置: 支線(G-107 frontier の完了)。

### R4 一様判定の計算量(二分割)

- **R4a 与えられた対の判定**(中): candidate = **UNIFORM は coNP 完全**
  (所属: `A` を証拠に有理 rank は多項式。困難性: Monotone 3-SAT からの帰着案 —
  target = 変数、粗側に長い閉路、正節を辺の台、負節ごとに cone を立て、`A` が充足
  割当のときだけ閉路が生き残る。gadget の well-formedness は未検証)、
  **pointwise(law 固定)は P**。構造: 台-連結 `A` で足りる(支持超グラフが非連結
  なら `N_A` が直和分解し `J` が加法的)、incidence 型の同値類で `2^{#型}` に落ちる、
  しかし instance 非依存の族は全 `2^n − 1` 通り必要(任意の部分集合族が defect
  集合として実現される。単調性・劣モジュラ性は無い)。C3′ は fiber 局所なので
  安価な前検査に使える。
- **R4b 最粗の一様粗化の構造と計算量**(中〜大): 「chart 数 `≤ m` の一様粗化が
  存在するか」の計算量(困難性を予想、根拠なし)。構造の半分は R10。
- 位置: 支線。中心構造ではないので、`Σ_M` による exact 圧縮・最悪 `2^n − 1`・
  指数 frontier(R10)の後に問う。gadget が崩れても本体の価値は落ちない構成に
  する。「任意の部分集合族が欠損集合として実現される」は R19 へ格上げし、立てば
  coNP 困難性はその系になる。CS に可読な問いであり、かつツールの量化域の設計(一様モードの
  実現可能性)に直結する。
- 判定: 多項式アルゴリズム+正当性、または困難性証明のいずれか。

### R5 条件 C の合成閉(残り)

- 内容: 関手性・零欠損射の合成閉・2-out-of-3 は R14 に移した。残るのは**条件 C を
  満たす射の合成閉性**(証明、または反例と正確な追加条件)。C^loc の合成閉は VB 型で
  自明、C 自身は別問で、C3 は fiber 内 face の lift 条項を足して初めて合成する
  可能性がある。否定半分「零 locus は共通粗化でも区間でも閉じない」(R10)と対に
  する。
- 位置: 支線。判定: theorem または反例。「compositional verification」と名乗らない
  (禁忌 4・5)。規模: 小〜中。

### R6 defect の合成計算(R14 に吸収)

- 合成射の `J_A` を各段の核・余核から計算する六項完全列と相殺写像 `χ_A` は
  R14(§1.2 (f))の内容である。blame(どの段で何を失ったか)と差分更新(K1 の
  局所性により、変更 cell の台と交わる `A` の block だけ再計算)は論文の一節と
  ツールの更新則に置く。独立の定理として主要な成果に掲げない。

### R7 最小精細化の合成(MIN-ATLAS-REFINE)

- 内容: 非零の `J_A` と許容 elementary modification(cell の追加・除去、台の
  精細化、reading の精細化、law 保存の分割、lift 追加・fiber 連結・fiber 面追加・
  平行 lift の同一視 = 「茎を殺す手」)を入力に、全 `J_A = 0` にする最小コストの
  変形を合成する。決定問題版、計算量、Lean 検証 checker、edit ごとの更新則。
  下界補題: 一手の編集で `J_A` は各成分 ≤ 1 しか動かないので、零 locus までの
  編集距離 `≥ max_A max(phantom_A, hidden_A)`、かつ `≥ max_A Σ_c dim H¹(Φ_c^A)`。
  R4b(最大粗化)と双対なので問題定義ノートは一本にする。
- 位置: 支線(大)。本計画では**問題定義の固定まで**。起票は Atlas 論文の後。

### R8 完全局所分解 — defect triangle と観測クラスの退化定理(最優先の後継 GOAL)

- 主目標(candidate): cochain 水準で比較写像を `C_A --η_A--> P_A --ε_A--> C'_A`
  (`η_A` = 粗い観測者が自前で再構成した係数と細かい観測の順像の差、`ε_A` = fiber
  topology / higher direct image の寄与)と二段に分け、`D^reobs_A := Cone(η_A)`、
  `D^fiber_A := Cone(ε_A)`、`D^total_A := Cone(ε_A ∘ η_A)` に対する八面体公理の
  exact triangle `D^reobs_A → D^total_A → D^fiber_A → D^reobs_A[1]` を **defect
  triangle** と呼ぶ。三項の意味は再観測欠損 / 総欠損 / fiber 欠損で、phantom
  (unit 側)・hidden(unit 余核+fiber 側)・`d₂`(fiber 欠損が二次整合性へ移る
  connecting 機構)がこの一つの三角形から降りる。主定理として狙うのは
  **観測クラスの退化定理**: 許容される退化 face パターンのどの組合せ条件の下で `d₂`
  が全 `A`・全係数で恒等的に零になるかの特徴づけ(iff が重ければ、`d₂ = 0` となる
  最大の観測クラスと、非零 transgression を生む最小の禁止パターンの対)。
- 系として並ぶもの(旧 1–9): `f_A = edge ∘ H¹(unit)`、`phantom_A = dim ker H¹(unit)`、
  hidden の短完全列 `0 → coker H¹(unit) → hidden_A → ker d₂ → 0`、pure class
  (面は全辺 mapped か全辺退化)= degeneration-safe class での等式
  `hidden_A = dim coker H¹(unit) + Σ_c b₁(Φ_c^A)`、必要条件 C3′、順像の系(unit 側を
  殺した特殊化)、弱化十分条件 C^loc と `C ⊊ C^loc ⊆ 零 locus ⊆ {C3′}`(strictness
  witness は G-107 の C3 witness が候補。C0 / C2 / C4 / C5 の成立は要確認)、誤差
  予算不等式(次元化した系)、混在 face の transgression 定理(R9 で実現)。
- 失敗しうる主張: Leray 列が部分写像+退化宣言の観測クラスで成り立つこと、pure
  class で `d₂ = 0`、退化定理の特徴づけ、C3′、`C ⊊ C^loc`、transgression の実例。
  defect triangle・八面体公理は標準構成であり成果に数えない(§6)。
- なぜ CS の外が気にするか: 「粗 chart 内部の閉路は粗い観測からは見えず、隠蔽
  される類の個数は chart ごとの `H¹` の和以上」「偽の類は集計でなく再観測から
  生まれる」「観測モデルが、局所欠損を一次診断として残すか二次整合性へ送るかを
  決める」の三文が定理で言える。SAGA / G-106 の `H²` 整合性と接続すれば `d₂` は
  「解像度診断の情報が coherence obstruction へ移る」橋になる。
- 既知との関係: 三角形・Leray / Grothendieck は標準理論であり新規性なし。成果は
  Atlas 固有の観測クラス・law 由来係数・退化の意味論の下で、各項と connecting
  morphism がどの診断機構に対応するかにある。
- 位置: 幹寄りの土台。R6 を R14 へ、R9 を後半として吸収。
- 判定: pure class の等式・C3′・transgression の実例が Lean で立つ(今回の論文)。
  退化定理の特徴づけは主定理候補として同カードの上位目標。
- 規模: 系の部分 小〜中、退化定理 中〜大。

### R9 観測モデルの拡張 — 混在 face(R8 の後半を実現するカード)

- 内容: 細 face が粗側の退化 2 単体(`s₀E`、`s₁E`)へ写ること(2 者が同一 chart、
  1 者が外の三者合意)を許す。cochain map の可換は normalized cochain で成立
  (`c(e₀) − c(e₁) + c(e₂) = 0 − c(E) + c(E)`)、hereditary 規則は「boundary の像と
  整合する単体が存在する」に一般化される。`d₂` が生きるので内訳は `− rank d₂` を
  持ち、必要条件 C3′ は「外との合意で吸収されない限り」に条件付きになる。R8 の
  transgression 定理はこのカードで立つ。
- なぜ必要か: 実システムでは混在 face が普通にあり、現行クラスでは捨てるか不正な
  comparison data になる。R1c の前提。
- 位置: 土台補強(G-104 の fixed statement は変えず新カード)。
- 規模: 中。

### R10 安全な解像度の幾何 — No Complete-Shell / No Natural Selector / 指数 frontier

- 内容: 細読み `q'` と粗化の規約(商 nerve の作り方 — 平行辺の同一視、fiber 内辺の
  退化、face の扱い。R1 の抽出規約と同一物)を固定し、`U = {q ≤ q' : 一様}` に
  ついて三段で述べる。
  1. **No Complete-Shell**(candidate): `U` は reading 束上のどの閉包作用素・内部
     作用素の固定点集合としても表現できない。閉包の固定点集合は meet で、内部の
     固定点集合は join で閉じるので、**両方向の witness** が要る。join 側 = (a)
     共通粗化で閉じない(6 角形 `a…f` で `{a, c}` 併合・`{d, f}` 併合はそれぞれ
     `J = (0, 0)`、同時併合で hidden = 1)。meet 側(共通精細化で閉じない)は別途
     witness を固定する。あわせて (b) 区間で閉じない(経路 `a–b–c–d` で `{a, d}`
     併合は phantom = 1、全併合は `(0, 0)`。非空虚版は正方形 + pendant 経路で
     `(0,0) → (1,0) → (0,0)`)、(c) 4-cycle の辺縮約 4 本は `U` の極大元の反鎖、
     (d) よって貪欲併合は失敗する。(a)–(d) は例示スクリプトと同じ線形代数で検算
     済み(証拠ではない)。立てば、抽象解釈の complete shell / 最粗強保存 /
     最粗 lumpable 分割の regime との関係が related work の一文ではなく
     **分離定理**になる。
  2. **No Natural Selector**(candidate): 4-cycle の辺縮約 4 本は自己同型群 `D₄` の
     一軌道をなし、`D₄` の固定点を持たない。同型不変(自己同型同変)な selector
     `selector(M) ∈ MaxSafe(M)` は `Aut(M)` の固定点を選ばねばならないので、この
     witness 上に selector は存在しない。結論は「外部の cost / preference / task
     semantics を足さない限り、Atlas から正準な安全解像度を一つ選ぶことはできない」。
     抽象モデル構成・状態集約・graph coarsening・エージェントの文脈選択・zoom 水準
     選択の全てに同じ形で響く。
  3. **指数 frontier**(candidate): 互いに比較不能な極大安全読みを複数持つ gadget
     を `n` 個直和すると、`J` は成分ごとに直和分解するので、極大安全読みの数は積で
     増える(例: 4 個なら `4^n`)。証明義務: 直和の粗化 poset が積に分解すること —
     成分をまたぐ chart 併合(fiber が非連結になる)を安全でないと示すか、構造を
     尊重する粗化に poset を制限する。
- 三段が揃えば、実務の問い「どこまで粗く読めばよいか」に対し「一点解ではなく
  frontier を返す問題であり、一点を選ぶには理論外の utility が要る」と答えられる。
  R4 より前に置く理由は、計算量が gadget 帰着の成否に依存するのに対し、これらは
  安全解像度空間そのものの幾何から出ることにある。
- なぜ CS の外が気にするか: 抽象解釈には最粗の完全精細化が常にあり、bisimulation
  と lumpability には最粗の正確な商が、十分統計量には最小十分が一意にある。Atlas は
  「一意でない側」に立ち、理由は `H¹` が商で生じも消えもする構造にある。
- 位置: 支線(R4b の構造半分、R5 の否定半分)。§1.2 (c) の正準な意味閉包と対を
  なす(「診断の座標化は正準、安全な解像度の選択は非正準」)。
- 判定: 1 の両方向 witness と 2 の軌道論法が Lean で立つ。「`H¹` は閉包作用素で
  ないから当然」という読みに対しては、失われた束的性質を GRS の証明と対置して
  一文で言う。
- 規模: 1–2 小、3 中。

### R11 検証済み証書パイプライン

- 内容: ArchSig / harness が各 `A` の rank 証書(下界 = 選んだ小行列とその逆行列、
  上界 = 全列を選択列の線形結合で表す係数。行列積だけで検査でき行列式を要しない)
  を出し、Lean が soundness を証明した checker が検査する。Tier 1 = `lake exe`
  (compile 済み、全規模)、Tier 2 = 小部分系で kernel `decide`。検証される範囲は
  presentation から先(nerve → `H¹` → `J_A` と G-104 / G-107 の意味論への接続)で
  あり、source → ArchMap → presentation の観測の忠実性は設計上検証しない(ArchMap
  author の責務。CompCert が C の意味論を信頼するのと同じ位置)。差分テスト
  (ランダム presentation で harness と checker を突合)を実験設計に含める。
- 規律: 「Lean で検査済み」を ArchSig の正当化に転用しない。checker は AAT 側の
  監査器であり、badge は第三の artifact として出す。
- 将来: rank 証書に加えて核の基底・余核の生成系・完全列の可換性・欠損源の内訳の
  証書まで出し、checker が `presentation → cochain map → H¹ → 欠損対象 → 分解` の
  意味論を検証する。検証範囲を presentation 以降に限る限り「verified architecture
  diagnosis」と言える。R18(Excision)と結べば、変更差分に対する増分の検証済み
  診断になる。
- 位置: 土台補強。規模: Lean 2〜4k 行、harness 数百行。リスク: 係数体(R0)、
  `decide` の詰まり、一様モードの `2^|Target|`(R4a)。
- 判定: 実システムの数値(R1)と、checker が harness の誤りを弾いた実績の両方。

### R12 エージェント読解(別 PRD / 別論文)

- 内容: 欠損プロファイルを「規約整合診断に対する解像度安全な読み方針」として使い、
  粗い文脈 / 細い文脈全域 / 欠損プロファイル誘導(粗で読み `J_A ≠ 0` の領域だけ降りる)/
  同一トークン予算の既存戦略(Agentless、HCP、RepoGraph 系)を比較する。正解は
  実コードへの注入(fiber を切って phantom 形、内部三角形を足して hidden 形)で統制。
  予言: FP は phantom 領域、FN は hidden 領域に集中し、`J = 0` 領域では粗 ≈ 細。
  観測起因の誤り(理論が天井を決める)と推論起因の誤り(モデル性能)を分離する
  評価枠。
- 名乗り: 「安全な文脈圧縮の定理」とは言わない(禁忌 4)。venue は AI4SE(ASE /
  FSE / ICSE の枠)。
- 位置: 支線。規模: 中。

### R13 方法論論文(別トラック)

- 内容: 「AI が書いた 35 万行の数学に機械の門を立てた」を論文にする条件は三つ:
  GOAL ごとの statement 改訂数・反証数・cycle 数・指摘分類のデータ、核が弾けない
  欠陥の分類学(空虚な真、structure-field escape、answer-encoding、premise 密輸、
  定義の言い換え)とそれを塞いだ装置(premise ledger、anti-weakening、dullness
  filter、公理監査)、外部が気にする定理が一つあること(= Atlas + R1)。データで
  書けなければ出さない。
- 位置: 支線(執筆トラック)。

### R14 欠損対象・意味閉包・表現・合成(枠の構成と合成定理)

- 内容: §1.2 (a)–(d)・(f)。(i) 比較写像錐 `D_A` の定義と、`J_A` が `H¹` 水準の
  切片であることの明示 (ii) **意味閉包**: 比較データの全 cell `Ω_M` と各 target
  `t` が選ぶ cell 集合 `S_t` から `α_M(A) := ⋃_{t∈A} S_t`、`γ_M(X) := {t | S_t ⊆ X}`
  を置くと `α_M(A) ⊆ X ⟺ A ⊆ γ_M(X)`(Galois 接続 `α_M ⊣ γ_M`)、
  `cl_M := γ_M ∘ α_M` は有限閉包作用素、台署名半束 `Σ_M ≅ Fix(cl_M) ≅ im α_M`、
  `D_A ≃ D_{cl_M(A)}`。`Σ_M` は「comparison geometry を保存する意味商の中で最粗」
  であり、診断に必要な意味の区別だけを残した正準な最小座標系になる (iii) 表現
  `D_L ≅ ⊕_λ D_{cl_M(A_λ)}`、`J_L = Σ_λ J_{A_λ}`、指示 law による実現(G-104 の
  block 直和分解と G-107 (i) の錐水準への持ち上げ)。普遍性(直和加法的な law
  診断不変量は `Σ_M` 上の値から一意に復元される)は candidate (iv) `Σ_M^op` 上の
  欠損加群 `Phantom_u / Hidden_u` と比較写像の自然変換性 (v) 解像度合成の六項
  完全列と相殺写像 `χ_A`、合成式、零欠損射の合成閉と 2-out-of-3 (vi) 多段精細化
  `q₀ ≤ … ≤ q_n` では `D_A(q₀, q_n)` に隣接比較 `D_A(q_{i−1}, q_i)` からの filtration
  が入り、`χ_A` はその三段ケースである(一般の multiresolution は R16)。
- 性格: (i)–(iv)・(vi) と (v) の完全列は構成と命題であり失敗しえない。定理として
  数えるのは (v) の合成式の semantic 化(相殺写像の解釈)と、その witness(R10 の
  非単調例が相殺の発火例であること)、(iii) の普遍性のみ。
- 位置: 幹寄りの土台(reading 圏の関手化。R5 の関手性・R6 を吸収)。
- 判定: Lean で (ii)(iii)(v) が立ち、R1 の P7・P9 と接続する。
- 規模: 小〜中。

### R15 概念方向の Mayer–Vietoris(局所大域定理)

- 内容: §1.2 (g)。二領域版の短完全列と、比較写像を縦に置いた錐の長完全列。
  `J_A = J_B = 0 ∧ J_{A∪B} ≠ 0` の源を `N_A ∩ N_B` 上の連結射として同定する定理。
  R3-w の交互多角形を sharp witness として取り込む。多領域の MV スペクトル系列と
  解像度方向との二重複体は frontier。
- なぜ CS の外が気にするか: 「関心事を分けると見えない欠損は、関心事の交差に住む
  貼り合わせデータから生じる」が AAT の主題の概念方向版として一文で言える。
- 位置: 支線(R3-w を吸収)。判定: 連結射の同定が Lean で立ち、R1 の P10 に接続
  する。規模: 小〜中。

### R16 Interchange / Multiresolution(次の大定理候補。別論文)

- 内容: (i) 解像度列 `q₀ ≤ … ≤ q_n` の総比較の欠損対象に隣接比較からの filtration を
  入れ、`E₁^{i,*} ≃ H*(D_A(q_{i−1}, q_i)) ⇒ H*(D_A(q₀, q_n))` 型のスペクトル系列を
  立てる(higher differential = ある粒度で生じた欠損が後続の粒度変更でどの欠損と
  相殺されるか。`χ_A` はその最初の非自明ケース)。(ii) 意味領域の被覆 `{A_i}` と
  解像度方向を一つの二重複体 `B^{p,q} = ⊕ D^q_{A_{i₀}∩…∩A_{i_p}}` に並べ、意味の
  貼り合わせを先に取る経路と解像度欠損を先に取る経路が同じ total 欠損に収束する
  条件(**Interchange**: 「関心事で分けてから zoom するのと、zoom してから関心事で
  分けるのは、いつ同じ診断を与えるか」)を示し、破れる場合は差を higher differential
  として残す。
- 位置: 支線(SHIGURE / 係数 base change / G-106 と接続)。今回の論文の完成条件には
  入れない。規模: 大。

### R17 Support-width の算法(正の計算可能性。candidate)

- 内容: `Σ_M` は target–cell の台 incidence から得られる近傍和の族なので、generic
  treewidth より先に、台 incidence グラフの boolean-width / neighborhood-union width
  型の既存パラメータで状態数を制御できるかを調べる。候補 statement: 台 incidence
  グラフの分解幅 `b` と nerve 側の separator 幅 `τ` に対し、一様性と全欠損源を
  `f(b, τ) · poly(|M|)` で計算する(分解の separator ごとに署名状態を有限個保持し、
  台の和を動的計画で合成、各状態上に rank 情報を局所行列として保持、root で全
  `A`-欠損を復元)。概念台の hypergraph が join-tree / 非輪状 / 有界 hypertree-width
  を持つ場合に R15 の Mayer–Vietoris で欠損を局所計算できるかも問う。
- 意味: R3 / R10 / R4 が負の側、これが正の側。「無制限の意味的相互作用は非局所で
  困難だが、台の幾何の幅が小さい系では exact な診断が tractable」という二分法に
  なる。R1 / R11 の一様モードの実現可能性にも直結する。
- 位置: 支線。Atlas 固有のパラメータを新造する前に既存 width で試す。規模: 中〜大。

### R18 Excision と増分更新(candidate)

- 内容: presentation の変更 `M → M'` が cell 部分複体 `K` と意味台 `S` に限られる
  とき、relative cone `E_A(M', M) := Cone(D_A(M) → D_A(M'))` について、
  `A ∩ S = ∅ ⇒ E_A ≃ 0`(K1 の局所性から大半は定義的)、影響する台署名は `S` と
  交わる正準な ideal に限られる、欠損の変化量は relative complex の rank / Betti
  data で制御される、影響外の証書・核の基底・完全列 witness は再利用できる。対に
  なる一文は「**判定は大域的だが、判定値の変化は台-局所である**」(R3 との対)。
- 接続: R11 と結べば、ArchSig / harness が変更台 `S`・影響署名・局所 rank 更新・
  再利用証書・新しい欠損の provenance を出し、Lean checker がその局所更新だけを
  検証する「変更差分に対する verified incremental architecture diagnosis」になる。
  R7 の編集下界も relative defect の応用として再配置できる(どの変形がどの
  relative defect を殺すか、一手で消せる rank の上限)。
- 位置: 支線(tooling と R11 の柱)。規模: 中。

### R19 Defect-Locus Realization(high-upside frontier。別論文)

- 内容: R4a に埋まっている「任意の部分集合族が欠損集合として実現される」を独立の
  定理候補に上げる。段階: Stage A 任意の反鎖 `𝒜 ⊆ 2^Target` を
  `Min{A | J_A ≠ 0}` として実現 / Stage B 任意の単調 Boolean 関数 `F` で
  `J_A ≠ 0 ⟺ F(A) = 1` / Stage C 任意の Boolean 回路 / CNF から多項式サイズの
  Atlas instance(coNP 困難性は系)。立てば、欠損 locus は単調でも劣モジュラでも
  なく、貪欲精細化に一般保証は無く、最小の欠損台は指数個になりえ、
  `|Σ_M| = 2^|Target| − 1` が最悪例として実現され、有界幅の観測者は完全でない、が
  一つの表現完全性定理から降りる。
- リスク: 高。K0 / K1・比較射・nerve の well-formedness・law 由来台の制約の下で
  どこまで任意パターンを符号化できるかは未検証。完成条件には入れず、別カード候補。
- 位置: 支線(R3-w・R10 frontier・R4a・`Σ_M` 最悪サイズを束ねる可能性)。規模: 大。

## 5. 優先順位と配分

- 優先順位: **R0 > R2 > R1a(並走)> R14 > R8(最小成員)> R10(No Complete-Shell /
  No Natural Selector)> R3-w > R15 > R18(基本部分)> R11 > R3-r > R9 > R1c > R17 >
  R4a > R19 > R16 > R4b > R5 ≫ R7**。R12・R13 は別トラック。R1a は Codex 並走で
  理論項目と同時に進む。
- **論文の形と着手時期**: Atlas 論文は一本で、**大定理版の最小構成**で閉じる。§6 の
  Main theorem の四クラスには、それぞれ小さくて本物の成員がある — (1) 鋭い構造
  定理 = pure class の等式+必要条件 C3′+混在 face の最小禁止パターン(`d₂ ≠ 0` の
  実例。「最大の degeneration-safe class と最小禁止パターンの対」)、(2) 正準 /
  非正準 = 意味閉包 `cl_M`+No Complete-Shell(両方向 witness)+No Natural Selector、
  (3) 無限族 = 幅の族(交互 `(k+1)` 多角形、全 `k`)または半径の族
  `T_{2n}` vs `T_n ⊔ T_n`、(4) 正の算法 = Excision の基本部分または R15 による
  join-tree の局所計算。これに Foundation(R14 (i)–(iv)・R14 (v) 合成・R15 二領域版・
  R11 最小構成)、Lean、実測(R1a、P1–P10)、差分と translation 二本(R2)、応用節を
  合わせて一本にする。「大」は個々の定理の深さではなく、一つの対象から四クラスの
  定理が出て実測に降りることで立つ。重い成員 — `d₂ ≡ 0` の完全な特徴づけ、`(r, k)`
  同時分離、指数 frontier、Realization(R19)、support-width の動的計画(R17)、
  Interchange(R16)、coNP 完全性(R4a)— は別の問いとして別論文にし、約束しない。
  **着手は Gr4 完了後**(Gr4 は G-110 一枚では閉じず、G-110 と後続 n 枚のカードで成る)、期間の目安は 1 か月。候補題「Atlas: An Exact
  Resolution Calculus for Software Architecture Diagnostics」は証明の後に決める
  (禁忌 4)。
- 抽象核は degree-parametric にしておく(`J_A^i`、`Safe_[a,b]`)。今回の論文の実証は
  `H¹` に集中し、`H⁰` = 切断 / 大域整合、`H²` = 整合性の意味づけは AAT 既存の
  ものを使う。混在 face の `d₂` は `H¹` 欠損が `H²` 整合性へ移る最初の例。
- 係数: 今回の論文は ℚ 固定(現行 Lean 資産と整合し、証明コストが最小)。整数係数の
  比較写像錐 `D_{A,ℤ}` と `D_{A,k} ≃ D_{A,ℤ} ⊗^L_ℤ k`、ℚ と F₂ の差 = torsion、
  係数の選択で安全性が変わる素数 = determinantal / Fitting locus、は次カード
  (n1005 の係数 base change・jump-locus の相対幾何と接続)。
- 後継 GOAL の単位: R14、R8、R10、R15、R3、R9、R17、R18、R4a、R19、R16、R5 を
  それぞれ 1 カード(採番は起票時)。G-104 / G-107 の fixed statement は変更しない。
  active GOAL と並走可能かはコスト基準で裁定する。
- 論文A との関係: R1 は論文A 実証節計画の第三段と同一対象であり、Atlas 論文が
  先行して測り、論文A はその結果を参照する。
- 打ち切りの条件: R2 の判定で実証研究が無く、R1 の欠損プロファイルが全域非零
  なら、Atlas は「AAT の測定器の校正理論」として正確に主張し、CS への接点は
  exactness と「局所 ⟹ 大域」族の差分表のみで戦う。全域零なら method 水準と他系へ
  進む。どちらの結果も資産として記録する。
- **計画の凍結**: 本ノートの補強項目はこの版で固定する。以後の追加・格上げは
  カード起票時の statement 固定と、論文の執筆で行う(レビューの往復を飽和させ
  ない。研究の全体目標の禁忌 9)。

## 6. 判定規準 — 二段のゲート

**最低条件(「CS に届いた」)**。次の三つが揃ったとき、Atlas は AAT の外に貢献した
と言う。

1. §1.1 の統一表の各行に、§3 の外部先行との差分が肯定形で書けている(R2)。
2. 実システムで欠損プロファイルが領域ごと・欠損源ごとに異なる値を取り、phantom と
   hidden の両方に実例がある(R1a)。概念またぎ(P3)と打ち消し例は必答の問いと
   して報告する。
3. R8 の完全局所分解(少なくとも必要条件 C3′)、R10 の非一意性、R15 の連結射の
   同定、R3 の分離族のいずれかが定理として立っている(R3-w 単独は補助定理と数え、
   R4a は立てば加点)。

**大定理の完成条件(ジャーナルの主定理として)**。二階建てにする。

- **Foundation complete**(構成。失敗しえない): 比較写像錐 `D_A`、意味の Galois
  接続と `Σ_M`、law block 表現、defect triangle、pairwise(と多段の filtration)
  合成、検証済み checker。
- **Main theorem complete**(失敗しうる主張。少なくとも次の四本):
  1. **鋭い構造定理**: `d₂ = 0` の最大観測クラス / 禁止パターンの特徴づけ、または
     同等に鋭い退化定理(R8)。
  2. **正準 / 非正準の定理**: 意味側の正準閉包(R14 (ii))と、解像度側の No
     Complete-Shell / No Natural Selector(R10)。
  3. **無限族の定理**: `(r, k)` 非局所性(R3)、指数 frontier(R10)、欠損 locus の
     実現(R19)の少なくとも一つ。
  4. **正の算法 / 応用定理**: support-width の tractability(R17)、join-tree 定理、
     Excision / 増分更新(R18)のいずれか。
- そのうえで Lean(中心定理の機械検証)と実測(複数実システムで完全列の各項の
  測定。R1a、R11)を必須とする。

揃えば Atlas は「AAT の測定器を校正する補助定理」ではなく、architecture 診断の
exact resolution calculus として独立に読める。最低条件だけなら「校正理論」として
正確に主張し、それ以上を名乗らない。論文は Foundation と Main の最小成員(§5)で
閉じ、重い成員は別の問いとして別論文にする。

**失敗しうる主張と構成の区別**(禁忌 5)。主定理は前者から選ぶ。

| 構成・命題(失敗しえない) | 定理(失敗しうる) |
| --- | --- |
| 比較写像錐 `D_A`、Galois 接続と閉包 `cl_M`、`Σ_M ≅ Fix(cl_M)`、表現 `D_L ≅ ⊕ D_{A_λ}`、欠損加群と自然変換、defect triangle(八面体公理)、六項完全列、2-out-of-3、関手性、多段 filtration、rank–nullity の打ち消し、Excision の `A ∩ S = ∅` 部分 | Leray 列が部分写像+退化宣言の観測クラスで成り立つこと、pure class の `d₂ = 0`、退化定理の特徴づけ、必要条件 C3′、transgression の実例、`C ⊊ C^loc`、合成式の semantic 化の witness、表現の普遍性、No Complete-Shell(両方向 witness)、No Natural Selector、指数 frontier、MV 連結射の同定、`(r, k)` 分離族、support-width の tractability、Excision の rank 制御、欠損 locus の実現、Interchange、coNP 困難性 |

本計画の停止規則は研究の全体目標の禁忌に従う: 比喩に定理の代役をさせない(4)、
関手性・合成閉・rank–nullity のような言い換えに定理の名を与えない(5)、`J_A` と
そこから導かれる整数(幅・`χ_A`)以外の数を並べない(6)、計測に降りない定理を
積まない(7)、レビュー指摘ゼロ・補強項目の増殖を目標にしない(9)。

## 7. 説明素材 — 還元の最小例

[`research/experiments/atlas-reduction-toy/depth_map_toy.py`](../../research/experiments/atlas-reduction-toy/depth_map_toy.py)
は、還元(G-107 (i))を外部ライブラリなしの ℚ 線形代数で見せる最小例である
(証拠ではない。定理の正本は G-107 report と Lean)。

- 系 A: 4 サービス 11 モジュール 3 概念。配線だけから領域ごとの
  `(phantom, hidden)` を出し、観点(law)を 4 種入れて直接計算しても欠損プロファイル
  の値の和に分解されること、各領域 `A` が指示 law の 1 クラスとして実現できる
  ことを確認する。
- 系 B: サービス内部の閉路が 2 概念にまたがる変種。単独概念の領域では欠損が
  消え、2 概念の和集合で現れる — `A` が集合で効くことの例示(§1.4 の 2)。
- 簡略化: 概念は両水準で同じ(canonical factor は恒等)、サービス内部の辺は
  すべて退化、混在 face なし、pullback は辺の向きが揃う前提で符号なし。計算の
  形は本物と同じで、細側の領域が `π⁻¹(A)` になる点と、一般の分割では符号付き
  pullback が要る点が異なる。
- R3-w・R10 の witness(交互多角形、6 角形の併合、経路の距離 3 併合、4-cycle の
  辺縮約)は同じ線形代数で再導出できる。カード起票時に Lean の witness として
  固定する。

「law の直接計算 = 値クラスの和」は表現命題(§1.2 (b))の最小発火例でもある。
統一表の各行を最小例で動かして見せる用途(論文の付録・記事・登壇)に限る。

## 8. 範囲・規律

- 本ノートは正本ではない。G-104 / G-107 の事実関係は各 report を、証明義務を
  持つ statement の固定はカード起票時を正とする。
- §1.2・§4 の R3 / R4 / R8 / R10 / R14–R19 に書いた数学(欠損対象、意味閉包と
  `Σ_M`、表現、Leray 分解と defect triangle、退化定理、必要条件 C3′、C^loc、
  transgression、六項完全列と `χ_A`、MV、No Complete-Shell / No Natural Selector、
  指数 frontier、`T_n` 族、coNP 完全性、support-width、Excision、欠損 locus の実現、
  Interchange)はすべて candidate であり、手証明と
  有限例の機械検算しか無い。Lean で立つまで、本文・記事・カードの statement に
  事実として書かない。
- 錐の次数混合に注意: `J_A` は `H¹` 水準の切片であり、錐コホモロジーの次元その
  ものではない(§1.2 (a))。
- 本計画は G-104 / G-107 の fixed statement を変更しない。補強はすべて後継
  GOAL・PRD・論文の側で行う。
- 命名: Atlas は G-104 の固有名であり、正式名は維持する。観測の枠への置き直しは
  定理名の変更を伴わない。
- 隊列は指針であり、採否・順序はユーザー裁定を正とする。運用上の状態は GOAL
  カードと tracking Issue が正本である。
